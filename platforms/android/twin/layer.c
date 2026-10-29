// The app's layers on the compositor
// ==================================

// Lean publishes the painted extent and holdLine plane with each frame.
// Each vsync applies the compiled Lean translation/fill helpers to the OS
// sample; new pixels may be late without stopping this composition.

#include "layer.h"
#include "../../native/thread.h"
#ifdef LQ_LAYER_TEST
#include "../../../tests/app/layer_stub.h"
#else
#include "activity.h"
#include "scroll.h"

#include <android/choreographer.h>
#include <android/hardware_buffer.h>
#include <android/log.h>
#include <android/looper.h>
#include <android/surface_control.h>
#include <sys/system_properties.h>
#endif
#include <math.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#define BL_BUFS 3

typedef enum { BL_FREE, BL_HELD, BL_NEXT, BL_SHOWN } BlState;

typedef struct {
  AHardwareBuffer* buf;
  BlState          state;
  int              fence;
  uint32_t         y;
  int64_t          asked;  // when Lean read the offset it drew at, ns
} BlBuf;

typedef struct {
  ASurfaceControl* sc;
  BlBuf            bufs[BL_BUFS];
  uint32_t         w, h, stride;
  int              shown;
} BlLayer;

static pthread_mutex_t bl_mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t  bl_cv = PTHREAD_COND_INITIALIZER;
static BlLayer         bl_l[4];
static ANativeWindow*  bl_win;
static bool            bl_running;
static _Atomic uint32_t bl_content_h, bl_view_h;
static _Atomic float bl_yf;
static _Atomic bool bl_has_y;
static uint32_t bl_place[LQ_PLACEMENT_WORDS], bl_next_place[LQ_PLACEMENT_WORDS];
static bool bl_ready, bl_published;
// A geometry publication remains outstanding until its compositor callback,
// not merely until vsync consumes it. Lean retains only accepted contexts.
static bool bl_awaiting_completion;
static uint64_t bl_transaction, bl_completed_transaction, bl_waiting_transaction;
static uint64_t bl_generation;
static _Atomic uint64_t bl_view;
uint64_t bl_view_id(void) { return atomic_load(&bl_view); }
uint32_t bl_frame_id(void) { return (uint32_t)bl_view_id(); }
static uint64_t bl_seq;

// Vsync thread
// ------------

typedef struct {
  int old[4];
  uint64_t view;
  uint64_t transaction, generation;
} BlDone;

// A transaction that showed a new buffer completed: the one it replaced
// is free once its release fence fires (AHardwareBuffer_lock waits on it).
static void bl_complete(void* ctx, ASurfaceTransactionStats* stats) {
  BlDone* d = ctx;
  pthread_mutex_lock(&bl_mu);
  if (d->generation == bl_generation) {
    for (int k = 0; k < 4; k++) {
      BlLayer* l = &bl_l[k];
      if (d->old[k] >= 0 && l->sc != NULL) {
        int fd = ASurfaceTransactionStats_getPreviousReleaseFenceFd(stats, l->sc);
        l->bufs[d->old[k]].fence = fd;
        l->bufs[d->old[k]].state = BL_FREE;
      }
    }
    // Callbacks may arrive after later animation callbacks or window recreation.
    // Retire every matching buffer, but never stamp an older displayed context.
    if (d->transaction > bl_completed_transaction) {
      atomic_store(&bl_view, d->view);
      bl_completed_transaction = d->transaction;
    }
    if (bl_awaiting_completion && d->transaction == bl_waiting_transaction)
      bl_awaiting_completion = false;
  }
  pthread_cond_broadcast(&bl_cv);
  pthread_mutex_unlock(&bl_mu);
  free(d);
}

static void bl_show(ASurfaceTransaction* t, BlLayer* l, const uint32_t* p) {
  if (p[1] <= p[0]) {
    ASurfaceTransaction_setVisibility(t, l->sc, ASURFACE_TRANSACTION_VISIBILITY_HIDE);
    return;
  }
  ARect src = {0, p[0], (int32_t)l->w, p[1]};
  ARect dst = {0, p[2], (int32_t)l->w, p[3]};
  ASurfaceTransaction_setGeometry(t, l->sc, &src, &dst, 0);
  ASurfaceTransaction_setVisibility(t, l->sc, ASURFACE_TRANSACTION_VISIBILITY_SHOW);
}

static void bl_vsync(int64_t ns, void* data);

static void bl_tick(void) {
  AChoreographer_postFrameCallback64(AChoreographer_getInstance(),
    (AChoreographer_frameCallback64)bl_vsync, NULL);
}

// The layer's newest buffer to show this vsync, if Lean handed one over:
// set in the transaction, the one it replaces freed on completion.
static int bl_take(ASurfaceTransaction* t, BlKind k, BlDone* d) {
  BlLayer* l    = &bl_l[k];
  int      next = -1;
  for (int i = 0; i < BL_BUFS; i += 1) {
    if (l->bufs[i].state == BL_NEXT) {
      next = i;
    }
  }
  if (next < 0) {
    return -1;
  }
  d->old[k] = l->shown;
  ASurfaceTransaction_setBuffer(t, l->sc, l->bufs[next].buf, l->bufs[next].fence);
  l->bufs[next].fence = -1;
  l->bufs[next].state = BL_SHOWN;
  l->shown            = next;
  return next;
}

static void bl_vsync(int64_t ns, void* data) {
  (void)data;
  uint32_t now;
  float nowf;
  if (bs_vsync(atomic_load(&bl_content_h), atomic_load(&bl_view_h), ns, &now, &nowf)) {
    atomic_store(&bl_yf, nowf);
    atomic_store(&bl_has_y, true);
  }
  pthread_mutex_lock(&bl_mu);
  if (bl_l[BL_LIST].sc != NULL && (bl_ready || bl_published)) {
    ASurfaceTransaction* t = ASurfaceTransaction_create();
    int32_t sample = atomic_load(&bl_has_y) ? (int32_t)lroundf(atomic_load(&bl_yf))
      : (int32_t)bl_next_place[15];
    BlDone* done = malloc(sizeof *done);
    *done = (BlDone){ .old = {-1, -1, -1, -1},
      .transaction = ++bl_transaction, .generation = bl_generation };
    if (bl_ready) {
      memcpy(bl_place, bl_next_place, sizeof bl_place);
      for (int k = 0; k < 4; k++) bl_take(t, k, done);
      for (int k = BL_TOP; k <= BL_BOT; k++)
        if (bl_l[k].shown >= 0) bl_show(t, &bl_l[k], bl_place + 4*k);
      bl_ready = false;
      bl_published = true;
      bl_awaiting_completion = true;
      bl_waiting_transaction = done->transaction;
    }
    uint32_t r[4];
    lq_slide_rect(bl_place, sample, 0, r);
    if (bl_l[BL_LIST].shown >= 0) bl_show(t, &bl_l[BL_LIST], r);
    lq_slide_rect(bl_place, sample, 1, r);
    if (bl_l[BL_HOLD].shown >= 0) bl_show(t, &bl_l[BL_HOLD], r);
    done->view = bl_place[16] | ((uint64_t)lq_slide_delta(bl_place[22], bl_place[15], sample) << 32);
    ASurfaceTransaction_setOnComplete(t, done, bl_complete);
    ASurfaceTransaction_apply(t);
    ASurfaceTransaction_delete(t);
  }
  bl_seq++;
  pthread_cond_broadcast(&bl_cv);
  pthread_mutex_unlock(&bl_mu);
  bl_tick();
}

static void* bl_run(void* arg) {
  lq_slide_thread_init();
  ALooper_prepare(0);
  bl_tick();
  for (;;) {
    ALooper_pollOnce(-1, NULL, NULL, NULL);
  }
  return NULL;
}

// Lean's side
// -----------

void bl_start(bool predict) {
  pthread_mutex_lock(&bl_mu);
  (void)predict;
  if (!bl_running) {
    lq_slide_warm();  // Called by the Lean frame thread before spawning vsync.
    bl_running = true;
    pthread_t t;
    pthread_create(&t, NULL, bl_run, NULL);
    pthread_detach(t);
  }
  pthread_mutex_unlock(&bl_mu);
}

void bl_scroll_needs(uint32_t content_h, uint32_t view_h) {
  atomic_store(&bl_content_h, content_h);
  atomic_store(&bl_view_h, view_h);
}

bool bl_scroll_y(float* y) {
  if (!atomic_load(&bl_has_y)) return false;
  *y = atomic_load(&bl_yf);
  return true;
}

// Called after all dirty buffers have been staged; pixels and their
// placement are adopted together in the next compositor transaction.
void bl_geometry(const uint32_t* place) {
  pthread_mutex_lock(&bl_mu);
  memcpy(bl_next_place, place, sizeof bl_next_place);
  bl_ready = true;
  pthread_mutex_unlock(&bl_mu);
}

static void bl_alloc(BlLayer* l, uint32_t w, uint32_t h) {
  for (int i = 0; i < BL_BUFS; i += 1) {
    if (l->bufs[i].buf != NULL) {
      AHardwareBuffer_release(l->bufs[i].buf);
      l->bufs[i].buf = NULL;
    }
    AHardwareBuffer_Desc d = { w, h, 1, AHARDWAREBUFFER_FORMAT_R8G8B8X8_UNORM,
      AHARDWAREBUFFER_USAGE_CPU_WRITE_OFTEN | AHARDWAREBUFFER_USAGE_GPU_SAMPLED_IMAGE
        | AHARDWAREBUFFER_USAGE_COMPOSER_OVERLAY, 0, 0, 0 };
    if (AHardwareBuffer_allocate(&d, &l->bufs[i].buf) != 0) {
      __android_log_print(ANDROID_LOG_ERROR, "lean", "cannot allocate a %ux%u buffer", w, h);
      l->bufs[i].buf = NULL;
      continue;
    }
    AHardwareBuffer_describe(l->bufs[i].buf, &d);
    l->stride        = d.stride;
    l->bufs[i].state = BL_FREE;
    l->bufs[i].fence = -1;
  }
  l->w     = w;
  l->h     = h;
  l->shown = -1;
}

void bl_attach(ANativeWindow* win) {
  static const char* names[4] = { "lean list", "lean header", "lean composer", "lean placeholder" };
  pthread_mutex_lock(&bl_mu);
  if (win != bl_win) {
    bl_generation++;
    bl_ready = bl_published = bl_awaiting_completion = false;
    atomic_store(&bl_view, 0);
    for (int k = 0; k < 4; k += 1) {
      BlLayer* l = &bl_l[k];
      if (l->sc != NULL) {
        ASurfaceControl_release(l->sc);
      }
      l->sc    = ASurfaceControl_createFromWindow(win, names[k]);
      l->shown = -1;
      for (int i = 0; i < BL_BUFS; i += 1) {
        if (l->bufs[i].state != BL_HELD) {
          l->bufs[i].state = BL_FREE;
        }
      }
      ASurfaceTransaction* t = ASurfaceTransaction_create();
      ASurfaceTransaction_setZOrder(t, l->sc, k == BL_HOLD ? 0 : k + 1);
      ASurfaceTransaction_apply(t);
      ASurfaceTransaction_delete(t);
    }
    bl_win = win;
  }
  pthread_mutex_unlock(&bl_mu);
}

// Waits on the condition until it is signalled or ms have passed since
// `from` (a CLOCK_REALTIME time, the condition's clock); false on timeout.
// Every wait of Lean's thread here is bounded: while the screen is off or
// locked over the app, vsyncs stop and the compositor releases nothing,
// and an unbounded wait would hang the app for good.
static bool bl_wait_until(const struct timespec* from, int ms) {
  struct timespec dl = *from;
  dl.tv_nsec += (long)(ms % 1000) * 1000000L;
  dl.tv_sec  += ms / 1000 + dl.tv_nsec / 1000000000L;
  dl.tv_nsec %= 1000000000L;
  return pthread_cond_timedwait(&bl_cv, &bl_mu, &dl) == 0;
}

static bool bl_late(const struct timespec* from, int ms) {
  struct timespec now;
  clock_gettime(CLOCK_REALTIME, &now);
  int64_t d = (int64_t)(now.tv_sec - from->tv_sec) * 1000 + (now.tv_nsec - from->tv_nsec) / 1000000;
  return d >= ms;
}

// No buffer of the next frame can enter BL_NEXT while the previous
// publication waits for vsync or its presentation callback. The latter
// also bounds how many accepted Lean contexts can precede displayed input.
// A timeout rejects this attempt; it does not replace the pending frame.
bool bl_begin(void) {
  struct timespec t0;
  clock_gettime(CLOCK_REALTIME, &t0);
  pthread_mutex_lock(&bl_mu);
  while ((bl_ready || bl_awaiting_completion) && bl_l[BL_LIST].sc != NULL && !bl_late(&t0, 200))
    bl_wait_until(&t0, 200);
  bool ok = !bl_ready && !bl_awaiting_completion && bl_l[BL_LIST].sc != NULL;
  pthread_mutex_unlock(&bl_mu);
  return ok;
}

// An incomplete frame is never published. The caller retries all layers.
void bl_abort(void) {
  pthread_mutex_lock(&bl_mu);
  for (int k = 0; k < 4; k++)
    for (int i = 0; i < BL_BUFS; i++)
      if (bl_l[k].bufs[i].state == BL_NEXT) bl_l[k].bufs[i].state = BL_FREE;
  pthread_mutex_unlock(&bl_mu);
}

bool bl_present(BlKind k, const uint32_t* pix, uint32_t w, uint32_t h, uint32_t y,
  uint32_t extend) {
  struct timespec t0;
  clock_gettime(CLOCK_REALTIME, &t0);
  BlLayer* l = &bl_l[k];
  pthread_mutex_lock(&bl_mu);
  if (l->sc == NULL) {
    pthread_mutex_unlock(&bl_mu);
    return false;
  }
  if (w != l->w || h + extend != l->h) {
    bl_alloc(l, w, h + extend);
  }
  // At most one frame of a layer waits for a vsync: Lean goes at the
  // display's pace. With no vsync for 200 ms, the waiting frame (never
  // shown) is overwritten by this one instead.
  int i = -1;
  for (bool waiting = true; waiting && l->sc != NULL;) {
    waiting = false;
    for (int j = 0; j < BL_BUFS; j += 1) {
      if (l->bufs[j].state == BL_NEXT) {
        waiting = true;
        if (bl_late(&t0, 200)) {
          i = j;
          waiting = false;
        }
      }
    }
    if (waiting) {
      bl_wait_until(&t0, 200);
    }
  }
  // A free buffer, waiting at most 200 ms for the compositor to release one.
  while (i < 0 && l->sc != NULL) {
    for (int j = 0; j < BL_BUFS && i < 0; j += 1) {
      if (l->bufs[j].state == BL_FREE && l->bufs[j].buf != NULL) {
        i = j;
      }
    }
    if (i < 0) {
      if (bl_late(&t0, 400)) {
        break;
      }
      bl_wait_until(&t0, 400);
    }
  }
  if (i < 0) {
    pthread_mutex_unlock(&bl_mu);
    return false;
  }
  l->bufs[i].state = BL_HELD;
  int fence = l->bufs[i].fence;
  l->bufs[i].fence = -1;
  uint32_t stride = l->stride;
  pthread_mutex_unlock(&bl_mu);
  void* bits = NULL;
  bool submitted = false;
  if (AHardwareBuffer_lock(l->bufs[i].buf, AHARDWAREBUFFER_USAGE_CPU_WRITE_OFTEN, fence, NULL,
      &bits) == 0) {
    for (uint32_t r = 0; r < h + extend; r += 1) {
      uint32_t from = r < h ? r : h - 1;
      memcpy((uint32_t*)bits + (size_t)r * stride, pix + (size_t)from * w, (size_t)w * 4);
    }
    int32_t done = -1;
    AHardwareBuffer_unlock(l->bufs[i].buf, &done);
    pthread_mutex_lock(&bl_mu);
    l->bufs[i].fence = done;
    l->bufs[i].y     = y;
    l->bufs[i].asked = 0;
    l->bufs[i].state = BL_NEXT;
    submitted = true;
    pthread_mutex_unlock(&bl_mu);
  } else {
    pthread_mutex_lock(&bl_mu);
    l->bufs[i].state = BL_FREE;
    pthread_mutex_unlock(&bl_mu);
  }
  return submitted;
}

bool bl_idle(void) {
  struct timespec t0;
  clock_gettime(CLOCK_REALTIME, &t0);
  pthread_mutex_lock(&bl_mu);
  uint64_t seq = bl_seq;
  // A vsync's wait, at most 100 ms (none come while the screen is off).
  while (bl_running && seq == bl_seq && bl_l[BL_LIST].sc != NULL && !bl_late(&t0, 100)) {
    bl_wait_until(&t0, 100);
  }
  bool on = bl_running && bl_l[BL_LIST].sc != NULL;
  pthread_mutex_unlock(&bl_mu);
  return on;
}

void bl_window_gone(void) {
  pthread_mutex_lock(&bl_mu);
  for (int k = 0; k < 4; k += 1) {
    BlLayer* l = &bl_l[k];
    if (l->sc != NULL) {
      ASurfaceTransaction* t = ASurfaceTransaction_create();
      ASurfaceTransaction_reparent(t, l->sc, NULL);
      ASurfaceTransaction_apply(t);
      ASurfaceTransaction_delete(t);
      ASurfaceControl_release(l->sc);
      l->sc = NULL;
    }
    l->shown = -1;
    for (int i = 0; i < BL_BUFS; i += 1) {
      if (l->bufs[i].state != BL_HELD) {
        l->bufs[i].state = BL_FREE;
      }
    }
  }
  bl_win = NULL;
  bl_generation++;
  bl_ready = bl_published = bl_awaiting_completion = false;
  atomic_store(&bl_view, 0);
  pthread_cond_broadcast(&bl_cv);
  pthread_mutex_unlock(&bl_mu);
}
