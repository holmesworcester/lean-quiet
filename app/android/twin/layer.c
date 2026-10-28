// The frame as a compositor-slid layer
// ====================================

// iOS's arrangement on Android: the OS scrolls, Lean draws. A thread of
// its own wakes at every vsync (AChoreographer), runs the scroller
// (scroll.c) to that vsync, and shows Lean's newest frame in a child
// surface (ASurfaceControl) cropped and placed for the difference between
// the offset it was drawn at and the vsync's offset: the compositor moves
// it, so motion is even whether or not Lean finished a frame in time.
// Lean draws ahead during a fling: Window.native_scroll answers the offset
// predicted for when its frame will be placed (the vsync offset's rate
// times the measured lead from answer to placement, at most two vsyncs,
// kept short of where the fling stops), so a new frame needs little
// sliding. Rows a slide
// still uncovers show the window behind (the frame's background colour)
// until Lean's next frame. Lean's thread hands finished frames over (bl_present) in a
// pool of buffers, each reused only once the compositor released it.

#include "layer.h"
#include "scroll.h"

#include <android/choreographer.h>
#include <android/hardware_buffer.h>
#include <android/log.h>
#include <android/looper.h>
#include <android/surface_control.h>
#include <sys/system_properties.h>
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

static pthread_mutex_t  bl_mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t   bl_cv = PTHREAD_COND_INITIALIZER;
static BlBuf            bl_bufs[BL_BUFS];
static uint32_t         bl_w, bl_h, bl_stride;
static ASurfaceControl* bl_sc;
static ANativeWindow*   bl_win;
static int32_t          bl_ox, bl_oy;
static float            bl_scale = 1;
static int              bl_shown = -1;
static bool             bl_slides;
static bool             bl_running;
static _Atomic uint32_t bl_content_h;
static _Atomic uint32_t bl_view_h;
static _Atomic float    bl_touch_scale = 1;
static _Atomic uint32_t bl_y;
static _Atomic float    bl_yf;  // bl_y unrounded: where the layer goes
static _Atomic bool     bl_has_y;
static _Atomic uint32_t bl_pred;
static _Atomic int64_t  bl_lead = 16000000;  // answer to placement, ns
static _Atomic int64_t  bl_asked;            // when Lean last read bl_pred
static uint64_t         bl_seq;
static int64_t          bl_period = 16666667;  // the shortest vsync gap seen
static uint32_t         bl_gap, bl_gaps, bl_gap_max;  // rows uncovered
static bool             bl_predict = true;
static bool             bl_trace;

// Vsync thread
// ------------

typedef struct {
  int old;
} BlDone;

// A transaction that showed a new buffer completed: the one it replaced
// is free once its release fence fires (AHardwareBuffer_lock waits on it).
static void bl_complete(void* ctx, ASurfaceTransactionStats* stats) {
  BlDone* d = ctx;
  pthread_mutex_lock(&bl_mu);
  if (d->old >= 0 && bl_sc != NULL) {
    int fd = ASurfaceTransactionStats_getPreviousReleaseFenceFd(stats, bl_sc);
    bl_bufs[d->old].fence = fd;
    bl_bufs[d->old].state = BL_FREE;
    pthread_cond_broadcast(&bl_cv);
  }
  pthread_mutex_unlock(&bl_mu);
  free(d);
}

// The newest frame (drawn at y) placed for offset now (frame px, not
// rounded: the layer moves in the window's own pixels, finer than the
// frame's): its rows from now - y on, into the frame's area.
static void bl_place(ASurfaceTransaction* t, uint32_t y, float now) {
  float   d   = now - (float)y;
  int32_t top = d > 0 ? (int32_t)floorf(d) : 0;
  int32_t bot = (int32_t)bl_h + (d < 0 ? (int32_t)floorf(d) : 0);
  // Uncovered rows: the screen's rows (from now, view_h of them) the
  // frame (from y, bl_h of them) does not reach, above or below.
  float vh    = (float)atomic_load(&bl_view_h);
  float above = d < 0 ? -d : 0;
  float below = d + vh - (float)bl_h;
  bl_gap = (uint32_t)lroundf(above + (below > 0 ? below : 0));
  if (bot <= top) {
    ASurfaceTransaction_setVisibility(t, bl_sc, ASURFACE_TRANSACTION_VISIBILITY_HIDE);
    return;
  }
  ARect src = { 0, top, (int32_t)bl_w, bot };
  int32_t y0 = bl_oy + (int32_t)lroundf(((float)top - d) / bl_scale);
  int32_t y1 = bl_oy + (int32_t)lroundf(((float)bot - d) / bl_scale);
  ARect dst = { bl_ox, y0, bl_ox + (int32_t)lroundf((float)bl_w / bl_scale), y1 };
  ASurfaceTransaction_setGeometry(t, bl_sc, &src, &dst, 0);
  ASurfaceTransaction_setVisibility(t, bl_sc, ASURFACE_TRANSACTION_VISIBILITY_SHOW);
}

static void bl_vsync(int64_t ns, void* data);

static void bl_tick(void) {
  AChoreographer_postFrameCallback64(AChoreographer_getInstance(),
    (AChoreographer_frameCallback64)bl_vsync, NULL);
}

// Every 120 vsyncs, logcat (tag bend) gets how many the thread missed
// (a callback more than 1.5 periods after the last) and how many new
// frames Lean handed over: motion stays even while missed is 0.
// (and the rows slides left uncovered: their mean over the vsyncs that
// moved, and the most).
static void bl_stats(int64_t ns, bool fresh) {
  static int64_t last;
  static int     n, missed, frames, moved;
  if (last != 0) {
    int64_t gap = ns - last;
    bl_period = gap < bl_period ? gap : bl_period;
    missed += gap * 2 > bl_period * 3;
  }
  last    = ns;
  frames += fresh;
  moved  += bl_gap > 0;
  bl_gaps += bl_gap;
  bl_gap_max = bl_gap > bl_gap_max ? bl_gap : bl_gap_max;
  bl_gap = 0;
  if (++n == 120) {
    __android_log_print(ANDROID_LOG_INFO, "lean",
      "layer: 120 vsyncs (%.1f ms), %d missed, %d new frames, uncovered rows "
      "mean %.1f max %u (lead %.1f ms)", bl_period / 1e6, missed, frames,
      moved ? (double)bl_gaps / moved : 0.0, bl_gap_max,
      atomic_load(&bl_lead) / 1e6);
    n = missed = frames = moved = 0;
    bl_gaps = bl_gap_max = 0;
  }
}

// The offset predicted lead ns on from now (at vsync ns), from the rate
// since the last vsync; a fling's prediction stays between now and where
// the fling stops, and every prediction within the content.
static uint32_t bl_ahead(uint32_t now, int64_t ns) {
  static int64_t last_ns;
  static uint32_t last;
  static double   rate;  // frame px per ns
  if (last_ns != 0 && ns > last_ns) {
    double r = (double)(int32_t)(now - last) / (double)(ns - last_ns);
    rate = rate * 0.5 + r * 0.5;
  }
  last_ns = ns;
  last    = now;
  // Only a fling is predicted (the scroller's curve is set); a finger can
  // turn at any moment. The lead is capped at two vsyncs, so a slow frame
  // cannot make the next draw further ahead and slower still.
  uint32_t fin;
  double   p = now;
  if (bl_predict && bs_target(&fin)) {
    int64_t lead = atomic_load(&bl_lead);
    lead = lead > 2 * bl_period ? 2 * bl_period : lead;
    p = (double)now + rate * (double)lead;
    double lo = now < fin ? now : fin, hi = now < fin ? fin : now;
    p = p < lo ? lo : p > hi ? hi : p;
  }
  uint32_t ch = atomic_load(&bl_content_h), vh = atomic_load(&bl_view_h);
  double max = ch > vh ? (double)(ch - vh) : 0;
  p = p < 0 ? 0 : p > max ? max : p;
  return (uint32_t)lround(p);
}

static void bl_vsync(int64_t ns, void* data) {
  uint32_t now;
  float    nowf;
  if (bs_vsync(atomic_load(&bl_content_h), atomic_load(&bl_view_h),
      atomic_load(&bl_touch_scale), ns, &now, &nowf)) {
    atomic_store(&bl_y, now);
    atomic_store(&bl_yf, nowf);
    atomic_store(&bl_pred, bl_ahead(now, ns));
    atomic_store(&bl_has_y, true);
  }
  pthread_mutex_lock(&bl_mu);
  if (bl_sc != NULL) {
    int next = -1;
    for (int i = 0; i < BL_BUFS; i += 1) {
      if (bl_bufs[i].state == BL_NEXT) {
        next = i;
      }
    }
    ASurfaceTransaction* t = ASurfaceTransaction_create();
    bl_stats(ns, next >= 0);
    if (next >= 0) {
      BlDone* d = malloc(sizeof *d);
      d->old    = bl_shown;
      if (bl_bufs[next].asked != 0) {
        // placed for this vsync's offset (both the buffer and its place
        // reach the screen together, so this is the lead that matters)
        int64_t sample = ns - bl_bufs[next].asked;
        if (sample > 0 && sample < 200000000) {
          atomic_store(&bl_lead, (atomic_load(&bl_lead) * 7 + sample) / 8);
        }
      }
      ASurfaceTransaction_setBuffer(t, bl_sc, bl_bufs[next].buf,
        bl_bufs[next].fence);
      bl_bufs[next].fence = -1;
      bl_bufs[next].state = BL_SHOWN;
      bl_shown            = next;
      ASurfaceTransaction_setOnComplete(t, d, bl_complete);
    }
    if (bl_shown >= 0) {
      bl_place(t, bl_bufs[bl_shown].y, bl_slides ? atomic_load(&bl_yf)
        : (float)bl_bufs[bl_shown].y);
      if (bl_trace) {
        __android_log_print(ANDROID_LOG_INFO, "leantrace",
          "%lld now %u nowf %.3f pred %u shown %u%s", (long long)(ns / 1000000),
          atomic_load(&bl_y), atomic_load(&bl_yf), atomic_load(&bl_pred),
          bl_bufs[bl_shown].y,
          next >= 0 ? " new" : "");
      }
    }
    ASurfaceTransaction_apply(t);
    ASurfaceTransaction_delete(t);
  }
  bl_seq += 1;
  pthread_cond_broadcast(&bl_cv);
  pthread_mutex_unlock(&bl_mu);
  bl_tick();
}

static void* bl_run(void* arg) {
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
  bl_predict = predict;
  char v[PROP_VALUE_MAX] = { 0 };
  bl_trace = __system_property_get("debug.lean.trace", v) > 0 && v[0] == '1';
  if (!bl_running) {
    bl_running = true;
    pthread_t t;
    pthread_create(&t, NULL, bl_run, NULL);
    pthread_detach(t);
  }
  pthread_mutex_unlock(&bl_mu);
}

void bl_scroll_needs(uint32_t content_h, uint32_t view_h, float scale) {
  atomic_store(&bl_content_h, content_h);
  atomic_store(&bl_view_h, view_h);
  atomic_store(&bl_touch_scale, scale);
}

static int64_t bl_clock(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (int64_t)ts.tv_sec * 1000000000 + ts.tv_nsec;
}

bool bl_scroll_y(uint32_t* y) {
  if (!atomic_load(&bl_has_y)) {
    return false;
  }
  *y = atomic_load(&bl_pred);
  atomic_store(&bl_asked, bl_clock());
  return true;
}

static void bl_alloc(uint32_t w, uint32_t h) {
  for (int i = 0; i < BL_BUFS; i += 1) {
    if (bl_bufs[i].buf != NULL) {
      AHardwareBuffer_release(bl_bufs[i].buf);
    }
    AHardwareBuffer_Desc d = { w, h, 1, AHARDWAREBUFFER_FORMAT_R8G8B8X8_UNORM,
      AHARDWAREBUFFER_USAGE_CPU_WRITE_OFTEN | AHARDWAREBUFFER_USAGE_GPU_SAMPLED_IMAGE
        | AHARDWAREBUFFER_USAGE_COMPOSER_OVERLAY, 0, 0, 0 };
    AHardwareBuffer_allocate(&d, &bl_bufs[i].buf);
    AHardwareBuffer_describe(bl_bufs[i].buf, &d);
    bl_stride        = d.stride;
    bl_bufs[i].state = BL_FREE;
    bl_bufs[i].fence = -1;
  }
  bl_w     = w;
  bl_h     = h;
  bl_shown = -1;
}

void bl_attach(ANativeWindow* win) {
  pthread_mutex_lock(&bl_mu);
  if (win != bl_win) {
    if (bl_sc != NULL) {
      ASurfaceControl_release(bl_sc);
    }
    bl_sc    = ASurfaceControl_createFromWindow(win, "lean");
    bl_win   = win;
    bl_shown = -1;
    for (int i = 0; i < BL_BUFS; i += 1) {
      if (bl_bufs[i].state != BL_HELD) {
        bl_bufs[i].state = BL_FREE;
      }
    }
  }
  pthread_mutex_unlock(&bl_mu);
}

bool bl_present(int32_t ox, int32_t oy, float scale, const uint32_t* pix,
  uint32_t w, uint32_t h, uint32_t y, bool slides) {
  pthread_mutex_lock(&bl_mu);
  if (bl_sc == NULL) {
    pthread_mutex_unlock(&bl_mu);
    return false;
  }
  if (w != bl_w || h != bl_h) {
    bl_alloc(w, h);
  }
  bl_ox     = ox;
  bl_oy     = oy;
  bl_scale  = scale;
  bl_slides = slides;
  // At most one frame waits for a vsync: Lean goes at the display's pace.
  for (bool waiting = true; waiting && bl_sc != NULL;) {
    waiting = false;
    for (int k = 0; k < BL_BUFS; k += 1) {
      waiting |= bl_bufs[k].state == BL_NEXT;
    }
    if (waiting) {
      pthread_cond_wait(&bl_cv, &bl_mu);
    }
  }
  int i = -1;
  while (i < 0) {
    for (int k = 0; k < BL_BUFS && i < 0; k += 1) {
      if (bl_bufs[k].state == BL_FREE) {
        i = k;
      }
    }
    if (i < 0) {
      pthread_cond_wait(&bl_cv, &bl_mu);
    }
  }
  bl_bufs[i].state = BL_HELD;
  int fence = bl_bufs[i].fence;
  bl_bufs[i].fence = -1;
  pthread_mutex_unlock(&bl_mu);
  void* bits = NULL;
  if (AHardwareBuffer_lock(bl_bufs[i].buf, AHARDWAREBUFFER_USAGE_CPU_WRITE_OFTEN,
      fence, NULL, &bits) == 0) {
    for (uint32_t r = 0; r < h; r += 1) {
      memcpy((uint32_t*)bits + (size_t)r * bl_stride, pix + (size_t)r * w,
        (size_t)w * 4);
    }
    int32_t done = -1;
    AHardwareBuffer_unlock(bl_bufs[i].buf, &done);
    pthread_mutex_lock(&bl_mu);
    bl_bufs[i].fence = done;
    bl_bufs[i].y     = y;
    bl_bufs[i].asked = slides ? atomic_load(&bl_asked) : 0;
    bl_bufs[i].state = BL_NEXT;
    pthread_mutex_unlock(&bl_mu);
  } else {
    pthread_mutex_lock(&bl_mu);
    bl_bufs[i].state = BL_FREE;
    pthread_mutex_unlock(&bl_mu);
  }
  return true;
}

bool bl_idle(void) {
  pthread_mutex_lock(&bl_mu);
  uint64_t seq = bl_seq;
  while (bl_running && seq == bl_seq && bl_sc != NULL) {
    pthread_cond_wait(&bl_cv, &bl_mu);
  }
  bool on = bl_running && bl_sc != NULL;
  pthread_mutex_unlock(&bl_mu);
  return on;
}

void bl_window_gone(void) {
  pthread_mutex_lock(&bl_mu);
  if (bl_sc != NULL) {
    ASurfaceTransaction* t = ASurfaceTransaction_create();
    ASurfaceTransaction_reparent(t, bl_sc, NULL);
    ASurfaceTransaction_apply(t);
    ASurfaceTransaction_delete(t);
    ASurfaceControl_release(bl_sc);
    bl_sc = NULL;
  }
  bl_win   = NULL;
  bl_shown = -1;
  for (int i = 0; i < BL_BUFS; i += 1) {
    if (bl_bufs[i].state != BL_HELD) {
      bl_bufs[i].state = BL_FREE;
    }
  }
  pthread_cond_broadcast(&bl_cv);
  pthread_mutex_unlock(&bl_mu);
}
