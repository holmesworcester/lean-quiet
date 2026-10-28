// The app's layers on the compositor
// ==================================

// iOS's arrangement on Android: the OS scrolls, Lean draws. A thread of
// its own wakes at every vsync (AChoreographer), runs the scroller
// (scroll.c) to that vsync, and in one transaction shows Lean's newest
// frames in three child surfaces (ASurfaceControl), bottom to top:
//
// - the list, cropped to the viewport and placed for the difference
//   between the offset it was drawn at and the vsync's, and shifted up by
//   the keyboard's height above the navigation bar: the compositor moves
//   it, so motion is even whether or not Lean finished a frame in time;
// - the header, at the screen's top;
// - the composer, above the navigation bar or the keyboard, following the
//   keyboard's animation (the insets the Java half reports per animation
//   frame) at every vsync.
//
// The list's offset is bottom-anchored (Platform.lean): frame row r,
// drawn at offset bf with overscan `over`, shows the content at distance
// bf + viewH + over - 1 - r above its end. At the vsync's offset bn, with
// the keyboard shifting the list up by s, that row belongs at screen row
// top - over - s + (bn - bf) + r.
//
// Lean draws ahead during a fling: Platform.scroll answers the offset
// predicted for when its frame will be placed (the vsync offset's rate
// times the measured lead from answer to placement, at most two vsyncs,
// kept short of where the fling stops), so a new frame needs little
// sliding. Rows a slide still uncovers show the window behind (the list's
// background colour) until Lean's next frame. Lean's thread hands finished
// frames over (bl_present) in a pool of buffers per layer, each reused
// only once the compositor released it.

#include "layer.h"
#include "activity.h"
#include "scroll.h"

#include <android/choreographer.h>
#include <android/hardware_buffer.h>
#include <android/log.h>
#include <android/looper.h>
#include <android/surface_control.h>
#include <math.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>
#include <sys/system_properties.h>
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
static BlLayer         bl_l[3];
static ANativeWindow*  bl_win;
static bool            bl_running;
static uint32_t        bl_sw, bl_sh, bl_top, bl_bot, bl_over, bl_inset;
static _Atomic uint32_t bl_content_h;
static _Atomic uint32_t bl_view_h;   // with the keyboard closed
static _Atomic uint32_t bl_view_e;   // with the keyboard's shift taken off
static _Atomic float    bl_yf;
static _Atomic bool     bl_has_y;
static _Atomic uint32_t bl_pred;
static _Atomic int64_t  bl_lead = 16000000;  // answer to placement, ns
static _Atomic int64_t  bl_asked;            // when Lean last read bl_pred
static _Atomic int32_t  bl_ctop;
static _Atomic int32_t  bl_shift;
// The list frame is a page, pinned to the top (Geometry.Seam.pinned): no
// slide, no lift by the keyboard; the keyboard covers its lower rows.
static _Atomic bool     bl_pin;
static uint64_t         bl_seq;
static int64_t          bl_period = 16666667;  // the shortest vsync gap seen
static uint32_t         bl_gap, bl_gaps, bl_gap_max;  // rows uncovered
static bool             bl_predict = true;
static bool             bl_trace;

// Vsync thread
// ------------

typedef struct {
  int k;
  int old;
} BlDone;

// A transaction that showed a new buffer completed: the one it replaced
// is free once its release fence fires (AHardwareBuffer_lock waits on it).
static void bl_complete(void* ctx, ASurfaceTransactionStats* stats) {
  BlDone* d = ctx;
  pthread_mutex_lock(&bl_mu);
  BlLayer* l = &bl_l[d->k];
  if (d->old >= 0 && l->sc != NULL) {
    int fd = ASurfaceTransactionStats_getPreviousReleaseFenceFd(stats, l->sc);
    l->bufs[d->old].fence = fd;
    l->bufs[d->old].state = BL_FREE;
    pthread_cond_broadcast(&bl_cv);
  }
  pthread_mutex_unlock(&bl_mu);
  free(d);
}

static void bl_show(ASurfaceTransaction* t, BlLayer* l, int32_t sy0, int32_t sy1, int32_t dy) {
  if (sy1 <= sy0) {
    ASurfaceTransaction_setVisibility(t, l->sc, ASURFACE_TRANSACTION_VISIBILITY_HIDE);
    return;
  }
  ARect src = { 0, sy0, (int32_t)l->w, sy1 };
  ARect dst = { 0, dy + sy0, (int32_t)l->w, dy + sy1 };
  ASurfaceTransaction_setGeometry(t, l->sc, &src, &dst, 0);
  ASurfaceTransaction_setVisibility(t, l->sc, ASURFACE_TRANSACTION_VISIBILITY_SHOW);
}

// The list's frame (drawn at bf) for offset bn: its rows on screen at
// k + r, cropped to the viewport [top, ctop).
static void bl_place_list(ASurfaceTransaction* t, uint32_t bf, float bn, int32_t s, int32_t ctop) {
  BlLayer* l  = &bl_l[BL_LIST];
  // Geometry.Seam.place (slid and lifted), or Seam.pinned (a page)
  int32_t  k  = atomic_load(&bl_pin) ? (int32_t)bl_top - (int32_t)bl_over
    : (int32_t)lroundf((float)bl_top - (float)bl_over - (float)s + (bn - (float)bf));
  int32_t  r0 = (int32_t)bl_top - k;
  int32_t  r1 = ctop - k;
  r0 = r0 < 0 ? 0 : r0;
  r1 = r1 > (int32_t)l->h ? (int32_t)l->h : r1;
  int32_t above = k > (int32_t)bl_top ? k - (int32_t)bl_top : 0;
  int32_t below = ctop - (k + (int32_t)l->h);
  bl_gap = (uint32_t)(above + (below > 0 ? below : 0));
  bl_show(t, l, r0, r1, k);
}

static void bl_vsync(int64_t ns, void* data);

static void bl_tick(void) {
  AChoreographer_postFrameCallback64(AChoreographer_getInstance(),
    (AChoreographer_frameCallback64)bl_vsync, NULL);
}

// Every 120 vsyncs, logcat (tag lean) gets how many the thread missed
// (a callback more than 1.5 periods after the last), how many new list
// frames Lean handed over, and the rows slides left uncovered: their mean
// over the vsyncs that moved, and the most. Motion stays even while
// missed is 0.
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
      moved ? (double)bl_gaps / moved : 0.0, bl_gap_max, atomic_load(&bl_lead) / 1e6);
    n = missed = frames = moved = 0;
    bl_gaps = bl_gap_max = 0;
  }
}

// The offset predicted lead ns on from now (at vsync ns), from the rate
// since the last vsync; a fling's prediction stays between now and where
// the fling stops, and every prediction within the content.
static uint32_t bl_ahead(uint32_t now, int64_t ns) {
  static int64_t  last_ns;
  static uint32_t last;
  static double   rate;  // px per ns
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
  uint32_t ch = atomic_load(&bl_content_h), vh = atomic_load(&bl_view_e);
  double   max = ch > vh ? (double)(ch - vh) : 0;
  p = p < 0 ? 0 : p > max ? max : p;
  return (uint32_t)lround(p);
}

// The layer's newest buffer to show this vsync, if Lean handed one over:
// set in the transaction, the one it replaces freed on completion.
static int bl_take(ASurfaceTransaction* t, BlKind k, int64_t ns) {
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
  BlDone* d = malloc(sizeof *d);
  d->k      = k;
  d->old    = l->shown;
  if (k == BL_LIST && l->bufs[next].asked != 0) {
    // placed for this vsync's offset (both the buffer and its place reach
    // the screen together, so this is the lead that matters)
    int64_t sample = ns - l->bufs[next].asked;
    if (sample > 0 && sample < 200000000) {
      atomic_store(&bl_lead, (atomic_load(&bl_lead) * 7 + sample) / 8);
    }
  }
  ASurfaceTransaction_setBuffer(t, l->sc, l->bufs[next].buf, l->bufs[next].fence);
  ASurfaceTransaction_setOnComplete(t, d, bl_complete);
  l->bufs[next].fence = -1;
  l->bufs[next].state = BL_SHOWN;
  l->shown            = next;
  return next;
}

static void bl_vsync(int64_t ns, void* data) {
  int32_t itop, ibot, ime;
  ba_insets(&itop, &ibot, &ime);
  pthread_mutex_lock(&bl_mu);
  int32_t inset = (int32_t)bl_inset > ibot ? (int32_t)bl_inset : ibot;
  int32_t s     = ime > inset ? ime - inset : 0;
  int32_t ctop  = (int32_t)bl_sh - (int32_t)bl_bot - (ime > inset ? ime : inset);
  uint32_t top  = bl_top;
  pthread_mutex_unlock(&bl_mu);
  uint32_t vh = atomic_load(&bl_view_h);
  uint32_t ve = vh > (uint32_t)s ? vh - (uint32_t)s : 0;
  atomic_store(&bl_view_e, ve);
  uint32_t now;
  float    nowf;
  if (bs_vsync(atomic_load(&bl_content_h), ve, ns, &now, &nowf)) {
    atomic_store(&bl_yf, nowf);
    atomic_store(&bl_pred, bl_ahead(now, ns));
    atomic_store(&bl_has_y, true);
  }
  atomic_store(&bl_ctop, ctop);
  atomic_store(&bl_shift, s);
  ba_set_viewport((int32_t)top, ctop);
  pthread_mutex_lock(&bl_mu);
  if (bl_l[BL_LIST].sc != NULL) {
    ASurfaceTransaction* t = ASurfaceTransaction_create();
    bool fresh = bl_take(t, BL_LIST, ns) >= 0;
    bl_take(t, BL_TOP, ns);
    bl_take(t, BL_BOT, ns);
    bl_stats(ns, fresh);
    BlLayer* l = &bl_l[BL_LIST];
    if (l->shown >= 0) {
      bl_place_list(t, l->bufs[l->shown].y, atomic_load(&bl_yf), s, ctop);
      if (bl_trace) {
        __android_log_print(ANDROID_LOG_INFO, "leantrace", "%lld now %.3f pred %u shown %u shift %d%s",
          (long long)(ns / 1000000), atomic_load(&bl_yf), atomic_load(&bl_pred),
          l->bufs[l->shown].y, s, fresh ? " new" : "");
      }
    }
    BlLayer* tl = &bl_l[BL_TOP];
    if (tl->shown >= 0) {
      bl_show(t, tl, 0, (int32_t)tl->h, 0);
    }
    BlLayer* bl = &bl_l[BL_BOT];
    if (bl->shown >= 0) {
      bl_show(t, bl, 0, (int32_t)bl->h, ctop);
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

void bl_scroll_needs(uint32_t content_h, uint32_t view_h) {
  atomic_store(&bl_content_h, content_h);
  atomic_store(&bl_view_h, view_h);
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

void bl_layout(uint32_t w, uint32_t h, uint32_t top_h, uint32_t bot_h, uint32_t over,
  uint32_t inset_bottom) {
  pthread_mutex_lock(&bl_mu);
  bl_sw    = w;
  bl_sh    = h;
  bl_top   = top_h;
  bl_bot   = bot_h;
  bl_over  = over;
  bl_inset = inset_bottom;
  pthread_mutex_unlock(&bl_mu);
}

void bl_set_pin(bool pin) {
  atomic_store(&bl_pin, pin);
}

bool bl_pinned(void) {
  return atomic_load(&bl_pin);
}

void bl_placed(float* b, int32_t* composer_top, int32_t* shift) {
  *b            = atomic_load(&bl_yf);
  *composer_top = atomic_load(&bl_ctop);
  *shift        = atomic_load(&bl_shift);
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
  static const char* names[3] = { "lean list", "lean header", "lean composer" };
  pthread_mutex_lock(&bl_mu);
  if (win != bl_win) {
    for (int k = 0; k < 3; k += 1) {
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
      ASurfaceTransaction_setZOrder(t, l->sc, k);
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
    l->bufs[i].asked = k == BL_LIST ? atomic_load(&bl_asked) : 0;
    l->bufs[i].state = BL_NEXT;
    pthread_mutex_unlock(&bl_mu);
  } else {
    pthread_mutex_lock(&bl_mu);
    l->bufs[i].state = BL_FREE;
    pthread_mutex_unlock(&bl_mu);
  }
  return true;
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
  for (int k = 0; k < 3; k += 1) {
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
  pthread_cond_broadcast(&bl_cv);
  pthread_mutex_unlock(&bl_mu);
}
