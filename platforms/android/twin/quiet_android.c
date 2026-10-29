// The Lean app's window on Android
// ================================

// Platform.lean's effects on the activity (activity.c), its layers
// (layer.c) and its scroller (scroll.c). The frames Lean hands over are
// arrays of pixel rows, 4 bytes a pixel in R G B X order, the
// compositor's own layout: each row is copied with memcpy into the
// layer's staging buffer, and from there into a buffer of the layer.
//
// A row Lean kept from the last frame of a layer is the same object in
// the new one, so its pixels are already in the staging buffer: for the
// list, the buffer is shifted by the offset's change (the list is
// bottom-anchored: frame row r drawn at offset b holds what row
// r + (lb - b) held at offset lb), and only rows that are new objects are
// copied. The last frame is held (a reference) while its rows are
// compared, so an object seen again is the same immutable row, never a
// freed one's address reused.

#include "activity.h"
#include "layer.h"
#include "../../native/translate.h"
#include "scroll.h"

#include <android/log.h>
#include <lean/lean.h>
#include <math.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <pthread.h>
#include <stdatomic.h>


typedef struct {
  uint32_t*    pix;
  uint32_t     w, h;
  lean_object* last;  // the frame in pix (a reference), or NULL
  uint32_t     off;   // its offset (the list's)
  bool         dirty;
  uint64_t     rows;  // rows copied, since the last report
} LqStage;

typedef struct {
  LqStage        st[4];
  ANativeWindow* painted;
  uint32_t       w, h, inset_top, inset_bottom;
  bool           active;
  uint32_t       n, cap;
  uint32_t*      evs;
  bool           closed;
} LqWin;

static LqWin lq;
lean_obj_res lq_poll(void);

static uint64_t lq_tick(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (uint64_t)ts.tv_sec * 1000000000u + (uint64_t)ts.tv_nsec;
}

static void lq_raw(uint32_t kind, uint32_t a, uint32_t b, uint32_t c, uint64_t ms, uint64_t frame) {
  if (lq.n == lq.cap) {
    lq.cap = lq.cap == 0 ? 64 : lq.cap * 2;
    lq.evs = realloc(lq.evs, lq.cap * 32);
    if (lq.evs == NULL) {
      abort();
    }
  }
  uint32_t* ev = lq.evs + lq.n * 8;
  ev[0] = kind;
  ev[1] = a;
  ev[2] = b;
  ev[3] = c;
  ev[4] = ms; ev[5] = ms >> 32; ev[6] = frame; ev[7] = frame >> 32;
  lq.n += 1;
}

static void lq_push(uint32_t k, uint32_t a, uint32_t b, uint32_t c) {
  lq_raw(k >= 9 && k <= 12 ? k + 7 : k, a, b, c, lq_tick() / 1000000, bl_view_id());
}

// Raw transport, including all pointers, cancellation and monotonic time.
static void lq_pump(void) {
  BaTouch ts[256];
  bool closed = false;
  uint32_t n;
  do {
    n = ba_drain(ts, 256, &closed);
    for (uint32_t i = 0; i < n; i++)
      lq_raw(9 + ts[i].kind, ts[i].id, (int32_t)lroundf(ts[i].x),
        (int32_t)lroundf(ts[i].y), ts[i].t / 1000000, ts[i].frame);
  } while (n == 256);
  uint32_t ws[256];
  do {
    n = ba_drain_events(ws, 256);
    for (uint32_t i = 0; i + 3 < n; i += 4) lq_push(ws[i], ws[i+1], ws[i+2], ws[i+3]);
  } while (n == 256);
  lq_push(13, 0, 0, 0);
  bool active = bs_active();
  if (active != lq.active) { lq.active = active; lq_push(7, active, 0, 0); }
  if (closed && !lq.closed) { lq.closed = true; lq_push(1, 0, 0, 0); }
}

lean_obj_res lq_motion(b_lean_obj_arg samples) {
  for (size_t i = 0; i + 7 < lean_array_size(samples); i += 8) {
    uint32_t v[6];
    for (int j = 0; j < 6; j++) v[j] = lean_unbox_uint32(lean_array_get_core(samples, i+j));
    ba_accept_scroll((BaTouch){v[0]-9, (int32_t)v[2], (int32_t)v[3],
      (int64_t)(((uint64_t)v[5] << 32) | v[4]) * 1000000, v[1]});
  }
  return lean_io_result_mk_ok(lean_box(0));
}

// Frames
// ------

static void lq_row(uint32_t* dst, lean_object* row, uint32_t w) {
  size_t n = lean_sarray_size(row) / 4;
  n = n < w ? n : w;
  memcpy(dst, lean_sarray_cptr(row), n * 4);
  if (n < w) {
    memset(dst + n, 0, (w - n) * 4);
  }
}

// The frame f into a layer's staging buffer. For the list (shift), rows
// kept from the last frame move with the offset's change.
static void lq_stage(LqStage* s, b_lean_obj_arg f, uint32_t w, uint32_t y, bool shift) {
  uint32_t h = (uint32_t)lean_array_size(f);
  if (h == 0) {
    s->dirty = false;
    return;
  }
  if (s->pix == NULL || s->w != w || s->h != h) {
    free(s->pix);
    s->pix = calloc((size_t)w * h, 4);
    if (s->pix == NULL) {
      abort();
    }
    s->w = w;
    s->h = h;
    if (s->last != NULL) {
      lean_dec(s->last);
      s->last = NULL;
    }
  }
  if (f == s->last && y == s->off) {
    s->dirty = false;
    return;
  }
  lean_object** rows = lean_array_cptr(f);
  lean_object** old  = NULL;
  int64_t       d    = 0;
  size_t        oh   = 0;
  if (s->last != NULL) {
    old = lean_array_cptr(s->last);
    oh  = lean_array_size(s->last);
    d   = shift ? (int64_t)s->off - (int64_t)y : 0;
    if (d >= (int64_t)h || -d >= (int64_t)h) {
      old = NULL;
    } else if (d > 0) {
      memmove(s->pix, s->pix + (size_t)d * w, (size_t)(h - d) * w * 4);
    } else if (d < 0) {
      memmove(s->pix + (size_t)(-d) * w, s->pix, (size_t)(h + d) * w * 4);
    }
  }
  bool changed = old == NULL || d != 0;
  for (uint32_t r = 0; r < h; r += 1) {
    int64_t at = (int64_t)r + d;  // the row's place in the last frame
    if (old != NULL && at >= 0 && at < (int64_t)oh && old[at] == rows[r]) {
      continue;
    }
    lq_row(s->pix + (size_t)r * w, rows[r], w);
    s->rows += 1;
    changed = true;
  }
  lean_inc(f);
  if (s->last != NULL) {
    lean_dec(s->last);
  }
  s->last  = f;
  s->off   = y;
  s->dirty = changed;
}

// The window itself, once per window: the list's background colour
// (behind rows a slide uncovers), at the surface's own size.
static void lq_paint(ANativeWindow* on, int32_t sw, int32_t sh) {
  if (on == lq.painted) {
    return;
  }
  LqStage* s  = &lq.st[BL_LIST];
  uint32_t bg = s->pix != NULL ? s->pix[0] : 0xFF000000u;
  ANativeWindow_setBuffersGeometry(on, sw, sh, WINDOW_FORMAT_RGBX_8888);
  ANativeWindow_Buffer b;
  if (ANativeWindow_lock(on, &b, NULL) == 0) {
    for (int32_t y = 0; y < b.height; y += 1) {
      uint32_t* row = (uint32_t*)b.bits + (size_t)y * b.stride;
      for (int32_t x = 0; x < b.width; x += 1) {
        row[x] = bg;
      }
    }
    ANativeWindow_unlockAndPost(on);
  }
  lq.painted = on;
}

// Every 120 frames, logcat (tag lean) gets the mean cost per frame: Lean's
// own time, the rows copied into staging (and how many), and the time
// handing frames to the layers (waits for the vsync and a free buffer).
static void lq_time(uint64_t t0, uint64_t t1, uint64_t t2) {
  static uint64_t n, copy, show, app, last;
  if (last != 0) {
    app += t0 - last;
  }
  copy += t1 - t0;
  show += t2 - t1;
  last  = t2;
  if (++n == 120) {
    uint64_t rows = lq.st[0].rows + lq.st[1].rows + lq.st[2].rows;
    __android_log_print(ANDROID_LOG_INFO, "lean",
      "twin ms/frame: lean %.1f copy %.1f (%llu rows) show %.1f", app / 120e6, copy / 120e6,
      (unsigned long long)(rows / 120), show / 120e6);
    n = copy = show = app = 0;
    lq.st[0].rows = lq.st[1].rows = lq.st[2].rows = 0;
  }
}

// The watchdog
// ------------

// Where Lean's thread is (0: in Lean; 1 frame start; 2 waiting for the
// window; 3 drawing; 4 waiting a vsync; 10-12 presenting a layer), and
// when it last moved. A thread on Lean's side or in a wait that has not
// moved for 3 s while the window exists is reported: its phase, and a
// backtrace of Lean's thread taken by a signal on it, so a hang names
// the function it is in.
#include <signal.h>
#include <unwind.h>
#include <dlfcn.h>

static _Atomic int      lq_ph;
static _Atomic int64_t  lq_moved;
static pthread_t        lq_thread;
static bool             lq_thread_known;

static void lq_phase(int p) {
  atomic_store(&lq_ph, p);
  atomic_store(&lq_moved, (int64_t)lq_tick());
}

typedef struct { void** pcs; int n, max; } LqTrace;

static _Unwind_Reason_Code lq_unwind(struct _Unwind_Context* c, void* arg) {
  LqTrace* t = arg;
  uintptr_t pc = _Unwind_GetIP(c);
  if (pc != 0 && t->n < t->max) {
    t->pcs[t->n++] = (void*)pc;
  }
  return t->n < t->max ? _URC_NO_REASON : _URC_END_OF_STACK;
}

static void lq_dump(int sig) {
  (void)sig;
  void*   pcs[40];
  LqTrace t = { pcs, 0, 40 };
  _Unwind_Backtrace(lq_unwind, &t);
  for (int i = 0; i < t.n; i += 1) {
    Dl_info d;
    if (dladdr(pcs[i], &d) && d.dli_sname != NULL) {
      __android_log_print(ANDROID_LOG_WARN, "lean", "  #%02d %s+%td", i, d.dli_sname,
        (char*)pcs[i] - (char*)d.dli_saddr);
    } else {
      __android_log_print(ANDROID_LOG_WARN, "lean", "  #%02d %p", i, pcs[i]);
    }
  }
}

static void* lq_watch(void* arg) {
  (void)arg;
  int64_t reported = 0;
  for (;;) {
    struct timespec ts = { 1, 0 };
    nanosleep(&ts, NULL);
    int64_t moved = atomic_load(&lq_moved);
    int     ph    = atomic_load(&lq_ph);
    int64_t idle  = (int64_t)lq_tick() - moved;
    // with no window, waiting is no hang (it waits for one)
    if (moved == 0 || moved == reported || idle < 3000000000LL || !ba_has_window()) {
      continue;
    }
    reported = moved;
    __android_log_print(ANDROID_LOG_WARN, "lean", "watchdog: Lean's thread stuck %lld ms in phase %d",
      (long long)(idle / 1000000), ph);
    if (lq_thread_known) {
      pthread_kill(lq_thread, SIGUSR2);
    }
  }
  return NULL;
}

static void lq_watch_start(void) {
  static bool started;
  if (started) {
    return;
  }
  started = true;
  lq_thread       = pthread_self();
  lq_thread_known = true;
  struct sigaction sa;
  memset(&sa, 0, sizeof sa);
  sa.sa_handler = lq_dump;
  sigaction(SIGUSR2, &sa, NULL);
  lq_phase(0);
  pthread_t t;
  pthread_create(&t, NULL, lq_watch, NULL);
  pthread_detach(t);
}

// Platform.lean
// -------------

lean_obj_res lq_screen(void) {
  lq_watch_start();
  lq_phase(0);
  int32_t w, h, top, bottom, ime;
  // The first call waits for the window and its insets (up to a second
  // for those); later calls (the app reads the screen every frame) never
  // wait: with no window they answer the last size known. Waiting for a
  // window happens in one place, lq_frame.
  static bool waited;
  if (!waited) {
    ba_size(&w, &h);
    for (int i = 0; i < 100; i += 1) {
      ba_insets(&top, &bottom, &ime);
      if (top > 0) {
        break;
      }
      struct timespec ts = { 0, 10000000 };
      nanosleep(&ts, NULL);
    }
    waited = true;
  } else {
    if (!ba_size_now(&w, &h)) {
      w = (int32_t)lq.w;
      h = (int32_t)lq.h;
    }
    ba_insets(&top, &bottom, &ime);
  }
  lq.w            = (uint32_t)w;
  lq.h            = (uint32_t)h;
  lq.inset_top    = (uint32_t)top;
  lq.inset_bottom = (uint32_t)bottom;
  int32_t sides[7];
  ba_safe(sides);
  uint32_t v[13] = { (uint32_t)w, (uint32_t)h, (uint32_t)top, (uint32_t)bottom, (uint32_t)ba_dpi(), ba_dark() };
  for (int i = 0; i < 7; i++) v[i + 6] = (uint32_t)sides[i];
  lean_object* a = lean_mk_empty_array_with_capacity(lean_box(13));
  for (int i = 0; i < 13; i++) a = lean_array_push(a, lean_box_uint32(v[i]));
  return lean_io_result_mk_ok(a);
}

lean_obj_res lq_bars(uint32_t top, uint32_t bottom, uint8_t light_top, uint8_t light_bottom) {
  ba_bars(top, bottom, light_top, light_bottom);
  return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res lq_scroll(uint32_t content_h, uint32_t view_h) {
  float y = 0;
  bl_start(ba_ahead());
  bl_scroll_needs(content_h, view_h);
  float got;
  if (bl_scroll_y(&got)) {
    y = got;
  }
  return lean_io_result_mk_ok(lean_box_float(y));
}

lean_obj_res lq_scroll_by(double d) {
  bs_by((float)d);
  return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res lq_scroll_to(double b) {
  bs_to((float)b);
  return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res lq_frame(b_lean_obj_arg list, uint32_t b, uint32_t over, b_lean_obj_arg top,
  b_lean_obj_arg bot, uint8_t pin, b_lean_obj_arg placement, b_lean_obj_arg hold) {
  lq_phase(1);
  if (!ba_has_window()) return lq_poll();
  (void)pin;
  uint32_t place[LQ_PLACEMENT_WORDS];
  for (int i = 0; i < LQ_PLACEMENT_WORDS; i++) place[i] = lean_unbox_uint32(lean_array_get_core(placement, i));
  uint64_t t0    = lq_tick();
  uint32_t top_h = (uint32_t)lean_array_size(top);
  uint32_t bot_h = (uint32_t)lean_array_size(bot);
  int32_t  itop, ibot, ime;
  ba_insets(&itop, &ibot, &ime);
  if (ibot > 0) {
    lq.inset_bottom = (uint32_t)ibot;
  }
  bl_start(ba_ahead());
  (void)over; (void)top_h; (void)bot_h;
  lq_pump();
  lq_stage(&lq.st[BL_LIST], list, lq.w, b, true);
  lq_stage(&lq.st[BL_TOP], top, lq.w, 0, false);
  lq_stage(&lq.st[BL_BOT], bot, lq.w, 0, false);
  lq_stage(&lq.st[BL_HOLD], hold, lq.w, 0, false);
  uint64_t t1 = lq_tick();
  bool any = lq.st[0].dirty || lq.st[1].dirty || lq.st[2].dirty || lq.st[3].dirty;
  int32_t sw, sh;
  lq_phase(2);
  ANativeWindow* on = ba_lock(&sw, &sh);
  lq_phase(3);
  if (on != NULL) {
    if (sw != (int32_t)lq.w || sh != (int32_t)lq.h) {
      ba_unlock();
      lq.painted = NULL;
      lq_push(12, 0, 0, 0);
      return lq_poll();
    }
    bool fresh = on != lq.painted;
    lq_paint(on, sw, sh);
    bl_attach(on);
    ba_unlock();
    if (fresh) {
      for (int k = 0; k < 4; k += 1) {
        lq.st[k].dirty = lq.st[k].pix != NULL;
      }
      any = true;
    }
    if (!any) {
      lq_phase(4);
      bl_idle();
    }
    bool begun = bl_begin();
    bool complete = begun;
    for (int k = 0; complete && k < 4; k += 1) {
      LqStage* s = &lq.st[k];
      if (s->dirty) {
        lq_phase(10 + k);
        complete = bl_present((BlKind)k, s->pix, s->w, s->h, s->off, 0);
      }
    }
    if (complete) bl_geometry(place);
    else {
      // A pending older publication is left intact. Partial new staging
      // is discarded, and every layer is retried with the next frame.
      if (begun) bl_abort();
      lq.painted = NULL;
    }
  }
  lq_time(t0, t1, lq_tick());
  lq_phase(0);
  lean_object* evs = lean_mk_empty_array_with_capacity(lean_box(lq.n * 8));
  for (uint32_t i = 0; i < lq.n * 8; i += 1) {
    evs = lean_array_push(evs, lean_box_uint32(lq.evs[i]));
  }
  lq.n = 0;
  return lean_io_result_mk_ok(evs);
}

lean_obj_res lq_text(void) {
  uint32_t     pos[4];
  char*        s = ba_text(pos);
  lean_object* a = lean_mk_empty_array_with_capacity(lean_box(4));
  for (int i = 0; i < 4; i += 1) {
    a = lean_array_push(a, lean_box_uint32(pos[i]));
  }
  lean_object* p = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p, 0, lean_mk_string(s != NULL ? s : ""));
  lean_ctor_set(p, 1, a);
  free(s);
  return lean_io_result_mk_ok(p);
}

lean_obj_res lq_ime(uint8_t show) {
  ba_ime(show != 0);
  return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res lq_scan(uint8_t on) {
  ba_scan(on != 0);
  return lean_io_result_mk_ok(lean_box(0));
}

// The newest frame's Y plane, copied into a Lean ByteArray (Platform.luma).
lean_obj_res lq_luma(void) {
  size_t       n;
  uint32_t     wh[4];
  uint8_t*     p   = ba_take_luma(&n, wh);
  lean_object* hdr = lean_mk_empty_array();
  lean_object* px  = lean_alloc_sarray(1, p != NULL ? n : 0, p != NULL ? n : 0);
  if (p != NULL) {
    for (int i = 0; i < 4; i += 1) {
      hdr = lean_array_push(hdr, lean_box_uint32(wh[i]));
    }
    memcpy(lean_sarray_cptr(px), p, n);
    free(p);
  }
  lean_object* r = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(r, 0, hdr);
  lean_ctor_set(r, 1, px);
  return lean_io_result_mk_ok(r);
}

lean_obj_res lq_copy(b_lean_obj_arg text) {
  ba_copy(lean_string_cstr(text));
  return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res lq_set_text(b_lean_obj_arg text) {
  ba_set_text(lean_string_cstr(text));
  return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res lq_now_us(void) {
  return lean_io_result_mk_ok(lean_box_uint64(lq_tick() / 1000));
}

lean_obj_res lq_poll(void) {
  lq_pump();
  lean_object* evs = lean_mk_empty_array();
  for (uint32_t i = 0; i < lq.n * 8; i++) {
    if (i % 8 == 0 && (lq.evs[i] == 16 || lq.evs[i] == 18)) lq.painted = NULL;
    evs = lean_array_push(evs, lean_box_uint32(lq.evs[i]));
  }
  lq.n = 0;
  return lean_io_result_mk_ok(evs);
}

lean_obj_res lq_links(void) {
  lean_object* links = lean_mk_empty_array();
  char* url;
  while ((url = ba_take_link()) != NULL) {
    links = lean_array_push(links, lean_mk_string(url));
    free(url);
  }
  return lean_io_result_mk_ok(links);
}



lean_obj_res lq_log(b_lean_obj_arg s) {
  __android_log_write(ANDROID_LOG_INFO, "lean", lean_string_cstr(s));
  return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res lq_tz_min(void) {
  time_t t = time(NULL);
  struct tm tm;
  localtime_r(&t, &tm);
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(int32_t)(tm.tm_gmtoff / 60)));
}

lean_obj_res lq_appearance(uint8_t dark, uint32_t background) {
  ba_appearance(dark, background);
  return lean_io_result_mk_ok(lean_box(0));
}
