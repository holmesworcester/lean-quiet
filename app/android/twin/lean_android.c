// The Lean app's window on Android
// ================================

// Platform.lean's effects on a NativeActivity (activity.c). The frames
// Lean hands over are arrays of pixel rows (Render.Frame: row r shows
// content row y + r, 4 bytes a pixel, B G R X); this copies them into the
// frame buffer and shows it, through the compositor-slid layer (layer.c)
// when that is on, else straight into the window's buffer, letterboxed.
// The OS owns scrolling: Platform.nativeScroll answers the scroller's
// offset (scroll.c, Android's own physics).
//
// A row Lean kept from the last frame (Frame.next shifts the last frame,
// law reuse_is_render) is the same object in the new frame, so its
// pixels are already in the buffer: the buffer is shifted by the offset's
// change and only rows that are new objects are copied. The last frame
// is held (a reference) while its rows are compared, so an object seen
// again is the same immutable row, never a freed one's address reused.

#include "activity.h"
#include "layer.h"
#include "scroll.h"

#include <android/log.h>
#include <lean/lean.h>
#include <math.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define WIN_LAG   5000000
#define WIN_REACH 8000000
#define WIN_HIST  8

// Set by activity.c at startup: whether frames slide (Platform.slides).
bool lc_slides_on;

typedef struct {
  uint32_t       w;
  uint32_t       h;
  ANativeWindow* on;
  int32_t        sw;
  int32_t        sh;
  uint32_t       bw;
  uint32_t       bh;
  uint32_t       ox;
  uint32_t       oy;
  BaTouch        hist[WIN_HIST];
  uint32_t       nh;
  bool           held;
  bool           moved;
  uint32_t*      pix;
  lean_object*   last;  // the frame in pix (a reference), or NULL
  uint32_t       off;   // its offset
  uint32_t       ver;
  uint64_t       rows;  // rows copied, since the last report
  uint32_t       top;   // the native scroll's last offset (the visible top)
  void*          barred[4];
  ANativeWindow* layered;
  bool           dirty;
  uint32_t       n;
  uint32_t       cap;
  uint32_t*      evs;
  bool           closed;
} LcWin;

static LcWin* win_current;

static uint64_t lc_tick(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (uint64_t)ts.tv_sec * 1000000000u + (uint64_t)ts.tv_nsec;
}

static void lc_push(LcWin* win, uint32_t kind, uint32_t a, uint32_t b, uint32_t c) {
  if (win->n == win->cap) {
    win->cap = win->cap == 0 ? 64 : win->cap * 2;
    win->evs = realloc(win->evs, win->cap * 16);
    if (win->evs == NULL) {
      abort();
    }
  }
  uint32_t* ev = win->evs + win->n * 4;
  ev[0] = kind;
  ev[1] = a;
  ev[2] = b;
  ev[3] = c;
  win->n += 1;
}

// A buffer of the surface's aspect that holds the frame, the frame
// centred in it; set again whenever the surface is new or resized (a new
// surface forgets its buffers' size). A slid frame is taller than the
// screen by the overscan: its width is fitted, and the screen shows the
// rows the layer places in view.
static void lc_fit(LcWin* win, ANativeWindow* on, int32_t sw, int32_t sh) {
  if (on == win->on && sw == win->sw && sh == win->sh) {
    return;
  }
  uint64_t w = win->w;
  uint64_t h = win->h;
  if (lc_slides_on || (uint64_t)sh * w >= (uint64_t)sw * h) {
    win->bw = (uint32_t)w;
    win->bh = (uint32_t)(((uint64_t)sh * w + sw - 1) / sw);
  } else {
    win->bh = (uint32_t)h;
    win->bw = (uint32_t)(((uint64_t)sw * h + sh - 1) / sh);
  }
  win->ox = lc_slides_on ? 0 : (win->bw - win->w) / 2;
  win->oy = lc_slides_on ? 0 : (win->bh - win->h) / 2;
  win->on = on;
  win->sw = sw;
  win->sh = sh;
  memset(win->barred, 0, sizeof win->barred);
  // With the layer, the window's own buffer is the surface's size (it is
  // only the background), so the layer is placed to a surface pixel.
  ANativeWindow_setBuffersGeometry(on, ba_layer() ? sw : (int32_t)win->bw,
    ba_layer() ? sh : (int32_t)win->bh, WINDOW_FORMAT_RGBX_8888);
}

// Touches
// -------

static uint32_t lc_at(float v, int32_t s, uint32_t b, uint32_t o, uint32_t most) {
  float f = s > 0 ? floorf(v * (float)b / (float)s) - (float)o : 0;
  return f < 0 ? 0 : f >= (float)most ? most - 1 : (uint32_t)f;
}

// The held finger's position at t (ns), from its last samples.
static void lc_at_time(LcWin* win, int64_t t, float* x, float* y) {
  BaTouch* h = win->hist;
  uint32_t n = win->nh;
  uint32_t i = n - 1;
  while (i > 0 && h[i - 1].t >= t) {
    i -= 1;
  }
  BaTouch a = i > 0 ? h[i - 1] : h[0];
  BaTouch b = h[i];
  if (i == n - 1 && n > 1 && t > b.t) {
    a = h[n - 2];
    int64_t gap  = b.t - a.t;
    int64_t most = gap / 2 < WIN_REACH ? gap / 2 : WIN_REACH;
    t = b.t + (t - b.t < most ? t - b.t : most);
  }
  float f = b.t > a.t ? (float)(t - a.t) / (float)(b.t - a.t) : 1;
  f = f < 0 ? 0 : f;
  *x = a.x + (b.x - a.x) * f;
  *y = a.y + (b.y - a.y) * f;
}

static void lc_hold(LcWin* win, BaTouch t) {
  if (win->nh == WIN_HIST) {
    memmove(win->hist, win->hist + 1, (WIN_HIST - 1) * sizeof t);
    win->nh -= 1;
  }
  win->hist[win->nh++] = t;
}

static void lc_mouse(LcWin* win, float sx, float sy, bool down) {
  lc_push(win, 2, lc_at(sx, win->sw, win->bw, win->ox, win->w),
    lc_at(sy, win->sh, win->bh, win->oy, win->h), down);
}

static void lc_move(LcWin* win, float sx, float sy) {
  lc_push(win, 3, lc_at(sx, win->sw, win->bw, win->ox, win->w),
    lc_at(sy, win->sh, win->bh, win->oy, win->h), 0);
}

// The touches since the last frame as events: a press, one move per
// frame (the finger resampled to WIN_LAG before now), a release.
static void lc_pump(LcWin* win) {
  BaTouch  ts[256];
  bool     closed = false;
  uint32_t n;
  do {
    n = ba_drain(ts, 256, &closed);
    for (uint32_t i = 0; i < n; i += 1) {
      BaTouch t = ts[i];
      if (t.kind == BA_DOWN) {
        win->nh    = 0;
        win->held  = true;
        win->moved = false;
        lc_hold(win, t);
        lc_mouse(win, t.x, t.y, true);
      } else if (t.kind == BA_MOVE) {
        lc_hold(win, t);
        win->moved = true;
      } else {
        lc_move(win, t.x, t.y);
        lc_mouse(win, t.x, t.y, false);
        win->held  = false;
        win->moved = false;
      }
    }
  } while (n == 256);
  if (win->held && win->moved) {
    float x, y;
    lc_at_time(win, (int64_t)lc_tick() - WIN_LAG, &x, &y);
    lc_move(win, x, y);
    win->moved = false;
  }
  if (closed && !win->closed) {
    win->closed = true;
    lc_push(win, 1, 0, 0, 0);
  }
}

// Frames
// ------

// A row of the frame, B G R X, into RGBX_8888's words (bytes R G B X).
static void lc_row(uint32_t* dst, lean_object* row, uint32_t w) {
  const uint8_t* s = lean_sarray_cptr(row);
  size_t         n = lean_sarray_size(row) / 4;
  n = n < w ? n : w;
  for (size_t x = 0; x < n; x += 1) {
    dst[x] = 0xFF000000u | (uint32_t)s[4 * x] << 16 | (uint32_t)s[4 * x + 1] << 8 | s[4 * x + 2];
  }
}

// The frame f at offset y into pix: the rows kept from the last frame
// moved with the offset's change, the new ones copied.
static void lc_draw(LcWin* win, b_lean_obj_arg f, uint32_t y, uint32_t ver) {
  uint32_t w = win->w;
  uint32_t h = win->h;
  if (win->pix == NULL) {
    win->pix = calloc((size_t)w * h, 4);
    if (win->pix == NULL) {
      abort();
    }
  }
  size_t        fh   = lean_array_size(f);
  lean_object** rows = lean_array_cptr(f);
  if (f == win->last && y == win->off) {
    win->dirty = false;
    return;
  }
  win->dirty = true;
  lean_object** old = NULL;
  int64_t       d   = 0;
  if (win->last != NULL && ver == win->ver) {
    old = lean_array_cptr(win->last);
    d   = (int64_t)y - (int64_t)win->off;
    if (d >= (int64_t)h || -d >= (int64_t)h) {
      old = NULL;
    } else if (d > 0) {
      memmove(win->pix, win->pix + (size_t)d * w, (size_t)(h - d) * w * 4);
    } else if (d < 0) {
      memmove(win->pix + (size_t)(-d) * w, win->pix, (size_t)(h + d) * w * 4);
    }
  }
  size_t oh = win->last != NULL ? lean_array_size(win->last) : 0;
  for (uint32_t r = 0; r < h && r < fh; r += 1) {
    int64_t at = (int64_t)r + d;  // the row's place in the last frame
    if (old != NULL && at >= 0 && at < (int64_t)oh && old[at] == rows[r]) {
      continue;
    }
    lc_row(win->pix + (size_t)r * w, rows[r], w);
    win->rows += 1;
  }
  lean_inc(f);
  if (win->last != NULL) {
    lean_dec(win->last);
  }
  win->last = f;
  win->off  = y;
  win->ver  = ver;
}

// The bars around the frame, black, once per buffer of the surface's
// queue (the frame's copy never touches them): a buffer is known by its
// address, forgotten when the surface or its size changes (lc_fit).
static void lc_bars(LcWin* win, uint32_t* bits, int32_t stride) {
  for (uint32_t i = 0; i < 4; i += 1) {
    if (win->barred[i] == bits) {
      return;
    }
  }
  memmove(win->barred + 1, win->barred, 3 * sizeof(void*));
  win->barred[0] = bits;
  for (uint32_t y = 0; y < win->bh; y += 1) {
    uint32_t* row = bits + (size_t)y * stride;
    bool      all = y < win->oy || y >= win->oy + win->h;
    for (uint32_t x = 0; x < win->bw; x += 1) {
      if (all || x < win->ox || x >= win->ox + win->w) {
        row[x] = 0xFF000000u;
      }
    }
  }
}

// With the layer (layer.c): the window itself is posted once in the
// frame's corner colour (behind rows a slide uncovers), and the frame
// goes to the layer, drawn at its offset (sliding with the vsync's
// scroll when the app follows the native scroll).
static bool lc_layer(LcWin* win, ANativeWindow* on) {
  if (!ba_layer()) {
    return false;
  }
  if (on != win->layered) {
    ANativeWindow_Buffer b;
    if (ANativeWindow_lock(on, &b, NULL) == 0) {
      uint32_t bg = win->pix[0];  // the frame's corner: the app's background
      for (int32_t y = 0; y < b.height; y += 1) {
        uint32_t* row = (uint32_t*)b.bits + (size_t)y * b.stride;
        for (int32_t x = 0; x < b.width; x += 1) {
          row[x] = bg;
        }
      }
      ANativeWindow_unlockAndPost(on);
    }
    win->layered = on;
  }
  bl_attach(on);
  ba_unlock();
  // The layer is placed in the window's buffer coordinates, surface px.
  float s = (float)win->bh / (float)win->sh;
  bl_present((int32_t)lroundf((float)win->ox / s), (int32_t)lroundf((float)win->oy / s), s,
    win->pix, win->w, win->h, win->off, ba_native_scroll());
  return true;
}

// Posting waits for a free buffer of the surface's queue: the display's
// pace. With no surface (the app in the background) it waits for one.
static void lc_show(LcWin* win) {
  // An unchanged frame on the layer: nothing to hand over, one vsync's wait.
  if (ba_layer() && !win->dirty && win->layered != NULL && bl_idle()) {
    return;
  }
  int32_t        sw, sh;
  ANativeWindow* on = ba_lock(&sw, &sh);
  if (on == NULL) {
    return;
  }
  lc_fit(win, on, sw, sh);
  if (lc_layer(win, on)) {
    return;  // lc_layer released the window
  }
  ANativeWindow_Buffer b;
  if (ANativeWindow_lock(on, &b, NULL) == 0) {
    if ((uint32_t)b.width >= win->bw && (uint32_t)b.height >= win->bh) {
      uint32_t* bits = b.bits;
      lc_bars(win, bits, b.stride);
      for (uint32_t y = 0; y < win->h; y += 1) {
        memcpy(bits + (size_t)(y + win->oy) * b.stride + win->ox,
          win->pix + (size_t)y * win->w, (size_t)win->w * 4);
      }
    }
    ANativeWindow_unlockAndPost(on);
  }
  ba_unlock();
}

// Every 120 frames, logcat (tag lean) gets the mean cost per frame: the
// copy of the new rows (with how many), the show (the waits for the
// surface and a free buffer, the post), and the time in Lean (the app's
// frame and tick), and the native scroll's last offset (the e2e test
// renders the frame at it to compare with the screen).
static void lc_time(LcWin* win, uint64_t t0, uint64_t t1, uint64_t t2) {
  static uint64_t n, copy, show, app, last;
  if (last != 0) {
    app += t0 - last;
  }
  copy += t1 - t0;
  show += t2 - t1;
  last  = t2;
  if (++n == 120) {
    __android_log_print(ANDROID_LOG_INFO, "lean",
      "twin ms/frame: lean %.1f copy %.1f (%llu rows) show %.1f top %u", app / 120e6,
      copy / 120e6, (unsigned long long)(win->rows / 120), show / 120e6, win->top);
    n = copy = show = app = 0;
    win->rows = 0;
  }
}

// Platform.lean
// -------------

lean_obj_res lc_window_open(uint32_t w, uint32_t h) {
  LcWin* win = calloc(1, sizeof *win);
  if (win == NULL || w < 1 || h < 1 || w > 16384 || h > 16384) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("window: bad size")));
  }
  win->w      = w;
  win->h      = h;
  win_current = win;
  return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res lc_window_frame(b_lean_obj_arg f, uint32_t y, uint32_t v) {
  LcWin* win = win_current;
  if (win == NULL) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("window: not open")));
  }
  uint64_t t0 = lc_tick();
  lc_pump(win);
  lc_draw(win, f, y, v);
  uint64_t t1 = lc_tick();
  lc_show(win);
  lc_time(win, t0, t1, lc_tick());
  lean_object* evs = lean_mk_empty_array_with_capacity(lean_box(win->n * 4));
  for (uint32_t i = 0; i < win->n * 4; i += 1) {
    evs = lean_array_push(evs, lean_box_uint32(win->evs[i]));
  }
  win->n = 0;
  return lean_io_result_mk_ok(evs);
}

lean_obj_res lc_native_scroll(uint32_t content_h) {
  LcWin*   win = win_current;
  uint32_t y   = 0xFFFFFFFFu;
  if (win != NULL && ba_native_scroll()) {
    float scale = win->sh > 0 ? (float)win->bh / (float)win->sh : 1;
    bl_start(ba_ahead());
    bl_scroll_needs(content_h, win->bh, scale);  // the screen's height, frame px
    uint32_t got;
    if (bl_scroll_y(&got)) {
      y        = got;
      win->top = got;
    }
  }
  return lean_io_result_mk_ok(lean_box_uint32(y));
}

lean_obj_res lc_slides(void) {
  return lean_io_result_mk_ok(lean_box(lc_slides_on));
}
