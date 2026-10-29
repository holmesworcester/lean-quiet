// The Lean app's window on iOS
// Lean publishes cropped rectangles and pixels through Session.present.
// The visible list is outside the physics scroll view, so UIKit cannot
// move it independently. Each vsync calls the compiled Lean translation
// and holdLine-fill helpers. Pixel/point conversion and copying are native.
// Raw touches retain pointer identity, time, cancellation and displayed
// frame serial; Input classifies them. Only accepted samples drive the
// hidden UIScrollView's native animation. IME text/composition stays UIKit's.

// The control channel (ctl_ios.c) exists only in development builds
// (LQ_CTL, set by build_ios.sh unless RELEASE=1), and every connection
// must first send its token. From the launch's environment (SIMCTL_CHILD_x
// for simctl launch): LEANQUIET_CTL_PORT=<port> (default 7417, 0: none),
// LEANQUIET_CTL_TOKEN=<hex> (else a new one in Documents/ctl.token),
// LEANQUIET_CTL_REMOTE=1 (listen on every interface, for a device test).

#import <UIKit/UIKit.h>
#import <AVFoundation/AVFoundation.h>
#import <QuartzCore/QuartzCore.h>
#import <IOSurface/IOSurfaceRef.h>
#include <lean/lean.h>
#include "../native/thread.h"
#import <UIKit/UIGestureRecognizerSubclass.h>
#include <math.h>
#include <pthread.h>
#include <stdatomic.h>
#include <time.h>
#include <fcntl.h>
#include <unistd.h>

int  lean_app_main(int argc, char** argv);
#ifdef LQ_CTL
void lq_ctl_start(int port, const char* token_file);
#endif

#define LQ_RING 3


enum { LQ_LIST = 0, LQ_TOP = 1, LQ_BOT = 2, LQ_HOLD = 3 };

typedef struct {
  uint32_t*    pix;     // B G R A words, w x h
  uint32_t     w, h;
  lean_object* last;    // the frame in pix (a reference), or NULL
  uint32_t     off;     // its offset (the list's)
  bool         dirty;   // pix changed since it was last shown
  IOSurfaceRef ring[LQ_RING];
  uint32_t     next;
  IOSurfaceRef shown;   // what the layer shows (one of ring), to be set
} LqStage;

static pthread_mutex_t lq_mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t  lq_cv = PTHREAD_COND_INITIALIZER;
static bool            lq_up;      // the view is laid out in its window
static _Atomic bool    lq_foreground;
static NSMutableArray<NSString*>* lq_urls;
lean_obj_res lq_poll(void);
static bool            lq_gone;    // the app is going away
static bool            lq_closed;  // the close event was handed over

// The screen, px, as of the last layout (under lq_mu).
static uint32_t lq_w, lq_h, lq_itop, lq_ibot, lq_dpi;
static uint32_t lq_read_w, lq_read_h;
static double   lq_k = 3;          // px per point

// Events for the next frame, eight words each (under lq_mu).
static uint32_t* lq_evs;
static uint32_t  lq_n, lq_cap;

// The keyboard's text as last reported (under lq_mu): UTF-8, and
// [selStart, selEnd, compStart, compEnd] in code points.
static char*    lq_text_s;
static uint32_t lq_pos[4];

static _Atomic double   lq_offset;     // the scroll view's offset, px
static _Atomic uint32_t lq_content_h;  // Lean's content height, px
static _Atomic double   lq_pend_by;    // scrollBy's not yet applied, px
static _Atomic bool     lq_pend_to;
static _Atomic double   lq_pend_b;

static LqStage           lq_st[4];
static uint32_t          lq_over;
static uint32_t          lq_list_bg = 0xFF000000u;
static dispatch_semaphore_t lq_vsync;
static _Atomic bool      lq_vsync_due;

static UIView*        lq_root;
static UIScrollView*  lq_sv;
static CALayer*       lq_list;
static CALayer*       lq_hold;
static uint32_t       lq_place[LQ_PLACEMENT_WORDS];
static bool           lq_placed;
static int32_t        lq_shown_shift;
static UIView*        lq_header;
static UIView*        lq_composer;
static UIView*        lq_fill;     // below the composer, to the screen's bottom
static UIView*        lq_probe;    // on the keyboard layout guide's top
static UITextField*   lq_field;
static uint32_t       lq_shown_top_h, lq_shown_bot_h;
static bool           lq_shown_pin;
static uint32_t       lq_shown_frame;
static uint32_t       lq_tap[3];       // the last list tap reported: kind, x, y

static uint64_t lq_tick(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (uint64_t)ts.tv_sec * 1000000000u + (uint64_t)ts.tv_nsec;
}

// Under lq_mu.
static void lq_raw(uint32_t kind, uint32_t a, uint32_t b, uint32_t c, uint64_t ms) {
  if (lq_n == lq_cap) {
    lq_cap = lq_cap == 0 ? 64 : lq_cap * 2;
    lq_evs = realloc(lq_evs, (size_t)lq_cap * 32);
    if (lq_evs == NULL) {
      abort();
    }
  }
  uint32_t* ev = lq_evs + (size_t)lq_n * 8;
  ev[0] = kind;
  ev[1] = a;
  ev[2] = b;
  ev[3] = c;
  ev[4] = ms; ev[5] = ms >> 32; ev[6] = lq_shown_frame; ev[7] = lq_shown_shift;
  lq_n += 1;
}

static void lq_push(uint32_t kind, uint32_t a, uint32_t b, uint32_t c) {
  lq_raw(kind >= 9 && kind <= 12 ? kind + 7 : kind, a, b, c, lq_tick() / 1000000);
}

static void lq_event(uint32_t kind, uint32_t a, uint32_t b, uint32_t c) {
  pthread_mutex_lock(&lq_mu);
  lq_push(kind, a, b, c);
  pthread_mutex_unlock(&lq_mu);
}

static uint32_t lq_px(double pt) {
  double v = round(pt * lq_k);
  return v <= 0 ? 0 : (uint32_t)v;
}

// Frames
// ------

// A Lean row (R G B X) into B G R A words.
static void lq_row(uint32_t* dst, lean_object* row, uint32_t w) {
  size_t n = lean_sarray_size(row) / 4;
  n = n < w ? n : w;
  const uint32_t* src = (const uint32_t*)lean_sarray_cptr(row);
  for (size_t i = 0; i < n; i += 1) {
    uint32_t p = src[i];
    dst[i] = 0xFF000000u | ((p & 0xFFu) << 16) | (p & 0xFF00u) | ((p >> 16) & 0xFFu);
  }
  for (size_t i = n; i < w; i += 1) {
    dst[i] = 0xFF000000u;
  }
}

static IOSurfaceRef lq_surface(uint32_t w, uint32_t h) {
  NSDictionary* p = @{
    (id)kIOSurfaceWidth: @(w), (id)kIOSurfaceHeight: @(h),
    (id)kIOSurfaceBytesPerElement: @4, (id)kIOSurfacePixelFormat: @((uint32_t)'BGRA'),
  };
  return IOSurfaceCreate((__bridge CFDictionaryRef)p);
}

// The frame f into a layer's staging buffer. For the list (shift), rows
// kept from the last frame move with the offset's change: frame row r
// drawn at offset y holds what row r + (last - y) held at the last offset.
static void lq_stage(LqStage* s, b_lean_obj_arg f, uint32_t w, uint32_t y, bool shift) {
  uint32_t h = (uint32_t)lean_array_size(f);
  if (h == 0) {
    return;
  }
  if (s->pix == NULL || s->w != w || s->h != h) {
    free(s->pix);
    s->pix = calloc((size_t)w * h, 4);
    if (s->pix == NULL) {
      abort();
    }
    for (int i = 0; i < LQ_RING; i += 1) {
      if (s->ring[i] != NULL) {
        CFRelease(s->ring[i]);
      }
      s->ring[i] = lq_surface(w, h);
      if (s->ring[i] == NULL) {
        abort();
      }
    }
    s->w = w;
    s->h = h;
    if (s->last != NULL) {
      lean_dec(s->last);
      s->last = NULL;
    }
  }
  if (f == s->last && y == s->off) {
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
    changed = true;
  }
  lean_inc(f);
  if (s->last != NULL) {
    lean_dec(s->last);
  }
  s->last  = f;
  s->off   = y;
  s->dirty = s->dirty || changed;
}

// Waits for the next display refresh (at most 50 ms: none come while the
// app is in the background), so Lean shows at most one frame a refresh.
static void lq_wait_vsync(void) {
  dispatch_semaphore_wait(lq_vsync, dispatch_time(DISPATCH_TIME_NOW, 50 * NSEC_PER_MSEC));
  lq_vsync_due = false;
}

// The staging buffer into a surface of its ring the compositor is not
// reading; false (nothing shown) if all stay in use for 8 refreshes.
static bool lq_fill_surface(LqStage* s) {
  IOSurfaceRef to = NULL;
  for (int tries = 0; tries < 8 && to == NULL; tries += 1) {
    for (int i = 0; i < LQ_RING; i += 1) {
      IOSurfaceRef c = s->ring[(s->next + i) % LQ_RING];
      if (c != s->shown && !IOSurfaceIsInUse(c)) {
        s->next = (s->next + i + 1) % LQ_RING;
        to = c;
        break;
      }
    }
    if (to == NULL) {
      lq_wait_vsync();
    }
  }
  if (to == NULL) {
    return false;
  }
  size_t rb = (size_t)s->w * 4;
  IOSurfaceLock(to, 0, NULL);
  uint8_t* base   = IOSurfaceGetBaseAddress(to);
  size_t   stride = IOSurfaceGetBytesPerRow(to);
  if (stride == rb) {
    memcpy(base, s->pix, rb * s->h);
  } else {
    for (uint32_t r = 0; r < s->h; r += 1) {
      memcpy(base + r * stride, (uint8_t*)s->pix + r * rb, rb);
    }
  }
  IOSurfaceUnlock(to, 0, NULL);
  s->shown = to;
  s->dirty = false;
  return true;
}

static UIColor* lq_color(uint32_t bgra) {
  return [UIColor colorWithRed:((bgra >> 16) & 0xFF) / 255.0 green:((bgra >> 8) & 0xFF) / 255.0
                          blue:(bgra & 0xFF) / 255.0 alpha:1];
}

// Platform.lean
// -------------

lean_obj_res lq_screen(void) {
  pthread_mutex_lock(&lq_mu);
  static bool waited;
  while (!waited && !lq_up && !lq_gone) {
    pthread_cond_wait(&lq_cv, &lq_mu);
  }
  waited = true;
  uint32_t v[5] = { lq_w, lq_h, lq_itop, lq_ibot, lq_dpi };
  lq_read_w = lq_w; lq_read_h = lq_h;
  pthread_mutex_unlock(&lq_mu);
  lean_object* a = lean_mk_empty_array_with_capacity(lean_box(5));
  for (int i = 0; i < 5; i += 1) {
    a = lean_array_push(a, lean_box_uint32(v[i]));
  }
  return lean_io_result_mk_ok(a);
}

lean_obj_res lq_scroll(uint32_t content_h, uint32_t view_h) {
  (void)view_h;  // the scroll view's own height is the viewport's now
  atomic_store(&lq_content_h, content_h);
  double b = atomic_load(&lq_offset);
  return lean_io_result_mk_ok(lean_box_float(b));
}

lean_obj_res lq_scroll_by(double d) {
  double cur = atomic_load(&lq_pend_by);
  while (!atomic_compare_exchange_weak(&lq_pend_by, &cur, cur + d)) {
  }
  return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res lq_scroll_to(double b) {
  atomic_store(&lq_pend_b, b);
  atomic_store(&lq_pend_by, 0.0);
  atomic_store(&lq_pend_to, true);
  return lean_io_result_mk_ok(lean_box(0));
}

// The same compiled Lean translation/fill on each display refresh.
// UIKit only converts the resulting rectangles from pixels to points.
static void lq_translate(void) {
  if (!lq_placed) return;
  lq_slide_thread_init();  // Both first publication and CADisplayLink run here.
  int32_t sample = (int32_t)llround(atomic_load(&lq_offset));
  CALayer* layers[2] = {lq_list, lq_hold};
  uint32_t heights[2] = {lq_place[21], lq_place[25]};
  [CATransaction begin];
  [CATransaction setDisableActions:YES];
  for (int k = 0; k < 2; k++) {
    uint32_t r[4]; lq_slide_rect(lq_place, sample, k, r);
    CALayer* layer = layers[k];
    layer.hidden = r[1] <= r[0];
    layer.contentsRect = CGRectMake(0, heights[k] ? (double)r[0] / heights[k] : 0,
      1, heights[k] ? (double)(r[1] - r[0]) / heights[k] : 0);
    layer.frame = CGRectMake(0, r[2] / lq_k, lq_w / lq_k, (r[3] - r[2]) / lq_k);
  }
  [CATransaction commit];
  pthread_mutex_lock(&lq_mu);
  lq_shown_shift = (int32_t)lq_slide_delta(lq_place[22], lq_place[15], sample);
  pthread_mutex_unlock(&lq_mu);
}

// pin: the list frame is a page, pinned (the header comment; Placement.lean).
lean_obj_res lq_frame(b_lean_obj_arg list, uint32_t b, uint32_t over, b_lean_obj_arg top,
  b_lean_obj_arg bot, uint8_t pin, b_lean_obj_arg placement, b_lean_obj_arg hold) {
  lq_slide_warm();  // Lean thread, before dispatching the first publication.
  uint32_t p[LQ_PLACEMENT_WORDS];
  for (int i = 0; i < LQ_PLACEMENT_WORDS; i++) p[i] = lean_unbox_uint32(lean_array_get_core(placement, i));
  NSData* geometry = [NSData dataWithBytes:p length:sizeof p];
  pthread_mutex_lock(&lq_mu);
  bool available = lq_foreground && lq_up;
  pthread_mutex_unlock(&lq_mu);
  if (!available) return lq_poll();
  uint32_t w  = lq_read_w;
  uint32_t h  = lq_read_h;
  lq_over     = over;
  lq_stage(&lq_st[LQ_LIST], list, w, b, true);
  lq_stage(&lq_st[LQ_TOP], top, w, 0, false);
  lq_stage(&lq_st[LQ_BOT], bot, w, 0, false);
  lq_stage(&lq_st[LQ_HOLD], hold, w, 0, false);
  IOSurfaceRef show[4] = { NULL, NULL, NULL, NULL };
  for (int k = 0; k < 4; k += 1) {
    if (lq_st[k].dirty && lq_fill_surface(&lq_st[k])) {
      show[k] = lq_st[k].shown;
    }
  }
  IOSurfaceRef show_list = show[LQ_LIST], show_top = show[LQ_TOP], show_bot = show[LQ_BOT], show_hold = show[LQ_HOLD];
  // What the layers need beside their contents: the list frame's place
  // (content px [bf - over, bf + h - over)), the chrome's heights, the
  // composer's last row (repeated down to the screen's bottom), the list's
  // background (its frame's first pixel, behind rows a slide uncovers).
  LqStage* ls     = &lq_st[LQ_LIST];
  uint32_t lh     = ls->h;
  uint32_t top_h  = (uint32_t)lean_array_size(top);
  uint32_t bot_h  = (uint32_t)lean_array_size(bot);
  uint32_t fill   = lq_st[LQ_BOT].pix != NULL
    ? lq_st[LQ_BOT].pix[(size_t)(lq_st[LQ_BOT].h - 1) * lq_st[LQ_BOT].w] : 0xFF000000u;
  uint32_t list_bg = ls->pix != NULL ? ls->pix[0] : 0xFF000000u;
  uint32_t ch      = atomic_load(&lq_content_h);
  bool     to      = atomic_exchange(&lq_pend_to, false);
  double   tob     = atomic_load(&lq_pend_b);
  double   by      = atomic_exchange(&lq_pend_by, 0.0);
  lq_wait_vsync();
  __block bool presented = false;
  dispatch_sync(dispatch_get_main_queue(), ^{
    if (!lq_foreground || !lq_up || w != lq_w || h != lq_h) return;
    presented = true;
    [CATransaction begin];
    [CATransaction setDisableActions:YES];
    double k = lq_k;
    if (show_top != NULL) {
      lq_header.layer.contents = (__bridge id)show_top;
    }
    if (show_bot != NULL) {
      lq_composer.layer.contents = (__bridge id)show_bot;
      lq_fill.backgroundColor    = lq_color(fill);
    }
    if (list_bg != lq_list_bg) {
      lq_list_bg = list_bg;
      lq_sv.backgroundColor = lq_color(list_bg);
      lq_root.backgroundColor   = lq_color(list_bg);
    }
    lq_shown_top_h = top_h;
    lq_shown_bot_h = bot_h;
    lq_shown_pin = pin != 0;
    const uint32_t* r = geometry.bytes;
    memcpy(lq_place, r, sizeof lq_place);
    lq_placed = true;
    lq_shown_frame = r[16];
    // Copy Lean's classified event for the existing test diagnostic.
    memcpy(lq_tap, r + 17, sizeof lq_tap);
    // Only conversion from physical pixels to UIKit points lives here.
    lq_header.frame = CGRectMake(0, r[6] / k, w / k, (r[7] - r[6]) / k);
    lq_composer.frame = CGRectMake(0, r[10] / k, w / k, (r[11] - r[10]) / k);
    lq_fill.frame = CGRectMake(0, r[12] / k, w / k, (r[13] - r[12]) / k);
    lq_sv.frame = CGRectMake(0, 0, w / k, r[14] / k);
    CGFloat height = ch / k;
    if (lq_sv.contentSize.height != height) {
      lq_sv.contentSize = CGSizeMake(lq_sv.bounds.size.width, height);
    }
    if (to) {
      // a jump: stops a fling
      [lq_sv setContentOffset:CGPointMake(0, tob / k) animated:NO];
    }
    if (by != 0) {
      // a move: the property keeps a fling going from the moved place
      CGPoint p = lq_sv.contentOffset;
      p.y += by / k;
      lq_sv.contentOffset = p;
    }
    if (show_list != NULL) lq_list.contents = (__bridge id)show_list;
    if (show_hold != NULL) lq_hold.contents = (__bridge id)show_hold;
    lq_translate();
    [CATransaction commit];
  });
  if (!presented) {
    for (int k = 0; k < 4; k++) {
      if (lq_st[k].last != NULL) lean_dec(lq_st[k].last);
      lq_st[k].last = NULL;
    }
  }
  pthread_mutex_lock(&lq_mu);
  if (lq_gone && !lq_closed) {
    lq_closed = true;
    lq_push(1, 0, 0, 0);
  }
  lq_push(13, 0, 0, 0);
  lean_object* evs = lean_mk_empty_array_with_capacity(lean_box(lq_n * 8));
  for (uint32_t i = 0; i < lq_n * 8; i += 1) {
    evs = lean_array_push(evs, lean_box_uint32(lq_evs[i]));
  }
  lq_n = 0;
  pthread_mutex_unlock(&lq_mu);
  return lean_io_result_mk_ok(evs);
}

lean_obj_res lq_text(void) {
  pthread_mutex_lock(&lq_mu);
  lean_object* s = lean_mk_string(lq_text_s != NULL ? lq_text_s : "");
  lean_object* a = lean_mk_empty_array_with_capacity(lean_box(4));
  for (int i = 0; i < 4; i += 1) {
    a = lean_array_push(a, lean_box_uint32(lq_pos[i]));
  }
  pthread_mutex_unlock(&lq_mu);
  lean_object* p = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p, 0, s);
  lean_ctor_set(p, 1, a);
  return lean_io_result_mk_ok(p);
}

lean_obj_res lq_ime(uint8_t show) {
  dispatch_async(dispatch_get_main_queue(), ^{
    if (show) {
      [lq_field becomeFirstResponder];
    } else {
      [lq_field resignFirstResponder];
    }
  });
  return lean_io_result_mk_ok(lean_box(0));
}

static void lq_report(void);

// The camera
// ----------

// Platform.scan and luma, as android/twin's Camera2 does them: the back
// camera's frames (1280 x 720, 420f: full-range luma), and the newest
// one's Y plane handed to Lean with the clockwise turn it still needs to be
// upright on the portrait screen. The connection is asked to rotate the
// buffers to portrait itself (videoRotationAngle 90, AVFoundation's
// portrait), so AVFoundation, which knows how the camera is mounted, does
// the turning; the turn handed to Lean is read off each frame as it comes:
// 0 for a portrait buffer, 90 (the quarter that makes a back camera's
// landscape buffer portrait) where the connection could not rotate. Lean
// draws the preview and decodes (Camera.preview, Qr.decodeLuma). With no
// camera (the Simulator) nothing starts and no frames come: Lean keeps its
// waiting state.

@interface LeanCamera : NSObject <AVCaptureVideoDataOutputSampleBufferDelegate>
@end

static dispatch_queue_t lq_cam_q;    // the camera's own (start, stop, frames)
static AVCaptureSession* lq_cam;     // running, or nil
static LeanCamera*       lq_cam_d;
static bool              lq_cam_want;
static uint8_t*          lq_y;       // the newest Y plane, or NULL (under lq_mu)
static size_t            lq_yn;
static uint32_t          lq_yhdr[4]; // w, h, stride, orientation

@implementation LeanCamera

- (void)captureOutput:(AVCaptureOutput*)o didOutputSampleBuffer:(CMSampleBufferRef)sb
    fromConnection:(AVCaptureConnection*)c {
  if (!lq_cam_want || !lq_foreground) return;
  CVPixelBufferRef pb = CMSampleBufferGetImageBuffer(sb);
  CVPixelBufferLockBaseAddress(pb, kCVPixelBufferLock_ReadOnly);
  size_t   h = CVPixelBufferGetHeightOfPlane(pb, 0);
  size_t   r = CVPixelBufferGetBytesPerRowOfPlane(pb, 0);
  uint8_t* y = malloc(r * h);
  memcpy(y, CVPixelBufferGetBaseAddressOfPlane(pb, 0), r * h);
  uint32_t w = (uint32_t)CVPixelBufferGetWidthOfPlane(pb, 0);
  uint32_t hdr[4] = { w, (uint32_t)h, (uint32_t)r, w > h ? 90 : 0 };
  CVPixelBufferUnlockBaseAddress(pb, kCVPixelBufferLock_ReadOnly);
  pthread_mutex_lock(&lq_mu);
  free(lq_y);
  lq_y  = y;
  lq_yn = r * h;
  memcpy(lq_yhdr, hdr, sizeof hdr);
  pthread_mutex_unlock(&lq_mu);
}

@end

static AVCaptureDevice* lq_cam_device(void) {
  return [AVCaptureDevice defaultDeviceWithDeviceType:AVCaptureDeviceTypeBuiltInWideAngleCamera
    mediaType:AVMediaTypeVideo position:AVCaptureDevicePositionBack];
}

// On lq_cam_q.
static void lq_cam_start(void) {
  NSError*              e  = nil;
  AVCaptureDeviceInput* in = [AVCaptureDeviceInput deviceInputWithDevice:lq_cam_device() error:&e];
  if (in == nil) {
    fprintf(stderr, "camera: cannot open: %s\n", e.localizedDescription.UTF8String);
    return;
  }
  AVCaptureSession*         s   = [AVCaptureSession new];
  AVCaptureVideoDataOutput* out = [AVCaptureVideoDataOutput new];
  s.sessionPreset   = AVCaptureSessionPreset1280x720;
  out.videoSettings = @{ (id)kCVPixelBufferPixelFormatTypeKey: @(kCVPixelFormatType_420YpCbCr8BiPlanarFullRange) };
  out.alwaysDiscardsLateVideoFrames = YES;
  [out setSampleBufferDelegate:lq_cam_d queue:lq_cam_q];
  if (![s canAddInput:in] || ![s canAddOutput:out]) {
    fprintf(stderr, "camera: cannot open\n");
    return;
  }
  [s addInput:in];
  [s addOutput:out];
  AVCaptureConnection* cn = [out connectionWithMediaType:AVMediaTypeVideo];
  if ([cn isVideoRotationAngleSupported:90]) {
    cn.videoRotationAngle = 90;  // portrait buffers (see the top)
  }
  [s startRunning];
  lq_cam = s;
  fprintf(stderr, "camera: opened 1280x720, %s\n",
    cn.videoRotationAngle == 90 ? "rotated to portrait by the connection" : "unrotated (Lean turns it)");
}

lean_obj_res lq_scan(uint8_t on) {
  dispatch_async(lq_cam_q, ^{
    fprintf(stderr, "camera %s\n", on ? "on" : "off");
    lq_cam_want = on != 0 && lq_foreground;
    pthread_mutex_lock(&lq_mu);
    free(lq_y); lq_y = NULL; lq_yn = 0;
    pthread_mutex_unlock(&lq_mu);
    if (lq_cam_want && lq_cam == nil && lq_cam_device() == nil) {
      fprintf(stderr, "camera: none\n");  // (the Simulator): no frames, and no permission asked
    } else if (lq_cam_want && lq_cam == nil) {
      AVAuthorizationStatus st = [AVCaptureDevice authorizationStatusForMediaType:AVMediaTypeVideo];
      if (st == AVAuthorizationStatusAuthorized) {
        lq_cam_start();
      } else if (st == AVAuthorizationStatusNotDetermined) {
        fprintf(stderr, "camera: asking for the permission\n");
        [AVCaptureDevice requestAccessForMediaType:AVMediaTypeVideo completionHandler:^(BOOL ok) {
          dispatch_async(lq_cam_q, ^{
            if (ok && lq_cam_want && lq_cam == nil) {
              lq_cam_start();
            }
          });
        }];
      } else {
        fprintf(stderr, "camera: not permitted\n");
      }
    } else if (!lq_cam_want && lq_cam != nil) {
      [lq_cam stopRunning];
      lq_cam = nil;
    }
  });
  return lean_io_result_mk_ok(lean_box(0));
}

// The newest frame's Y plane since the last call (Platform.luma).
lean_obj_res lq_luma(void) {
  pthread_mutex_lock(&lq_mu);
  uint8_t* y = lq_y;
  size_t   n = lq_yn;
  lq_y       = NULL;
  lean_object* hdr = lean_mk_empty_array();
  for (int i = 0; y != NULL && i < 4; i += 1) {
    hdr = lean_array_push(hdr, lean_box_uint32(lq_yhdr[i]));
  }
  pthread_mutex_unlock(&lq_mu);
  lean_object* px = lean_alloc_sarray(1, y ? n : 0, y ? n : 0);
  if (y != NULL) {
    memcpy(lean_sarray_cptr(px), y, n);
    free(y);
  }
  lean_object* p = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p, 0, hdr);
  lean_ctor_set(p, 1, px);
  return lean_io_result_mk_ok(p);
}

lean_obj_res lq_set_text(b_lean_obj_arg text) {
  NSString* s = [NSString stringWithUTF8String:lean_string_cstr(text)];
  dispatch_async(dispatch_get_main_queue(), ^{
    if ([lq_field.text isEqualToString:s]) return;
    lq_field.text = s;
    lq_report();
  });
  return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res lq_copy(b_lean_obj_arg text) {
  NSString* s = [NSString stringWithUTF8String:lean_string_cstr(text)];
  dispatch_async(dispatch_get_main_queue(), ^{
    UIPasteboard.generalPasteboard.string = s;
  });
  return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res lq_now_us(void) {
  return lean_io_result_mk_ok(lean_box_uint64(lq_tick() / 1000));
}

lean_obj_res lq_log(b_lean_obj_arg s) {
  NSLog(@"lean: %@", [NSString stringWithUTF8String:lean_string_cstr(s)]);
  return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res lq_tz_min(void) {
  time_t t = time(NULL);
  struct tm tm;
  localtime_r(&t, &tm);
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(int32_t)(tm.tm_gmtoff / 60)));
}

#ifdef LQ_CTL
// What the twin did, as UIKit has it, for tests (the control channel's
// `twin` line, answered here, not by Lean): the screen's width and
// density, whether the list frame is a page, the header's height and the
// frame's overscan, the screen rows of
// the list frame's first row and of the scroll view's bottom edge, the
// composer's top now, the last list tap reported (kind, x, y), the last
// camera frame's [w, h, stride, orientation], and the keyboard's text.
void lq_twin(char* out, size_t n) {
  dispatch_sync(dispatch_get_main_queue(), ^{
    double k    = lq_k;
    CGRect list = [lq_root.layer convertRect:lq_list.bounds fromLayer:lq_list];
    CGRect sv   = [lq_root convertRect:lq_sv.bounds fromView:lq_sv];
    CALayer* c  = lq_composer.layer.presentationLayer ?: lq_composer.layer;
    pthread_mutex_lock(&lq_mu);
    snprintf(out, n, "w %u dpi %u pin %d top %u over %u listY %ld svBottom %ld composerTop %ld "
      "tap %u %u %u luma %u %u %u %u field %s", lq_w, lq_dpi, lq_shown_pin, lq_shown_top_h, lq_over,
      lround(list.origin.y * k), lround(CGRectGetMaxY(sv) * k), lround(c.frame.origin.y * k),
      lq_tap[0], lq_tap[1], lq_tap[2], lq_yhdr[0], lq_yhdr[1], lq_yhdr[2], lq_yhdr[3],
      lq_text_s ? lq_text_s : "");
    pthread_mutex_unlock(&lq_mu);
  });
}

// `twin shot`: the app's window as UIKit renders it, to Documents/
// screen.png (read back with devicectl device copy from: there is no
// remote screenshot of an iPhone here). The status bar and the keyboard
// are other windows and are not in it.
void lq_twin_shot(char* out, size_t n) {
  dispatch_sync(dispatch_get_main_queue(), ^{
    UIView*  v = lq_root.window ?: lq_root;
    UIGraphicsImageRendererFormat* f = [UIGraphicsImageRendererFormat preferredFormat];
    f.scale = lq_k;
    UIImage* im = [[[UIGraphicsImageRenderer alloc] initWithBounds:v.bounds format:f]
      imageWithActions:^(UIGraphicsImageRendererContext* c) {
        [v drawViewHierarchyInRect:v.bounds afterScreenUpdates:NO];
      }];
    NSData* png = UIImagePNGRepresentation(im);
    BOOL    ok  = [png writeToFile:@"screen.png" atomically:YES];
    snprintf(out, n, "shot %s %.0fx%.0f", ok ? "Documents/screen.png" : "failed",
      im.size.width * im.scale, im.size.height * im.scale);
  });
}
#endif

// The keyboard's text
// -------------------

// UTF-16 offset i of s in code points.
static uint32_t lq_cp(NSString* s, NSInteger i) {
  NSUInteger n = s.length;
  uint32_t   c = 0;
  for (NSUInteger j = 0; j < (NSUInteger)i && j < n; j += 1) {
    unichar u = [s characterAtIndex:j];
    if (!(u >= 0xDC00 && u <= 0xDFFF)) {
      c += 1;
    }
  }
  return c;
}

// The field's text, selection and marked (composing) range to Lean, with
// a text event.
static void lq_report(void) {
  UITextField* f = lq_field;
  NSString*    t = f.text ?: @"";
  UITextRange* sel = f.selectedTextRange;
  UITextRange* mk  = f.markedTextRange;
  NSInteger ss = sel ? [f offsetFromPosition:f.beginningOfDocument toPosition:sel.start] : t.length;
  NSInteger se = sel ? [f offsetFromPosition:f.beginningOfDocument toPosition:sel.end] : t.length;
  NSInteger ms = mk ? [f offsetFromPosition:f.beginningOfDocument toPosition:mk.start] : ss;
  NSInteger me = mk ? [f offsetFromPosition:f.beginningOfDocument toPosition:mk.end] : ss;
  uint32_t  pos[4] = { lq_cp(t, ss), lq_cp(t, se), lq_cp(t, ms), lq_cp(t, me) };
  const char* u = t.UTF8String ?: "";
  pthread_mutex_lock(&lq_mu);
  free(lq_text_s);
  lq_text_s = strdup(u);
  memcpy(lq_pos, pos, sizeof pos);
  lq_push(4, 0, 0, 0);
  pthread_mutex_unlock(&lq_mu);
}

@interface LeanField : UITextField <UITextFieldDelegate>
@property(nonatomic) BOOL forwardingKey;
@end

@implementation LeanField

- (instancetype)initWithFrame:(CGRect)r {
  self = [super initWithFrame:r];
  // Drawn in nothing but clear (not alpha 0, which would hide it from
  // accessibility, and from XCUITest's typing too).
  self.delegate                       = self;
  self.borderStyle                    = UITextBorderStyleNone;
  self.backgroundColor                = UIColor.clearColor;
  self.tintColor                      = UIColor.clearColor;
  self.textColor                      = UIColor.clearColor;
  self.returnKeyType                  = UIReturnKeySend;
  self.autocapitalizationType         = UITextAutocapitalizationTypeSentences;
  self.enablesReturnKeyAutomatically  = NO;
  [self addTarget:self action:@selector(changed) forControlEvents:UIControlEventEditingChanged];
  return self;
}

- (void)changed {
  lq_report();
}

- (void)textFieldDidChangeSelection:(UITextField*)f {
  lq_report();
}

- (void)setMarkedText:(NSString*)s selectedRange:(NSRange)r {
  [super setMarkedText:s selectedRange:r];
  lq_report();
}

- (void)unmarkText {
  [super unmarkText];
  lq_report();
}

- (void)pressesBegan:(NSSet<UIPress*>*)presses withEvent:(UIPressesEvent*)event {
  for (UIPress* press in presses) if (press.key) lq_event(15, press.key.keyCode, 0, 0);
  self.forwardingKey = YES;
  [super pressesBegan:presses withEvent:event];
  self.forwardingKey = NO;
}
- (void)pressesEnded:(NSSet<UIPress*>*)presses withEvent:(UIPressesEvent*)event {
  for (UIPress* press in presses) if (press.key) lq_event(15, press.key.keyCode, 1, 0);
  [super pressesEnded:presses withEvent:event];
}

- (BOOL)textFieldShouldReturn:(UITextField*)f {
  // Hardware keys already have a raw record; this callback is the IME action.
  if (!self.forwardingKey) lq_event(5, 4, 0, 0);
  return NO;
}

@end

// Touches
// -------

// A passive raw observer: no tap/long/drag recognizers or thresholds.
@interface LeanTouches : UIGestureRecognizer
@property(nonatomic, strong) NSMapTable<UITouch*, NSNumber*>* ids;
@property(nonatomic) uint32_t nextId;
@end
@implementation LeanTouches
- (BOOL)canPreventGestureRecognizer:(UIGestureRecognizer*)other { return NO; }
- (BOOL)canBePreventedByGestureRecognizer:(UIGestureRecognizer*)other { return NO; }
- (void)forward:(NSSet<UITouch*>*)touches phase:(uint32_t)phase event:(UIEvent*)event {
  if (!self.ids) self.ids = [NSMapTable strongToStrongObjectsMapTable];
  NSArray* ordered = [[touches allObjects] sortedArrayUsingComparator:^NSComparisonResult(UITouch* a, UITouch* b) {
    if (a.timestamp != b.timestamp) return a.timestamp < b.timestamp ? NSOrderedAscending : NSOrderedDescending;
    return (uintptr_t)(__bridge void*)a < (uintptr_t)(__bridge void*)b ? NSOrderedAscending : NSOrderedDescending;
  }];
  for (UITouch* touch in ordered) {
    if (phase == 0) [self.ids setObject:@(++self.nextId) forKey:touch];
    NSNumber* pointer = [self.ids objectForKey:touch];
    if (!pointer) continue;
    NSArray* samples = phase == 1 ? [event coalescedTouchesForTouch:touch] : nil;
    if (!samples.count) samples = @[touch];
    pthread_mutex_lock(&lq_mu);
    for (UITouch* sample in samples) {
      CGPoint pos = [sample locationInView:lq_root];
      lq_raw(9 + phase, pointer.unsignedIntValue, (int32_t)lround(pos.x * lq_k),
        (int32_t)lround(pos.y * lq_k), (uint64_t)llround(sample.timestamp * 1000));
    }
    pthread_mutex_unlock(&lq_mu);
    if (phase >= 2) [self.ids removeObjectForKey:touch];
  }
  if (!self.ids.count) self.state = UIGestureRecognizerStateFailed;
}
- (void)touchesBegan:(NSSet*)touches withEvent:(UIEvent*)event { [self forward:touches phase:0 event:event]; }
- (void)touchesMoved:(NSSet*)touches withEvent:(UIEvent*)event { [self forward:touches phase:1 event:event]; }
- (void)touchesEnded:(NSSet*)touches withEvent:(UIEvent*)event { [self forward:touches phase:2 event:event]; }
- (void)touchesCancelled:(NSSet*)touches withEvent:(UIEvent*)event { [self forward:touches phase:3 event:event]; }
@end

// Accepted samples alone drive the native scroll animation. Its samples
// remain advisory; Lean clamps them before painting or mapping a touch.
lean_obj_res lq_motion(b_lean_obj_arg samples) {
  size_t n = lean_array_size(samples);
  uint32_t* words = malloc(n * sizeof *words);
  for (size_t i = 0; i < n; i++) words[i] = lean_unbox_uint32(lean_array_get_core(samples, i));
  dispatch_sync(dispatch_get_main_queue(), ^{
    static double last, time, velocity;
    static bool down;
    for (size_t i = 0; i + 7 < n; i += 8) {
      uint32_t phase = words[i] - 9;
      double y = (int32_t)words[i+3];
      double now = ((uint64_t)words[i+5] << 32) | words[i+4];
      if (phase == 3) { down = false; [lq_sv setContentOffset:lq_sv.contentOffset animated:NO]; }
      else if (phase == 0) { down = true; last = y; time = now; velocity = 0; }
      else if (down) {
        CGPoint pos = lq_sv.contentOffset;
        pos.y += (y - last) / lq_k;
        if (now > time) velocity = (y - last) / (now - time);
        lq_sv.contentOffset = pos;
        last = y; time = now;
        if (phase == 2) {
          down = false;
          pos.y += velocity * 180 / lq_k;
          [lq_sv setContentOffset:pos animated:YES];
        }
      }
    }
  });
  free(words);
  return lean_io_result_mk_ok(lean_box(0));
}

// The view
// --------

@interface LeanScroll : UIScrollView <UIScrollViewDelegate>
@end

@implementation LeanScroll

- (void)scrollViewDidScroll:(UIScrollView*)v {
  // The hidden physics view supplies signed samples. Lean interprets them
  // as distance from the content's end and clamps before painting.
  atomic_store(&lq_offset, v.contentOffset.y * lq_k);
}

@end

@interface LeanController : UIViewController
@end

@implementation LeanController

- (void)loadView {
  UIView* root = [UIView new];
  root.backgroundColor = UIColor.blackColor;
  self.view = root;
  lq_root   = root;

  LeanScroll* sv = [LeanScroll new];
  sv.delegate                               = sv;
  sv.userInteractionEnabled                 = NO;
  sv.hidden                                 = YES;
  sv.alwaysBounceVertical                   = YES;
  sv.scrollsToTop                           = NO;
  sv.contentInsetAdjustmentBehavior         = UIScrollViewContentInsetAdjustmentNever;
  sv.automaticallyAdjustsScrollIndicatorInsets = NO;

  lq_sv = sv;
  lq_hold = [CALayer layer];
  lq_hold.opaque = YES;
  [root.layer insertSublayer:lq_hold atIndex:0];
  lq_list   = [CALayer layer];
  lq_list.opaque    = YES;
  [root.layer insertSublayer:lq_list atIndex:1];

  UIView* header   = [UIView new];
  UIView* composer = [UIView new];
  UIView* fill     = [UIView new];
  for (UIView* v in @[ header, composer, fill ]) {
    v.userInteractionEnabled = NO;
  }
  UIView* probe = [UIView new];
  probe.userInteractionEnabled = NO;
  probe.translatesAutoresizingMaskIntoConstraints = NO;
  LeanField* field = [[LeanField alloc] initWithFrame:CGRectMake(0, 0, 1, 1)];
  lq_header   = header;
  lq_composer = composer;
  lq_fill     = fill;
  lq_probe    = probe;
  lq_field    = field;
  for (UIView* v in @[ sv, fill, composer, header, probe ]) {
    [root addSubview:v];
  }
  [composer addSubview:field];
  LeanTouches* raw = [[LeanTouches alloc] initWithTarget:nil action:nil];
  raw.cancelsTouchesInView = NO;
  raw.delaysTouchesBegan = NO;
  raw.delaysTouchesEnded = NO;
  [root addGestureRecognizer:raw];
  root.multipleTouchEnabled = YES;
  UILayoutGuide* kb = root.keyboardLayoutGuide;
  [NSLayoutConstraint activateConstraints:@[
    [probe.topAnchor constraintEqualToAnchor:kb.topAnchor],
    [probe.bottomAnchor constraintEqualToAnchor:root.bottomAnchor],
    [probe.leadingAnchor constraintEqualToAnchor:root.leadingAnchor],
    [probe.widthAnchor constraintEqualToConstant:1],
  ]];
}

// The screen's size and insets, px, for Platform.screen; the first layout
// in the window lets Lean's main go on.
- (void)viewDidLayoutSubviews {
  [super viewDidLayoutSubviews];
  UIView* v = self.view;
  if (v.window == nil) {
    pthread_mutex_lock(&lq_mu);
    lq_up = false;
    lq_push(11, 0, 0, 0);
    pthread_mutex_unlock(&lq_mu);
    return;
  }
  lq_k = v.window.screen.scale;
  UIEdgeInsets in = v.safeAreaInsets;
  pthread_mutex_lock(&lq_mu);
  lq_w    = lq_px(v.bounds.size.width);
  lq_h    = lq_px(v.bounds.size.height);
  lq_itop = lq_px(in.top);
  lq_ibot = lq_px(in.bottom);
  lq_dpi  = (uint32_t)lround(160 * lq_k);
  lq_push(12, 0, 0, 0);
  if (!lq_up && lq_w > 0 && lq_h > 0) {
    lq_up = true;
    lq_push(11, 1, 0, 0);
    pthread_cond_broadcast(&lq_cv);
  }
  pthread_mutex_unlock(&lq_mu);
}

- (UIStatusBarStyle)preferredStatusBarStyle {
  return UIStatusBarStyleLightContent;
}

@end

// The app
// -------

// Lean's stderr (and the twin's) also goes to Documents/lean.log, new at
// each launch, so a phone's run can be read back (devicectl device copy
// from) without holding its console: fd 2 becomes a pipe whose reader
// writes each chunk to the old stderr and to the file.
static void* lq_tee(void* arg) {
  int*    fds = arg;  // the pipe's read end, the old stderr, the file
  char    buf[4096];
  ssize_t n;
  while ((n = read(fds[0], buf, sizeof buf)) > 0) {
    write(fds[1], buf, (size_t)n);
    write(fds[2], buf, (size_t)n);
  }
  return NULL;
}

static void lq_log_to(const char* path) {
  static int fds[3];
  int        p[2];
  fds[2] = open(path, O_WRONLY | O_CREAT | O_TRUNC, 0644);
  if (fds[2] < 0 || pipe(p) != 0) {
    return;
  }
  fds[0] = p[0];
  fds[1] = dup(2);
  dup2(p[1], 2);
  close(p[1]);
  setvbuf(stderr, NULL, _IOLBF, 0);
  pthread_t t;
  pthread_create(&t, NULL, lq_tee, fds);
  pthread_detach(t);
}

static void* lq_run(void* arg) {
  // Lean's working directory: Documents (writable; quiet.db goes there),
  // with `assets` a link to the bundle's, made anew each launch (the
  // bundle's path changes with each install).
  NSString* docs = NSSearchPathForDirectoriesInDomains(NSDocumentDirectory, NSUserDomainMask, YES)[0];
  NSString* res  = [NSBundle.mainBundle.resourcePath stringByAppendingPathComponent:@"assets"];
  NSString* link = [docs stringByAppendingPathComponent:@"assets"];
  NSFileManager* fm = NSFileManager.defaultManager;
  [fm createDirectoryAtPath:docs withIntermediateDirectories:YES attributes:nil error:NULL];
  [fm removeItemAtPath:link error:NULL];
  [fm createSymbolicLinkAtPath:link withDestinationPath:res error:NULL];
  chdir(docs.fileSystemRepresentation);
  lq_log_to("lean.log");
  // Lean's threads (its main and every task worker) reserve 1 GB of stack
  // each on 64-bit; an iOS app's address space runs out after a few, and
  // pthread_create fails with EAGAIN (on the phone, not the Simulator).
  // 64 MB each, unless the launch says otherwise (read by lean_run_main).
  setenv("LEAN_STACK_SIZE_KB", "65536", 0);
  char* argv[] = { "LeanQuiet", NULL };
  int   code   = lean_app_main(1, argv);
  fflush(stderr);
  exit(code);
  return NULL;
}

@interface LeanDelegate : UIResponder <UIApplicationDelegate>
@property (strong, nonatomic) UIWindow* window;
@property (nonatomic) uint32_t ime;
@property (nonatomic) bool active;
@property (strong, nonatomic) CADisplayLink* displayLink;
@end

@implementation LeanDelegate

- (BOOL)application:(UIApplication*)app didFinishLaunchingWithOptions:(NSDictionary*)opts {
  lq_urls = [NSMutableArray new];
  NSURL* url = opts[UIApplicationLaunchOptionsURLKey];
  if (url != nil) [lq_urls addObject:url.absoluteString];
#ifdef LQ_CTL
  const char* port = getenv("LEANQUIET_CTL_PORT");
  int p = port != NULL ? atoi(port) : 7417;
  if (p > 0) {
    NSString* docs = NSSearchPathForDirectoriesInDomains(NSDocumentDirectory, NSUserDomainMask, YES)[0];
    [NSFileManager.defaultManager createDirectoryAtPath:docs withIntermediateDirectories:YES
      attributes:nil error:NULL];
    lq_ctl_start(p, [docs stringByAppendingPathComponent:@"ctl.token"].fileSystemRepresentation);
  }
#endif
  lq_vsync = dispatch_semaphore_create(0);
  lq_cam_q = dispatch_queue_create("lean.camera", DISPATCH_QUEUE_SERIAL);
  lq_cam_d = [LeanCamera new];
  self.window = [[UIWindow alloc] initWithFrame:UIScreen.mainScreen.bounds];
  self.window.rootViewController = [LeanController new];
  self.window.backgroundColor    = UIColor.blackColor;
  [self.window makeKeyAndVisible];
  // Lean's main on a thread of its own, with a deep stack for its
  // recursion.
  pthread_t      t;
  pthread_attr_t at;
  pthread_attr_init(&at);
  pthread_attr_setstacksize(&at, 64 << 20);
  pthread_create(&t, &at, lq_run, NULL);
  CADisplayLink* link = [CADisplayLink displayLinkWithTarget:self selector:@selector(vsync:)];
  self.displayLink = link;
  [link addToRunLoop:NSRunLoop.mainRunLoop forMode:NSRunLoopCommonModes];
  return YES;
}

// Once a display refresh: Lean's pace (one signal, never banked: a slow
// frame does not earn the next ones a head start), the keyboard's height
// mid-animation, and whether the list is scrolling.
- (void)vsync:(CADisplayLink*)l {
  lq_translate();
  if (!lq_vsync_due) {
    lq_vsync_due = true;
    dispatch_semaphore_signal(lq_vsync);
  }
  CALayer* pl  = lq_probe.layer.presentationLayer ?: lq_probe.layer;
  double   kbh = lq_root.bounds.size.height - pl.frame.origin.y;
  uint32_t kb  = lq_px(kbh);
  uint32_t ime = kb > lq_ibot + 1 ? kb : 0;  // closed: the guide is the safe area's bottom
  if (ime != self.ime) {
    self.ime = ime;
    lq_event(6, ime, 0, 0);
  }
  bool active = lq_sv.isTracking || lq_sv.isDecelerating;
  if (active != self.active) {
    self.active = active;
    lq_event(7, active, 0, 0);
  }
}

- (void)applicationWillResignActive:(UIApplication*)app {
  lq_foreground = false;
  self.displayLink.paused = YES;
  [lq_field resignFirstResponder];
  [lq_sv setContentOffset:lq_sv.contentOffset animated:NO];
  dispatch_async(lq_cam_q, ^{
    lq_cam_want = false;
    [lq_cam stopRunning];
    lq_cam = nil;
  });
  lq_event(9, 0, 0, 0);
  // Release a frame already waiting for vsync before the display paused.
  dispatch_semaphore_signal(lq_vsync);
}

- (void)applicationDidBecomeActive:(UIApplication*)app {
  lq_foreground = true;
  self.displayLink.paused = NO;
  [lq_root setNeedsLayout];
  [lq_root layoutIfNeeded];
  lq_event(10, 0, 0, 0);
}

- (BOOL)application:(UIApplication*)app openURL:(NSURL*)url options:(NSDictionary*)options {
  if (![url.scheme.lowercaseString isEqualToString:@"quiet"]) return NO;
  pthread_mutex_lock(&lq_mu);
  [lq_urls addObject:url.absoluteString];
  pthread_mutex_unlock(&lq_mu);
  return YES;
}

- (void)applicationWillTerminate:(UIApplication*)app {
  pthread_mutex_lock(&lq_mu);
  lq_gone = true;
  pthread_cond_broadcast(&lq_cv);
  pthread_mutex_unlock(&lq_mu);
}

@end

int main(int argc, char** argv) {
  @autoreleasepool {
    return UIApplicationMain(argc, argv, nil, NSStringFromClass([LeanDelegate class]));
  }
}

lean_obj_res lq_poll(void) {
  pthread_mutex_lock(&lq_mu);
  if (lq_gone && !lq_closed) { lq_closed = true; lq_push(1, 0, 0, 0); }
  lean_object* evs = lean_mk_empty_array();
  for (uint32_t i = 0; i < lq_n * 8; i++) evs = lean_array_push(evs, lean_box_uint32(lq_evs[i]));
  lq_n = 0;
  pthread_mutex_unlock(&lq_mu);
  return lean_io_result_mk_ok(evs);
}

lean_obj_res lq_links(void) {
  pthread_mutex_lock(&lq_mu);
  lean_object* links = lean_mk_empty_array();
  for (NSString* url in lq_urls) links = lean_array_push(links, lean_mk_string(url.UTF8String));
  [lq_urls removeAllObjects];
  pthread_mutex_unlock(&lq_mu);
  return lean_io_result_mk_ok(links);
}
