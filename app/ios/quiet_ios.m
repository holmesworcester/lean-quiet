// The Lean app's window on iOS
// ============================

// Platform.lean's effects on UIKit, as android/twin does them on Android.
// UIKit owns the main thread; Lean's main (Main.lean's, renamed
// lean_app_main by build_ios.sh) runs on a thread of its own, in the
// app's Documents directory (quiet.db is made there) with `assets` linked
// to the bundle's assets. Its stderr shows in `simctl launch --console`
// or `devicectl ... launch --console`.
//
// The OS owns the three things Platform.lean gives it:
//
// - **Scrolling**: a UIScrollView turned upside down (scale y by -1), so
//   its content offset is the list's bottom-anchored offset b itself: 0
//   is the newest end, at the viewport's bottom edge, and content
//   measured late at the far (older) end never moves what is on screen.
//   Its physics, bounce and indicator are UIKit's. Each list frame is
//   the contents of one layer in the scroll view's content, placed at
//   the distances it was drawn for (content y = distance above the
//   content's end, the layer flipped back upright), so Core Animation
//   slides the latest frame with the finger at the display's rate and
//   Lean renders the current offset as fast as it can: frame row r drawn
//   at bf lands at screen row composerTop - 1 - (bf + viewH + over - 1 -
//   r - bn) for the offset bn now (Geometry.Seam.place's formula).
// - **The keyboard**: a UITextField drawn in clear holds the composer's text
//   (so every keyboard works as in any app: autocorrection, marked text
//   of Japanese or Chinese input, dictation, emoji), mirrored to Lean as
//   text, selection and marked range in code points.
// - **The insets**: the header is pinned to the screen's top; the
//   composer to the keyboard layout guide's top (the safe area's bottom
//   while the keyboard is closed), so Auto Layout moves it inside the
//   keyboard's own animation; the list's viewport is what lies between,
//   so the newest messages ride up with the keyboard. The keyboard's
//   height is read every refresh from a probe view on the guide (its
//   presentation layer, mid-animation) and handed to Lean as ime events.
//
// Frames are arrays of pixel rows, R G B X bytes (Platform.lean); IOSurface
// layer contents are B G R A, so a row is swizzled as it is copied. A row
// that is the same object as a row of the last frame of that layer (at
// the place the offset change moves it to) is not copied again: the
// staging buffer shifts and only new rows are copied into it (the last
// frame is held, so an object seen again is the same immutable row, never
// a freed one's address reused). Each changed layer's staging buffer then
// goes whole into one of its three IOSurfaces the compositor is not
// reading, and the contents change in one Core Animation transaction with
// the list layer's place, the chrome's heights and any offset Lean moved.
//
// Pixels map to points by the screen's scale (a frame pixel is a device
// pixel), and the density Lean sizes its dp by is 160 per point.
//
// Debugging, from the environment (SIMCTL_CHILD_x for simctl launch):
// LEANQUIET_CTL_PORT=<port> the control channel's TCP port on 127.0.0.1
// (default 7417, 0: none; ctl_ios.c); LEANQUIET_TRACE=1 logs each frame.

#import <UIKit/UIKit.h>
#import <QuartzCore/QuartzCore.h>
#import <IOSurface/IOSurfaceRef.h>
#include <lean/lean.h>
#include <math.h>
#include <pthread.h>
#include <stdatomic.h>
#include <time.h>
#include <unistd.h>

int  lean_app_main(int argc, char** argv);
void lq_ctl_start(int port);

#define LQ_RING 3
#define LQ_LONG_NS 500000000LL

enum { LQ_LIST = 0, LQ_TOP = 1, LQ_BOT = 2 };

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
static bool            lq_gone;    // the app is going away
static bool            lq_closed;  // the close event was handed over

// The screen, px, as of the last layout (under lq_mu).
static uint32_t lq_w, lq_h, lq_itop, lq_ibot, lq_dpi;
static double   lq_k = 3;          // px per point

// Events for the next frame, four words each (under lq_mu).
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

static LqStage           lq_st[3];
static uint32_t          lq_over;
static uint32_t          lq_list_bg = 0xFF000000u;
static bool              lq_trace;
static dispatch_semaphore_t lq_vsync;
static _Atomic bool      lq_vsync_due;

static UIView*        lq_root;
static UIScrollView*  lq_sv;
static CALayer*       lq_list;
static UIView*        lq_header;
static UIView*        lq_composer;
static UIView*        lq_fill;     // below the composer, to the screen's bottom
static UIView*        lq_probe;    // on the keyboard layout guide's top
static UITextField*   lq_field;
static NSLayoutConstraint* lq_header_h;
static NSLayoutConstraint* lq_composer_h;
static uint32_t       lq_shown_top_h, lq_shown_bot_h;

static uint64_t lq_tick(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (uint64_t)ts.tv_sec * 1000000000u + (uint64_t)ts.tv_nsec;
}

// Under lq_mu.
static void lq_push(uint32_t kind, uint32_t a, uint32_t b, uint32_t c) {
  if (lq_n == lq_cap) {
    lq_cap = lq_cap == 0 ? 64 : lq_cap * 2;
    lq_evs = realloc(lq_evs, (size_t)lq_cap * 16);
    if (lq_evs == NULL) {
      abort();
    }
  }
  uint32_t* ev = lq_evs + (size_t)lq_n * 4;
  ev[0] = kind;
  ev[1] = a;
  ev[2] = b;
  ev[3] = c;
  lq_n += 1;
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

// Every 120 frames, the mean cost per frame on stderr: Lean's own time,
// the staging (row copies), and the show (surface copies, the wait for a
// refresh and the transaction).
static void lq_time(uint64_t t0, uint64_t t1, uint64_t t2) {
  static uint64_t n, copy, show, app, last;
  if (last != 0) {
    app += t0 - last;
  }
  copy += t1 - t0;
  show += t2 - t1;
  last  = t2;
  if (++n == 120) {
    fprintf(stderr, "twin ms/frame: lean %.1f copy %.1f show %.1f b %.0f\n", app / 120e6,
      copy / 120e6, show / 120e6, atomic_load(&lq_offset));
    n = copy = show = app = 0;
  }
}

// Platform.lean
// -------------

lean_obj_res lq_screen(void) {
  pthread_mutex_lock(&lq_mu);
  while (!lq_up && !lq_gone) {
    pthread_cond_wait(&lq_cv, &lq_mu);
  }
  uint32_t v[5] = { lq_w, lq_h, lq_itop, lq_ibot, lq_dpi };
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
  return lean_io_result_mk_ok(lean_box_uint32(b <= 0 ? 0 : (uint32_t)lround(b)));
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

lean_obj_res lq_frame(b_lean_obj_arg list, uint32_t b, uint32_t over, b_lean_obj_arg top,
  b_lean_obj_arg bot) {
  uint64_t t0 = lq_tick();
  uint32_t w  = lq_w;
  lq_over     = over;
  lq_stage(&lq_st[LQ_LIST], list, w, b, true);
  lq_stage(&lq_st[LQ_TOP], top, w, 0, false);
  lq_stage(&lq_st[LQ_BOT], bot, w, 0, false);
  uint64_t t1 = lq_tick();
  IOSurfaceRef show[3] = { NULL, NULL, NULL };
  for (int k = 0; k < 3; k += 1) {
    if (lq_st[k].dirty && lq_fill_surface(&lq_st[k])) {
      show[k] = lq_st[k].shown;
    }
  }
  IOSurfaceRef show_list = show[LQ_LIST], show_top = show[LQ_TOP], show_bot = show[LQ_BOT];
  // What the layers need beside their contents: the list frame's place
  // (content px [bf - over, bf + h - over)), the chrome's heights, the
  // composer's last row (repeated down to the screen's bottom), the list's
  // background (its frame's first pixel, behind rows a slide uncovers).
  LqStage* ls     = &lq_st[LQ_LIST];
  uint32_t lb     = ls->off;
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
  dispatch_sync(dispatch_get_main_queue(), ^{
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
    if (top_h != lq_shown_top_h || bot_h != lq_shown_bot_h) {
      lq_shown_top_h          = top_h;
      lq_shown_bot_h          = bot_h;
      lq_header_h.constant    = top_h / k;
      lq_composer_h.constant  = bot_h / k;
      [lq_root layoutIfNeeded];
    }
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
    if (show_list != NULL) {
      // (bounds and position: the layer is flipped, so its frame is derived)
      lq_list.contents = (__bridge id)show_list;
      lq_list.bounds   = CGRectMake(0, 0, lq_w / k, lh / k);
      lq_list.position = CGPointMake(lq_w / k / 2, ((double)lb - (double)lq_over + lh / 2.0) / k);
    }
    [CATransaction commit];
  });
  if (lq_trace) {
    fprintf(stderr, "frame b %u shown %d%d%d content %u\n", b, show[0] != NULL, show[1] != NULL,
      show[2] != NULL, ch);
  }
  lq_time(t0, t1, lq_tick());
  pthread_mutex_lock(&lq_mu);
  if (lq_gone && !lq_closed) {
    lq_closed = true;
    lq_push(1, 0, 0, 0);
  }
  lean_object* evs = lean_mk_empty_array_with_capacity(lean_box(lq_n * 4));
  for (uint32_t i = 0; i < lq_n * 4; i += 1) {
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

lean_obj_res lq_text_clear(void) {
  dispatch_async(dispatch_get_main_queue(), ^{
    lq_field.text = @"";
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
// a text event if any changed.
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
  bool same = lq_text_s != NULL && strcmp(lq_text_s, u) == 0 && memcmp(pos, lq_pos, sizeof pos) == 0;
  if (!same) {
    free(lq_text_s);
    lq_text_s = strdup(u);
    memcpy(lq_pos, pos, sizeof pos);
    lq_push(4, 0, 0, 0);
  }
  pthread_mutex_unlock(&lq_mu);
}

@interface LeanField : UITextField <UITextFieldDelegate>
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

- (BOOL)textFieldShouldReturn:(UITextField*)f {
  lq_event(5, 0, 0, 0);
  return NO;
}

@end

// Touches
// -------

// A finger on the header or the composer: a press and release that never
// moved past the slop (8 points) is a tap, or a long press once held
// LQ_LONG_NS (reported while still held, as the list's is; its release is
// then no tap). A finger down on the composer (or the sheet in its place)
// is the app's to scroll: its drag goes to Lean as event 8, at rows within
// the composer as it was when the finger went down.
static struct {
  bool     down, moved, held;
  uint32_t region;   // 1 header, 2 composer
  double   x0, y0;   // where it went down, points on the screen
  double   ctop;     // the composer's top then, points
  uint64_t t0;
} lq_touch;

static void lq_press(uint32_t kind) {
  uint32_t x = lq_px(lq_touch.x0);
  if (lq_touch.region == 1) {
    lq_event(kind, 1, x, lq_px(lq_touch.y0));
  } else {
    uint32_t y  = lq_px(lq_touch.y0 - lq_touch.ctop);
    uint32_t bh = lq_shown_bot_h;
    lq_event(kind, 2, x, bh > 0 && y >= bh ? bh - 1 : y);
  }
}

@interface LeanChrome : UIView
@property (nonatomic) uint32_t region;
@end

@implementation LeanChrome

- (void)touchesBegan:(NSSet<UITouch*>*)touches withEvent:(UIEvent*)e {
  if (lq_touch.down) {
    return;
  }
  CGPoint p        = [touches.anyObject locationInView:lq_root];
  lq_touch.down    = true;
  lq_touch.moved   = false;
  lq_touch.held    = false;
  lq_touch.region  = self.region;
  lq_touch.x0      = p.x;
  lq_touch.y0      = p.y;
  lq_touch.ctop    = lq_composer.layer.presentationLayer.frame.origin.y;
  lq_touch.t0      = lq_tick();
  if (self.region == 2) {
    lq_event(8, 0, lq_px(p.x), lq_px(p.y - lq_touch.ctop));
  }
}

- (void)touchesMoved:(NSSet<UITouch*>*)touches withEvent:(UIEvent*)e {
  if (!lq_touch.down) {
    return;
  }
  CGPoint p = [touches.anyObject locationInView:lq_root];
  if (fabs(p.x - lq_touch.x0) > 8 || fabs(p.y - lq_touch.y0) > 8) {
    lq_touch.moved = true;
  }
  if (lq_touch.region == 2) {
    lq_event(8, 1, lq_px(p.x), lq_px(p.y - lq_touch.ctop));
  }
}

- (void)lift:(NSSet<UITouch*>*)touches {
  if (!lq_touch.down) {
    return;
  }
  CGPoint p = [touches.anyObject locationInView:lq_root];
  if (lq_touch.region == 2) {
    lq_event(8, 2, lq_px(p.x), lq_px(p.y - lq_touch.ctop));
  }
  if (!lq_touch.moved && !lq_touch.held) {
    lq_press((int64_t)(lq_tick() - lq_touch.t0) >= LQ_LONG_NS ? 3 : 2);
  }
  lq_touch.down = false;
}

- (void)touchesEnded:(NSSet<UITouch*>*)touches withEvent:(UIEvent*)e {
  [self lift:touches];
}

- (void)touchesCancelled:(NSSet<UITouch*>*)touches withEvent:(UIEvent*)e {
  [self lift:touches];
}

@end

// The view
// --------

@interface LeanScroll : UIScrollView <UIScrollViewDelegate>
@end

@implementation LeanScroll

- (void)scrollViewDidScroll:(UIScrollView*)v {
  // Upside down, the offset is the distance from the content's end to the
  // viewport's bottom edge: Platform.scroll's b (negative in a bounce at
  // the newest end; scroll answers 0 there).
  atomic_store(&lq_offset, v.contentOffset.y * lq_k);
}

// A list tap or long press: x, and y as the distance above the content's
// end (the scroll view's own coordinates are content distances).
- (void)tapped:(UIGestureRecognizer*)g {
  if (g.state != UIGestureRecognizerStateEnded) {
    return;
  }
  CGPoint p = [g locationInView:self];
  lq_event(2, 0, lq_px(p.x), (uint32_t)fmax(0, floor(p.y * lq_k)));
}

- (void)held:(UIGestureRecognizer*)g {
  if (g.state != UIGestureRecognizerStateBegan) {
    return;
  }
  CGPoint p = [g locationInView:self];
  lq_event(3, 0, lq_px(p.x), (uint32_t)fmax(0, floor(p.y * lq_k)));
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
  sv.transform                              = CGAffineTransformMakeScale(1, -1);
  sv.alwaysBounceVertical                   = YES;
  sv.scrollsToTop                           = NO;
  sv.contentInsetAdjustmentBehavior         = UIScrollViewContentInsetAdjustmentNever;
  sv.automaticallyAdjustsScrollIndicatorInsets = NO;
  sv.translatesAutoresizingMaskIntoConstraints = NO;
  lq_sv = sv;
  lq_list   = [CALayer layer];
  lq_list.opaque    = YES;
  lq_list.transform = CATransform3DMakeScale(1, -1, 1);  // upright again
  [sv.layer insertSublayer:lq_list atIndex:0];
  UILongPressGestureRecognizer* hold = [[UILongPressGestureRecognizer alloc] initWithTarget:sv
    action:@selector(held:)];
  hold.minimumPressDuration = LQ_LONG_NS / 1e9;
  hold.allowableMovement    = 8;
  UITapGestureRecognizer* tap = [[UITapGestureRecognizer alloc] initWithTarget:sv
    action:@selector(tapped:)];
  [tap requireGestureRecognizerToFail:hold];
  [sv addGestureRecognizer:hold];
  [sv addGestureRecognizer:tap];

  LeanChrome* header = [LeanChrome new];
  header.region = 1;
  header.translatesAutoresizingMaskIntoConstraints = NO;
  LeanChrome* composer = [LeanChrome new];
  composer.region = 2;
  composer.translatesAutoresizingMaskIntoConstraints = NO;
  LeanChrome* fill = [LeanChrome new];
  fill.region = 2;
  fill.translatesAutoresizingMaskIntoConstraints = NO;
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

  UILayoutGuide* kb = root.keyboardLayoutGuide;
  lq_header_h   = [header.heightAnchor constraintEqualToConstant:0];
  lq_composer_h = [composer.heightAnchor constraintEqualToConstant:0];
  [NSLayoutConstraint activateConstraints:@[
    [header.topAnchor constraintEqualToAnchor:root.topAnchor],
    [header.leadingAnchor constraintEqualToAnchor:root.leadingAnchor],
    [header.trailingAnchor constraintEqualToAnchor:root.trailingAnchor],
    lq_header_h,
    [composer.bottomAnchor constraintEqualToAnchor:kb.topAnchor],
    [composer.leadingAnchor constraintEqualToAnchor:root.leadingAnchor],
    [composer.trailingAnchor constraintEqualToAnchor:root.trailingAnchor],
    lq_composer_h,
    [fill.topAnchor constraintEqualToAnchor:composer.bottomAnchor],
    [fill.bottomAnchor constraintEqualToAnchor:root.bottomAnchor],
    [fill.leadingAnchor constraintEqualToAnchor:root.leadingAnchor],
    [fill.trailingAnchor constraintEqualToAnchor:root.trailingAnchor],
    [sv.topAnchor constraintEqualToAnchor:header.bottomAnchor],
    [sv.bottomAnchor constraintEqualToAnchor:composer.topAnchor],
    [sv.leadingAnchor constraintEqualToAnchor:root.leadingAnchor],
    [sv.trailingAnchor constraintEqualToAnchor:root.trailingAnchor],
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
  if (!lq_up && lq_w > 0 && lq_h > 0) {
    lq_up = true;
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
@end

@implementation LeanDelegate

- (BOOL)application:(UIApplication*)app didFinishLaunchingWithOptions:(NSDictionary*)opts {
  const char* tr = getenv("LEANQUIET_TRACE");
  lq_trace = tr != NULL && tr[0] == '1';
  const char* port = getenv("LEANQUIET_CTL_PORT");
  int p = port != NULL ? atoi(port) : 7417;
  if (p > 0) {
    lq_ctl_start(p);
  }
  lq_vsync = dispatch_semaphore_create(0);
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
  [link addToRunLoop:NSRunLoop.mainRunLoop forMode:NSRunLoopCommonModes];
  return YES;
}

// Once a display refresh: Lean's pace (one signal, never banked: a slow
// frame does not earn the next ones a head start), the keyboard's height
// mid-animation, whether the list is scrolling, and a long press held on
// the chrome.
- (void)vsync:(CADisplayLink*)l {
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
  if (lq_touch.down && !lq_touch.moved && !lq_touch.held &&
      (int64_t)(lq_tick() - lq_touch.t0) >= LQ_LONG_NS) {
    lq_touch.held = true;
    lq_press(3);
  }
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
