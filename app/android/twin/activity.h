// The Android activity, as the app's twin (quiet_android.c) sees it
// ================================================================

// activity.c owns the NativeActivity and its Java half (LeanActivity):
// their callbacks arrive on the UI thread, and Lean's main runs on a
// thread of its own. The two meet here, under one lock: the surface, the
// touches since the last frame, the insets, the keyboard's text and its
// events, and whether the activity is going away.

#ifndef LQ_ACTIVITY_H
#define LQ_ACTIVITY_H

#include <android/native_window.h>
#include <stdbool.h>
#include <stdint.h>

// A touch of the first finger down, in surface pixels: down, a move, or up
// (a cancel is an up), at t, the sample's CLOCK_MONOTONIC time in ns.
typedef enum { BA_DOWN, BA_MOVE, BA_UP } BaKind;

typedef struct {
  BaKind  kind;
  float   x;
  float   y;
  int64_t t;
} BaTouch;

// Blocks until the activity has a surface or is going away; with a
// surface, returns it locked for use, with its size, until ba_unlock.
// Returns NULL once the activity is going away.
ANativeWindow* ba_lock(int32_t* w, int32_t* h);
void           ba_unlock(void);

// Whether the activity has a surface now (it never blocks for one).
bool           ba_has_window(void);

// The surface's size if there is one now, without waiting.
bool           ba_size_now(int32_t* w, int32_t* h);

// The surface's size once there is one (blocking), and the insets as last
// reported: status bar, navigation bar, keyboard (0 when closed), px.
void ba_size(int32_t* w, int32_t* h);
void ba_insets(int32_t* top, int32_t* bottom, int32_t* ime);
int32_t ba_dpi(void);

// Moves up to max touches since the last call into out; returns the
// count. *closed is set once the activity is going away.
uint32_t ba_drain(BaTouch* out, uint32_t max, bool* closed);

// The touches that began in the list's viewport, for the scroller
// (scroll.c): its own queue.
uint32_t ba_drain_scroll(BaTouch* out, uint32_t max);

// The list viewport's rows on screen, [top, bot): a touch that starts
// there scrolls the list. Set by the twin each frame.
void ba_set_viewport(int32_t top, int32_t bot);

// Events from the Java half since the last call (four words each, as
// App.Event.decode reads them: 4 text, 5 send, 6 ime height).
uint32_t ba_drain_events(uint32_t* out, uint32_t max_words);

// The keyboard's text, as the EditText last reported it (UTF-8, owned by
// the caller: free it), and [selStart, selEnd, compStart, compEnd].
char* ba_text(uint32_t pos[4]);

// Asks the Java half to open or close the keyboard, or empty the text
// (from any thread).
void ba_ime(bool show);
void ba_text_clear(void);

// Debug properties, read at start: debug.lean.ahead=0 (no drawing ahead
// of a fling), debug.lean.trace=1 (per-vsync log).
bool ba_ahead(void);

// Puts UTF-8 text on the clipboard (the Java half, on the UI thread).
void ba_copy(const char* utf8);

// The camera (Join with QR code): on or off; and the newest frame's Y plane
// since the last take ([w, h, stride, sensor orientation]), malloc'd, the
// caller's to free (NULL when there is none).
void     ba_scan(bool on);
uint8_t* ba_take_luma(size_t* n, uint32_t wh[4]);

#endif

bool ba_dark(void);
void ba_appearance(bool dark, uint32_t background);
