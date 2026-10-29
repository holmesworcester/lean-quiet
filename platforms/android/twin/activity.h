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

// Every pointer sample, in surface pixels, with cancellation preserved,
// CLOCK_MONOTONIC ns and the serial of the displayed Lean frame.
typedef enum { BA_DOWN, BA_MOVE, BA_UP, BA_CANCEL } BaKind;

typedef struct {
  BaKind  kind;
  float   x;
  float   y;
  int64_t t;
  int32_t id;
  uint64_t frame;
} BaTouch;

// Returns the resumed activity's current surface locked until ba_unlock.
// Returns NULL immediately while paused, without a surface, or closing.
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
void ba_safe(int32_t out[7]);
void ba_bars(uint32_t top, uint32_t bottom, bool light_top, bool light_bottom);
int32_t ba_dpi(void);

// Moves up to max touches since the last call into out; returns the
// count. *closed is set once the activity is going away.
uint32_t ba_drain(BaTouch* out, uint32_t max, bool* closed);

// Only samples Lean has accepted, for the native physics queue.
uint32_t ba_drain_scroll(BaTouch* out, uint32_t max);
void ba_accept_scroll(BaTouch sample);

// Events from the Java half since the last call (four words each, as
// Input.decode reads them: 4 text, 5 IME action, 6 height, 14 key).
uint32_t ba_drain_events(uint32_t* out, uint32_t max_words);

// The keyboard's text, as the EditText last reported it (UTF-8, owned by
// the caller: free it), and [selStart, selEnd, compStart, compEnd].
char* ba_text(uint32_t pos[4]);

// Asks the Java half to open or close the keyboard, or empty the text
// (from any thread).
void ba_ime(bool show);
char* ba_take_link(void);

// Debug properties, read at start: debug.lean.ahead=0 (no drawing ahead
// of a fling), debug.lean.trace=1 (per-vsync log).
bool ba_ahead(void);

// Puts UTF-8 text on the clipboard (the Java half, on the UI thread).
void ba_copy(const char* utf8);
void ba_set_text(const char* utf8);

// The camera (Join with QR code): on or off; and the newest frame's Y plane
// since the last take ([w, h, stride, sensor orientation]), malloc'd, the
// caller's to free (NULL when there is none).
void     ba_scan(bool on);
uint8_t* ba_take_luma(size_t* n, uint32_t wh[4]);

#endif

bool ba_dark(void);
void ba_appearance(bool dark, uint32_t background);
