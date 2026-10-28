// The Android activity, as the app's window twin (lean_android.c) sees it
// =======================================================================

// activity.c owns the NativeActivity: its callbacks arrive on the UI
// thread, and Lean's main runs on a thread of its own. The two meet
// here, under one lock: the surface, the touches since the last frame,
// and whether the activity is going away.

#ifndef LC_ACTIVITY_H
#define LC_ACTIVITY_H

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

// Moves up to max touches since the last call into out; returns the
// count. *closed is set once the activity is going away.
uint32_t ba_drain(BaTouch* out, uint32_t max, bool* closed);

// Whether Window.native_scroll answers Android's scroll physics: true
// unless the system property debug.lean.scroll was "app" at start (then
// the app keeps its own scrolling, for comparison).
bool ba_native_scroll(void);

// The same touches for the scroller (scroll.c), its own queue.
uint32_t ba_drain_scroll(BaTouch* out, uint32_t max);

// Whether frames go to the compositor-slid layer (layer.c): true unless
// the system property debug.lean.layer was 0 at start.
bool ba_layer(void);

// Whether Lean draws ahead of the scroll (layer.c): true unless the
// system property debug.lean.ahead was 0 at start.
bool ba_ahead(void);

#endif
