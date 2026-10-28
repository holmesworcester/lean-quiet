// Native scrolling (scroll.c): Android's VelocityTracker and OverScroller
// behind Window.native_scroll, run on the vsync thread (layer.c).

#ifndef LC_SCROLL_H
#define LC_SCROLL_H

#include "activity.h"
#include <jni.h>

// From ANativeActivity_onCreate: the VM and the activity (a Context).
void bs_init(JavaVM* vm, jobject activity);

// At the vsync of time ns: takes the finger's samples since the last
// (a drag follows the finger as of ns minus a resampling lag), answers
// the offset in frame pixels for content content_h high in a view_h-high
// frame (scale: frame px per surface px), whole (y) and exact (yf); false
// if the scroller could not be set up.
bool bs_vsync(uint32_t content_h, uint32_t view_h, float scale, int64_t ns,
  uint32_t* y, float* yf);

// While a fling runs (as of the last bs_vsync): where it will stop, in
// frame pixels.
bool bs_target(uint32_t* y);

#endif
