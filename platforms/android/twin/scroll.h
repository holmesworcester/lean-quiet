// Native scrolling (scroll.c): Android's VelocityTracker and OverScroller
// behind Platform.scroll, run on the vsync thread (layer.c). The offset
// is bottom-anchored: the distance from the content's end up to the
// viewport's bottom edge, so a drag down raises it.

#ifndef LQ_SCROLL_H
#define LQ_SCROLL_H

#include "activity.h"
#include <jni.h>

// From ANativeActivity_onCreate: the VM and the activity (a Context).
void bs_init(JavaVM* vm, jobject activity);

// At the vsync of time ns: takes the finger's samples since the last
// (a drag follows the finger as of ns minus a resampling lag), applies
// any pending bs_by/bs_to, and answers the offset in px, for content
// content_h high in a view view_h high, whole (y) and exact (yf); false if
// the scroller could not be set up.
bool bs_vsync(uint32_t content_h, uint32_t view_h, int64_t ns, uint32_t* y, float* yf);

// While a fling runs (as of the last bs_vsync): where it will stop.
bool bs_target(uint32_t* y);

// Whether a finger is on the list or a fling runs (as of the last bs_vsync).
bool bs_active(void);

// From any thread, applied at the next vsync: move the offset by d px
// keeping a fling going, or set it, stopping any fling.
void bs_by(float d);
void bs_to(float b);

#endif
