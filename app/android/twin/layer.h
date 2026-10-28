// The app's three layers on the compositor (layer.c): the list, slid at
// every vsync for the scroller's offset, and the header and composer,
// pinned above it, the composer riding the keyboard's animation.

#ifndef LQ_LAYER_H
#define LQ_LAYER_H

#include <android/native_window.h>
#include <stdbool.h>
#include <stdint.h>

typedef enum { BL_LIST = 0, BL_TOP = 1, BL_BOT = 2 } BlKind;

// Starts the vsync thread (once): it runs the scroller and places the
// layers; predict: whether Lean draws at the predicted offset.
void bl_start(bool predict);

// What the scroller needs (Platform.scroll): the content's height and the
// viewport's with the keyboard closed, px.
void bl_scroll_needs(uint32_t content_h, uint32_t view_h);

// The offset Lean should draw at: the latest vsync's, predicted on to when
// Lean's frame will be on screen; false before the first vsync.
bool bl_scroll_y(uint32_t* y);

// The layout the vsync places by: the screen's size, the header's and the
// composer's heights, the list frame's overscan, the navigation bar.
void bl_layout(uint32_t w, uint32_t h, uint32_t top_h, uint32_t bot_h, uint32_t over,
  uint32_t inset_bottom);

// The latest vsync's placement, for taps: the offset (exact), the
// composer's top on screen, the keyboard's shift of the list.
void bl_placed(float* b, int32_t* composer_top, int32_t* shift);

// Whether the list frame is a page pinned to the top (no slide, no lift
// by the keyboard: Geometry.Seam.pinned), from the app's frame call.
void bl_set_pin(bool pin);
bool bl_pinned(void);

// The window's layers, made if win is new. Call with the window held
// (activity.c's ba_lock); it never waits.
void bl_attach(ANativeWindow* win);

// Hands a finished w x h frame (RGBX words) of a layer to the compositor;
// for the list, drawn at offset y. Waits for the vsync to take that
// layer's last frame and for a free buffer. False if there is no layer.
// The composer's buffer is extend rows taller than its frame: its last
// row repeats down to the screen's bottom (behind the navigation bar).
bool bl_present(BlKind k, const uint32_t* pix, uint32_t w, uint32_t h, uint32_t y,
  uint32_t extend);

// Waits for the next vsync: Lean's pace when no frame changed; false (at
// once) if there are no layers to show it.
bool bl_idle(void);

// The window is going: the layers go with it (before it returns).
void bl_window_gone(void);

#endif
