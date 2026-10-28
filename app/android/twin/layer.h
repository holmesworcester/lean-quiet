// The frame as a compositor-slid layer (layer.c).

#ifndef LC_LAYER_H
#define LC_LAYER_H

#include <android/native_window.h>
#include <stdbool.h>
#include <stdint.h>

// Starts the vsync thread (once): it runs the scroller and places frames;
// predict: whether Lean draws at the predicted offset (else the vsync's).
void bl_start(bool predict);

// What the scroller needs (from Window.native_scroll): the content's and
// frame's heights in frame px, and frame px per surface px.
void bl_scroll_needs(uint32_t content_h, uint32_t view_h, float scale);

// The offset Lean should draw at, in frame px: the latest vsync's,
// predicted on to when Lean's frame will be on screen; false before the
// first vsync.
bool bl_scroll_y(uint32_t* y);

// The window's layer, made if win is new. Call with the window held
// (activity.c's ba_lock); it never waits.
void bl_attach(ANativeWindow* win);

// Hands a finished w x h frame (RGBX words), drawn at offset y, to the
// layer, placed at (ox, oy) in the window's buffer coordinates (scale:
// frame px per unit of those; the twin keeps the window's buffer at the
// surface's own size, so the layer can move by a surface pixel);
// slides: whether to place it for the vsync's offset (else at y). Call
// with the window released: it waits for the vsync to take the last
// frame and for a free buffer. False if there is no layer.
bool bl_present(int32_t ox, int32_t oy, float scale, const uint32_t* pix,
  uint32_t w, uint32_t h, uint32_t y, bool slides);

// Waits for the next vsync: Lean's pace when its frame did not change;
// false (at once) if there is no layer to show it.
bool bl_idle(void);

// The window is going: the layer goes with it (before it returns).
void bl_window_gone(void);

#endif
