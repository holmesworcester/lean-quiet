// Native buffers and vsync. Every placement rectangle is supplied by Lean.

#ifndef LQ_LAYER_H
#define LQ_LAYER_H

#include <stdbool.h>
#include <stdint.h>
typedef struct ANativeWindow ANativeWindow;

typedef enum { BL_LIST = 0, BL_TOP = 1, BL_BOT = 2, BL_HOLD = 3 } BlKind;

// Starts vsync and the OS physics sampler. Prediction is no longer used.
void bl_start(bool predict);
void bl_scroll_needs(uint32_t content_h, uint32_t view_h);
bool bl_scroll_y(float* y);

// Publish after staging all buffers; the next transaction adopts both.
// Begin waits for the previous publication before staging any new layer.
bool bl_begin(void);
void bl_abort(void);
void bl_geometry(const uint32_t* place);
uint32_t bl_frame_id(void);
uint64_t bl_view_id(void);

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
