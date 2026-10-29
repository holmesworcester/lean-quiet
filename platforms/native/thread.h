// Defence in depth at native compositor entry points. Warm-up runs on
// the Lean frame thread before the first publication; TLS guards entry.
#ifndef LQ_THREAD_H
#define LQ_THREAD_H
#include <stdbool.h>
#include "translate.h"
void lean_initialize_thread(void);

static inline void lq_slide_thread_init(void) {
  static _Thread_local bool ready;
  if (!ready) {
    lean_initialize_thread();
    ready = true;
  }
}

static inline void lq_slide_warm(void) {
  static _Thread_local bool ready;
  if (ready) return;
  volatile uint64_t sink;
  for (uint8_t pin = 0; pin < 2; pin++) {
    for (uint8_t fill = 0; fill < 2; fill++)
      for (uint8_t edge = 0; edge < 4; edge++)
        sink = lq_slide_edge(fill, edge, pin, 0, 0, 1, 0, 1, 0);
    sink = lq_slide_delta(pin, 0, 0);
    sink = lq_slide_source(pin, 0, 0, 1, 0, 0);
    sink = lq_slide_fill_row(pin, 0, 0, 1, 0, 0);
  }
  (void)sink;
  ready = true;
}
#endif
