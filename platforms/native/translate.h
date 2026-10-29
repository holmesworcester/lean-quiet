// Pure scalar helpers compiled from engine.renderer.Slide, not native copies.
#ifndef LQ_TRANSLATE_H
#define LQ_TRANSLATE_H
#include <stdint.h>
#define LQ_PLACEMENT_WORDS 29
uint32_t lq_slide_edge(uint8_t fill, uint8_t which, uint8_t pin, uint32_t base,
  uint32_t origin, uint32_t height, uint32_t top, uint32_t bottom, uint32_t sample);
uint32_t lq_slide_delta(uint8_t pin, uint32_t base, uint32_t sample);
uint64_t lq_slide_source(uint8_t pin, uint32_t base, uint32_t origin,
  uint32_t height, uint32_t sample, uint32_t y);
uint32_t lq_slide_fill_row(uint8_t pin, uint32_t base, uint32_t top,
  uint32_t bottom, uint32_t sample, uint32_t y);
static inline void lq_slide_rect(const uint32_t* p, int32_t sample, int fill, uint32_t r[4]) {
  for (uint8_t i = 0; i < 4; i++)
    r[i] = lq_slide_edge(fill, i, p[22], p[15], p[20], p[21], p[7], p[10], sample);
}
#endif
