#ifndef LQ_FLING_H
#define LQ_FLING_H
#include <stdbool.h>
#include <stdint.h>

/* Accepted touch samples only, in physical pixels and UIKit uptime ms.
 * A zero-displacement UP is common. It must not erase recent movement;
 * holding still for 80ms, cancellation, and a new gesture do erase momentum. */
typedef struct {
  bool down;
  double y, velocity;
  uint64_t time, moved;
} LqFling;
typedef struct {
  double delta, velocity;
  bool stop, released;
} LqFlingStep;

static LqFlingStep lq_fling_sample(LqFling *s, uint32_t phase, double y, uint64_t now) {
  LqFlingStep out = {0};
  if (phase == 3 || phase == 0) {
    *s = (LqFling){.down = phase == 0, .y = y, .time = now, .moved = now};
    out.stop = true;
    return out;
  }
  if (!s->down || now < s->time) return out;
  out.delta = y - s->y;
  if (out.delta != 0 && now > s->time) {
    s->velocity = out.delta / (double)(now - s->time);
    s->moved = now;
  }
  s->y = y;
  s->time = now;
  if (phase == 2) {
    out.released = true;
    out.velocity = now - s->moved <= 80 ? s->velocity : 0;
    s->down = false;
    s->velocity = 0;
  }
  return out;
}
#endif
