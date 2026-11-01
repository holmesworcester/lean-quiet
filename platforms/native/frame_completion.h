#ifndef LQ_FRAME_COMPLETION_H
#define LQ_FRAME_COMPLETION_H
#include <stdbool.h>
#include <stdint.h>

// Called under the shell mutex. One callback owns a ticket until it returns,
// even across reset. Completion is a native API seam, not physical scanout.
// Publication identity does not reuse the wrapped UInt32 input-frame serial.
// Exhausted counters fail closed instead of aliasing an earlier obligation.
typedef struct { uint64_t generation, serial; } LqFrameTicket;
typedef struct {
  uint64_t generation, serial, accepted, publication;
  bool pending, valid, revoked;
  uint32_t frame;
  int32_t shift;
} LqFrameCompletion;

static inline bool lq_frame_accept(LqFrameCompletion* s) {
  if (s->accepted == UINT64_MAX) return false;
  s->accepted++;
  return true;
}
static inline bool lq_frame_begin(LqFrameCompletion* s, LqFrameTicket* ticket) {
  if (s->pending || s->serial == UINT64_MAX) return false;
  s->pending = true;
  s->revoked = false;
  s->serial++;
  *ticket = (LqFrameTicket){s->generation, s->serial};
  return true;
}
static inline bool lq_frame_complete(LqFrameCompletion* s, LqFrameTicket ticket,
    uint64_t publication, uint32_t frame, int32_t shift) {
  if (!s->pending || ticket.serial != s->serial) return false;
  s->pending = false;
  if (s->revoked || ticket.generation != s->generation) return false;
  s->valid = true;
  s->publication = publication;
  s->frame = frame;
  s->shift = shift;
  return true;
}
static inline void lq_frame_reset(LqFrameCompletion* s) {
  s->generation++;
  s->valid = false;
  s->revoked = true;
}
#endif
