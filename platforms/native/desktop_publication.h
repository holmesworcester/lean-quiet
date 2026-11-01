#ifndef LQ_DESKTOP_PUBLICATION_H
#define LQ_DESKTOP_PUBLICATION_H
#include <lean/lean.h>
#include <stdbool.h>
#include <stdint.h>

// Desktop event records have four words. Metadata is appended outside the
// input queue, so a full input batch cannot silently drop completion status.
static lean_obj_res lq_desktop_result(const uint32_t* events, size_t count,
    bool accepted, uint64_t tracking, uint64_t completed, int32_t shift) {
  lean_object* a = lean_mk_empty_array_with_capacity(lean_box(count + 8));
  for (size_t i = 0; i < count; i++) a = lean_array_push(a, lean_box_uint32(events[i]));
  uint32_t status[8] = {20, accepted ? 1 : 0, (uint32_t)tracking, (uint32_t)(tracking >> 32),
    21, (uint32_t)completed, (uint32_t)(completed >> 32), (uint32_t)shift};
  for (size_t i = 0; i < 8; i++) a = lean_array_push(a, lean_box_uint32(status[i]));
  return lean_io_result_mk_ok(a);
}
#endif
