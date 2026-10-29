/* Observe Runner.stop's native close without opening a forbidden socket.
   The object is retained throughout the check, so GC cannot satisfy it. */
#include <lean/lean.h>
#include <stdatomic.h>
static _Atomic unsigned closed;
static void finish(void *p) { (void)p; closed++; }
static void visit(void *p, b_lean_obj_arg f) { (void)p; (void)f; }
lean_obj_res lq_test_listener(void) {
  lean_object *o = lean_alloc_external(lean_register_external_class(finish, visit), NULL);
  lean_mark_mt(o);
  return lean_io_result_mk_ok(o);
}
lean_obj_res lq_test_listener_closed(void) {
  return lean_io_result_mk_ok(lean_box_uint32(closed));
}
