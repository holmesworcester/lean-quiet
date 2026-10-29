/* Explicit close for a stopped Lean 4.34 UV listener. The runtime exposes
   cancelAccept but no close operation. Its external finalizer calls
   uv_close under the loop lock, releasing the descriptor synchronously.
   Invoke it once, replacing this object's destructor so retained Runner
   references cannot keep the port bound or close a recycled descriptor.

   Only Runner.stop calls this, after joining the sole tryAccept caller.
   No socket operation may use this native object afterwards. This uses
   Lean's external-object ABI; same-port restart tests cover the seam. */
#include <lean/lean.h>
#include <pthread.h>

static lean_external_class *lq_closed_listener;
static pthread_once_t lq_closed_once = PTHREAD_ONCE_INIT;
static void lq_closed_finalize(void *p) { (void)p; }
static void lq_closed_foreach(void *p, b_lean_obj_arg f) { (void)p; (void)f; }
static void lq_closed_init(void) {
  lq_closed_listener = lean_register_external_class(lq_closed_finalize, lq_closed_foreach);
}

lean_obj_res lq_listener_close(b_lean_obj_arg socket) {
  pthread_once(&lq_closed_once, lq_closed_init);
  lean_external_object *o = lean_to_external(socket);
  if (o->m_class != lq_closed_listener) {
    lean_external_finalize_proc close = o->m_class->m_finalize;
    void *data = o->m_data;
    o->m_class = lq_closed_listener;
    o->m_data = NULL;
    close(data);
  }
  return lean_io_result_mk_ok(lean_box(0));
}
