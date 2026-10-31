/* Explicit close for a stopped Lean 4.34 UV listener. The runtime exposes
   cancelAccept but no close operation. Its external finalizer calls
   uv_close under the loop lock, releasing the descriptor synchronously.
   Invoke it once, replacing this object's destructor so retained Runner
   references cannot keep the port bound or close a recycled descriptor.

   Only Runner.stop calls this, after joining the sole tryAccept caller.
   No socket operation may use this native object afterwards. This uses
   Lean's external-object ABI; same-port restart tests cover the seam. */
#include <lean/lean.h>
#ifdef _WIN32
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#else
#include <pthread.h>
#endif

static lean_external_class *lq_closed_listener;
#ifdef _WIN32
static INIT_ONCE lq_closed_once = INIT_ONCE_STATIC_INIT;
#else
static pthread_once_t lq_closed_once = PTHREAD_ONCE_INIT;
#endif
static void lq_closed_finalize(void *p) { (void)p; }
static void lq_closed_foreach(void *p, b_lean_obj_arg f) { (void)p; (void)f; }
static void lq_closed_init(void) {
  lq_closed_listener = lean_register_external_class(lq_closed_finalize, lq_closed_foreach);
}

#ifdef _WIN32
static BOOL CALLBACK lq_closed_init_windows(PINIT_ONCE once, PVOID parameter, PVOID *context) {
  (void)once; (void)parameter; (void)context;
  lq_closed_init();
  return TRUE;
}
#endif

lean_obj_res lq_listener_close(b_lean_obj_arg socket) {
#ifdef _WIN32
  InitOnceExecuteOnce(&lq_closed_once, lq_closed_init_windows, NULL, NULL);
#else
  pthread_once(&lq_closed_once, lq_closed_init);
#endif
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
