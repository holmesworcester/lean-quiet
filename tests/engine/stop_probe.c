/* Scheduling fixture for the pinned Linux/x86-64 SDK regression. No flag
   value is mutated here. The actual Lean task calls the production stop helper. */
#include <lean/lean.h>
#include <stdatomic.h>
#include <stdio.h>
#include <unistd.h>
lean_object *lq_stop_probe_ref;
static _Atomic bool released, requesting, completed, did_inject;
lean_obj_res lq_stop_probe_arm(b_lean_obj_arg flag) {
  /* StopFlag's single-field wrapper is erased; Mutex keeps ref in field 0.
     The pointer is borrowed while main and its task own the flag. */
  lean_mark_mt((lean_object*)flag);  /* Also shared in a mutant that erases its writer. */
  lq_stop_probe_ref = lean_ctor_get(flag, 0);
  return lean_io_result_mk_ok(lean_box(0));
}
/* Reader.Worker holds an ordinary IO.Ref, rather than a Mutex wrapper. */
lean_obj_res lq_stop_probe_arm_ref(b_lean_obj_arg ref) {
  lean_mark_mt((lean_object*)ref);
  lq_stop_probe_ref = (lean_object*)ref;
  return lean_io_result_mk_ok(lean_box(0));
}
lean_obj_res lq_stop_probe_wait(void) {
  while (!atomic_load(&released)) usleep(1000);
  return lean_io_result_mk_ok(lean_box(0));
}
lean_obj_res lq_stop_probe_entered(void) {
  atomic_store(&requesting, true);
  return lean_io_result_mk_ok(lean_box(0));
}
lean_obj_res lq_stop_probe_done(void) {
  atomic_store(&completed, true);
  return lean_io_result_mk_ok(lean_box(0));
}
lean_obj_res lq_stop_probe_injected(void) {
  return lean_io_result_mk_ok(lean_box(atomic_load(&did_inject)));
}
/* GDB calls this while an actual SDK getter holds the previous value. */
__attribute__((noinline)) void lq_stop_probe_release(void) {
  atomic_store(&released, true);
  for (unsigned i = 0; i < 1000 && !atomic_load(&requesting); ++i) usleep(1000);
  atomic_store(&did_inject, atomic_load(&requesting));
  usleep(20000);
  printf("request entered=%d completed while read paused=%d\n",
    atomic_load(&requesting), atomic_load(&completed));
  fflush(stdout);
}
