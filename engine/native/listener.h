/* Explicit close for a stopped Lean 4.35 UV listener. The runtime exposes
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

/* Socket abort capability: captures before client tasks begin. */
/* Isolated POSIX prototype. Not installed in the application's runtime.
 * ABI seam: Lean 4.35.0's TCP native state begins with uv_tcp_t *m_uv_tcp.
 * Reviewed against 4.34.0 (src/runtime/uv/tcp.{h,cpp}): 4.35 only appends
 * m_shutdown_requested to the struct, the finalizer still uv_closes under
 * the loop lock, and getsockname still takes that lock.
 * Capture happens on an idle client after an SDK UV-mutex barrier, before
 * reader/writer tasks start. Failed connects may still own a descriptor.
 * uv_fileno is not called concurrently with operations on this handle.
 * The returned capability retains the native socket: its descriptor cannot
 * be finalized/reused before a capability borrow has finished. No descriptor,
 * handle, request or SDK promise is freed or completed by this adapter.
 */
#include <lean/lean.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#if LEAN_VERSION_MAJOR != 4 || LEAN_VERSION_MINOR != 35 || LEAN_VERSION_PATCH != 0
#error "Review the TCP native-state ABI before using another Lean version"
#endif

#ifndef _WIN32
#include <errno.h>
#include <pthread.h>
#include <sys/socket.h>

/* uv_os_fd_t is int on all supported POSIX targets. Deliberately avoid the
 * platform-specific libuv struct layout; only the SDK's first pointer field
 * is read, while the socket is idle. uv_fileno is exported by Lean's SDK. */
struct uv_handle_s;
extern int uv_fileno(const struct uv_handle_s *handle, int *fd);
extern lean_obj_res lean_uv_tcp_getsockname(b_lean_obj_arg socket);

typedef struct {
  lean_object *socket;
  int fd;
} abort_capability;

static lean_external_class *abort_class;
static pthread_once_t abort_once = PTHREAD_ONCE_INIT;

static void abort_finalize(void *ptr) {
  abort_capability *cap = ptr;
  lean_dec(cap->socket);
  free(cap);
}

static void abort_foreach(void *ptr, b_lean_obj_arg f) {
  abort_capability *cap = ptr;
  lean_inc(f);
  /* The visitor consumes its argument (mark_mt_fn decrements it). */
  lean_inc(cap->socket);
  lean_apply_1(f, cap->socket);
}

static void abort_init(void) {
  abort_class = lean_register_external_class(abort_finalize, abort_foreach);
}

lean_obj_res lq_socket_abort_capture(b_lean_obj_arg socket) {
  void *handle;
  memcpy(&handle, lean_get_external_data(socket), sizeof(handle));
  int fd;
  if (uv_fileno((const struct uv_handle_s *)handle, &fd) != 0)
    return lean_io_result_mk_ok(lean_box(0));
  abort_capability *cap = malloc(sizeof(*cap));
  if (!cap) return lean_io_result_mk_ok(lean_box(0));
  cap->fd = fd;
  cap->socket = socket;
  lean_inc(socket);
  pthread_once(&abort_once, abort_init);
  lean_object *object = lean_alloc_external(abort_class, cap);
  lean_mark_mt(object);
  lean_object *some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, object);
  return lean_io_result_mk_ok(some);
}

lean_obj_res lq_socket_abort(b_lean_obj_arg capability) {
  abort_capability *cap = lean_get_external_data(capability);
  int result = shutdown(cap->fd, SHUT_RDWR);
  /* Repeated shutdown and a peer that has already disconnected are benign.
   * EBADF is deliberately not accepted: that would violate ownership. */
  return lean_io_result_mk_ok(lean_box(result == 0 || errno == ENOTCONN));
}

/* A FIN after every byte already written; the receiving direction stays
 * open, so a peer still writing meets no reset (lq_socket_abort's SHUT_RD
 * makes the kernel answer its next segment with one). */
lean_obj_res lq_socket_finish_write(b_lean_obj_arg capability) {
  abort_capability *cap = lean_get_external_data(capability);
  return lean_io_result_mk_ok(lean_box(shutdown(cap->fd, SHUT_WR) == 0));
}

lean_obj_res lq_socket_abort_barrier(b_lean_obj_arg capability) {
  abort_capability *cap = lean_get_external_data(capability);
  /* SDK getSockName takes/releases the same mutex held across uv_run and
   * its send callback. The address/error result is immaterial; discard it.
   * Cap ownership pins the original socket while callback refs disappear. */
  lean_object *result = lean_uv_tcp_getsockname(cap->socket);
  lean_dec(result);
  return lean_io_result_mk_ok(lean_box(0));
}
#else
/* No claim that SD_BOTH cancels pending Windows overlapped writes. */
lean_obj_res lq_socket_abort_capture(b_lean_obj_arg socket) {
  (void)socket;
  return lean_io_result_mk_ok(lean_box(0));
}
lean_obj_res lq_socket_abort(b_lean_obj_arg capability) {
  (void)capability;
  return lean_io_result_mk_ok(lean_box(0));
}
lean_obj_res lq_socket_finish_write(b_lean_obj_arg capability) {
  (void)capability;
  return lean_io_result_mk_ok(lean_box(0));
}
lean_obj_res lq_socket_abort_barrier(b_lean_obj_arg capability) {
  (void)capability;
  return lean_io_result_mk_ok(lean_box(0));
}
#endif
