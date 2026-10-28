// The JNI seam between ScanActivity and Lean's decoder
// ====================================================
//
// ScanActivity.decode(y, width, height, rowStride) hands over the Y plane
// of a camera frame as the direct ByteBuffer Camera2 filled. This copies
// those bytes, as they are, into a Lean ByteArray (one memcpy: the Lean
// runtime owns its objects) and calls Qr.decodeLuma (lean_qr_decode_luma),
// which does everything else: binarizing, finding the symbol, sampling,
// error correction, segments. Back come the payload bytes and Lean's
// one-line description, as a Java Object[] {byte[], String}, or null.
//
// Lean's runtime is started once, on the first call; each thread that
// calls in is registered with it (and released when it ends).

#include <jni.h>
#include <lean/lean.h>
#include <pthread.h>
#include <string.h>
#include <android/log.h>

#define TAG "LeanQR"

lean_object* initialize_qr_Qr(uint8_t builtin);
// declared by Lean's generated C, not by lean.h
void lean_initialize_runtime_module(void);
// runtime/thread.h (not in lean.h): a thread Lean did not start registers
// with the runtime, and runs its finalizers (its heap) when it ends
void lean_initialize_thread(void);
void lean_finalize_thread(void);
lean_object* lean_qr_decode_luma(uint32_t w, uint32_t h, uint32_t stride, lean_obj_arg px);

static pthread_once_t once = PTHREAD_ONCE_INIT;
static pthread_key_t key;
static int ready;

static void thread_done(void* v) {
  (void)v;
  lean_finalize_thread();
}

static void start_lean(void) {
  lean_initialize_runtime_module();
  lean_object* r = initialize_qr_Qr(1);
  if (lean_io_result_is_ok(r)) {
    ready = 1;
  } else {
    __android_log_print(ANDROID_LOG_ERROR, TAG, "Lean's module initialization failed");
  }
  lean_dec_ref(r);
  lean_io_mark_end_initialization();
  pthread_key_create(&key, thread_done);
  // the starting thread is Lean's already
  pthread_setspecific(key, (void*)2);
}

JNIEXPORT jobjectArray JNICALL
Java_com_holmes_leanqr_ScanActivity_decode(JNIEnv* env, jclass cls, jobject buf, jint w, jint h,
                                            jint stride) {
  (void)cls;
  pthread_once(&once, start_lean);
  if (!ready) return NULL;
  if (pthread_getspecific(key) == NULL) {
    lean_initialize_thread();
    pthread_setspecific(key, (void*)1);
  }
  const uint8_t* y = (*env)->GetDirectBufferAddress(env, buf);
  jlong cap = (*env)->GetDirectBufferCapacity(env, buf);
  if (y == NULL || cap <= 0 || w <= 0 || h <= 0 || stride <= 0) return NULL;

  lean_object* px = lean_alloc_sarray(1, (size_t)cap, (size_t)cap);
  memcpy(lean_sarray_cptr(px), y, (size_t)cap);
  lean_object* res = lean_qr_decode_luma((uint32_t)w, (uint32_t)h, (uint32_t)stride, px);  // takes px
  if (lean_obj_tag(res) == 0) {  // none
    lean_dec(res);
    return NULL;
  }
  lean_object* pair = lean_ctor_get(res, 0);
  lean_object* payload = lean_ctor_get(pair, 0);
  lean_object* info = lean_ctor_get(pair, 1);
  jsize n = (jsize)lean_sarray_size(payload);
  jbyteArray bytes = (*env)->NewByteArray(env, n);
  (*env)->SetByteArrayRegion(env, bytes, 0, n, (const jbyte*)lean_sarray_cptr(payload));
  jstring desc = (*env)->NewStringUTF(env, lean_string_cstr(info));
  lean_dec(res);
  jclass obj = (*env)->FindClass(env, "java/lang/Object");
  jobjectArray out = (*env)->NewObjectArray(env, 2, obj, NULL);
  (*env)->SetObjectArrayElement(env, out, 0, bytes);
  (*env)->SetObjectArrayElement(env, out, 1, desc);
  return out;
}
