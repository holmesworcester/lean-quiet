// The JNI seam of the composer's image tools (Pics.java <-> Pic/Composer.lean)
// ===========================================================================
//
// Pics.java decodes and downsamples a picked or captured picture and passes
// its RGBA here; this copies the bytes into a Lean ByteArray and calls Lean,
// which checks it, stores it as QOI and draws the tray. The composer's state
// is a Lean value this file holds (one reference) and passes back on every
// call. Nothing here looks at a pixel.
//
// Needs lean_harness_ready(): Lean started and the calling thread registered
// (qr_jni.c here; whichever file starts Lean in another app).

#include <jni.h>
#include <lean/lean.h>
#include <pthread.h>
#include <string.h>

int lean_harness_ready(void);
lean_object* lean_pic_empty(lean_object* unit);
uint64_t lean_pic_fit(uint32_t w, uint32_t h, uint32_t edge);
lean_object* lean_pic_add(lean_object* c, uint32_t ow, uint32_t oh, uint32_t w, uint32_t h,
                          lean_object* px);
lean_object* lean_pic_tray(lean_object* c, uint32_t height);
lean_object* lean_pic_blob(lean_object* c, uint32_t i);

static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;
static lean_object* composer;  // owned; NULL until the first call

static lean_object* state(void) {  // under mu; a new reference
  if (composer == NULL) composer = lean_pic_empty(lean_box(0));
  lean_inc(composer);
  return composer;
}

static jbyteArray bytes(JNIEnv* env, lean_object* ba) {  // consumes ba
  jsize n = (jsize)lean_sarray_size(ba);
  jbyteArray out = (*env)->NewByteArray(env, n);
  (*env)->SetByteArrayRegion(env, out, 0, n, (const jbyte*)lean_sarray_cptr(ba));
  lean_dec(ba);
  return out;
}

JNIEXPORT jlong JNICALL Java_com_holmes_leanqr_Pics_fit(JNIEnv* env, jclass cls, jint w, jint h,
                                                        jint edge) {
  (void)env; (void)cls;
  if (!lean_harness_ready() || w < 0 || h < 0 || edge < 0) return 0;
  return (jlong)lean_pic_fit((uint32_t)w, (uint32_t)h, (uint32_t)edge);
}

JNIEXPORT jstring JNICALL Java_com_holmes_leanqr_Pics_add(JNIEnv* env, jclass cls, jint ow, jint oh,
                                                          jobject buf, jint w, jint h) {
  (void)cls;
  if (!lean_harness_ready()) return (*env)->NewStringUTF(env, "Lean is not running");
  const uint8_t* p = (*env)->GetDirectBufferAddress(env, buf);
  jlong n = (*env)->GetDirectBufferCapacity(env, buf);
  if (p == NULL || n < 0 || ow < 0 || oh < 0 || w < 0 || h < 0)
    return (*env)->NewStringUTF(env, "no pixels");
  lean_object* px = lean_alloc_sarray(1, (size_t)n, (size_t)n);
  memcpy(lean_sarray_cptr(px), p, (size_t)n);
  pthread_mutex_lock(&mu);
  lean_object* c = state();
  lean_dec(composer);  // the call takes the reference state() made; the old state goes with it
  lean_object* r = lean_pic_add(c, (uint32_t)ow, (uint32_t)oh, (uint32_t)w, (uint32_t)h, px);
  composer = lean_ctor_get(r, 0);
  lean_inc(composer);
  jstring said = (*env)->NewStringUTF(env, lean_string_cstr(lean_ctor_get(r, 1)));
  lean_dec(r);
  pthread_mutex_unlock(&mu);
  return said;
}

JNIEXPORT jbyteArray JNICALL Java_com_holmes_leanqr_Pics_tray(JNIEnv* env, jclass cls, jint height) {
  (void)cls;
  if (!lean_harness_ready() || height <= 0) return (*env)->NewByteArray(env, 0);
  pthread_mutex_lock(&mu);
  lean_object* ba = lean_pic_tray(state(), (uint32_t)height);
  pthread_mutex_unlock(&mu);
  return bytes(env, ba);
}

JNIEXPORT jbyteArray JNICALL Java_com_holmes_leanqr_Pics_blob(JNIEnv* env, jclass cls, jint i) {
  (void)cls;
  if (!lean_harness_ready() || i < 0) return (*env)->NewByteArray(env, 0);
  pthread_mutex_lock(&mu);
  lean_object* ba = lean_pic_blob(state(), (uint32_t)i);
  pthread_mutex_unlock(&mu);
  return bytes(env, ba);
}
