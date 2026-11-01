#include <jni.h>
#include <android/log.h>
#include <stdlib.h>
static void forbidden_destructor(void) {
  __android_log_write(ANDROID_LOG_ERROR, "LifecycleProbe", "FORBIDDEN: process exit ran global destructors");
  _Exit(91); /* deterministic control, before unrelated HWUI teardown can race */
}
JNIEXPORT void JNICALL Java_com_holmes_lifecycle_LifecycleProbe_installExitProbe(JNIEnv* e, jclass c) {
  (void)e; (void)c;
  atexit(forbidden_destructor);
}
