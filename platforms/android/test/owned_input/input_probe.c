#include <jni.h>
#include <dlfcn.h>
#include <stdbool.h>
#include <stdint.h>
static void (*set_hold)(bool);
static uint64_t (*get_blocked)(void);
static void (*set_view)(bool);
static void (*set_copy_failure)(int);
static uint64_t (*copy_failures)(int);
JNIEXPORT void JNICALL Java_com_holmes_ownedinput_OwnedInputProbe_attach(JNIEnv *env,jclass cls,jstring path) {
  (void)cls;
  const char *name=(*env)->GetStringUTFChars(env,path,0);
  void *h=dlopen(name,RTLD_NOW|RTLD_NOLOAD);
  (*env)->ReleaseStringUTFChars(env,path,name);
  if(h) {set_hold=dlsym(h,"lq_input_probe_gate");get_blocked=dlsym(h,"lq_input_probe_blocked");
    set_view=dlsym(h,"lq_input_probe_view");set_copy_failure=dlsym(h,"lq_input_probe_fail_copy");
    copy_failures=dlsym(h,"lq_input_probe_copy_failures");}
  if(!h||!set_hold||!get_blocked) {
    jclass ex=(*env)->FindClass(env,"java/lang/IllegalStateException");
    (*env)->ThrowNew(env,ex,"already-loaded real app gate symbols unavailable");
  }
}
JNIEXPORT void JNICALL Java_com_holmes_ownedinput_OwnedInputProbe_hold(JNIEnv *env,jclass cls,jboolean value) {
  (void)env;(void)cls;if(set_hold)set_hold(value);
}
JNIEXPORT jlong JNICALL Java_com_holmes_ownedinput_OwnedInputProbe_blocked(JNIEnv *env,jclass cls) {
  (void)env;(void)cls;return get_blocked?(jlong)get_blocked():0;
}
JNIEXPORT void JNICALL Java_com_holmes_ownedinput_OwnedInputProbe_holdView(JNIEnv *env,jclass cls,jboolean value) {
  (void)cls;
  if(!set_view){(*env)->ThrowNew(env,(*env)->FindClass(env,"java/lang/IllegalStateException"),"viewport gate unavailable");return;}
  set_view(value);
}
JNIEXPORT void JNICALL Java_com_holmes_ownedinput_OwnedInputProbe_failCopy(JNIEnv *env,jclass cls,jint site) {
  (void)cls;
  if(!set_copy_failure){(*env)->ThrowNew(env,(*env)->FindClass(env,"java/lang/IllegalStateException"),"allocation gate unavailable");return;}
  set_copy_failure(site);
}
JNIEXPORT jlong JNICALL Java_com_holmes_ownedinput_OwnedInputProbe_failedCopies(JNIEnv *env,jclass cls,jint site) {
  (void)cls;
  if(!copy_failures){(*env)->ThrowNew(env,(*env)->FindClass(env,"java/lang/IllegalStateException"),"allocation count unavailable");return 0;}
  return copy_failures(site);
}
