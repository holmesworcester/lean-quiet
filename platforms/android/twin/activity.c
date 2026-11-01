// The Android activity for a Lean app
// ===================================

// A NativeActivity whose Java half (java/.../LeanActivity.java) reports
// the insets and mirrors the keyboard's text. NativeActivity's callbacks
// and the Java half's natives run on the UI thread; Lean's main
// (lean_app_main, the app's main, renamed by build_apk.sh) runs on a
// thread of its own, and its stdout and stderr go to logcat under the tag
// "lean". Lean's cwd is the app's internal data directory, where the
// APK's assets/ is copied first, so a relative path like assets/x reads
// as on the desktop. The process ends when Lean's main returns: the
// runtime's state is global, so a second run in one process is unsafe.

#include "activity.h"
#include "layer.h"
#include "scroll.h"
#include "../../native/photo.h"
#include "../../native/editor_action.h"
#include <math.h>
#include <limits.h>

#include <android/asset_manager.h>
#include <dlfcn.h>
#include <android/configuration.h>
#include <android/log.h>
#include <android/native_activity.h>
#include <jni.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/system_properties.h>
#include <unistd.h>

int lean_app_main(int argc, char** argv);

#define BA_CAP 4096
#define BA_EVS 1024

static pthread_mutex_t ba_mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t  ba_cv = PTHREAD_COND_INITIALIZER;
static ANativeWindow*  ba_win;
static int32_t         ba_w;
static int32_t         ba_h;
static int32_t         ba_top, ba_bottom, ba_kb;
static int32_t         ba_sides[7];
static int32_t         ba_density = 420;
static int32_t         ba_text_dpi;
static bool            ba_closing;
static bool            ba_resumed;
static char*           ba_links[32];
static unsigned        ba_nlinks;
static void ba_event(uint32_t k, uint32_t a, uint32_t b, uint32_t c);
static bool ba_editor_enabled=true, ba_editor_ready, ba_editor_exhausted;
static uint64_t ba_editor_owner, ba_editor_installed, ba_editor_revision, ba_editor_content;
static bool ba_editor_handoff;
static LqEditorAction ba_action_slot;
static jmethodID ba_update_editor_m, ba_clear_action_m, ba_action_disposition_m;
static void ba_raw(uint32_t k,uint32_t a,uint32_t b,uint32_t c,uint64_t ms,uint64_t frame);
static uint32_t ba_admit(uint64_t owner,uint64_t revision);
static void ba_action_prefix(uint32_t refusal);

static BaTouch*        ba_q;
static uint32_t        ba_cap;
static uint32_t        ba_n;
static BaTouch*        ba_sq;
static uint32_t        ba_scap;
static uint32_t        ba_sn;

static bool            ba_started;
static bool            ba_lead = true;
static uint32_t*       ba_ev;
static uint32_t        ba_ecap;
static uint32_t        ba_en;
static char*           ba_txt;
static size_t          ba_txt_n;
static uint32_t        ba_pos[4];

static JavaVM*   ba_vm;
static jobject   ba_act;
static ANativeActivity* ba_owner;
static jmethodID ba_appearance_m;
static bool ba_system_dark;
static jmethodID ba_show_ime, ba_copy_text, ba_scan_m, ba_set_text_m;
static jmethodID ba_bars_m, ba_pick_photo_m;
static LqPhoto ba_photo = LQ_PHOTO_INIT;

// A caller owns a local Java reference, independent of Activity replacement.
// Only the first Activity initializes method IDs, before Lean's thread starts.
typedef struct { JNIEnv* env; jobject activity; bool attached; } BaJava;
static BaJava ba_target(void) {
  BaJava j = {0};
  if (!ba_vm) return j;
  j.attached = (*ba_vm)->GetEnv(ba_vm, (void**)&j.env, JNI_VERSION_1_6) != JNI_OK;
  if (j.attached && (*ba_vm)->AttachCurrentThread(ba_vm, &j.env, NULL) != JNI_OK) {
    j.env = NULL; j.attached = false; return j;
  }
  pthread_mutex_lock(&ba_mu);
  if (ba_act) j.activity = (*j.env)->NewLocalRef(j.env, ba_act);
  pthread_mutex_unlock(&ba_mu);
  return j;
}
static void ba_target_done(BaJava j) {
  if (j.activity) (*j.env)->DeleteLocalRef(j.env, j.activity);
  if (j.attached) (*ba_vm)->DetachCurrentThread(ba_vm);
}
// The caller holds ba_mu; stale Java callbacks cannot affect a new owner.
static bool ba_current(JNIEnv* env, jobject activity) {
  return ba_act && (*env)->IsSameObject(env, activity, ba_act);
}

// The newest camera frame's Y plane, until Lean takes it (ba_take_luma).
static bool     ba_camera_wanted;
static uint8_t* ba_luma;
static size_t   ba_luma_n;
static uint32_t ba_luma_wh[4];

bool ba_ahead(void) {
  return ba_lead;
}

// Surface
// -------

ANativeWindow* ba_lock(int32_t* w, int32_t* h) {
  pthread_mutex_lock(&ba_mu);
  if (ba_win == NULL || !ba_resumed || ba_closing) {
    pthread_mutex_unlock(&ba_mu);
    return NULL;
  }
  *w = ba_w;
  *h = ba_h;
  return ba_win;
}

bool ba_has_window(void) {
  pthread_mutex_lock(&ba_mu);
  bool on = ba_win != NULL && ba_resumed;
  pthread_mutex_unlock(&ba_mu);
  return on;
}

void ba_unlock(void) {
  pthread_mutex_unlock(&ba_mu);
}

void ba_size(int32_t* w, int32_t* h) {
  pthread_mutex_lock(&ba_mu);
  while (ba_win == NULL && !ba_closing) {
    pthread_cond_wait(&ba_cv, &ba_mu);
  }
  *w = ba_w;
  *h = ba_h;
  pthread_mutex_unlock(&ba_mu);
}

bool ba_size_now(int32_t* w, int32_t* h) {
  pthread_mutex_lock(&ba_mu);
  bool on = ba_win != NULL;
  if (on) {
    *w = ba_w;
    *h = ba_h;
  }
  pthread_mutex_unlock(&ba_mu);
  return on;
}

void ba_insets(int32_t* top, int32_t* bottom, int32_t* ime) {
  pthread_mutex_lock(&ba_mu);
  *top    = ba_top;
  *bottom = ba_bottom;
  *ime    = ba_kb;
  pthread_mutex_unlock(&ba_mu);
}

void ba_safe(int32_t out[7]) {
  pthread_mutex_lock(&ba_mu);
  memcpy(out, ba_sides, sizeof ba_sides);
  pthread_mutex_unlock(&ba_mu);
}

int32_t ba_dpi(void) {
  pthread_mutex_lock(&ba_mu);
  int32_t dpi = ba_text_dpi > 0 ? ba_text_dpi : ba_density;
  pthread_mutex_unlock(&ba_mu);
  return dpi;
}

static void ba_window_created(ANativeActivity* act, ANativeWindow* win) {
  pthread_mutex_lock(&ba_mu);
  if (ba_owner != act) { pthread_mutex_unlock(&ba_mu); return; }
  ba_win = win;
  ba_w   = ANativeWindow_getWidth(win);
  ba_h   = ANativeWindow_getHeight(win);
  ba_event(11, 1, 0, 0);
  ba_event(12, 0, 0, 0);
  pthread_cond_broadcast(&ba_cv);
  pthread_mutex_unlock(&ba_mu);
}

static void ba_window_resized(ANativeActivity* act, ANativeWindow* win) {
  ba_window_created(act, win);
}

// Returns only once Lean's thread is not drawing to the surface.
static void ba_window_destroyed(ANativeActivity* act, ANativeWindow* win) {
  pthread_mutex_lock(&ba_mu);
  if (ba_owner != act || ba_win != win) { pthread_mutex_unlock(&ba_mu); return; }
  ba_win = NULL;
  ba_event(11, 0, 0, 0);
  bl_window_gone();
  pthread_mutex_unlock(&ba_mu);
}

static void ba_pause(ANativeActivity* act) {
  pthread_mutex_lock(&ba_mu);
  if (ba_owner != act) { pthread_mutex_unlock(&ba_mu); return; }
  ba_resumed = false;
  ba_camera_wanted = false;
  free(ba_luma); ba_luma = NULL; ba_luma_n = 0;
  ba_kb = 0;
  ba_n = ba_sn = 0;
  ba_event(9, 0, 0, 0);
  bl_window_gone();
  pthread_cond_broadcast(&ba_cv);
  pthread_mutex_unlock(&ba_mu);
}

static void ba_resume(ANativeActivity* act) {
  pthread_mutex_lock(&ba_mu);
  if (ba_owner != act) { pthread_mutex_unlock(&ba_mu); return; }
  ba_resumed = true;
  ba_event(10, 0, 0, 0);
  pthread_cond_broadcast(&ba_cv);
  pthread_mutex_unlock(&ba_mu);
}

static void ba_destroy(ANativeActivity* act) {
  JNIEnv* env = act->env;
  jclass cls = (*env)->GetObjectClass(env, act->clazz);
  jmethodID changing = (*env)->GetMethodID(env, cls, "isChangingConfigurations", "()Z");
  bool recreate = changing && (*env)->CallBooleanMethod(env, act->clazz, changing);
  if ((*env)->ExceptionCheck(env)) { (*env)->ExceptionClear(env); recreate = false; }
  (*env)->DeleteLocalRef(env, cls);
  pthread_mutex_lock(&ba_mu);
  if (ba_owner == act) {
    ba_owner = NULL;
    ba_resumed = false;
    ba_win = NULL;
    bl_window_gone();
    if (ba_act) { (*env)->DeleteGlobalRef(env, ba_act); ba_act = NULL; }
    // Configuration destruction replaces the Android owner, not Lean's run.
    if (!recreate) ba_closing = true;
    pthread_cond_broadcast(&ba_cv);
  }
  pthread_mutex_unlock(&ba_mu);
  __android_log_print(ANDROID_LOG_INFO, "lean", "activity destroyed: configuration=%d", recreate);
}

// Events from the Java half
// -------------------------

static uint64_t ba_input_ms(void) {
  struct timespec ts;clock_gettime(CLOCK_MONOTONIC,&ts);
  return (uint64_t)ts.tv_sec*1000u+(uint64_t)ts.tv_nsec/1000000u;
}
/* Touches and Java events enter this one ordered stream under ba_mu. */
static void ba_raw(uint32_t k,uint32_t a,uint32_t b,uint32_t c,uint64_t ms,uint64_t frame) {
  if(ba_en==ba_ecap) {
    ba_ecap=ba_ecap?ba_ecap*2:BA_EVS;
    ba_ev=realloc(ba_ev,ba_ecap*8*sizeof *ba_ev);if(!ba_ev)abort();
  }
  uint32_t *e=ba_ev+8*ba_en++;
  e[0]=k;e[1]=a;e[2]=b;e[3]=c;e[4]=ms;e[5]=ms>>32;e[6]=frame;e[7]=frame>>32;
}
static void ba_event(uint32_t k,uint32_t a,uint32_t b,uint32_t c) {
  ba_raw(k>=9&&k<=12?k+7:k,a,b,c,ba_input_ms(),bl_view_id());
}
uint32_t ba_drain_events(uint32_t *out,uint32_t max_words,bool *closed) {
  pthread_mutex_lock(&ba_mu);
  uint32_t n=ba_en<max_words/8?ba_en:max_words/8;
  /* Never separate an owned prefix from its terminal sample. */
  if(n&&ba_ev[(n-1)*8]==22)n--;
  memcpy(out,ba_ev,n*8*sizeof *out);
  memmove(ba_ev,ba_ev+n*8,(ba_en-n)*8*sizeof *out);ba_en-=n;
  *closed=ba_closing;
  pthread_mutex_unlock(&ba_mu);return n*8;
}
static uint32_t ba_admit(uint64_t owner,uint64_t revision) {
  return lq_action_admit(&ba_action_slot,owner,revision,ba_editor_content,ba_txt?ba_txt:"",ba_txt_n,ba_pos,
    ba_resumed&&ba_editor_ready&&!ba_editor_exhausted&&owner==ba_editor_owner&&owner==ba_editor_installed&&revision==ba_editor_revision);
}
static void ba_action_prefix(uint32_t refusal) {
  uint64_t ticket=refusal?0:ba_action_slot.ticket;
  uint64_t owner=refusal?ba_editor_installed:ba_action_slot.owner;
  ba_raw(22,ticket,ticket>>32,refusal,owner,0);
}

char* ba_text(uint32_t pos[4]) {
  pthread_mutex_lock(&ba_mu);
  char* s = strdup(ba_txt != NULL ? ba_txt : "");
  memcpy(pos, ba_pos, sizeof ba_pos);
  pthread_mutex_unlock(&ba_mu);
  return s;
}

static void JNICALL ba_n_appearance(JNIEnv* env, jobject activity, jboolean dark, jint text_dpi) {
  pthread_mutex_lock(&ba_mu);
  if (!ba_current(env, activity)) { pthread_mutex_unlock(&ba_mu); return; }
  ba_system_dark = dark;
  if (text_dpi > 0 && text_dpi <= 2560) ba_text_dpi = text_dpi;
  pthread_mutex_unlock(&ba_mu);
}

bool ba_dark(void) {
  pthread_mutex_lock(&ba_mu);
  bool dark = ba_system_dark;
  pthread_mutex_unlock(&ba_mu);
  return dark;
}

void ba_appearance(bool dark, uint32_t background) {
  if (!ba_appearance_m) return;
  BaJava j = ba_target();
  if (!j.activity) { ba_target_done(j); return; }
  JNIEnv* env = j.env;
  (*env)->CallVoidMethod(env, j.activity, ba_appearance_m, (jboolean)dark, (jint)background);
  if ((*env)->ExceptionCheck(env)) {
    (*env)->ExceptionDescribe(env);
    (*env)->ExceptionClear(env);
  }
  ba_target_done(j);
}

static void JNICALL ba_n_insets(JNIEnv* env, jobject activity, jint top, jint bottom, jint ime,
    jint left, jint right, jint cl, jint ct, jint cr, jint cb) {
  pthread_mutex_lock(&ba_mu);
  if (!ba_current(env, activity)) { pthread_mutex_unlock(&ba_mu); return; }
  bool kb = ime != ba_kb;
  ba_top    = top;
  ba_bottom = bottom;
  ba_kb     = ime;
  int32_t sides[7] = { left, right, ime, cl, ct, cr, cb };
  memcpy(ba_sides, sides, sizeof sides);
  if (kb) {
    ba_event(6, (uint32_t)ime, 0, 0);
  }
  pthread_mutex_unlock(&ba_mu);
}

// Java's modified UTF-8 is converted by the JVM; GetStringUTFChars gives
// modified UTF-8, which differs from UTF-8 for supplementary characters
// (emoji) and NUL, so the text is converted here from UTF-16 instead.
static char* ba_utf8_len(JNIEnv* env, jstring text, size_t *length) {
  jsize        n = (*env)->GetStringLength(env, text);
  const jchar* u = (*env)->GetStringChars(env, text, NULL);
  char*        s = malloc((size_t)n * 3 + 1);
  size_t       k = 0;
  for (jsize i = 0; u != NULL && s != NULL && i < n; i += 1) {
    uint32_t c = u[i];
    if (c >= 0xD800 && c < 0xDC00 && i + 1 < n && u[i + 1] >= 0xDC00 && u[i + 1] < 0xE000) {
      c = 0x10000 + ((c - 0xD800) << 10) + (u[i + 1] - 0xDC00);
      i += 1;
    } else if (c >= 0xD800 && c < 0xE000) {
      c = 0xFFFD;
    }
    if (c < 0x80) {
      s[k++] = (char)c;
    } else if (c < 0x800) {
      s[k++] = (char)(0xC0 | c >> 6);
      s[k++] = (char)(0x80 | (c & 63));
    } else if (c < 0x10000) {
      s[k++] = (char)(0xE0 | c >> 12);
      s[k++] = (char)(0x80 | (c >> 6 & 63));
      s[k++] = (char)(0x80 | (c & 63));
    } else {
      s[k++] = (char)(0xF0 | c >> 18);
      s[k++] = (char)(0x80 | (c >> 12 & 63));
      s[k++] = (char)(0x80 | (c >> 6 & 63));
      s[k++] = (char)(0x80 | (c & 63));
    }
  }
  if (s != NULL) {
    s[k] = 0;
  }
  if (u != NULL) {
    (*env)->ReleaseStringChars(env, text, u);
  }
  if(length)*length=k;
  return s;
}
static char* ba_utf8(JNIEnv* env,jstring text) {return ba_utf8_len(env,text,NULL);}

static void JNICALL ba_n_text(JNIEnv* env,jobject activity,jlong owner,jlong revision,
    jstring text,jint ss,jint se,jint cs,jint ce,jboolean installed) {
  size_t length=0;char *value=ba_utf8_len(env,text,&length);if(!value)return;
  pthread_mutex_lock(&ba_mu);
  bool current=ba_current(env,activity);
  bool handoff=ba_editor_handoff&&(uint64_t)owner==ba_editor_installed;
  bool target=(uint64_t)owner==ba_editor_owner;
  if(!current||(ba_editor_enabled&&(!owner||(!target&&!handoff)||(!installed&&!ba_resumed)))) {
    free(value);pthread_mutex_unlock(&ba_mu);return;
  }
  if(ba_editor_enabled&&!revision) {
    ba_editor_ready=false;ba_editor_exhausted=true;ba_editor_revision=0;lq_action_retire(&ba_action_slot);
  } else if(ba_editor_enabled) {
    if(!installed&&(uint64_t)revision<=ba_editor_revision) {
      free(value);pthread_mutex_unlock(&ba_mu);return;
    }
    ba_editor_revision=revision;
    if(installed) {ba_editor_installed=owner;ba_editor_ready=target;ba_editor_handoff=false;}
  }
  free(ba_txt);ba_txt=value;ba_txt_n=length;
  ba_pos[0]=ss;ba_pos[1]=se;ba_pos[2]=cs;ba_pos[3]=ce;
  ba_event(4,0,0,0);pthread_mutex_unlock(&ba_mu);
}

static void JNICALL ba_n_action_done(JNIEnv *env,jobject activity,jlong ticket) {
  pthread_mutex_lock(&ba_mu);
  if(ba_current(env,activity))lq_action_clear_done(&ba_action_slot,ticket);
  pthread_mutex_unlock(&ba_mu);
}

static jboolean JNICALL ba_n_editor_ready(JNIEnv *env,jobject activity,jlong owner,jlong revision) {
  pthread_mutex_lock(&ba_mu);
  bool ready=ba_current(env,activity)&&ba_editor_ready&&!ba_editor_exhausted&&owner&&revision&&
    (uint64_t)owner==ba_editor_owner&&(uint64_t)owner==ba_editor_installed&&
    (uint64_t)revision==ba_editor_revision;
  pthread_mutex_unlock(&ba_mu);return ready;
}

static void JNICALL ba_n_photo(JNIEnv* env, jobject activity, jint token, jint status,
    jint w, jint h, jbyteArray rgba) {
  if (status == 4) {
    pthread_mutex_lock(&ba_mu);
    if (ba_current(env, activity)) lq_photo_selected(&ba_photo, (uint32_t)token);
    pthread_mutex_unlock(&ba_mu);
    return;
  }
  jsize n = rgba ? (*env)->GetArrayLength(env, rgba) : 0;
  if (status == 1 && (w <= 0 || h <= 0 || w > 2048 || h > 2048 || n != (int64_t)w*h*4)) return;
  jbyte* bytes = rgba ? (*env)->GetByteArrayElements(env, rgba, NULL) : NULL;
  if (rgba && !bytes) return;
  pthread_mutex_lock(&ba_mu);
  if (ba_current(env, activity)) lq_photo_publish(&ba_photo, (uint32_t)token, (uint32_t)status, (uint32_t)w, (uint32_t)h,
      (const unsigned char*)bytes, (size_t)n);
  pthread_mutex_unlock(&ba_mu);
  if (bytes) (*env)->ReleaseByteArrayElements(env, rgba, bytes, JNI_ABORT);
}

bool ba_take_photo(uint32_t header[4], uint8_t** bytes, size_t* size) {
  return lq_photo_take(&ba_photo, header, bytes, size);
}

bool ba_pick_photo(uint32_t token) {
  lq_photo_begin(&ba_photo, token);
  if (!ba_pick_photo_m) return false;
  BaJava j = ba_target();
  if (!j.activity) { ba_target_done(j); return false; }
  JNIEnv* env = j.env;
  (*env)->CallVoidMethod(env, j.activity, ba_pick_photo_m, (jint)token);
  bool ok = !(*env)->ExceptionCheck(env);
  if (!ok) (*env)->ExceptionClear(env);
  ba_target_done(j);
  return ok;
}

static void JNICALL ba_n_luma(JNIEnv* env, jobject activity, jobject buf, jint w, jint h, jint stride,
  jint orient) {
  const uint8_t* y = (*env)->GetDirectBufferAddress(env, buf);
  jlong          n = (*env)->GetDirectBufferCapacity(env, buf);
  if (y == NULL || n <= 0 || w <= 0 || h <= 0 || stride <= 0) {
    return;
  }
  pthread_mutex_lock(&ba_mu);
  if (!ba_current(env, activity)) { pthread_mutex_unlock(&ba_mu); return; }
  if (!ba_camera_wanted || !ba_resumed) { pthread_mutex_unlock(&ba_mu); return; }
  uint8_t* p = realloc(ba_luma, (size_t)n);
  if (p != NULL) {
    memcpy(p, y, (size_t)n);
    ba_luma       = p;
    ba_luma_n     = (size_t)n;
    ba_luma_wh[0] = (uint32_t)w;
    ba_luma_wh[1] = (uint32_t)h;
    ba_luma_wh[2] = (uint32_t)stride;
    ba_luma_wh[3] = (uint32_t)orient;
  }
  pthread_mutex_unlock(&ba_mu);
}

uint8_t* ba_take_luma(size_t* n, uint32_t wh[4]) {
  pthread_mutex_lock(&ba_mu);
  uint8_t* p = ba_luma;
  *n         = ba_luma_n;
  memcpy(wh, ba_luma_wh, sizeof ba_luma_wh);
  ba_luma   = NULL;
  ba_luma_n = 0;
  pthread_mutex_unlock(&ba_mu);
  return p;
}

static jint JNICALL ba_n_action(JNIEnv* env,jobject activity,jlong owner,jlong revision,
    jint kind,jint code,jint action) {
  pthread_mutex_lock(&ba_mu);
  if(!ba_current(env,activity)){pthread_mutex_unlock(&ba_mu);return LQ_ACTION_STALE;}
  uint32_t refusal=0;
  bool submission=(kind==5&&code==4)||(kind==14&&code==66&&action==0);
  if(ba_editor_enabled&&submission) {
    refusal=ba_admit(owner,revision);
    if(!refusal){ba_action_prefix(0);ba_event(kind,code,action,0);}
  } else ba_event(kind,code,action,0);
  pthread_mutex_unlock(&ba_mu);return refusal;
}

// Calls into the Java half, from any thread (they post to the UI thread).
// Newly attached worker calls detach after releasing their local reference.
static void ba_call(jmethodID m, bool arg) {
  if (!m) return;
  BaJava j = ba_target();
  if (!j.activity) { ba_target_done(j); return; }
  JNIEnv* env = j.env;
  if (m == ba_show_ime) {
    (*env)->CallVoidMethod(env, j.activity, m, (jboolean)arg);
  } else {
    (*env)->CallVoidMethod(env, j.activity, m);
  }
  if ((*env)->ExceptionCheck(env)) {
    (*env)->ExceptionDescribe(env);
    (*env)->ExceptionClear(env);
  }
  ba_target_done(j);
}

void ba_ime(bool show) {
  ba_call(ba_show_ime, show);
}


void ba_scan(bool on) {
  pthread_mutex_lock(&ba_mu);
  ba_camera_wanted = on;
  free(ba_luma); ba_luma = NULL; ba_luma_n = 0;
  pthread_mutex_unlock(&ba_mu);
  if (!ba_scan_m) return;
  BaJava j = ba_target();
  if (!j.activity) { ba_target_done(j); return; }
  JNIEnv* env = j.env;
  (*env)->CallVoidMethod(env, j.activity, ba_scan_m, (jboolean)on);
  if ((*env)->ExceptionCheck(env)) {
    (*env)->ExceptionDescribe(env);
    (*env)->ExceptionClear(env);
  }
  ba_target_done(j);
}

void ba_copy(const char* utf8) {
  if (!ba_copy_text) return;
  BaJava j = ba_target();
  if (!j.activity) { ba_target_done(j); return; }
  JNIEnv* env = j.env;
  jstring s = (*env)->NewStringUTF(env, utf8);
  (*env)->CallVoidMethod(env, j.activity, ba_copy_text, s);
  (*env)->DeleteLocalRef(env, s);
  if ((*env)->ExceptionCheck(env)) {
    (*env)->ExceptionDescribe(env);
    (*env)->ExceptionClear(env);
  }
  ba_target_done(j);
}

void ba_set_text(const char* utf8) {
  pthread_mutex_lock(&ba_mu);bool owned=ba_editor_enabled;pthread_mutex_unlock(&ba_mu);
  if(owned)return; // owned editors use revision-aware asynchronous commands only
  if (!ba_set_text_m) return;
  BaJava j = ba_target();
  if (!j.activity) { ba_target_done(j); return; }
  JNIEnv* env = j.env;
  jstring s = (*env)->NewStringUTF(env, utf8);
  (*env)->CallVoidMethod(env, j.activity, ba_set_text_m, s);
  (*env)->DeleteLocalRef(env, s);
  if ((*env)->ExceptionCheck(env)) {
    (*env)->ExceptionDescribe(env);
    (*env)->ExceptionClear(env);
  }
  ba_target_done(j);
}

// URL delivery is independent of the debug control socket.
static void JNICALL ba_n_link(JNIEnv* env, jobject activity, jstring text) {
  char* url = ba_utf8(env, text);
  pthread_mutex_lock(&ba_mu);
  if (!ba_current(env, activity)) { free(url); pthread_mutex_unlock(&ba_mu); return; }
  if (ba_nlinks < 32) ba_links[ba_nlinks++] = url;
  else free(url);
  pthread_mutex_unlock(&ba_mu);
}

char* ba_take_link(void) {
  pthread_mutex_lock(&ba_mu);
  char* url = ba_nlinks ? ba_links[0] : NULL;
  if (ba_nlinks) {
    --ba_nlinks;
    memmove(ba_links, ba_links + 1, ba_nlinks * sizeof(char*));
  }
  pthread_mutex_unlock(&ba_mu);
  return url;
}

void ba_bars(uint32_t top, uint32_t bottom, bool light_top, bool light_bottom) {
  if (!ba_bars_m) return;
  BaJava j = ba_target();
  if (!j.activity) { ba_target_done(j); return; }
  JNIEnv* env = j.env;
  (*env)->CallVoidMethod(env, j.activity, ba_bars_m, (jint)top, (jint)bottom,
      (jboolean)light_top, (jboolean)light_bottom);
  if ((*env)->ExceptionCheck(env)) {
    (*env)->ExceptionDescribe(env);
    (*env)->ExceptionClear(env);
  }
  ba_target_done(j);
}

static void ba_java(ANativeActivity* act) {
  pthread_mutex_lock(&ba_mu);ba_editor_ready=false;lq_action_retire(&ba_action_slot);pthread_mutex_unlock(&ba_mu);
  JNIEnv* env = act->env;
  jclass  cls = (*env)->GetObjectClass(env, act->clazz);
  JNINativeMethod ms[] = {
    { "nAppearance", "(ZI)V", (void*)ba_n_appearance },
    { "nInsets", "(IIIIIIIII)V", (void*)ba_n_insets },
    { "nText", "(JJLjava/lang/String;IIIIZ)V", (void*)ba_n_text },
    { "nActionDone", "(J)V", (void*)ba_n_action_done },
    { "nEditorReady", "(JJ)Z", (void*)ba_n_editor_ready },
    { "nLink", "(Ljava/lang/String;)V", (void*)ba_n_link },
    { "nAction", "(JJIII)I", (void*)ba_n_action },
    { "nLuma", "(Ljava/nio/ByteBuffer;IIII)V", (void*)ba_n_luma },
    { "nPhoto", "(IIII[B)V", (void*)ba_n_photo },
  };
  if ((*env)->RegisterNatives(env, cls, ms, (jint)(sizeof ms / sizeof ms[0])) != 0) {
    (*env)->ExceptionClear(env);
    __android_log_write(ANDROID_LOG_ERROR, "lean", "cannot register the Java half's natives");
    return;
  }
  if (ba_vm == NULL) {
    ba_vm = act->vm;
    ba_appearance_m = (*env)->GetMethodID(env, cls, "appearance", "(ZI)V");
    ba_show_ime   = (*env)->GetMethodID(env, cls, "showIme", "(Z)V");
    ba_copy_text  = (*env)->GetMethodID(env, cls, "copyText", "(Ljava/lang/String;)V");
    ba_set_text_m = (*env)->GetMethodID(env, cls, "setText", "(Ljava/lang/String;)V");
    ba_update_editor_m = (*env)->GetMethodID(env, cls, "updateEditor", "(JJ[BI)V");
    ba_clear_action_m = (*env)->GetMethodID(env, cls, "clearAction", "(JJJ)V");
    ba_action_disposition_m = (*env)->GetMethodID(env, cls, "actionDisposition", "(JI)V");
    ba_pick_photo_m = (*env)->GetMethodID(env, cls, "pickPhoto", "(I)V");
    ba_scan_m     = (*env)->GetMethodID(env, cls, "scan", "(Z)V");
    ba_bars_m     = (*env)->GetMethodID(env, cls, "applyBars", "(IIZZ)V");
    if ((*env)->ExceptionCheck(env)) {
      (*env)->ExceptionClear(env);
      ba_appearance_m = ba_pick_photo_m = ba_show_ime = ba_copy_text = ba_scan_m = ba_set_text_m = ba_bars_m = NULL;
    }
  }
  pthread_mutex_lock(&ba_mu);
  if (ba_owner != act) {
    ba_win = NULL;
    ba_resumed = false;
    bl_window_gone();
  }
  if (ba_act) (*env)->DeleteGlobalRef(env, ba_act);
  ba_act = (*env)->NewGlobalRef(env, act->clazz);
  ba_owner = act;
  pthread_mutex_unlock(&ba_mu);
  (*env)->DeleteLocalRef(env, cls);

}

// Touches
// -------



uint32_t ba_drain(BaTouch* out, uint32_t max, bool* closed) {
  pthread_mutex_lock(&ba_mu);
  uint32_t n = ba_n < max ? ba_n : max;
  memcpy(out, ba_q, n * sizeof *out);
  memmove(ba_q, ba_q + n, (ba_n - n) * sizeof *out);
  ba_n   -= n;
  *closed = ba_closing;
  pthread_mutex_unlock(&ba_mu);
  return n;
}

// Lossless transport. Lean decides ownership, slop and scroll routing.
static void ba_push(BaKind kind,int32_t id,float x,float y,int64_t t) {
  if(ba_editor_enabled&&kind==BA_UP)ba_action_prefix(ba_admit(ba_editor_installed,ba_editor_revision));
  ba_raw(9+kind,id,(int32_t)lroundf(x),(int32_t)lroundf(y),(uint64_t)t/1000000u,bl_view_id());
}

void ba_accept_scroll(BaTouch sample) {
  pthread_mutex_lock(&ba_mu);
  if (ba_sn == ba_scap) {
    ba_scap = ba_scap ? ba_scap * 2 : BA_CAP;
    ba_sq = realloc(ba_sq, ba_scap * sizeof *ba_sq);
    if (!ba_sq) abort();
  }
  ba_sq[ba_sn++] = sample;
  pthread_mutex_unlock(&ba_mu);
}

uint32_t ba_drain_scroll(BaTouch* out, uint32_t max) {
  pthread_mutex_lock(&ba_mu);
  uint32_t n = ba_sn < max ? ba_sn : max;
  memcpy(out, ba_sq, n * sizeof *out);
  memmove(ba_sq, ba_sq + n, (ba_sn - n) * sizeof *out);
  ba_sn -= n;
  pthread_mutex_unlock(&ba_mu);
  return n;
}

static void ba_motion(const AInputEvent* ev) {
  int32_t action = AMotionEvent_getAction(ev);
  int32_t kind = action & AMOTION_EVENT_ACTION_MASK;
  int32_t at = (action & AMOTION_EVENT_ACTION_POINTER_INDEX_MASK)
    >> AMOTION_EVENT_ACTION_POINTER_INDEX_SHIFT;
  pthread_mutex_lock(&ba_mu);
  for (size_t i = 0; i < AMotionEvent_getPointerCount(ev); i++) {
    int32_t id = AMotionEvent_getPointerId(ev, i);
    if (kind == AMOTION_EVENT_ACTION_MOVE) {
      for (size_t h = 0; h < AMotionEvent_getHistorySize(ev); h++)
        ba_push(BA_MOVE, id, AMotionEvent_getHistoricalX(ev, i, h),
          AMotionEvent_getHistoricalY(ev, i, h), AMotionEvent_getHistoricalEventTime(ev, h));
      ba_push(BA_MOVE, id, AMotionEvent_getX(ev, i), AMotionEvent_getY(ev, i), AMotionEvent_getEventTime(ev));
    } else if (kind == AMOTION_EVENT_ACTION_CANCEL) {
      ba_push(BA_CANCEL, id, AMotionEvent_getX(ev, i), AMotionEvent_getY(ev, i), AMotionEvent_getEventTime(ev));
    } else if ((int32_t)i == at) {
      if (kind == AMOTION_EVENT_ACTION_DOWN || kind == AMOTION_EVENT_ACTION_POINTER_DOWN)
        ba_push(BA_DOWN, id, AMotionEvent_getX(ev, i), AMotionEvent_getY(ev, i), AMotionEvent_getEventTime(ev));
      else if (kind == AMOTION_EVENT_ACTION_UP || kind == AMOTION_EVENT_ACTION_POINTER_UP)
        ba_push(BA_UP, id, AMotionEvent_getX(ev, i), AMotionEvent_getY(ev, i), AMotionEvent_getEventTime(ev));
    }
  }
  pthread_mutex_unlock(&ba_mu);
}

// Keys stay unhandled: they continue to the focused EditText (a hardware
// keyboard, `adb shell input text`), and Back closes the keyboard, else
// finishes the activity (a Close).
static int ba_input(int fd, int events, void* data) {
  AInputQueue* q = data;
  AInputEvent* ev;
  while (AInputQueue_getEvent(q, &ev) >= 0) {
    if (AInputQueue_preDispatchEvent(q, ev)) {
      continue;
    }
    int handled = AInputEvent_getType(ev) == AINPUT_EVENT_TYPE_MOTION;
    if (handled) {
      ba_motion(ev);
    }
    AInputQueue_finishEvent(q, ev, handled);
  }
  return 1;
}

static void ba_queue_created(ANativeActivity* act, AInputQueue* q) {
  AInputQueue_attachLooper(q, ALooper_forThread(), 1, ba_input, q);
}

static void ba_queue_destroyed(ANativeActivity* act, AInputQueue* q) {
  AInputQueue_detachLooper(q);
}

// Files
// -----

// The install this library came from: its file's modification time,
// which an update or reinstall changes.
static long long ba_install_stamp(void) {
  Dl_info     info;
  struct stat st;
  if (dladdr((void*)ba_install_stamp, &info) == 0 || info.dli_fname == NULL
    || stat(info.dli_fname, &st) != 0) {
    return -1;
  }
  return (long long)st.st_mtime;
}

// Copies the APK's assets/assets/* (one level) to <dir>/assets/ and
// makes dir the cwd, unless assets/.stamp says this install's assets are
// already there (the font is large: a launch should not copy it again).
// Returns false (logged) on any failure.
static bool ba_files(ANativeActivity* act) {
  const char* dir = act->internalDataPath;
  if (dir == NULL || chdir(dir) != 0) {
    __android_log_print(ANDROID_LOG_ERROR, "lean", "cannot enter %s", dir);
    return false;
  }
  long long stamp = ba_install_stamp();
  FILE*     sf    = fopen("assets/.stamp", "r");
  long long had   = -2;
  if (sf != NULL) {
    if (fscanf(sf, "%lld", &had) != 1) {
      had = -2;
    }
    fclose(sf);
  }
  if (stamp >= 0 && had == stamp) {
    return true;
  }
  AAssetDir* ad = AAssetManager_openDir(act->assetManager, "assets");
  if (ad == NULL) {
    return true;
  }
  mkdir("assets", 0700);
  bool        ok = true;
  const char* name;
  while ((name = AAssetDir_getNextFileName(ad)) != NULL) {
    char path[512];
    snprintf(path, sizeof path, "assets/%s", name);
    AAsset* a   = AAssetManager_open(act->assetManager, path, AASSET_MODE_STREAMING);
    FILE*   out = a != NULL ? fopen(path, "wb") : NULL;
    char    buf[1 << 16];
    int     n   = 0;
    while (out != NULL && (n = AAsset_read(a, buf, sizeof buf)) > 0) {
      if (fwrite(buf, 1, (size_t)n, out) != (size_t)n) {
        n = -1;
        break;
      }
    }
    if (out == NULL || n < 0 || fclose(out) != 0) {
      __android_log_print(ANDROID_LOG_ERROR, "lean", "cannot copy %s", path);
      ok = false;
    }
    if (a != NULL) {
      AAsset_close(a);
    }
  }
  AAssetDir_close(ad);
  if (ok && stamp >= 0 && (sf = fopen("assets/.stamp", "w")) != NULL) {
    fprintf(sf, "%lld\n", stamp);
    fclose(sf);
  }
  return ok;
}

// Threads
// -------

static void* ba_log(void* arg) {
  FILE* in = fdopen((int)(intptr_t)arg, "r");
  char  line[1024];
  while (fgets(line, sizeof line, in) != NULL) {
    line[strcspn(line, "\n")] = 0;
    __android_log_write(ANDROID_LOG_INFO, "lean", line);
  }
  return NULL;
}

static void* ba_run(void* arg) {
  char* argv[] = { "lean", NULL };
  int   code   = lean_app_main(1, argv);
  fflush(stdout);
  fflush(stderr);
  __android_log_print(ANDROID_LOG_INFO, "lean", "main returned %d", code);
  // Android/HWUI threads still run. Never run their global destructors here.
  _Exit(code);
}

static void ba_spawn(void* (*fn)(void*), void* arg, size_t stack) {
  pthread_t      t;
  pthread_attr_t a;
  pthread_attr_init(&a);
  pthread_attr_setstacksize(&a, stack);
  pthread_attr_setdetachstate(&a, PTHREAD_CREATE_DETACHED);
  if (pthread_create(&t, &a, fn, arg) != 0) {
    __android_log_write(ANDROID_LOG_FATAL, "lean", "cannot start a thread");
    abort();
  }
  pthread_attr_destroy(&a);
}

void lq_ctl_start(void);

void ANativeActivity_onCreate(ANativeActivity* act, void* saved, size_t n) {
  act->callbacks->onNativeWindowCreated   = ba_window_created;
  act->callbacks->onNativeWindowResized   = ba_window_resized;
  act->callbacks->onNativeWindowDestroyed = ba_window_destroyed;
  act->callbacks->onInputQueueCreated     = ba_queue_created;
  act->callbacks->onInputQueueDestroyed   = ba_queue_destroyed;
  act->callbacks->onPause                 = ba_pause;
  act->callbacks->onResume                = ba_resume;
  act->callbacks->onDestroy               = ba_destroy;
  ba_java(act);
  if (ba_started) {
    return;
  }
  ba_started = true;
  AConfiguration* cfg = AConfiguration_new();
  AConfiguration_fromAssetManager(cfg, act->assetManager);
  int32_t d = AConfiguration_getDensity(cfg);
  if (d > 0 && d != ACONFIGURATION_DENSITY_ANY && d != ACONFIGURATION_DENSITY_NONE) {
    ba_density = d;
  }
  AConfiguration_delete(cfg);
  bs_init(act->vm, act->clazz);
  char v[PROP_VALUE_MAX] = { 0 };
  ba_lead = !(__system_property_get("debug.lean.ahead", v) > 0 && strcmp(v, "0") == 0);
  int fds[2];
  if (pipe(fds) == 0) {
    setvbuf(stdout, NULL, _IOLBF, 0);
    setvbuf(stderr, NULL, _IONBF, 0);
    dup2(fds[1], STDOUT_FILENO);
    dup2(fds[1], STDERR_FILENO);
    ba_spawn(ba_log, (void*)(intptr_t)fds[0], 64 << 10);
  }
  ba_files(act);
#ifdef LQ_CTL
  lq_ctl_start();
#endif
  ba_spawn(ba_run, NULL, 256 << 20);
}

static void ba_editor_post(uint64_t owner,uint64_t revision,const char *text,size_t n,uint32_t mode) {
  if(!ba_update_editor_m)return;
  if(n>INT_MAX)return;
  BaJava j=ba_target();if(!j.activity){ba_target_done(j);return;}
  jbyteArray bytes=(*j.env)->NewByteArray(j.env,(jsize)n);
  if(bytes) {
    (*j.env)->SetByteArrayRegion(j.env,bytes,0,(jsize)n,(const jbyte*)text);
    (*j.env)->CallVoidMethod(j.env,j.activity,ba_update_editor_m,(jlong)owner,(jlong)revision,bytes,(jint)mode);
    (*j.env)->DeleteLocalRef(j.env,bytes);
  }
  if((*j.env)->ExceptionCheck(j.env))(*j.env)->ExceptionClear(j.env);
  ba_target_done(j);
}
char *ba_editor(uint32_t mode,uint64_t owner,uint64_t revision,const char *text,size_t length,uint64_t out[12],size_t *size) {
  bool post=false;char *handoff_text=NULL;size_t handoff_size=0;uint64_t clear_revision=0;
  pthread_mutex_lock(&ba_mu);ba_editor_enabled=mode!=4;
  if((mode==1||mode==5)&&owner) {
    ba_editor_content=revision;
    if(owner!=ba_editor_owner) {
      bool preserve=mode==5&&(ba_editor_ready||ba_editor_handoff||
        (ba_editor_owner&&ba_editor_owner==ba_editor_installed));
      ba_editor_owner=owner;ba_editor_ready=false;ba_editor_exhausted=false;
      ba_editor_handoff=preserve;lq_action_retire(&ba_action_slot);
    }
    post=!ba_editor_ready&&!ba_editor_exhausted;
    if(post&&ba_editor_handoff) {
      bool consumed=lq_action_consumed(&ba_action_slot,ba_editor_installed,ba_editor_revision);
      handoff_size=consumed?0:ba_txt_n;
      handoff_text=lq_editor_copy(ba_txt?ba_txt:"",handoff_size,1);
      clear_revision=consumed?ba_editor_revision:0;
      if(!handoff_text)post=false;
      mode=5;
    } else mode=1;
  } else if(mode==3) {
    // Keep the consumed-revision receipt and latest text across retirement.
    ba_editor_ready=false;lq_action_retire(&ba_action_slot);
  } else if(mode==6&&owner==ba_editor_owner)ba_editor_content=revision;
  else if(mode==4)post=true;
  else if(mode==2)post=owner&&owner==ba_editor_owner&&ba_editor_ready;
  pthread_mutex_unlock(&ba_mu);
  if(post)ba_editor_post(owner,mode==5?clear_revision:revision,
    handoff_text?handoff_text:text,handoff_text?handoff_size:length,mode);
  free(handoff_text);
  pthread_mutex_lock(&ba_mu);
  bool consumed=lq_action_consumed(&ba_action_slot,ba_editor_installed,ba_editor_revision);
  uint64_t logical=ba_editor_handoff?ba_editor_owner:ba_editor_installed;
  out[0]=1;out[1]=logical;out[2]=ba_editor_revision;out[3]=ba_editor_ready;
  out[4]=ba_action_slot.clearing?ba_action_slot.ticket:0;out[5]=ba_editor_exhausted;
  for(int i=0;i<4;i++)out[6+i]=ba_pos[i];
  out[10]=consumed;out[11]=ba_editor_installed;
  *size=mode==0&&owner==logical&&revision!=ba_editor_revision&&!consumed?ba_txt_n:0;
  char *value=lq_editor_copy(ba_txt?ba_txt:"",*size,1);
  pthread_mutex_unlock(&ba_mu);return value;
}

char *ba_editor_action(uint64_t ticket,uint32_t disposition,uint64_t out[8],uint32_t *count,size_t *size) {
  uint64_t owner=0,revision=0;char *value=NULL;
  pthread_mutex_lock(&ba_mu);*count=0;*size=0;
  if(!disposition&&ticket&&ba_action_slot.ticket==ticket&&!ba_action_slot.clearing) {
    *count=8;out[0]=ticket;out[1]=ba_action_slot.owner;out[2]=ba_action_slot.revision;out[3]=ba_action_slot.content;
    for(int i=0;i<4;i++)out[4+i]=ba_action_slot.pos[i];
    *size=ba_action_slot.length;value=lq_editor_copy(ba_action_slot.text,*size,2);
  } else if(disposition) {
    owner=ba_action_slot.owner;revision=ba_action_slot.revision;
    if(!lq_action_finish(&ba_action_slot,ticket,disposition))owner=0;
  }
  if(!*count&&ticket&&ba_action_slot.last_ticket==ticket) {
    *count=2;out[0]=ticket;out[1]=ba_action_slot.last_disposition;
  }
  pthread_mutex_unlock(&ba_mu);
  if(owner&&disposition!=3) {
    BaJava j=ba_target();
    if(j.activity&&ba_action_disposition_m) {
      (*j.env)->CallVoidMethod(j.env,j.activity,ba_action_disposition_m,(jlong)ticket,(jint)disposition);
      if((*j.env)->ExceptionCheck(j.env))(*j.env)->ExceptionClear(j.env);
    }
    ba_target_done(j);
  }
  if(owner&&disposition==3) {
    BaJava j=ba_target();
    if(j.activity&&ba_clear_action_m) {
      (*j.env)->CallVoidMethod(j.env,j.activity,ba_clear_action_m,(jlong)ticket,(jlong)owner,(jlong)revision);
      if((*j.env)->ExceptionCheck(j.env)) {
        (*j.env)->ExceptionClear(j.env);
        pthread_mutex_lock(&ba_mu);lq_action_clear_done(&ba_action_slot,ticket);pthread_mutex_unlock(&ba_mu);
      }
    } else {
      pthread_mutex_lock(&ba_mu);lq_action_clear_done(&ba_action_slot,ticket);pthread_mutex_unlock(&ba_mu);
    }
    ba_target_done(j);
  }
  return value;
}
