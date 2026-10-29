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
static int32_t         ba_density = 420;
static bool            ba_closing;
static bool            ba_resumed;
static char*           ba_links[32];
static unsigned        ba_nlinks;
static void ba_event(uint32_t k, uint32_t a, uint32_t b, uint32_t c);
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
static uint32_t        ba_pos[4];

static JavaVM*   ba_vm;
static jobject   ba_act;
static jmethodID ba_show_ime, ba_copy_text, ba_scan_m, ba_set_text_m;

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

int32_t ba_dpi(void) {
  return ba_density;
}

static void ba_window_created(ANativeActivity* act, ANativeWindow* win) {
  pthread_mutex_lock(&ba_mu);
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
  ba_win = NULL;
  ba_event(11, 0, 0, 0);
  bl_window_gone();
  pthread_mutex_unlock(&ba_mu);
}

static void ba_pause(ANativeActivity* act) {
  pthread_mutex_lock(&ba_mu);
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
  ba_resumed = true;
  ba_event(10, 0, 0, 0);
  pthread_cond_broadcast(&ba_cv);
  pthread_mutex_unlock(&ba_mu);
}

static void ba_destroy(ANativeActivity* act) {
  pthread_mutex_lock(&ba_mu);
  ba_closing = true;
  pthread_cond_broadcast(&ba_cv);
  pthread_mutex_unlock(&ba_mu);
}

// Events from the Java half
// -------------------------

static void ba_event(uint32_t k, uint32_t a, uint32_t b, uint32_t c) {
  if (ba_en == ba_ecap) {
    ba_ecap = ba_ecap ? ba_ecap * 2 : BA_EVS;
    ba_ev = realloc(ba_ev, ba_ecap * 4 * sizeof *ba_ev);
    if (!ba_ev) abort();
  }
  uint32_t* e = ba_ev + 4 * ba_en++;
  e[0] = k;
  e[1] = a;
  e[2] = b;
  e[3] = c;
}

uint32_t ba_drain_events(uint32_t* out, uint32_t max_words) {
  pthread_mutex_lock(&ba_mu);
  uint32_t n = ba_en * 4 < max_words ? ba_en * 4 : max_words - max_words % 4;
  memcpy(out, ba_ev, n * 4);
  memmove(ba_ev, ba_ev + n, (ba_en * 4 - n) * 4);
  ba_en -= n / 4;
  pthread_mutex_unlock(&ba_mu);
  return n;
}

char* ba_text(uint32_t pos[4]) {
  pthread_mutex_lock(&ba_mu);
  char* s = strdup(ba_txt != NULL ? ba_txt : "");
  memcpy(pos, ba_pos, sizeof ba_pos);
  pthread_mutex_unlock(&ba_mu);
  return s;
}

static void JNICALL ba_n_insets(JNIEnv* env, jclass cls, jint top, jint bottom, jint ime) {
  pthread_mutex_lock(&ba_mu);
  bool kb = ime != ba_kb;
  ba_top    = top;
  ba_bottom = bottom;
  ba_kb     = ime;
  if (kb) {
    ba_event(6, (uint32_t)ime, 0, 0);
  }
  pthread_mutex_unlock(&ba_mu);
}

// Java's modified UTF-8 is converted by the JVM; GetStringUTFChars gives
// modified UTF-8, which differs from UTF-8 for supplementary characters
// (emoji) and NUL, so the text is converted here from UTF-16 instead.
static char* ba_utf8(JNIEnv* env, jstring text) {
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
  return s;
}

static void JNICALL ba_n_text(JNIEnv* env, jclass cls, jstring text, jint ss, jint se,
  jint cs, jint ce) {
  char* s = ba_utf8(env, text);
  pthread_mutex_lock(&ba_mu);
  free(ba_txt);
  ba_txt    = s;
  ba_pos[0] = (uint32_t)ss;
  ba_pos[1] = (uint32_t)se;
  ba_pos[2] = (uint32_t)cs;
  ba_pos[3] = (uint32_t)ce;
  ba_event(4, 0, 0, 0);
  pthread_mutex_unlock(&ba_mu);
}

static void JNICALL ba_n_luma(JNIEnv* env, jclass cls, jobject buf, jint w, jint h, jint stride,
  jint orient) {
  const uint8_t* y = (*env)->GetDirectBufferAddress(env, buf);
  jlong          n = (*env)->GetDirectBufferCapacity(env, buf);
  if (y == NULL || n <= 0 || w <= 0 || h <= 0 || stride <= 0) {
    return;
  }
  pthread_mutex_lock(&ba_mu);
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

static void JNICALL ba_n_action(JNIEnv* env, jclass cls, jint kind, jint code, jint action) {
  pthread_mutex_lock(&ba_mu);
  ba_event(kind, code, action, 0);
  pthread_mutex_unlock(&ba_mu);
}

// Calls into the Java half, from any thread (they post to the UI thread).
// A thread attached here stays attached (Lean's thread is, for scroll.c).
static void ba_call(jmethodID m, bool arg) {
  if (ba_vm == NULL || ba_act == NULL || m == NULL) {
    return;
  }
  JNIEnv* env;
  if ((*ba_vm)->GetEnv(ba_vm, (void**)&env, JNI_VERSION_1_6) != JNI_OK
    && (*ba_vm)->AttachCurrentThread(ba_vm, &env, NULL) != JNI_OK) {
    return;
  }
  if (m == ba_show_ime) {
    (*env)->CallVoidMethod(env, ba_act, m, (jboolean)arg);
  } else {
    (*env)->CallVoidMethod(env, ba_act, m);
  }
  if ((*env)->ExceptionCheck(env)) {
    (*env)->ExceptionDescribe(env);
    (*env)->ExceptionClear(env);
  }
}

void ba_ime(bool show) {
  ba_call(ba_show_ime, show);
}


void ba_scan(bool on) {
  pthread_mutex_lock(&ba_mu);
  ba_camera_wanted = on;
  free(ba_luma); ba_luma = NULL; ba_luma_n = 0;
  pthread_mutex_unlock(&ba_mu);
  if (ba_vm == NULL || ba_act == NULL || ba_scan_m == NULL) {
    return;
  }
  JNIEnv* env;
  if ((*ba_vm)->GetEnv(ba_vm, (void**)&env, JNI_VERSION_1_6) != JNI_OK
    && (*ba_vm)->AttachCurrentThread(ba_vm, &env, NULL) != JNI_OK) {
    return;
  }
  (*env)->CallVoidMethod(env, ba_act, ba_scan_m, (jboolean)on);
  if ((*env)->ExceptionCheck(env)) {
    (*env)->ExceptionDescribe(env);
    (*env)->ExceptionClear(env);
  }
}

void ba_copy(const char* utf8) {
  if (ba_vm == NULL || ba_act == NULL || ba_copy_text == NULL) {
    return;
  }
  JNIEnv* env;
  if ((*ba_vm)->GetEnv(ba_vm, (void**)&env, JNI_VERSION_1_6) != JNI_OK
    && (*ba_vm)->AttachCurrentThread(ba_vm, &env, NULL) != JNI_OK) {
    return;
  }
  jstring s = (*env)->NewStringUTF(env, utf8);
  (*env)->CallVoidMethod(env, ba_act, ba_copy_text, s);
  (*env)->DeleteLocalRef(env, s);
  if ((*env)->ExceptionCheck(env)) {
    (*env)->ExceptionDescribe(env);
    (*env)->ExceptionClear(env);
  }
}

void ba_set_text(const char* utf8) {
  if (ba_vm == NULL || ba_act == NULL || ba_set_text_m == NULL) {
    return;
  }
  JNIEnv* env;
  if ((*ba_vm)->GetEnv(ba_vm, (void**)&env, JNI_VERSION_1_6) != JNI_OK
    && (*ba_vm)->AttachCurrentThread(ba_vm, &env, NULL) != JNI_OK) {
    return;
  }
  jstring s = (*env)->NewStringUTF(env, utf8);
  (*env)->CallVoidMethod(env, ba_act, ba_set_text_m, s);
  (*env)->DeleteLocalRef(env, s);
  if ((*env)->ExceptionCheck(env)) {
    (*env)->ExceptionDescribe(env);
    (*env)->ExceptionClear(env);
  }
}

// URL delivery is independent of the debug control socket.
static void JNICALL ba_n_link(JNIEnv* env, jclass cls, jstring text) {
  char* url = ba_utf8(env, text);
  pthread_mutex_lock(&ba_mu);
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

static void ba_java(ANativeActivity* act) {
  JNIEnv* env = act->env;
  jclass  cls = (*env)->GetObjectClass(env, act->clazz);
  JNINativeMethod ms[] = {
    { "nInsets", "(III)V", (void*)ba_n_insets },
    { "nText", "(Ljava/lang/String;IIII)V", (void*)ba_n_text },
    { "nLink", "(Ljava/lang/String;)V", (void*)ba_n_link },
    { "nAction", "(III)V", (void*)ba_n_action },
    { "nLuma", "(Ljava/nio/ByteBuffer;IIII)V", (void*)ba_n_luma },
  };
  if ((*env)->RegisterNatives(env, cls, ms, 5) != 0) {
    (*env)->ExceptionClear(env);
    __android_log_write(ANDROID_LOG_ERROR, "lean", "cannot register the Java half's natives");
    return;
  }
  if (ba_act != NULL) {
    (*env)->DeleteGlobalRef(env, ba_act);
  }
  ba_vm         = act->vm;
  ba_act        = (*env)->NewGlobalRef(env, act->clazz);
  ba_show_ime   = (*env)->GetMethodID(env, cls, "showIme", "(Z)V");
  ba_copy_text  = (*env)->GetMethodID(env, cls, "copyText", "(Ljava/lang/String;)V");
  ba_set_text_m = (*env)->GetMethodID(env, cls, "setText", "(Ljava/lang/String;)V");
  ba_scan_m     = (*env)->GetMethodID(env, cls, "scan", "(Z)V");
  if ((*env)->ExceptionCheck(env)) {
    (*env)->ExceptionClear(env);
    ba_show_ime = ba_copy_text = ba_scan_m = ba_set_text_m = NULL;
  }
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
static void ba_push(BaKind kind, int32_t id, float x, float y, int64_t t) {
  if (ba_n == ba_cap) {
    ba_cap = ba_cap ? ba_cap * 2 : BA_CAP;
    ba_q = realloc(ba_q, ba_cap * sizeof *ba_q);
    if (!ba_q) abort();
  }
  ba_q[ba_n++] = (BaTouch){ kind, x, y, t, id, bl_view_id() };
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
  exit(code);
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
