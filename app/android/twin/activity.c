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
static int32_t         ba_vtop, ba_vbot = 1 << 30;
static bool            ba_closing;
static BaTouch         ba_q[BA_CAP];
static uint32_t        ba_n;
static BaTouch         ba_sq[BA_CAP];
static uint32_t        ba_sn;
static bool            ba_scrolls;  // the held finger began in the viewport
static int32_t         ba_finger = -1;
static bool            ba_started;
static bool            ba_lead = true;
static uint32_t        ba_ev[BA_EVS * 4];
static uint32_t        ba_en;
static char*           ba_txt;
static uint32_t        ba_pos[4];

static JavaVM*   ba_vm;
static jobject   ba_act;
static jmethodID ba_show_ime, ba_clear_text;

bool ba_ahead(void) {
  return ba_lead;
}

// Surface
// -------

ANativeWindow* ba_lock(int32_t* w, int32_t* h) {
  pthread_mutex_lock(&ba_mu);
  while (ba_win == NULL && !ba_closing) {
    pthread_cond_wait(&ba_cv, &ba_mu);
  }
  if (ba_closing) {
    pthread_mutex_unlock(&ba_mu);
    return NULL;
  }
  *w = ba_w;
  *h = ba_h;
  return ba_win;
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
  pthread_cond_broadcast(&ba_cv);
  pthread_mutex_unlock(&ba_mu);
}

static void ba_window_resized(ANativeActivity* act, ANativeWindow* win) {
  ba_window_created(act, win);
}

// Returns only once Lean's thread is not drawing to the surface.
static void ba_window_destroyed(ANativeActivity* act, ANativeWindow* win) {
  bl_window_gone();
  pthread_mutex_lock(&ba_mu);
  ba_win = NULL;
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
  if (ba_en == BA_EVS) {
    return;
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

static void JNICALL ba_n_send(JNIEnv* env, jclass cls) {
  pthread_mutex_lock(&ba_mu);
  ba_event(5, 0, 0, 0);
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

void ba_text_clear(void) {
  ba_call(ba_clear_text, false);
}

static void ba_java(ANativeActivity* act) {
  JNIEnv* env = act->env;
  jclass  cls = (*env)->GetObjectClass(env, act->clazz);
  JNINativeMethod ms[] = {
    { "nInsets", "(III)V", (void*)ba_n_insets },
    { "nText", "(Ljava/lang/String;IIII)V", (void*)ba_n_text },
    { "nSend", "()V", (void*)ba_n_send },
  };
  if ((*env)->RegisterNatives(env, cls, ms, 3) != 0) {
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
  ba_clear_text = (*env)->GetMethodID(env, cls, "clearText", "()V");
  if ((*env)->ExceptionCheck(env)) {
    (*env)->ExceptionClear(env);
    ba_show_ime = ba_clear_text = NULL;
  }
}

// Touches
// -------

void ba_set_viewport(int32_t top, int32_t bot) {
  pthread_mutex_lock(&ba_mu);
  ba_vtop = top;
  ba_vbot = bot;
  pthread_mutex_unlock(&ba_mu);
}

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

// A full queue (Lean not drawing) drops the touch, unless it is a down
// or an up: those replace the newest move, so a press is never lost.
// Only a finger that went down in the list's viewport feeds the scroller.
static void ba_push(BaKind kind, float x, float y, int64_t t) {
  if (kind == BA_DOWN) {
    ba_scrolls = y >= (float)ba_vtop && y < (float)ba_vbot;
  }
  if (ba_scrolls && ba_sn < BA_CAP) {
    ba_sq[ba_sn++] = (BaTouch){ kind, x, y, t };
  }
  if (ba_n == BA_CAP) {
    if (kind == BA_MOVE || ba_q[ba_n - 1].kind != BA_MOVE) {
      return;
    }
    ba_n -= 1;
  }
  ba_q[ba_n++] = (BaTouch){ kind, x, y, t };
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

static int32_t ba_index(const AInputEvent* ev, int32_t id) {
  size_t n = AMotionEvent_getPointerCount(ev);
  for (size_t i = 0; i < n; i += 1) {
    if (AMotionEvent_getPointerId(ev, i) == id) {
      return (int32_t)i;
    }
  }
  return -1;
}

// Only the first finger down counts, until it lifts; a move brings its
// batched history too, so a drag keeps every sample.
static void ba_motion(const AInputEvent* ev) {
  int32_t act  = AMotionEvent_getAction(ev);
  int32_t kind = act & AMOTION_EVENT_ACTION_MASK;
  int32_t at   = (act & AMOTION_EVENT_ACTION_POINTER_INDEX_MASK)
    >> AMOTION_EVENT_ACTION_POINTER_INDEX_SHIFT;
  pthread_mutex_lock(&ba_mu);
  int32_t i = ba_finger < 0 ? -1 : ba_index(ev, ba_finger);
  if (kind == AMOTION_EVENT_ACTION_DOWN) {
    ba_finger = AMotionEvent_getPointerId(ev, 0);
    ba_push(BA_DOWN, AMotionEvent_getX(ev, 0), AMotionEvent_getY(ev, 0),
      AMotionEvent_getEventTime(ev));
  } else if (kind == AMOTION_EVENT_ACTION_MOVE && i >= 0) {
    size_t n = AMotionEvent_getHistorySize(ev);
    for (size_t h = 0; h < n; h += 1) {
      ba_push(BA_MOVE, AMotionEvent_getHistoricalX(ev, i, h),
        AMotionEvent_getHistoricalY(ev, i, h),
        AMotionEvent_getHistoricalEventTime(ev, h));
    }
    ba_push(BA_MOVE, AMotionEvent_getX(ev, i), AMotionEvent_getY(ev, i),
      AMotionEvent_getEventTime(ev));
  } else if (i >= 0 && (kind == AMOTION_EVENT_ACTION_UP
    || kind == AMOTION_EVENT_ACTION_CANCEL
    || (kind == AMOTION_EVENT_ACTION_POINTER_UP && at == i))) {
    ba_push(BA_UP, AMotionEvent_getX(ev, i), AMotionEvent_getY(ev, i),
      AMotionEvent_getEventTime(ev));
    ba_finger = -1;
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

// Copies the APK's assets/assets/* (one level) to <dir>/assets/ and
// makes dir the cwd. Returns false (logged) on any failure.
static bool ba_files(ANativeActivity* act) {
  const char* dir = act->internalDataPath;
  if (dir == NULL || chdir(dir) != 0) {
    __android_log_print(ANDROID_LOG_ERROR, "lean", "cannot enter %s", dir);
    return false;
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
  lq_ctl_start();
  ba_spawn(ba_run, NULL, 256 << 20);
}
