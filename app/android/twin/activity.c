// The Android activity for a Lean app
// ===================================

// A NativeActivity (no Java): its callbacks run on the UI thread; Lean's
// main (lean_app_main, Main.lean's, renamed by build_apk.sh) runs on a
// thread of its own, and its stdout and stderr go to logcat under the tag
// "lean". The
// surface and the first finger's touches cross to Lean's thread under
// one lock (activity.h). Lean's cwd is the app's internal data
// directory, where the APK's assets/ is copied first, so a relative
// path like assets/x.qoi reads as on the desktop. The process ends when Lean's main returns: the
// runtime's state is global, so a second run in one process is unsafe.

#include "activity.h"
#include "layer.h"
#include "scroll.h"

#include <android/asset_manager.h>
#include <android/log.h>
#include <android/native_activity.h>
#include <sys/system_properties.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

int lean_app_main(int argc, char** argv);

#define BA_CAP 4096

static pthread_mutex_t ba_mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t  ba_cv = PTHREAD_COND_INITIALIZER;
static ANativeWindow*  ba_win;
static int32_t         ba_w;
static int32_t         ba_h;
static bool            ba_closing;
static BaTouch         ba_q[BA_CAP];
static uint32_t        ba_n;
static int32_t         ba_finger = -1;
static bool            ba_started;
static bool            ba_scroll = true;
static bool            ba_slide = true;
static bool            ba_lead = true;

bool ba_ahead(void) {
  return ba_lead;
}
static BaTouch         ba_sq[BA_CAP];
static uint32_t        ba_sn;

bool ba_layer(void) {
  return ba_slide;
}

bool ba_native_scroll(void) {
  return ba_scroll;
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

// The surface's size is read here, before Lean sets its buffers' size:
// a touch is in surface pixels.
static void ba_window_created(ANativeActivity* act, ANativeWindow* win) {
  pthread_mutex_lock(&ba_mu);
  ba_win = win;
  ba_w   = ANativeWindow_getWidth(win);
  ba_h   = ANativeWindow_getHeight(win);
  pthread_cond_broadcast(&ba_cv);
  pthread_mutex_unlock(&ba_mu);
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

// A full queue (Lean not drawing) drops the touch, unless it is a down
// or an up: those replace the newest move, so a press is never lost.
static void ba_push(BaKind kind, float x, float y, int64_t t) {
  if (ba_n == BA_CAP) {
    if (kind == BA_MOVE || ba_q[ba_n - 1].kind != BA_MOVE) {
      return;
    }
    ba_n -= 1;
  }
  ba_q[ba_n++] = (BaTouch){ kind, x, y, t };
  if (ba_sn < BA_CAP) {
    ba_sq[ba_sn++] = (BaTouch){ kind, x, y, t };
  }
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
  int32_t act = AMotionEvent_getAction(ev);
  int32_t kind = act & AMOTION_EVENT_ACTION_MASK;
  int32_t at = (act & AMOTION_EVENT_ACTION_POINTER_INDEX_MASK)
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

// Keys stay unhandled, so Back finishes the activity (a Close).
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
    AAsset* a   = AAssetManager_open(act->assetManager, path,
      AASSET_MODE_STREAMING);
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
  // Frames slide (so the app draws them with overscan, Platform.slides)
  // when the OS scrolls and the slid layer is on.
  extern bool lc_slides_on;
  lc_slides_on = ba_scroll && ba_slide;
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

void ANativeActivity_onCreate(ANativeActivity* act, void* saved, size_t n) {
  act->callbacks->onNativeWindowCreated   = ba_window_created;
  act->callbacks->onNativeWindowDestroyed = ba_window_destroyed;
  act->callbacks->onInputQueueCreated     = ba_queue_created;
  act->callbacks->onInputQueueDestroyed   = ba_queue_destroyed;
  act->callbacks->onDestroy               = ba_destroy;
  if (ba_started) {
    return;
  }
  ba_started = true;
  bs_init(act->vm, act->clazz);
  char v[PROP_VALUE_MAX] = { 0 };
  ba_scroll = !(__system_property_get("debug.lean.scroll", v) > 0
    && strcmp(v, "app") == 0);
  ba_slide = !(__system_property_get("debug.lean.layer", v) > 0
    && strcmp(v, "0") == 0);
  ba_lead = !(__system_property_get("debug.lean.ahead", v) > 0
    && strcmp(v, "0") == 0);
  int fds[2];
  if (pipe(fds) == 0) {
    setvbuf(stdout, NULL, _IOLBF, 0);
    setvbuf(stderr, NULL, _IONBF, 0);
    dup2(fds[1], STDOUT_FILENO);
    dup2(fds[1], STDERR_FILENO);
    ba_spawn(ba_log, (void*)(intptr_t)fds[0], 64 << 10);
  }
  ba_files(act);
  ba_spawn(ba_run, NULL, 64 << 20);
}
