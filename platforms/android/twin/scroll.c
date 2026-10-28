// Native scrolling for a Lean app on Android
// =========================================

// Platform.scroll's Android answer: Android's own scroll physics, driven
// through JNI on the vsync thread (layer.c), from the touches' own queue
// (ba_drain_scroll: fingers that went down in the list's viewport). The
// first finger's samples feed a VelocityTracker as MotionEvents; past the
// touch slop the offset follows the finger 1:1; a release flings an
// OverScroller with the tracker's velocity, and each vsync reads the
// scroller's offset. While the finger is down the offset follows it
// resampled to BS_LAG before the vsync (interpolated between the samples
// around that time, or extrapolated past the newest by at most half their
// spacing and BS_REACH), as Android's own views see touches. Every
// constant (slop, fling velocities, overfling) is the device's
// ViewConfiguration, so a fling feels like any Android list.
//
// The offset is bottom-anchored (Platform.lean): the distance from the
// content's end to the viewport's bottom. A finger moving down shows
// older content, so it raises the offset: the OverScroller runs on that
// axis directly (its 0 is the newest end), and the range's top end moves
// as content is measured without disturbing what is on screen.

#include "scroll.h"

#include <android/log.h>
#include <jni.h>
#include <math.h>
#include <pthread.h>
#include <stdbool.h>
#include <string.h>
#include <sys/system_properties.h>

static JavaVM*   bs_vm;
static jobject   bs_ctx;
static JNIEnv*   bs_env;
static jobject   bs_scroller;
static jobject   bs_tracker;
static jclass    bs_event;
static jmethodID bs_obtain, bs_recycle, bs_add, bs_clear, bs_compute, bs_vy;
static jmethodID bs_fling, bs_finish, bs_step, bs_cury, bs_finy, bs_vel;
static float     bs_slop, bs_vmin, bs_vmax, bs_over;
static bool      bs_ready;

#define BS_LAG   5000000
#define BS_REACH 8000000
#define BS_HIST  8

static int64_t bs_ht[BS_HIST];
static float   bs_hy[BS_HIST];
static int     bs_hn;

static bool  bs_down, bs_drag, bs_flinging;
static bool  bs_resample = true;  // debug.lean.resample=0: the raw newest
static float bs_final;
static float bs_y0, bs_off0, bs_off;
static float bs_max;
static jlong bs_t0;

static pthread_mutex_t bs_mu = PTHREAD_MUTEX_INITIALIZER;
static float           bs_pend_by;
static bool            bs_pend_to;
static float           bs_pend_b;

void bs_init(JavaVM* vm, jobject activity) {
  bs_vm = vm;
  JNIEnv* env;
  if ((*vm)->GetEnv(vm, (void**)&env, JNI_VERSION_1_6) != JNI_OK) {
    return;
  }
  bs_ctx = (*env)->NewGlobalRef(env, activity);
}

// JNI on the vsync thread, set up at its first use.
static bool bs_setup(void) {
  if (bs_ready || bs_vm == NULL) {
    return bs_ready;
  }
  if ((*bs_vm)->AttachCurrentThread(bs_vm, &bs_env, NULL) != JNI_OK) {
    return false;
  }
  JNIEnv* e  = bs_env;
  jclass  vc = (*e)->FindClass(e, "android/view/ViewConfiguration");
  jobject c  = (*e)->CallStaticObjectMethod(e, vc, (*e)->GetStaticMethodID(e, vc,
    "get", "(Landroid/content/Context;)Landroid/view/ViewConfiguration;"), bs_ctx);
  bs_slop = (*e)->CallIntMethod(e, c, (*e)->GetMethodID(e, vc, "getScaledTouchSlop", "()I"));
  bs_vmin = (*e)->CallIntMethod(e, c, (*e)->GetMethodID(e, vc,
    "getScaledMinimumFlingVelocity", "()I"));
  bs_vmax = (*e)->CallIntMethod(e, c, (*e)->GetMethodID(e, vc,
    "getScaledMaximumFlingVelocity", "()I"));
  bs_over = (*e)->CallIntMethod(e, c, (*e)->GetMethodID(e, vc,
    "getScaledOverflingDistance", "()I"));
  jclass os = (*e)->FindClass(e, "android/widget/OverScroller");
  bs_scroller = (*e)->NewGlobalRef(e, (*e)->NewObject(e, os,
    (*e)->GetMethodID(e, os, "<init>", "(Landroid/content/Context;)V"), bs_ctx));
  bs_fling  = (*e)->GetMethodID(e, os, "fling", "(IIIIIIIIII)V");
  bs_finish = (*e)->GetMethodID(e, os, "forceFinished", "(Z)V");
  bs_step   = (*e)->GetMethodID(e, os, "computeScrollOffset", "()Z");
  bs_cury   = (*e)->GetMethodID(e, os, "getCurrY", "()I");
  bs_finy   = (*e)->GetMethodID(e, os, "getFinalY", "()I");
  bs_vel    = (*e)->GetMethodID(e, os, "getCurrVelocity", "()F");
  jclass vt  = (*e)->FindClass(e, "android/view/VelocityTracker");
  bs_tracker = (*e)->NewGlobalRef(e, (*e)->CallStaticObjectMethod(e, vt,
    (*e)->GetStaticMethodID(e, vt, "obtain", "()Landroid/view/VelocityTracker;")));
  bs_add     = (*e)->GetMethodID(e, vt, "addMovement", "(Landroid/view/MotionEvent;)V");
  bs_clear   = (*e)->GetMethodID(e, vt, "clear", "()V");
  bs_compute = (*e)->GetMethodID(e, vt, "computeCurrentVelocity", "(IF)V");
  bs_vy      = (*e)->GetMethodID(e, vt, "getYVelocity", "()F");
  bs_event   = (*e)->NewGlobalRef(e, (*e)->FindClass(e, "android/view/MotionEvent"));
  bs_obtain  = (*e)->GetStaticMethodID(e, bs_event, "obtain",
    "(JJIFFI)Landroid/view/MotionEvent;");
  bs_recycle = (*e)->GetMethodID(e, bs_event, "recycle", "()V");
  if ((*e)->ExceptionCheck(e)) {
    (*e)->ExceptionDescribe(e);
    (*e)->ExceptionClear(e);
    __android_log_write(ANDROID_LOG_ERROR, "lean", "native scroll: JNI setup failed");
    return false;
  }
  __android_log_print(ANDROID_LOG_INFO, "lean",
    "native scroll: slop %.0f, fling %.0f..%.0f px/s, overfling %.0f",
    bs_slop, bs_vmin, bs_vmax, bs_over);
  char v[PROP_VALUE_MAX] = { 0 };
  bs_resample = !(__system_property_get("debug.lean.resample", v) > 0 && v[0] == '0');
  bs_ready = true;
  return true;
}

static void bs_track(int action, float y, int64_t t) {
  JNIEnv* e  = bs_env;
  jlong   ms = (jlong)(t / 1000000);
  jobject ev = (*e)->CallStaticObjectMethod(e, bs_event, bs_obtain, bs_t0, ms, action, 0.0f, y, 0);
  (*e)->CallVoidMethod(e, bs_tracker, bs_add, ev);
  (*e)->CallVoidMethod(e, ev, bs_recycle);
  (*e)->DeleteLocalRef(e, ev);
}

static float bs_clamp(float v) {
  return v < 0 ? 0 : v > bs_max ? bs_max : v;
}

static void bs_hold(float y, int64_t t) {
  if (bs_hn == BS_HIST) {
    memmove(bs_ht, bs_ht + 1, (BS_HIST - 1) * sizeof *bs_ht);
    memmove(bs_hy, bs_hy + 1, (BS_HIST - 1) * sizeof *bs_hy);
    bs_hn -= 1;
  }
  bs_ht[bs_hn] = t;
  bs_hy[bs_hn] = y;
  bs_hn += 1;
}

// The finger's y at t, from its last samples (bs_hn >= 1).
static float bs_at(int64_t t) {
  int n = bs_hn, i = n - 1;
  while (i > 0 && bs_ht[i - 1] >= t) {
    i -= 1;
  }
  int a = i > 0 ? i - 1 : 0, b = i;
  if (i == n - 1 && n > 1 && t > bs_ht[b]) {
    a = n - 2;
    int64_t gap  = bs_ht[b] - bs_ht[a];
    int64_t most = gap / 2 < BS_REACH ? gap / 2 : BS_REACH;
    t = bs_ht[b] + (t - bs_ht[b] < most ? t - bs_ht[b] : most);
  }
  float f = bs_ht[b] > bs_ht[a] ? (float)(t - bs_ht[a]) / (float)(bs_ht[b] - bs_ht[a]) : 1;
  f = f < 0 ? 0 : f;
  return bs_hy[a] + (bs_hy[b] - bs_hy[a]) * f;
}

static void bs_fling_from(float off, float v) {
  JNIEnv* e = bs_env;
  (*e)->CallVoidMethod(e, bs_scroller, bs_fling, 0, (jint)lroundf(off), 0, (jint)lroundf(v),
    0, 0, 0, (jint)lroundf(bs_max), 0, (jint)lroundf(bs_over));
}

static void bs_touch(BaKind kind, float y, int64_t t) {
  JNIEnv* e = bs_env;
  if (kind == BA_DOWN) {
    (*e)->CallVoidMethod(e, bs_scroller, bs_finish, JNI_TRUE);
    (*e)->CallVoidMethod(e, bs_tracker, bs_clear);
    bs_t0       = (jlong)(t / 1000000);
    bs_down     = true;
    bs_drag     = false;
    bs_flinging = false;
    bs_y0       = y;
    bs_off0     = bs_off;
    bs_hn       = 0;
    bs_hold(y, t);
    bs_track(0, y, t);
    return;
  }
  if (!bs_down) {
    return;
  }
  bs_track(kind == BA_UP ? 1 : 2, y, t);
  bs_hold(y, t);
  if (!bs_drag && fabsf(y - bs_y0) > bs_slop) {
    bs_drag = true;
    bs_y0   = y;
  }
  if (kind == BA_UP) {
    if (bs_drag) {
      bs_off = bs_clamp(bs_off0 + (y - bs_y0));  // where it lifted
    }
    bs_down = false;
    (*e)->CallVoidMethod(e, bs_tracker, bs_compute, 1000, bs_vmax);
    float vy = (*e)->CallFloatMethod(e, bs_tracker, bs_vy);
    if (bs_drag && fabsf(vy) >= bs_vmin) {
      bs_fling_from(bs_off, vy);  // a finger moving down (vy > 0) raises the offset
    }
    bs_drag = false;
  }
}

void bs_by(float d) {
  pthread_mutex_lock(&bs_mu);
  bs_pend_by += d;
  pthread_mutex_unlock(&bs_mu);
}

void bs_to(float b) {
  pthread_mutex_lock(&bs_mu);
  bs_pend_to = true;
  bs_pend_b  = b;
  bs_pend_by = 0;
  pthread_mutex_unlock(&bs_mu);
}

// A pending move or jump: a move shifts the offset (and the drag's anchor,
// so the finger keeps its place on the content) and re-flings a running
// fling from the shifted place with its current velocity; a jump stops it.
static void bs_pending(void) {
  pthread_mutex_lock(&bs_mu);
  float by = bs_pend_by;
  bool  to = bs_pend_to;
  float b  = bs_pend_b;
  bs_pend_by = 0;
  bs_pend_to = false;
  pthread_mutex_unlock(&bs_mu);
  JNIEnv* e = bs_env;
  if (to) {
    (*e)->CallVoidMethod(e, bs_scroller, bs_finish, JNI_TRUE);
    bs_flinging = false;
    bs_off      = bs_clamp(b);
    bs_off0     = bs_off;
    if (bs_down) {
      bs_y0 = bs_hn > 0 ? bs_hy[bs_hn - 1] : bs_y0;
    }
  }
  if (by != 0) {
    bs_off  += by;
    bs_off0 += by;
    if (!bs_down && (*e)->CallBooleanMethod(e, bs_scroller, bs_step)) {
      float cur = (float)(*e)->CallIntMethod(e, bs_scroller, bs_cury);
      float fin = (float)(*e)->CallIntMethod(e, bs_scroller, bs_finy);
      float v   = (*e)->CallFloatMethod(e, bs_scroller, bs_vel);
      (*e)->CallVoidMethod(e, bs_scroller, bs_finish, JNI_TRUE);
      bs_fling_from(cur + by, fin >= cur ? v : -v);
    } else {
      bs_off = bs_clamp(bs_off);
    }
  }
}

bool bs_vsync(uint32_t content_h, uint32_t view_h, int64_t ns, uint32_t* y, float* yf) {
  if (!bs_setup()) {
    return false;
  }
  bs_max = content_h > view_h ? (float)(content_h - view_h) : 0;
  BaTouch  ts[256];
  uint32_t n;
  do {
    n = ba_drain_scroll(ts, 256);
    for (uint32_t i = 0; i < n; i += 1) {
      bs_touch(ts[i].kind, ts[i].y, ts[i].t);
    }
  } while (n == 256);
  bs_pending();
  JNIEnv* e = bs_env;
  if (bs_down && bs_drag && bs_hn > 0) {
    float fy = bs_resample ? bs_at(ns - BS_LAG) : bs_hy[bs_hn - 1];
    bs_off = bs_clamp(bs_off0 + (fy - bs_y0));
  }
  bs_flinging = !bs_down && (*e)->CallBooleanMethod(e, bs_scroller, bs_step);
  if (bs_flinging) {
    bs_off   = (float)(*e)->CallIntMethod(e, bs_scroller, bs_cury);
    bs_final = (float)(*e)->CallIntMethod(e, bs_scroller, bs_finy);
  } else if (!bs_down && bs_off > bs_max) {
    bs_off = bs_max;  // the content shrank, or the keyboard opened
  }
  *yf = bs_off < 0 ? 0 : bs_off;
  *y  = (uint32_t)lroundf(*yf);
  return true;
}

bool bs_target(uint32_t* y) {
  if (!bs_flinging) {
    return false;
  }
  *y = (uint32_t)lroundf(bs_final < 0 ? 0 : bs_final);
  return true;
}

bool bs_active(void) {
  return bs_down || bs_flinging;
}
