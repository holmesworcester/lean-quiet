// Host substitutes for Android's buffer/transaction APIs. Tests include
// the actual layer.c; only allocation, copying and compositor calls are fake.
#include <assert.h>
#include <stdlib.h>
#include <string.h>

struct ANativeWindow { int unused; };
typedef struct { int32_t left, top, right, bottom; } ARect;
typedef struct { uint32_t width, height, layers, format; uint64_t usage; uint32_t stride, rfu0; uint64_t rfu1; } AHardwareBuffer_Desc;
typedef struct { AHardwareBuffer_Desc desc; uint32_t* pixels; } AHardwareBuffer;
typedef struct { int index; } ASurfaceControl;
typedef struct { int unused; } ASurfaceTransactionStats;
typedef void (*StubDone)(void*, ASurfaceTransactionStats*);
typedef struct {
  AHardwareBuffer* buffer[4];
  ARect source[4], destination[4];
  bool geometry[4];
  int visibility[4];
  int count;
  StubDone done[4];
  void* context[4];
} ASurfaceTransaction;
static AHardwareBuffer* stub_buffer[4];
static ARect stub_source[4], stub_destination[4];
static int stub_z[4];
static int stub_visible[4];
static ASurfaceTransaction stub_finished[32];
static int stub_n, stub_controls;
static bool stub_lock_fails;

enum { AHARDWAREBUFFER_FORMAT_R8G8B8X8_UNORM, AHARDWAREBUFFER_USAGE_CPU_WRITE_OFTEN = 1,
  AHARDWAREBUFFER_USAGE_GPU_SAMPLED_IMAGE = 2, AHARDWAREBUFFER_USAGE_COMPOSER_OVERLAY = 4,
  ASURFACE_TRANSACTION_VISIBILITY_HIDE, ASURFACE_TRANSACTION_VISIBILITY_SHOW, ANDROID_LOG_ERROR };
static int AHardwareBuffer_allocate(const AHardwareBuffer_Desc* d, AHardwareBuffer** b) {
  *b = calloc(1, sizeof **b); (*b)->desc = *d; (*b)->desc.stride = d->width;
  (*b)->pixels = calloc(d->width * d->height, 4); return 0;
}
static void AHardwareBuffer_release(AHardwareBuffer* b) { free(b->pixels); free(b); }
static void AHardwareBuffer_describe(AHardwareBuffer* b, AHardwareBuffer_Desc* d) { *d = b->desc; }
static int AHardwareBuffer_lock(AHardwareBuffer* b, uint64_t usage, int fence, const ARect* r, void** p) {
  if (stub_lock_fails) return -1;
  *p = b->pixels; return 0;
}
static void AHardwareBuffer_unlock(AHardwareBuffer* b, int32_t* fence) { *fence = -1; }
static ASurfaceControl* ASurfaceControl_createFromWindow(ANativeWindow* w, const char* name) {
  ASurfaceControl* c = malloc(sizeof *c); c->index = stub_controls++ % 4; return c;
}
static void ASurfaceControl_release(ASurfaceControl* c) { free(c); }
static ASurfaceTransaction* ASurfaceTransaction_create(void) { return calloc(1, sizeof(ASurfaceTransaction)); }
static void ASurfaceTransaction_delete(ASurfaceTransaction* t) { free(t); }
static void ASurfaceTransaction_setGeometry(ASurfaceTransaction* t, ASurfaceControl* c,
    const ARect* src, const ARect* dst, int transform) {
  t->source[c->index] = *src; t->destination[c->index] = *dst; t->geometry[c->index] = true;
}
static void ASurfaceTransaction_setBuffer(ASurfaceTransaction* t, ASurfaceControl* c, AHardwareBuffer* b, int fence) {
  t->buffer[c->index] = b;
}
static void ASurfaceTransaction_setOnComplete(ASurfaceTransaction* t, void* ctx, StubDone done) {
  assert(t->count < 4); t->context[t->count] = ctx; t->done[t->count++] = done;
}
static void ASurfaceTransaction_apply(ASurfaceTransaction* t) {
  for (int i = 0; i < 4; i++) {
    if (t->buffer[i]) stub_buffer[i] = t->buffer[i];
    if (t->geometry[i]) { stub_source[i] = t->source[i]; stub_destination[i] = t->destination[i]; }
    if (t->visibility[i]) stub_visible[i] = t->visibility[i];
  }
  assert(stub_n < 32); stub_finished[stub_n++] = *t;
}
static void stub_complete_at(int index) {
  assert(index >= 0 && index < stub_n);
  ASurfaceTransaction t = stub_finished[index];
  memmove(stub_finished + index, stub_finished + index + 1,
    (size_t)(--stub_n - index) * sizeof stub_finished[0]);
  ASurfaceTransactionStats stats;
  for (int i = 0; i < t.count; i++) t.done[i](t.context[i], &stats);
}
static void stub_complete(void) {
  while (stub_n) stub_complete_at(0);
}
static int ASurfaceTransactionStats_getPreviousReleaseFenceFd(ASurfaceTransactionStats* s, ASurfaceControl* c) { return -1; }
static void ASurfaceTransaction_setVisibility(ASurfaceTransaction* t, ASurfaceControl* c, int v) {
  t->visibility[c->index] = v == ASURFACE_TRANSACTION_VISIBILITY_SHOW ? 1 : -1;
}
static void ASurfaceTransaction_setZOrder(ASurfaceTransaction* t, ASurfaceControl* c, int z) { stub_z[c->index] = z; }
static void ASurfaceTransaction_reparent(ASurfaceTransaction* t, ASurfaceControl* c, ASurfaceControl* p) {}
typedef void (*AChoreographer_frameCallback64)(int64_t, void*);
static void* AChoreographer_getInstance(void) { return NULL; }
static void AChoreographer_postFrameCallback64(void* c, AChoreographer_frameCallback64 cb, void* data) {}
static void ALooper_prepare(int opts) {}
static void ALooper_pollOnce(int ms, int* fd, int* evs, void** data) {}
static int __android_log_print(int level, const char* tag, const char* fmt, ...) { return 0; }
static float stub_offset;
static bool stub_sample;
static bool bs_vsync(uint32_t content, uint32_t view, int64_t ns, uint32_t* y, float* yf) { *yf = stub_offset; *y = stub_offset; return stub_sample; }
