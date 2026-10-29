// Exercise the actual exports without linking Lean's runtime. A boxed
// operation or once-cell would prevent this executable from linking.
#include "../../platforms/native/translate.h"
#include <assert.h>
#include <pthread.h>
#include <stdio.h>

static _Thread_local unsigned warm_calls[4];
static uint32_t warm_edge(uint8_t f, uint8_t w, uint8_t p, uint32_t b, uint32_t o,
    uint32_t h, uint32_t t, uint32_t z, uint32_t s) {
  warm_calls[0]++; return lq_slide_edge(f, w, p, b, o, h, t, z, s);
}
static uint32_t warm_delta(uint8_t p, uint32_t b, uint32_t s) {
  warm_calls[1]++; return lq_slide_delta(p, b, s);
}
static uint64_t warm_source(uint8_t p, uint32_t b, uint32_t o, uint32_t h, uint32_t s, uint32_t y) {
  warm_calls[2]++; return lq_slide_source(p, b, o, h, s, y);
}
static uint32_t warm_fill(uint8_t p, uint32_t b, uint32_t t, uint32_t z, uint32_t s, uint32_t y) {
  warm_calls[3]++; return lq_slide_fill_row(p, b, t, z, s, y);
}
#define lq_slide_edge warm_edge
#define lq_slide_delta warm_delta
#define lq_slide_source warm_source
#define lq_slide_fill_row warm_fill
#include "../../platforms/native/thread.h"
#undef lq_slide_edge
#undef lq_slide_delta
#undef lq_slide_source
#undef lq_slide_fill_row

static _Thread_local unsigned init_calls;
static _Thread_local uint64_t checks;
void lean_initialize_thread(void) { init_calls++; }
static int64_t low(int64_t a, int64_t b) { return a < b ? a : b; }
static int64_t high(int64_t a, int64_t b) { return a > b ? a : b; }
static int64_t signed32(uint32_t x) { return x < 0x80000000u ? x : (int64_t)x - 4294967296LL; }
static int64_t fill_origin(int pin, uint32_t base, uint32_t top, uint32_t bottom, uint32_t sample) {
  int64_t p = (pin ? (int64_t)base : signed32(sample)) + bottom - top;
  return (int64_t)top - 48 + (p % 48 + 48) % 48;
}
static void equal(uint64_t actual, uint64_t expected) {
  if (actual != expected) {
    fprintf(stderr, "FAIL scalar: check %llu: %llu != %llu\n",
      (unsigned long long)checks, (unsigned long long)actual, (unsigned long long)expected);
    assert(actual == expected);
  }
  checks++;
}
static void one(uint32_t base, uint32_t origin, uint32_t height, uint32_t top,
    uint32_t bottom, uint32_t sample) {
  for (int pin = 0; pin < 2; pin++) {
    int64_t p = signed32(origin) + (pin ? 0 : signed32(sample) - base);
    for (int fill = 0; fill < 2; fill++) {
      int64_t pos = fill ? fill_origin(pin, base, top, bottom, sample) : p;
      int64_t h = fill ? high((int64_t)bottom - top, 0) + 48 : height;
      int64_t a = low(h, high((int64_t)top - pos, 0));
      int64_t z = high(a, low(h, high((int64_t)bottom - pos, 0)));
      uint32_t r[4] = {a, z, high(pos + a, 0), high(pos + z, 0)};
      for (int k = 0; k < 5; k++)
        equal(lq_slide_edge(fill, k == 4 ? 255 : k, pin, base, origin, height, top, bottom, sample), r[k < 4 ? k : 3]);
    }
    equal(lq_slide_delta(pin, base, sample), (uint32_t)(pin ? 0 : signed32(sample) - base));
    uint32_t ys[] = {0, top, bottom, UINT32_MAX};
    for (int k = 0; k < 4; k++) {
      int64_t r = (int64_t)ys[k] - p;
      equal(lq_slide_source(pin, base, origin, height, sample, ys[k]),
        0 <= r && r < height ? (uint64_t)r : UINT64_MAX);
      equal(lq_slide_fill_row(pin, base, top, bottom, sample, ys[k]),
        (uint32_t)high((int64_t)ys[k] - fill_origin(pin, base, top, bottom, sample), 0));
    }
  }
}
static uint32_t next(uint32_t* state) { *state = *state * 1664525u + 1013904223u; return *state; }
static void* worker(void* result) {
  for (int i = 0; i < 3; i++) lq_slide_thread_init();
  equal(init_calls, 1);
  lq_slide_warm(); lq_slide_warm();
  for (int i = 0; i < 4; i++) equal(warm_calls[i], i == 0 ? 16 : 2);
  uint32_t seed = 0x12345678;
  for (int i = 0; i < 1000; i++) {
    uint32_t v[6]; for (int j = 0; j < 6; j++) v[j] = next(&seed);
    one(v[0], v[1], v[2], v[3], v[4], v[5]);
  }
  *(uint64_t*)result = checks;
  return NULL;
}
int main(void) {
  const uint32_t v[] = {0, 1, 47, 48, 0x7fffffffu, 0x80000000u, UINT32_MAX};
  for (int a = 0; a < 7; a++) for (int b = 0; b < 7; b++)
    for (int c = 0; c < 7; c++) for (int d = 0; d < 7; d++)
      for (int e = 0; e < 7; e++) for (int f = 0; f < 7; f++)
        one(v[a], v[b], v[c], v[d], v[e], v[f]);
  equal(init_calls, 0);  // All first calls succeeded without any runtime.
  lq_slide_thread_init(); lq_slide_thread_init();
  equal(init_calls, 1);
  lq_slide_warm(); lq_slide_warm();
  for (int i = 0; i < 4; i++) equal(warm_calls[i], i == 0 ? 16 : 2);
  pthread_t threads[4]; uint64_t counts[4];
  for (int i = 0; i < 4; i++) assert(pthread_create(&threads[i], NULL, worker, &counts[i]) == 0);
  for (int i = 0; i < 4; i++) { pthread_join(threads[i], NULL); checks += counts[i]; }
  printf("slide: %llu scalar/boundary/thread checks; no Lean runtime linked; passed\n", (unsigned long long)checks);
}
