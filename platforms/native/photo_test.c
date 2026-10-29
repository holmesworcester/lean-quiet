#include "photo.h"
#include <assert.h>
#include <stdio.h>

static LqPhoto slot = LQ_PHOTO_INIT;
static unsigned char rgba[8] = {255,0,0,255, 0,255,0,128};
static void* late(void* unused) {
  (void)unused;
  for (unsigned i = 0; i < 10000; i++)
    assert(!lq_photo_publish(&slot, 10, 1, 2, 1, rgba, sizeof rgba));
  return NULL;
}
int main(void) {
  uint32_t h[4]; unsigned char* b; size_t n;
  assert(!lq_photo_take(&slot, h, &b, &n) && !b && !n);
  lq_photo_begin(&slot, 10);
  assert(!lq_photo_publish(&slot, 10, 1, 0, 1, rgba, 0));
  assert(!lq_photo_publish(&slot, 10, 1, 2049, 1, rgba, sizeof rgba));
  assert(!lq_photo_publish(&slot, 10, 1, 2, 1, rgba, 7));
  assert(!lq_photo_publish(&slot, 10, 9, 2, 1, rgba, sizeof rgba));
  lq_photo_begin(&slot, 11);
  pthread_t worker;
  assert(pthread_create(&worker, NULL, late, NULL) == 0);
  assert(lq_photo_current(&slot, 11));
  assert(lq_photo_publish(&slot, 11, 1, 2, 1, rgba, sizeof rgba));
  assert(!lq_photo_publish(&slot, 11, 2, 0, 0, NULL, 0));
  assert(lq_photo_take(&slot, h, &b, &n));
  assert(h[0] == 11 && h[1] == 1 && h[2] == 2 && h[3] == 1);
  assert(n == sizeof rgba && !memcmp(b, rgba, n)); free(b);
  assert(!lq_photo_current(&slot, 11));
  assert(!lq_photo_take(&slot, h, &b, &n));
  assert(pthread_join(worker, NULL) == 0);
  for (uint32_t status = 2; status <= 3; status++) {
    lq_photo_begin(&slot, 20);
    assert(lq_photo_publish(&slot, 20, status, 1, 1, rgba, 4));
    assert(lq_photo_take(&slot, h, &b, &n) && h[1] == status && !h[2] && !h[3] && !b && !n);
  }
  lq_photo_begin(&slot, 30);
  assert(lq_photo_publish(&slot, 30, 1, 2, 1, rgba, sizeof rgba));
  lq_photo_begin(&slot, 0); // cancellation releases an already decoded result
  assert(!lq_photo_take(&slot, h, &b, &n));
  assert(!lq_photo_publish(&slot, 30, 1, 2, 1, rgba, sizeof rgba));
  puts("native photo ownership: bounded pixels, stale/duplicate completions, cancellation, error and concurrent handoff pass");
  return 0;
}
