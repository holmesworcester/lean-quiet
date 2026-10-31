#include "fling.h"
#include <assert.h>
#include <math.h>
#include <stdio.h>

int main(void) {
  for (uint64_t epoch = 0; epoch <= UINT64_C(1) << 40; epoch += UINT64_C(1) << 40) {
    for (int direction = -1; direction <= 1; direction += 2) {
      LqFling s = {0};
      assert(lq_fling_sample(&s, 0, 300, epoch + 1000).stop);
      double distance = 0;
      for (int i = 1; i <= 10; i++) {
        LqFlingStep r = lq_fling_sample(&s, 1, 300 + direction * i * 10, epoch + 1000 + i * 10);
        distance += r.delta;
        assert(!r.released);
      }
      assert(distance == direction * 100);
      // Real UIKit failure: release repeats the last position at a later time.
      LqFlingStep up = lq_fling_sample(&s, 2, 300 + direction * 100, epoch + 1108);
      assert(up.released && up.delta == 0 && up.velocity == direction);
      assert(!lq_fling_sample(&s, 2, 400, epoch + 1109).released);
      // A deliberate pause before release must NOT resurrect old velocity.
      lq_fling_sample(&s, 0, 300, epoch + 2000);
      lq_fling_sample(&s, 1, 400, epoch + 2100);
      lq_fling_sample(&s, 1, 400, epoch + 2150);
      assert(lq_fling_sample(&s, 2, 400, epoch + 2181).velocity == 0);
      // Reversal, cancellation, no movement, and equal timestamp samples.
      lq_fling_sample(&s, 0, 300, epoch + 3000);
      lq_fling_sample(&s, 1, 400, epoch + 3100);
      lq_fling_sample(&s, 1, 380, epoch + 3120);
      assert(lq_fling_sample(&s, 2, 380, epoch + 3121).velocity == -1);
      lq_fling_sample(&s, 0, 300, epoch + 4000);
      lq_fling_sample(&s, 1, 400, epoch + 4100);
      assert(lq_fling_sample(&s, 3, 400, epoch + 4101).stop);
      assert(!lq_fling_sample(&s, 2, 400, epoch + 4102).released);
      lq_fling_sample(&s, 0, 300, epoch + 5000);
      assert(lq_fling_sample(&s, 2, 300, epoch + 5100).velocity == 0);
      lq_fling_sample(&s, 0, 300, epoch + 6000);
      lq_fling_sample(&s, 1, 400, epoch + 6000);
      assert(isfinite(lq_fling_sample(&s, 2, 400, epoch + 6000).velocity));
    }
  }
  puts("fling: repeated release, pause, reversal, cancellation and 64-bit clocks pass");
}
