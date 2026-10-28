// Lean's runtime drops the top byte of some heap pointers, which arm64
// Android tags (https://source.android.com/devices/tech/debug/tagged-pointers):
// free() aborts on them. Turn the tagging off before anything allocates;
// an APK says the same with allowNativeHeapPointerTagging="false".
#include <malloc.h>

__attribute__((constructor(101))) static void lean_notag(void) {
#ifdef M_BIONIC_SET_HEAP_TAGGING_LEVEL
  mallopt(M_BIONIC_SET_HEAP_TAGGING_LEVEL, M_HEAP_TAGGING_LEVEL_NONE);
#endif
}
