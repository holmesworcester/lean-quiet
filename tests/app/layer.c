// Exercise the production frame handoff with interleaved vsyncs and a
// buffer-lock failure. No Android process, window or device is used.
#include <lean/lean.h>
lean_object* initialize_quiet_engine_renderer_Translate(uint8_t builtin);
#define LQ_LAYER_TEST
#include "../../platforms/android/twin/layer.c"
#include <stdio.h>

static int checks;
static void demand(bool ok, const char* message) {
  if (!ok) { fprintf(stderr, "FAIL layer: %s\n", message); exit(1); }
  checks++;
}
static void tick(void) { bl_vsync(0, NULL); stub_complete(); }
static void* refresh_while_frame_sleeps(void* arg) {
  lq_slide_thread_init();
  for (int i = 1; i <= 7; i++) {
    stub_offset = i;
    tick();
    struct timespec delay = {0, 8000000};
    nanosleep(&delay, NULL);
  }
  return NULL;
}
static bool stage(BlKind k, uint32_t color) {
  uint32_t pixels[4] = {color, color, color, color};
  return bl_present(k, pixels, 2, 2, 0, 0);
}
static bool stage_hold(uint32_t height) {
  uint32_t pixels[2 * 67];
  for (int i = 0; i < 2 * 67; i++) pixels[i] = 44;
  return bl_present(BL_HOLD, pixels, 2, height, 0, 0);
}
int main(void) {
  lean_object* init = initialize_quiet_engine_renderer_Translate(1);
  assert(lean_io_result_is_ok(init)); lean_dec_ref(init);
  lean_io_mark_end_initialization();
  lq_slide_warm();
  ANativeWindow window;
  uint32_t p[LQ_PLACEMENT_WORDS] = {0,2,10,12, 0,2,0,2, 0,2,20,22, 22,22,18,0,1,
    0,0,0, 10,2,0, 0,2,66,48,0,0};
  bl_attach(&window);
  demand(stub_z[BL_HOLD] >= 0 && stub_z[BL_HOLD] < stub_z[BL_LIST],
    "placeholder is above window background and below the painted list");
  assert(bl_begin());
  assert(stage(BL_LIST, 11) && stage(BL_TOP, 12) && stage(BL_BOT, 13));
  assert(stage_hold(66));
  tick();
  demand(!stub_buffer[0] && bl_frame_id() == 0, "staging is invisible before publication");
  bl_geometry(p); bl_vsync(0, NULL);
  demand(bl_frame_id() == 0, "submitted frame is not stamped until presentation completes");
  stub_complete();
  demand(stub_buffer[0]->pixels[0] == 11 && stub_buffer[2]->pixels[0] == 13 &&
    stub_source[0].top == (int32_t)p[0] && stub_destination[0].top == (int32_t)p[2] &&
    stub_destination[2].top == (int32_t)p[10] && bl_frame_id() == 1, "pixels and rectangles publish together");
  // A previous geometry's animation callback may still be pending.
  bl_vsync(0, NULL);
  assert(bl_begin());
  assert(stage(BL_LIST, 21));
  p[2] = 11; p[3] = 13; p[20] = 11; p[16] = 2;
  bl_geometry(p);
  demand(!bl_begin() && bl_frame_id() == 1, "pending publication blocks next frame's different dirty layer");
  bl_vsync(0, NULL);
  demand(!bl_ready && !bl_begin() && bl_frame_id() == 1,
    "vsync consumption without completion still rejects a new publication");
  stub_complete_at(0);
  demand(!bl_begin() && bl_frame_id() == 1,
    "old animation completion cannot acknowledge pending new geometry");
  stub_complete();
  demand(bl_begin(), "completion acknowledgment permits the next publication");
  demand(stub_buffer[0]->pixels[0] == 21 && stub_buffer[2]->pixels[0] == 13 &&
    stub_destination[0].top == 11 && bl_frame_id() == 2, "previous pending frame survives timeout");
  assert(bl_begin());
  assert(stage(BL_BOT, 33));
  tick();
  demand(stub_buffer[2]->pixels[0] == 13 && bl_frame_id() == 2, "vsync during partial staging holds previous frame");
  stub_lock_fails = true;
  demand(!stage(BL_TOP, 32), "buffer lock failure propagates");
  stub_lock_fails = false;
  bl_abort(); tick();
  demand(stub_buffer[2]->pixels[0] == 13 && bl_frame_id() == 2, "aborted staging remains invisible");
  assert(bl_begin());
  assert(stage(BL_LIST, 41) && stage(BL_TOP, 42) && stage(BL_BOT, 43));
  p[10] = 21; p[11] = 23; p[16] = 3;
  assert(stage_hold(67)); p[25] = 67;
  bl_geometry(p); tick();
  demand(stub_buffer[0]->pixels[0] == 41 && stub_buffer[1]->pixels[0] == 42 &&
    stub_buffer[2]->pixels[0] == 43 && stub_destination[2].top == 21 && bl_frame_id() == 3,
    "retry publishes all layers with new placement");
  stub_sample = true;
  stub_offset = 3;
  tick();
  demand(stub_destination[0].top == 14 && bl_frame_id() == 3,
    "vsync translates without publishing another Lean frame");
  stub_offset = 1000; tick();
  demand(stub_visible[BL_LIST] == -1 && stub_visible[BL_HOLD] == 1 &&
    stub_destination[BL_HOLD].top == 2 && stub_destination[BL_HOLD].bottom == 21 &&
    stub_source[BL_HOLD].top >= 0 && stub_source[BL_HOLD].bottom <= 67 &&
    stub_buffer[BL_HOLD]->pixels[0] == 44,
    "published fill covers the viewport after the painted buffer leaves it");
  p[22] = 1;
  assert(bl_begin()); bl_geometry(p); tick();
  stub_offset = 9; tick();
  demand(stub_destination[0].top == 11, "pinned page ignores moving OS offset");
  p[22] = 0;
  assert(bl_begin()); bl_geometry(p); tick();
  pthread_t compositor;
  assert(pthread_create(&compositor, NULL, refresh_while_frame_sleeps, NULL) == 0);
  struct timespec slow_frame = {0, 50000000};
  nanosleep(&slow_frame, NULL);
  pthread_join(compositor, NULL);
  demand(stub_destination[0].top == 18 && bl_frame_id() == 3,
    "foreign compositor thread advances while Lean frame thread sleeps 50ms");
  // Newer animation completion must not be overwritten by an older one.
  stub_offset = 8; bl_vsync(0, NULL);
  stub_offset = 9; bl_vsync(0, NULL);
  stub_complete_at(1);
  uint64_t latest = bl_view_id();
  stub_complete_at(0);
  demand(bl_view_id() == latest && (uint32_t)(latest >> 32) == 9,
    "out-of-order callbacks cannot regress displayed input geometry");
  // A callback from a destroyed surface can arrive after its replacement
  // has accepted a frame. It must neither stamp nor unblock that frame.
  bl_vsync(0, NULL);
  bl_window_gone();
  ANativeWindow replacement;
  bl_attach(&replacement);
  demand(bl_frame_id() == 0 && bl_begin(), "new window starts without an old displayed context");
  assert(stage(BL_LIST, 51) && stage(BL_TOP, 52) && stage(BL_BOT, 53));
  assert(stage_hold(67));
  p[16] = 4;
  bl_geometry(p); bl_vsync(0, NULL);
  stub_complete_at(0);
  demand(bl_frame_id() == 0 && !bl_begin(),
    "old-window callback cannot stamp or acknowledge the replacement");
  stub_complete();
  demand(bl_frame_id() == 4 && bl_begin() && stub_buffer[0]->pixels[0] == 51,
    "replacement presentation recovers after its own completion");
  bl_window_gone();
  printf("layer: %d native handoff checks passed\n", checks);
  return 0;
}
