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
  LqFrameCompletion gate = {0}; LqFrameTicket ticket;
  demand(lq_frame_accept(&gate) && lq_frame_begin(&gate, &ticket),
    "native completion gate accepts a real first publication");
  bool bounded = true;
  for (int i = 0; i < 10000; i++) bounded &= !lq_frame_begin(&gate, &ticket);
  demand(bounded, "a delayed callback keeps native pending ownership bounded");
  LqFrameTicket first_ticket = ticket;
  lq_frame_reset(&gate);
  demand(!lq_frame_begin(&gate, &ticket) &&
    !lq_frame_complete(&gate, first_ticket, 1, 0, 0) && !gate.valid && !gate.pending,
    "reset retires delayed ownership without accepting old-surface completion");
  demand(lq_frame_accept(&gate) && lq_frame_begin(&gate, &ticket) &&
    lq_frame_complete(&gate, ticket, gate.accepted, 0, -7) && gate.valid &&
    gate.frame == 0 && gate.publication == 2 && gate.shift == -7,
    "wrapped frame zero has distinct publication identity and exact native translation");
  gate.accepted = UINT64_MAX; gate.serial = UINT64_MAX;
  demand(!lq_frame_accept(&gate) && !lq_frame_begin(&gate, &ticket),
    "exhausted native identity counters fail closed instead of aliasing a candidate");
  ANativeWindow window;
  uint32_t p[LQ_PLACEMENT_WORDS] = {0,2,10,12, 0,2,0,2, 0,2,20,22, 22,22,18,0,1,
    0,0,0, 10,2,0, 0,2,66,48,0,0};
  bl_attach(&window);
  demand(!bl_trace_enabled(), "compositor trace is disabled without the debug property");
  stub_debug_trace = true; bl_trace = bl_trace_enabled();
  demand(stub_z[BL_HOLD] >= 0 && stub_z[BL_HOLD] < stub_z[BL_LIST],
    "placeholder is above window background and below the painted list");
  assert(bl_begin());
  assert(stage(BL_LIST, 11) && stage(BL_TOP, 12) && stage(BL_BOT, 13));
  assert(stage_hold(66));
  tick();
  demand(!stub_buffer[0] && bl_frame_id() == 0, "staging is invisible before publication");
  bl_geometry(p); bl_vsync(0, NULL);
  uint64_t publication; uint32_t completed_frame; int32_t completed_shift;
  demand(!bl_completed_frame(&publication, &completed_frame, &completed_shift) && bl_frame_id() == 0,
    "submitted frame is not stamped until presentation completes");
  demand(stub_trace_count == 0, "staging and submission do not emit a presentation trace");
  stub_complete();
  demand(bl_completed_frame(&publication, &completed_frame, &completed_shift) &&
    publication == bl_acceptance_id() && completed_frame == 1 && completed_shift == 0,
    "native receipt names the completed accepted publication and translation");
  demand(stub_trace_count == 1 && strstr(stub_trace_last, "completed frame 1 composer-y 20"),
    "trace captures the actual completed composer destination");
  demand(stub_buffer[0]->pixels[0] == 11 && stub_buffer[2]->pixels[0] == 13 &&
    stub_source[0].top == (int32_t)p[0] && stub_destination[0].top == (int32_t)p[2] &&
    stub_destination[2].top == (int32_t)p[10] && bl_frame_id() == 1, "pixels and rectangles publish together");
  unsigned idle_trace = stub_trace_count;
  for (int i = 0; i < 10000; i++) bl_vsync(0, NULL);
  demand(stub_n == 0 && stub_trace_count == idle_trace && !bl_completion.pending,
    "unchanged geometry leaves the native callback slot available");
  stub_sample = true; stub_offset = 0.4f; bl_vsync(0, NULL);
  demand(stub_n == 0, "subpixel samples with unchanged rounded placement do not submit transactions");
  uint64_t before_same = bl_acceptance_id();
  assert(bl_begin()); bl_geometry(p); tick();
  demand(bl_completed_frame(&publication, &completed_frame, &completed_shift) &&
    publication == before_same + 1 && completed_frame == 1 && stub_trace_count == idle_trace + 1,
    "fresh unchanged placement still receives its exact publication acknowledgment");
  // A previous geometry's real animation callback may still be pending.
  stub_offset = 1; bl_vsync(0, NULL); stub_offset = 0;
  assert(bl_begin());
  assert(stage(BL_LIST, 21));
  p[2] = 11; p[3] = 13; p[20] = 11; p[16] = 2;
  bl_geometry(p);
  demand(!bl_begin() && bl_frame_id() == 1, "pending publication blocks next frame's different dirty layer");
  uint64_t unresolved = bl_acceptance_id(); int extra_accepted = 0;
  for (int i = 0; i < 3; i++)
    if (bl_begin()) extra_accepted += bl_geometry(p) ? 1 : 0;
  demand(extra_accepted == 0 && bl_acceptance_id() == unresolved,
    "three further native publications reject while one accepted geometry is unresolved");
  bl_vsync(0, NULL);
  demand(bl_ready && stub_n == 1 && !bl_begin() && bl_frame_id() == 1,
    "pending animation callback holds new geometry without allocating another callback");
  stub_complete_at(0);
  demand(!bl_begin() && bl_frame_id() == 1,
    "old animation completion cannot acknowledge pending new geometry");
  bl_vsync(0, NULL);
  demand(!bl_ready && !bl_begin(), "consumed geometry waits for its own completion");
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
  demand(bl_completed_frame(&publication, &completed_frame, &completed_shift) &&
    publication == unresolved && completed_frame == 2 && completed_shift == 0,
    "refused buffer staging still exposes the preceding native completion");
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
  // Repeated vsyncs cannot allocate callbacks while one is delayed.
  stub_offset = 8; bl_vsync(0, NULL);
  uint64_t prior_view = bl_view_id();
  unsigned prior_trace = stub_trace_count;
  for (int i = 0; i < 10000; i++) { stub_offset = 9; bl_vsync(0, NULL); }
  demand(stub_n == 1 && bl_view_id() == prior_view && stub_trace_count == prior_trace,
    "ten thousand vsyncs retain exactly one delayed native completion");
  stub_complete();
  demand((uint32_t)(bl_view_id() >> 32) == 8,
    "completion records the actual submitted sample rather than a newer pending offset");
  tick();
  demand((uint32_t)(bl_view_id() >> 32) == 9 &&
    bl_completed_frame(&publication, &completed_frame, &completed_shift) && completed_shift == 9,
    "next compositor service publishes the latest offset with its matching receipt");
  // A callback from a destroyed surface can arrive after its replacement
  // has accepted a frame. It must neither stamp nor unblock that frame.
  assert(bl_begin());
  assert(stage(BL_LIST, 49) && stage(BL_TOP, 50) && stage(BL_BOT, 51));
  p[16] = 0; bl_geometry(p); bl_vsync(0, NULL);
  // Exercise wrap directly: gone+attach must not resurrect the old owner
  // even when both native generation numbers alias its original value.
  bl_generation = UINT64_MAX; bl_completion.generation = UINT64_MAX;
  bl_window_gone();
  ANativeWindow replacement;
  bl_attach(&replacement);
  demand(bl_frame_id() == 0 && bl_begin() &&
    !bl_completed_frame(&publication, &completed_frame, &completed_shift),
    "new window starts without an old displayed context");
  assert(stage(BL_LIST, 51) && stage(BL_TOP, 52) && stage(BL_BOT, 53));
  assert(stage_hold(67));
  p[16] = 4;
  bl_geometry(p); bl_vsync(0, NULL);
  int callbacks = 0;
  for (int i = 0; i < stub_n; i++) callbacks += stub_finished[i].count;
  demand(callbacks == 1 && bl_ready, "surface recreation does not accumulate callback ownership");
  demand(bl_done.generation == bl_generation &&
    bl_done.completion.generation == bl_completion.generation && bl_completion.revoked,
    "forced generation wrap still marks old callback ownership revoked");
  unsigned before_gone = stub_trace_count;
  stub_complete_at(0);
  demand(stub_trace_count == before_gone, "destroyed-window completion does not emit presentation evidence");
  demand(bl_frame_id() == 0 && !bl_begin(),
    "old-window callback cannot stamp or acknowledge the replacement");
  bl_vsync(0, NULL); stub_complete();
  demand(bl_frame_id() == 4 && bl_begin() && stub_buffer[0]->pixels[0] == 51,
    "replacement presentation recovers after its own completion");
  unsigned before_hidden = stub_trace_count;
  p[9] = p[8];
  assert(bl_begin()); bl_geometry(p); tick();
  demand(stub_trace_count == before_hidden, "a hidden composer cannot manufacture a visible position");
  p[9] = p[8] + 2;
  assert(bl_begin()); bl_geometry(p); tick();
  stub_debug_trace = false; bl_trace = bl_trace_enabled();
  unsigned before_off = stub_trace_count;
  stub_offset += 1; tick();
  demand(stub_trace_count == before_off, "debug-disabled composition emits no per-frame trace");
  assert(bl_completed_frame(&publication, &completed_frame, &completed_shift));
  uint64_t last_publication = publication;
  bl_completion.accepted = UINT64_MAX;
  demand(!bl_begin() && bl_completed_frame(&publication, &completed_frame, &completed_shift) &&
    publication == last_publication,
    "permanent publication exhaustion does not hide the last completed receipt");
  bl_window_gone();
  printf("layer: %d native handoff checks passed\n", checks);
  return 0;
}
