// The headless twin
// =================

// Platform.lean's effects with no OS, for tests and CI. The screen is a
// initially 1080 x 2400 at 420 dpi with a 128 px status bar and a 63 px
// navigation bar. Everything the OS would do is driven by a script (the
// file named by QUIET_SCRIPT, else stdin), one line per frame:
//
//   <command>          a control command, for Platform.ctlPoll; its reply
//                      (Platform.ctlReply) is printed on stdout
//   !tap list|header|composer X Y
//                      a down/up pair; Lean classifies and maps it
//   !long ...          a down/up pair 500 ms apart
//   !text STRING       the keyboard's text becomes STRING (cursor at its end)
//   !send              the keyboard's send
//   !scroll B          the list's offset becomes B
//   !ime H             the keyboard's height becomes H (0: closed)
//   !background / !foreground / !surface 0|1
//                      lifecycle events, delivered even without a frame
//   !resize W H        change the viewport
//   !link URL          deliver a warm URL (QUIET_LINK supplies a launch URL)
//   !frames N          N frames pass with nothing new
//   !sync              frames pass until every command has been answered
//   !dump FILE.ppm     the screen as the compositor would show it
//   # ...              a comment
//
// At the script's end the window closes. Lines are read one per frame, so
// a command's effects are in the frames after it.

#include <lean/lean.h>
#include "../native/thread.h"
#include <math.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define HW host_w
#define HH host_h
static uint32_t host_w = 1080, host_h = 2400;
#define HTOP 128
#define HBOT 63
#define HDPI 420

typedef struct {
  FILE*        in;
  bool         eof;
  uint32_t     wait;       // frames still to pass (!frames)
  bool         syncing;    // !sync: until every command is answered
  // the last frames shown, held
  lean_object* list;
  lean_object* top;
  lean_object* bot;
  lean_object* hold;
  uint32_t     b, over;
  uint32_t     placement[LQ_PLACEMENT_WORDS];
  uint64_t     clock;
  bool         batch;
  // OS state
  float        off;
  uint32_t     content_h, view_h;
  uint32_t     ime;
  uint32_t     system_dark;
  bool         effective_dark;
  uint32_t     background;
  char*        text;
  uint32_t     pos[4];
  // events for the next frame
  uint32_t*    ev;
  uint32_t     cap;
  uint32_t     n;
  // control commands: queued for poll, then waiting for replies
  char*        cmds[256];
  uint32_t     ncmd;
  uint32_t     unanswered;
  bool         closed;
} Host;

static Host hs;
static bool polled, suspended, surface = true;
static char* pending_link;

static void raw_push(uint32_t k, uint32_t a, uint32_t b, uint32_t c, uint64_t time) {
  if (hs.n + 8 > hs.cap) {
    hs.cap = hs.cap ? hs.cap * 2 : 1024;
    hs.ev = realloc(hs.ev, hs.cap * sizeof *hs.ev);
    if (!hs.ev) abort();
  }
  uint32_t words[8] = {k, a, b, c, (uint32_t)time, (uint32_t)(time >> 32), hs.placement[16], lq_slide_delta(hs.placement[22], hs.placement[15], (int32_t)lroundf(hs.off))};
  memcpy(hs.ev + hs.n, words, sizeof words);
  hs.n += 8;
}
static void ev_push(uint32_t k, uint32_t a, uint32_t b, uint32_t c) {
  raw_push(k >= 9 && k <= 12 ? k + 7 : k, a, b, c, hs.clock);
}

static uint32_t rows_of(lean_object* a) {
  return a != NULL ? (uint32_t)lean_array_size(a) : 0;
}

// Codepoints in a UTF-8 string.
static uint32_t cps(const char* s) {
  uint32_t n = 0;
  for (; *s; s++) n += ((unsigned char)*s & 0xC0) != 0x80;
  return n;
}

static void set_text(const char* s) {
  free(hs.text);
  hs.text = strdup(s);
  uint32_t n = cps(s);
  hs.pos[0] = hs.pos[1] = hs.pos[2] = hs.pos[3] = n;
  ev_push(4, 0, 0, 0);
}

// Compatibility script gestures expand to raw samples, classified only in Lean.
static void tap(uint32_t kind, const char* region, int x, int y) {
  if (strcmp(region, "composer") == 0) y += (int)hs.placement[10];
  raw_push(9, 0, x, y, hs.clock);
  hs.clock += kind == 3 ? 500 : 30;
  raw_push(11, 0, x, y, hs.clock);
}

// Copy the published source/destination rectangles into a screen dump.
static void dump(const char* path) {
  uint8_t* px = calloc((size_t)HW * HH, 3);
  lean_object* layers[3] = { hs.list, hs.top, hs.bot };
  for (int32_t y = 0; y < HH; y++) {
    lean_object* row = NULL;
    if ((uint32_t)y >= hs.placement[7] && (uint32_t)y < hs.placement[10]) {
      int32_t sample = (int32_t)lroundf(hs.off);
      int64_t r = (int64_t)lq_slide_source(hs.placement[22], hs.placement[15],
        hs.placement[20], hs.placement[21], sample, y);
      if (r >= 0 && (uint64_t)r < rows_of(hs.list)) row = lean_array_get_core(hs.list, r);
      else {
        uint32_t r = lq_slide_fill_row(hs.placement[22], hs.placement[15],
          hs.placement[7], hs.placement[10], sample, y);
        if (r < rows_of(hs.hold)) row = lean_array_get_core(hs.hold, r);
      }
    }
    for (int k = 1; k < 3; k++) {
      uint32_t* r = hs.placement + 4 * k;
      if ((uint32_t)y >= r[2] && (uint32_t)y < r[3]) {
        size_t at = r[0] + (uint32_t)y - r[2];
        if (at < rows_of(layers[k])) row = lean_array_get_core(layers[k], at);
      }
    }
    if ((uint32_t)y >= hs.placement[12] && (uint32_t)y < hs.placement[13] && rows_of(hs.bot))
      row = lean_array_get_core(hs.bot, rows_of(hs.bot) - 1);
    if (row == NULL) continue;
    const uint8_t* p = lean_sarray_cptr(row);
    size_t         n = lean_sarray_size(row) / 4;
    for (size_t x = 0; x < n && x < HW; x++) {
      memcpy(px + ((size_t)y * HW + x) * 3, p + 4 * x, 3);
    }
  }
  FILE* f = fopen(path, "wb");
  if (f == NULL) {
    fprintf(stderr, "host: cannot write %s\n", path);
    free(px);
    return;
  }
  fprintf(f, "P6\n%d %d\n255\n", HW, HH);
  fwrite(px, 1, (size_t)HW * HH * 3, f);
  free(px);
  fclose(f);
}

// Reads script lines until one lets a frame pass (most do).
static void script(void) {
  if (hs.wait > 0) {
    hs.wait--;
    return;
  }
  if (hs.syncing) {
    if (hs.unanswered > 0 || hs.ncmd > 0) return;
    hs.syncing = false;
  }
  if (hs.in == NULL) {
    const char* p = getenv("QUIET_SCRIPT");
    hs.in = p != NULL ? fopen(p, "r") : stdin;
    if (hs.in == NULL) {
      fprintf(stderr, "host: cannot read %s\n", p);
      hs.eof = true;
    }
  }
  char line[8192];
  while (!hs.eof) {
    if (fgets(line, sizeof line, hs.in) == NULL) {
      hs.eof = true;
      break;
    }
    line[strcspn(line, "\r\n")] = 0;
    if (line[0] == 0 || line[0] == '#') continue;
    if (line[0] != '!') {
      if (hs.ncmd < 256) hs.cmds[hs.ncmd++] = strdup(line);
      return;
    }
    char a[64] = { 0 }, r[64] = { 0 };
    int  x = 0, y = 0, phase = 0, pointer = 0;
    unsigned long long time = 0;
    if (sscanf(line, "!vsync %llu %d %63s", &time, &x, a) == 3) {
      hs.clock = time; hs.off = x;
      dump(a);
      printf("vsync %llu %u %d %u %d %u\n", time, hs.placement[16], x,
        hs.placement[15], (int32_t)hs.placement[20], hs.placement[21]);
      continue;  // OS refresh, no call back into the Lean frame loop
    }
    if (sscanf(line, "!frame %llu %d", &time, &x) == 2) {
      hs.clock = time; hs.off = x; return;
    }
    if (strcmp(line, "!begin") == 0) { hs.batch = true; continue; }
    if (strcmp(line, "!end") == 0) { hs.batch = false; return; }
    if (sscanf(line, "!raw %d %d %d %d %llu", &phase, &pointer, &x, &y, &time) == 5) {
      hs.clock = time;
      raw_push(9 + phase, pointer, x, y, time);
      if (hs.batch) continue;
      return;
    }
    if (sscanf(line, "!key %d %d", &x, &y) == 2) { ev_push(14, x, y, 0); return; }
    if (sscanf(line, "!usb-key %d %d", &x, &y) == 2) { ev_push(15, x, y, 0); return; }
    if (sscanf(line, "!action %d", &x) == 1) { ev_push(5, x, 0, 0); return; }
    if (strcmp(line, "!background") == 0) {
      suspended = true; ev_push(9, 0, 0, 0);
    } else if (strcmp(line, "!foreground") == 0) {
      suspended = false; ev_push(10, 0, 0, 0);
    } else if (sscanf(line, "!surface %d", &x) == 1) {
      surface = x != 0; ev_push(11, surface, 0, 0);
    } else if (sscanf(line, "!resize %d %d", &x, &y) == 2 && x > 0 && y > 0) {
      host_w = x; host_h = y; ev_push(12, 0, 0, 0);
    } else if (strncmp(line, "!link ", 6) == 0) {
      free(pending_link); pending_link = strdup(line + 6);
    } else if (sscanf(line, "!tap %63s %d %d", r, &x, &y) == 3) {
      tap(2, r, x, y);
    } else if (sscanf(line, "!long %63s %d %d", r, &x, &y) == 3) {
      tap(3, r, x, y);
    } else if (strncmp(line, "!text ", 6) == 0) {
      set_text(line + 6);
    } else if (strcmp(line, "!text") == 0) {
      set_text("");
    } else if (strcmp(line, "!send") == 0) {
      ev_push(5, 4, 0, 0);
    } else if (sscanf(line, "!scroll %d", &x) == 1) {
      hs.off = (float)x;
    } else if (sscanf(line, "!theme %63s", a) == 1) {
      hs.system_dark = strcmp(a, "dark") == 0;
    } else if (sscanf(line, "!ime %d", &x) == 1) {
      hs.ime = (uint32_t)(x < 0 ? 0 : x);
      ev_push(6, hs.ime, 0, 0);
    } else if (sscanf(line, "!frames %d", &x) == 1) {
      hs.wait = x > 0 ? (uint32_t)x - 1 : 0;
    } else if (strcmp(line, "!sync") == 0) {
      hs.syncing = true;
    } else if (strncmp(line, "!dump ", 6) == 0) {
      dump(line + 6);
      continue;  // a dump shows what is there; no frame passes
    } else {
      fprintf(stderr, "host: unknown line: %s\n", line);
      continue;
    }
    if (hs.batch) continue;
    return;
  }
  if (hs.eof && !hs.closed && hs.unanswered == 0 && hs.ncmd == 0) {
    hs.closed = true;
    ev_push(1, 0, 0, 0);
  }
}

static void hold(lean_object** slot, b_lean_obj_arg f) {
  lean_inc(f);
  if (*slot != NULL) lean_dec(*slot);
  *slot = f;
}

// Platform.lean
// -------------

lean_obj_res lq_screen(void) {
  lq_slide_thread_init();
  lq_slide_warm();
  uint32_t     v[6] = { HW, HH, HTOP, HBOT, HDPI, hs.system_dark };
  lean_object* a    = lean_mk_empty_array_with_capacity(lean_box(6));
  for (int i = 0; i < 6; i++) a = lean_array_push(a, lean_box_uint32(v[i]));
  return lean_io_result_mk_ok(a);
}

lean_obj_res lq_scroll(uint32_t content_h, uint32_t view_h) {
  hs.content_h = content_h;
  hs.view_h    = view_h;
  return lean_io_result_mk_ok(lean_box_float(hs.off));
}

lean_obj_res lq_scroll_by(double d) {
  hs.off += (float)d;
  return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res lq_scroll_to(double b) {
  hs.off = (float)b;
  return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res lq_frame(b_lean_obj_arg list, uint32_t b, uint32_t over, b_lean_obj_arg top,
  b_lean_obj_arg bot, uint8_t pin, b_lean_obj_arg placement, b_lean_obj_arg holdPixels) {
  lq_slide_thread_init();
  lq_slide_warm();
  (void)pin;
  for (int i = 0; i < LQ_PLACEMENT_WORDS; i++) hs.placement[i] = lean_unbox_uint32(lean_array_get_core(placement, i));
  if (suspended || !surface) {
    fprintf(stderr, "host: frame without an active surface\n"); abort();
  }
  hold(&hs.list, list);
  hold(&hs.top, top);
  hold(&hs.bot, bot);
  hold(&hs.hold, holdPixels);
  hs.b    = b;
  hs.over = over;
  hs.clock += 16;
  if (!polled) script();
  ev_push(13, 0, 0, 0);
  lean_object* evs = lean_mk_empty_array_with_capacity(lean_box(hs.n));
  for (uint32_t i = 0; i < hs.n; i++) evs = lean_array_push(evs, lean_box_uint32(hs.ev[i]));
  hs.n = 0;
  return lean_io_result_mk_ok(evs);
}

lean_obj_res lq_text(void) {
  lean_object* a = lean_mk_empty_array_with_capacity(lean_box(4));
  for (int i = 0; i < 4; i++) a = lean_array_push(a, lean_box_uint32(hs.pos[i]));
  lean_object* p = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p, 0, lean_mk_string(hs.text != NULL ? hs.text : ""));
  lean_ctor_set(p, 1, a);
  return lean_io_result_mk_ok(p);
}

lean_obj_res lq_ime(uint8_t show) {
  hs.ime = show ? 900 : 0;  // a keyboard opens at once here
  ev_push(6, hs.ime, 0, 0);
  return lean_io_result_mk_ok(lean_box(0));
}

// The clipboard: what the app copied, printed as a reply line.
lean_obj_res lq_copy(b_lean_obj_arg text) {
  printf("copied %s\n", lean_string_cstr(text));
  fflush(stdout);
  return lean_io_result_mk_ok(lean_box(0));
}

// The camera: none here (QTests/Sim.lean feeds frames to its own Io).
lean_obj_res lq_scan(uint8_t on) {
  (void)on;
  return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res lq_luma(void) {
  lean_object* p = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p, 0, lean_mk_empty_array());
  lean_ctor_set(p, 1, lean_alloc_sarray(1, 0, 0));
  return lean_io_result_mk_ok(p);
}

lean_obj_res lq_set_text(b_lean_obj_arg text) {
  set_text(lean_string_cstr(text));
  return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res lq_ctl_poll(void) {
  lean_object* out = lean_mk_empty_array();
  for (uint32_t i = 0; i < hs.ncmd; i++) {
    out = lean_array_push(out, lean_mk_string(hs.cmds[i]));
    free(hs.cmds[i]);
  }
  hs.unanswered += hs.ncmd;
  hs.ncmd = 0;
  return lean_io_result_mk_ok(out);
}

lean_obj_res lq_ctl_reply(b_lean_obj_arg s) {
  if (hs.unanswered > 0) {
    hs.unanswered--;
    const char* str = lean_string_cstr(s);
    for (const char* c = str; *c; c++) putchar(*c == '\n' ? ' ' : *c);
    putchar('\n');
    fflush(stdout);
  }
  return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res lq_now_us(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return lean_io_result_mk_ok(lean_box_uint64((uint64_t)ts.tv_sec * 1000000u + (uint64_t)ts.tv_nsec / 1000u));
}

lean_obj_res lq_poll(void) {
  polled = true;
  script();
  lean_object* evs = lean_mk_empty_array();
  for (uint32_t i = 0; i < hs.n; i++) evs = lean_array_push(evs, lean_box_uint32(hs.ev[i]));
  hs.n = 0;
  return lean_io_result_mk_ok(evs);
}

lean_obj_res lq_links(void) {
  static bool launched;
  lean_object* links = lean_mk_empty_array();
  if (!launched) {
    launched = true;
    const char* url = getenv("QUIET_LINK");
    if (url != NULL) links = lean_array_push(links, lean_mk_string(url));
  }
  if (pending_link != NULL) {
    links = lean_array_push(links, lean_mk_string(pending_link));
    free(pending_link); pending_link = NULL;
  }
  return lean_io_result_mk_ok(links);
}



lean_obj_res lq_log(b_lean_obj_arg s) {
  fprintf(stderr, "%s\n", lean_string_cstr(s));
  return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res lq_tz_min(void) {
  time_t t = time(NULL);
  struct tm tm;
  localtime_r(&t, &tm);
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(int32_t)(tm.tm_gmtoff / 60)));
}

// Headless physics: accepted drag deltas, with no policy or draw clamp.
lean_obj_res lq_motion(b_lean_obj_arg samples) {
  static bool down;
  static float last;
  for (size_t i = 0; i + 7 < lean_array_size(samples); i += 8) {
    uint32_t k = lean_unbox_uint32(lean_array_get_core(samples, i));
    float y = (int32_t)lean_unbox_uint32(lean_array_get_core(samples, i + 3));
    if (k == 9) { down = true; last = y; }
    else if (k == 12) down = false;
    else if (down) { hs.off += y - last; last = y; if (k == 11) down = false; }
  }
  return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res lq_appearance(uint8_t dark, uint32_t background) {
  hs.effective_dark = dark;
  hs.background = background;
  return lean_io_result_mk_ok(lean_box(0));
}
