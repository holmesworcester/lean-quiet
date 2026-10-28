// The headless twin
// =================

// Platform.lean's effects with no OS, for tests and CI. The screen is a
// fixed 1080 x 2400 at 420 dpi with a 128 px status bar and a 63 px
// navigation bar. Everything the OS would do is driven by a script (the
// file named by QUIET_SCRIPT, else stdin), one line per frame:
//
//   <command>          a control command, for Platform.ctlPoll; its reply
//                      (Platform.ctlReply) is printed on stdout
//   !tap list|header|composer X Y
//                      a tap; a list tap's Y is the row on screen, turned
//                      into the content coordinate as Android's twin does
//   !long ...          the same, as a long press
//   !text STRING       the keyboard's text becomes STRING (cursor at its end)
//   !send              the keyboard's send
//   !scroll B          the list's offset becomes B
//   !ime H             the keyboard's height becomes H (0: closed)
//   !frames N          N frames pass with nothing new
//   !sync              frames pass until every command has been answered
//   !dump FILE.ppm     the screen as the compositor would show it
//   # ...              a comment
//
// At the script's end the window closes. Lines are read one per frame, so
// a command's effects are in the frames after it.

#include <lean/lean.h>
#include <math.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define HW 1080
#define HH 2400
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
  uint32_t     b, over;
  // OS state
  float        off;
  uint32_t     content_h, view_h;
  uint32_t     ime;
  char*        text;
  uint32_t     pos[4];
  // events for the next frame
  uint32_t     ev[1024];
  uint32_t     n;
  // control commands: queued for poll, then waiting for replies
  char*        cmds[256];
  uint32_t     ncmd;
  uint32_t     unanswered;
  bool         closed;
} Host;

static Host hs;

static void ev_push(uint32_t k, uint32_t a, uint32_t b, uint32_t c) {
  if (hs.n + 4 > 1024) return;
  hs.ev[hs.n++] = k;
  hs.ev[hs.n++] = a;
  hs.ev[hs.n++] = b;
  hs.ev[hs.n++] = c;
}

static uint32_t max_off(void) {
  uint32_t s  = hs.ime > HBOT ? hs.ime - HBOT : 0;
  uint32_t ve = hs.view_h > s ? hs.view_h - s : 0;
  return hs.content_h > ve ? hs.content_h - ve : 0;
}

static void clamp_off(void) {
  if (hs.off < 0) hs.off = 0;
  if (hs.off > (float)max_off()) hs.off = (float)max_off();
}

static uint32_t rows_of(lean_object* a) {
  return a != NULL ? (uint32_t)lean_array_size(a) : 0;
}

static int32_t composer_top(void) {
  uint32_t below = hs.ime > HBOT ? hs.ime : HBOT;
  return (int32_t)HH - (int32_t)rows_of(hs.bot) - (int32_t)below;
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

static void tap(uint32_t kind, const char* region, int x, int y) {
  if (strcmp(region, "header") == 0) {
    ev_push(kind, 1, (uint32_t)x, (uint32_t)y);
  } else if (strcmp(region, "composer") == 0) {
    ev_push(kind, 2, (uint32_t)x, (uint32_t)y);
  } else {
    int32_t d = (int32_t)lroundf(hs.off) + composer_top() - 1 - y;
    ev_push(kind, 0, (uint32_t)x, (uint32_t)(d < 0 ? 0 : d));
  }
}

// The screen as the compositor would show it: black, the list placed for
// the offset (frame row r at screen row top - over - shift + r, cropped to
// the viewport), the header at the top, the composer above the navigation
// bar or keyboard with its last row repeated to the screen's bottom.
static void dump(const char* path) {
  static uint8_t px[HW * HH * 3];
  memset(px, 0, sizeof px);
  uint32_t th   = rows_of(hs.top);
  int32_t  ctop = composer_top();
  int32_t  s    = hs.ime > HBOT ? (int32_t)hs.ime - HBOT : 0;
  for (int32_t y = 0; y < HH; y++) {
    lean_object* row = NULL;
    if (y < (int32_t)th) {
      row = lean_array_get_core(hs.top, (size_t)y);
    } else if (y >= ctop && rows_of(hs.bot) > 0) {
      uint32_t r = (uint32_t)(y - ctop);
      if (r >= rows_of(hs.bot)) r = rows_of(hs.bot) - 1;
      row = lean_array_get_core(hs.bot, r);
    } else if (hs.list != NULL) {
      int32_t r = y - ((int32_t)th - (int32_t)hs.over - s + ((int32_t)lroundf(hs.off) - (int32_t)hs.b));
      if (r >= 0 && r < (int32_t)rows_of(hs.list)) row = lean_array_get_core(hs.list, (size_t)r);
    }
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
    return;
  }
  fprintf(f, "P6\n%d %d\n255\n", HW, HH);
  fwrite(px, 1, sizeof px, f);
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
    int  x = 0, y = 0;
    if (sscanf(line, "!tap %63s %d %d", r, &x, &y) == 3) {
      tap(2, r, x, y);
    } else if (sscanf(line, "!long %63s %d %d", r, &x, &y) == 3) {
      tap(3, r, x, y);
    } else if (strncmp(line, "!text ", 6) == 0) {
      set_text(line + 6);
    } else if (strcmp(line, "!text") == 0) {
      set_text("");
    } else if (strcmp(line, "!send") == 0) {
      ev_push(5, 0, 0, 0);
    } else if (sscanf(line, "!scroll %d", &x) == 1) {
      hs.off = (float)x;
      clamp_off();
    } else if (sscanf(line, "!ime %d", &x) == 1) {
      hs.ime = (uint32_t)(x < 0 ? 0 : x);
      ev_push(6, hs.ime, 0, 0);
    } else if (sscanf(line, "!frames %d", &x) == 1) {
      hs.wait = x > 0 ? (uint32_t)x - 1 : 0;
    } else if (strcmp(line, "!sync") == 0) {
      hs.syncing = true;
    } else if (sscanf(line, "!dump %63s", a) == 1) {
      dump(a);
      continue;  // a dump shows what is there; no frame passes
    } else {
      fprintf(stderr, "host: unknown line: %s\n", line);
      continue;
    }
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
  uint32_t     v[5] = { HW, HH, HTOP, HBOT, HDPI };
  lean_object* a    = lean_mk_empty_array_with_capacity(lean_box(5));
  for (int i = 0; i < 5; i++) a = lean_array_push(a, lean_box_uint32(v[i]));
  return lean_io_result_mk_ok(a);
}

lean_obj_res lq_scroll(uint32_t content_h, uint32_t view_h) {
  hs.content_h = content_h;
  hs.view_h    = view_h;
  clamp_off();
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)lroundf(hs.off)));
}

lean_obj_res lq_scroll_by(double d) {
  hs.off += (float)d;
  clamp_off();
  return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res lq_scroll_to(double b) {
  hs.off = (float)b;
  clamp_off();
  return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res lq_frame(b_lean_obj_arg list, uint32_t b, uint32_t over, b_lean_obj_arg top,
  b_lean_obj_arg bot) {
  hold(&hs.list, list);
  hold(&hs.top, top);
  hold(&hs.bot, bot);
  hs.b    = b;
  hs.over = over;
  script();
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

lean_obj_res lq_text_clear(void) {
  set_text("");
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
