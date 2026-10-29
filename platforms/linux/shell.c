/* The Linux seam: xcb + MIT-SHM, no widget toolkit. Lean supplies every
 * pixel and all hit testing. X events and selection ownership stay here.
 * Coordinates crossing the seam are logical pixels; QUIET_SCALE is 1..4.
 * Keyboard mapping supports Latin/Unicode keysyms, not an IME or dead keys.
 */
#include <lean/lean.h>
#include "../native/thread.h"
#include <xcb/xcb.h>
#include <xcb/shm.h>
#include <xcb/sync.h>
#include <X11/keysym.h>
#include <sys/ipc.h>
#include <sys/shm.h>
#include <poll.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

static struct {
    xcb_connection_t *c;
    xcb_screen_t *screen;
    xcb_window_t win;
    xcb_gcontext_t gc;
    xcb_atom_t wm_delete, protocols, clipboard, utf8, targets, property, wm_sync;
    /* _NET_WM_SYNC_REQUEST: the counter the window manager waits on, the
       value it asked for, and whether the configure it announced came */
    xcb_sync_counter_t counter;
    xcb_sync_int64_t sync_value;
    bool sync_pending, sync_configured;
    xcb_shm_seg_t seg;
    uint8_t *pixels;
    size_t bytes;
    unsigned w, h, scale;
    bool shm, focused, down, moved;
    int dx, dy;
    uint32_t events[4096];
    size_t n;
    char text[65536];
    size_t anchor, caret; /* byte boundaries, converted at the seam */
    char *clip;
    double scroll;
    uint32_t content, view;
    xcb_get_keyboard_mapping_reply_t *keys;
    unsigned min_key;
} q;

static void fail(const char *s) { fprintf(stderr, "quiet-linux: %s\n", s); exit(1); }
static lean_obj_res unit(void) { return lean_io_result_mk_ok(lean_box(0)); }
static void event(uint32_t k, uint32_t a, uint32_t b, uint32_t c) {
    if (q.n + 4 <= sizeof(q.events)/sizeof(*q.events)) {
        q.events[q.n++] = k; q.events[q.n++] = a;
        q.events[q.n++] = b; q.events[q.n++] = c;
    }
}
static xcb_atom_t atom(const char *s) {
    xcb_intern_atom_reply_t *r = xcb_intern_atom_reply(q.c, xcb_intern_atom(q.c, 0, strlen(s), s), NULL);
    if (!r) fail("intern atom");
    xcb_atom_t a = r->atom; free(r); return a;
}
static unsigned setting(const char *s, unsigned fallback, unsigned lo, unsigned hi) {
    const char *v = getenv(s); if (!v) return fallback;
    char *end; unsigned long n = strtoul(v, &end, 10);
    if (*end || n < lo || n > hi) fail("invalid window size/scale");
    return n;
}
static void buffer_free(void) {
    if (!q.pixels) return;
    if (q.shm) { xcb_shm_detach(q.c, q.seg); xcb_flush(q.c); shmdt(q.pixels); }
    else free(q.pixels);
    q.pixels = NULL;
}
static void cleanup(void) {
    buffer_free(); free(q.clip); free(q.keys);
    if (q.c) xcb_disconnect(q.c);
}
static void buffer(void) {
    buffer_free(); q.bytes = (size_t)q.w * q.h * 4;
    q.shm = false;
    const xcb_query_extension_reply_t *ext = xcb_get_extension_data(q.c, &xcb_shm_id);
    if (ext && ext->present && !getenv("QUIET_NO_SHM")) {
        int id = shmget(IPC_PRIVATE, q.bytes, IPC_CREAT | 0600);
        if (id >= 0) {
            void *mem = shmat(id, NULL, 0);
            if (mem != (void *)-1) {
                q.seg = xcb_generate_id(q.c);
                xcb_generic_error_t *e = xcb_request_check(q.c, xcb_shm_attach_checked(q.c, q.seg, id, 0));
                if (!e) { q.pixels = mem; q.shm = true; }
                else { free(e); shmdt(mem); }
            }
            shmctl(id, IPC_RMID, NULL);
        }
    }
    if (!q.shm) q.pixels = malloc(q.bytes);
    if (!q.pixels) fail("frame allocation");
    fprintf(stderr, "surface %u %u scale %u %s\n", q.w, q.h, q.scale, q.shm ? "MIT-SHM" : "PutImage");
}
static void keys(void) {
    free(q.keys);
    const xcb_setup_t *s = xcb_get_setup(q.c);
    q.min_key = s->min_keycode;
    q.keys = xcb_get_keyboard_mapping_reply(q.c,
        xcb_get_keyboard_mapping(q.c, s->min_keycode, s->max_keycode - s->min_keycode + 1), NULL);
}
static void init(void) {
    if (q.c) return;
    int screen; q.c = xcb_connect(NULL, &screen);
    if (xcb_connection_has_error(q.c)) fail("cannot connect to DISPLAY");
    xcb_screen_iterator_t it = xcb_setup_roots_iterator(xcb_get_setup(q.c));
    while (screen--) xcb_screen_next(&it);
    q.screen = it.data;
    if (q.screen->root_depth != 24 || xcb_get_setup(q.c)->image_byte_order != XCB_IMAGE_ORDER_LSB_FIRST)
        fail("this slice requires a little-endian 24-bit TrueColor X server");
    q.scale = setting("QUIET_SCALE", 1, 1, 4);
    q.w = setting("QUIET_WIDTH", 1100, 320, 4096) * q.scale;
    q.h = setting("QUIET_HEIGHT", 760, 480, 2160) * q.scale;
    q.win = xcb_generate_id(q.c); q.gc = xcb_generate_id(q.c);
    /* No background and north-west gravity: a resize keeps what is shown
       and paints nothing of its own over it until Lean's next frame. */
    uint32_t values[] = {XCB_BACK_PIXMAP_NONE, XCB_GRAVITY_NORTH_WEST, XCB_EVENT_MASK_EXPOSURE |
        XCB_EVENT_MASK_STRUCTURE_NOTIFY | XCB_EVENT_MASK_KEY_PRESS | XCB_EVENT_MASK_BUTTON_PRESS |
        XCB_EVENT_MASK_BUTTON_RELEASE | XCB_EVENT_MASK_POINTER_MOTION | XCB_EVENT_MASK_FOCUS_CHANGE};
    xcb_create_window(q.c, XCB_COPY_FROM_PARENT, q.win, q.screen->root, 0, 0, q.w, q.h, 0,
        XCB_WINDOW_CLASS_INPUT_OUTPUT, q.screen->root_visual,
        XCB_CW_BACK_PIXMAP | XCB_CW_BIT_GRAVITY | XCB_CW_EVENT_MASK, values);
    xcb_create_gc(q.c, q.gc, q.win, 0, NULL);
    q.wm_delete = atom("WM_DELETE_WINDOW"); q.protocols = atom("WM_PROTOCOLS");
    q.clipboard = atom("CLIPBOARD"); q.utf8 = atom("UTF8_STRING");
    q.targets = atom("TARGETS"); q.property = atom("QUIET_PASTE");
    q.wm_sync = atom("_NET_WM_SYNC_REQUEST");
    xcb_atom_t protocols[2] = {q.wm_delete, q.wm_sync};
    int nprotocols = 1;
    /* A window manager that resizes waits for the frame at the new size
       (the counter set in lq_desktop_frame), never showing a stale one. */
    xcb_sync_initialize_reply_t *sync = xcb_sync_initialize_reply(q.c, xcb_sync_initialize(q.c, 3, 1), NULL);
    if (sync) {
        free(sync);
        q.counter = xcb_generate_id(q.c);
        xcb_sync_create_counter(q.c, q.counter, (xcb_sync_int64_t){0, 0});
        xcb_change_property(q.c, XCB_PROP_MODE_REPLACE, q.win, atom("_NET_WM_SYNC_REQUEST_COUNTER"),
            XCB_ATOM_CARDINAL, 32, 1, &q.counter);
        nprotocols = 2;
    }
    xcb_change_property(q.c, XCB_PROP_MODE_REPLACE, q.win, q.protocols, XCB_ATOM_ATOM, 32, nprotocols, protocols);
    const char *title = "Lean Quiet";
    xcb_change_property(q.c, XCB_PROP_MODE_REPLACE, q.win, XCB_ATOM_WM_NAME, XCB_ATOM_STRING, 8, strlen(title), title);
    xcb_change_property(q.c, XCB_PROP_MODE_REPLACE, q.win, atom("_NET_WM_NAME"), q.utf8, 8, strlen(title), title);
    uint32_t hints[18] = {0}; hints[0] = (1u << 4) | (1u << 5);
    hints[5] = 320 * q.scale; hints[6] = 480 * q.scale;
    hints[7] = 4096 * q.scale; hints[8] = 2160 * q.scale;
    xcb_change_property(q.c, XCB_PROP_MODE_REPLACE, q.win, atom("WM_NORMAL_HINTS"), atom("WM_SIZE_HINTS"), 32, 18, hints);
    keys(); buffer(); atexit(cleanup);
    xcb_map_window(q.c, q.win); xcb_flush(q.c);
}
static size_t next(size_t p) {
    if (!q.text[p]) return p;
    do p++; while (((unsigned char)q.text[p] & 0xc0) == 0x80);
    return p;
}
static size_t prev(size_t p) {
    if (!p) return 0;
    do p--; while (p && ((unsigned char)q.text[p] & 0xc0) == 0x80);
    return p;
}
static unsigned count(size_t p) {
    unsigned n = 0; for (size_t i = 0; i < p; i++) n += ((unsigned char)q.text[i] & 0xc0) != 0x80;
    return n;
}
static size_t byte_at(unsigned cp) {
    size_t p = 0; while (cp-- && q.text[p]) p = next(p); return p;
}
static bool utf8(const char *s, size_t n) {
    for (size_t i=0;i<n;) {
        uint32_t c=(unsigned char)s[i++], cp; unsigned k;
        if (!c) return false;
        if (c<128) continue;
        if (c>=0xc2 && c<=0xdf) { k=1; cp=c&31; }
        else if (c>=0xe0 && c<=0xef) { k=2; cp=c&15; }
        else if (c>=0xf0 && c<=0xf4) { k=3; cp=c&7; }
        else return false;
        unsigned len=k;
        if (i+k>n) return false;
        while (k--) { c=(unsigned char)s[i++]; if ((c&0xc0)!=0x80) return false; cp=(cp<<6)|(c&63); }
        if ((len==2 && cp<0x800) || (len==3 && cp<0x10000) || cp>0x10ffff || (cp>=0xd800 && cp<=0xdfff)) return false;
    }
    return true;
}
static void replace(const char *s, size_t n) {
    if (!utf8(s,n)) return;
    size_t a = q.anchor < q.caret ? q.anchor : q.caret, b = q.anchor > q.caret ? q.anchor : q.caret;
    size_t len = strlen(q.text);
    if (len - (b-a) + n >= sizeof(q.text)) return;
    memmove(q.text + a + n, q.text + b, len - b + 1);
    memcpy(q.text + a, s, n); q.anchor = q.caret = a+n;
    event(4, 0, 0, 0);
}
static void copy(const char *s, size_t n) {
    free(q.clip); q.clip = strndup(s, n);
    xcb_set_selection_owner(q.c, q.win, q.clipboard, XCB_CURRENT_TIME); xcb_flush(q.c);
}
static void key(xcb_key_press_event_t *e) {
    if (!q.keys || e->detail < q.min_key) return;
    unsigned per = q.keys->keysyms_per_keycode;
    unsigned index = (e->detail - q.min_key) * per;
    xcb_keysym_t *syms = xcb_get_keyboard_mapping_keysyms(q.keys);
    xcb_keysym_t k = syms[index];
    bool shift = e->state & XCB_MOD_MASK_SHIFT, caps = e->state & XCB_MOD_MASK_LOCK;
    if (shift && per > 1 && syms[index+1]) k = syms[index+1];
    if (caps && k >= 'a' && k <= 'z') k -= 32;
    else if (caps && k >= 'A' && k <= 'Z') k += 32;
    if (k == XK_Escape) { event(12, 0, 0, 0); return; }
    if (!q.focused) return;
    if (e->state & XCB_MOD_MASK_CONTROL) {
        if (k >= 'A' && k <= 'Z') k += 32;
        if (k == 'a') { q.anchor = 0; q.caret = strlen(q.text); event(4,0,0,0); }
        if (k == 'c' || k == 'x') {
            size_t a = q.anchor < q.caret ? q.anchor : q.caret, b = q.anchor > q.caret ? q.anchor : q.caret;
            if (b > a) { copy(q.text+a, b-a); if (k == 'x') replace("",0); }
        }
        if (k == 'v') xcb_convert_selection(q.c, q.win, q.clipboard, q.utf8, q.property, XCB_CURRENT_TIME);
        return;
    }
    if (k == XK_Return || k == XK_KP_Enter) {
        if (shift) replace("\n",1); else event(5,0,0,0); return;
    }
    if (k == XK_BackSpace || k == XK_Delete) {
        if (q.anchor == q.caret) { if (k == XK_BackSpace) q.anchor = prev(q.caret); else q.caret = next(q.caret); }
        replace("",0); return;
    }
    if (k == XK_Left || k == XK_Right || k == XK_Home || k == XK_End) {
        q.caret = k == XK_Left ? prev(q.caret) : k == XK_Right ? next(q.caret) : k == XK_Home ? 0 : strlen(q.text);
        if (!shift) q.anchor = q.caret;
        event(4,0,0,0); return;
    }
    /* Legacy non-Latin keysyms are not Unicode scalar values. */
    if (k > 255 && k < 0x01000000) return;
    uint32_t cp = k >= 0x01000000 ? k & 0xffffff : k;
    if (cp < 32 || (k >= 0xff00 && k < 0x01000000) || cp > 0x10ffff || (cp >= 0xd800 && cp <= 0xdfff)) return;
    char b[4]; size_t n;
    if (cp < 128) { b[0]=cp; n=1; }
    else if (cp < 2048) { b[0]=0xc0|(cp>>6); b[1]=0x80|(cp&63); n=2; }
    else if (cp < 65536) { b[0]=0xe0|(cp>>12); b[1]=0x80|((cp>>6)&63); b[2]=0x80|(cp&63); n=3; }
    else { b[0]=0xf0|(cp>>18); b[1]=0x80|((cp>>12)&63); b[2]=0x80|((cp>>6)&63); b[3]=0x80|(cp&63); n=4; }
    replace(b,n);
}
static void selection(xcb_selection_request_event_t *e) {
    xcb_selection_notify_event_t reply = {0};
    reply.response_type=XCB_SELECTION_NOTIFY; reply.time=e->time; reply.requestor=e->requestor;
    reply.selection=e->selection; reply.target=e->target;
    xcb_atom_t p = e->property ? e->property : e->target;
    if (q.clip && e->target == q.targets) {
        xcb_atom_t ts[] = {q.targets,q.utf8};
        xcb_change_property(q.c,XCB_PROP_MODE_REPLACE,e->requestor,p,XCB_ATOM_ATOM,32,2,ts); reply.property=p;
    } else if (q.clip && e->target == q.utf8) {
        xcb_change_property(q.c,XCB_PROP_MODE_REPLACE,e->requestor,p,e->target,8,strlen(q.clip),q.clip); reply.property=p;
    }
    xcb_send_event(q.c,0,e->requestor,0,(char *)&reply);
}
static void events(void) {
    xcb_generic_event_t *ev;
    while ((ev=xcb_poll_for_event(q.c))) {
        switch (ev->response_type & 127) {
        case XCB_CLIENT_MESSAGE: {
            const uint32_t *d=((xcb_client_message_event_t *)ev)->data.data32;
            if (d[0] == q.wm_delete) event(1,0,0,0);
            else if (d[0] == q.wm_sync && q.counter) {
                q.sync_value=(xcb_sync_int64_t){(int32_t)d[3], d[2]}; q.sync_pending=true;
            }
            break;
        }
        case XCB_DESTROY_NOTIFY: event(1,0,0,0); break;
        case XCB_CONFIGURE_NOTIFY: {
            xcb_configure_notify_event_t *e=(void *)ev;
            if (q.sync_pending) q.sync_configured=true;
            if (e->width != q.w || e->height != q.h) {
                unsigned w=e->width, h=e->height;
                if (w < 320*q.scale) w=320*q.scale;
                if (h < 480*q.scale) h=480*q.scale;
                if (w > 4096*q.scale) w=4096*q.scale;
                if (h > 2160*q.scale) h=2160*q.scale;
                w=w/q.scale*q.scale; h=h/q.scale*q.scale;
                if (w != e->width || h != e->height) { uint32_t v[]={w,h}; xcb_configure_window(q.c,q.win,XCB_CONFIG_WINDOW_WIDTH|XCB_CONFIG_WINDOW_HEIGHT,v); }
                q.w=w; q.h=h; buffer(); event(13,w/q.scale,h/q.scale,0);
            }
            break;
        }
        case XCB_KEY_PRESS: key((void *)ev); break;
        case XCB_MAPPING_NOTIFY: keys(); break;
        case XCB_FOCUS_OUT: q.down=false; break;
        case XCB_BUTTON_PRESS: {
            xcb_button_press_event_t *e=(void *)ev;
            unsigned x=(e->event_x < 0 ? 0 : e->event_x)/q.scale, y=(e->event_y < 0 ? 0 : e->event_y)/q.scale;
            if (e->detail == 4 || e->detail == 5) event(14,x,y,e->detail == 4 ? 1 : 0);
            if (e->detail == 1) { q.down=true; q.moved=false; q.dx=x; q.dy=y; event(10,x,y,0); }
            if (e->detail == 3) event(3,x,y,0);
            break;
        }
        case XCB_MOTION_NOTIFY: {
            xcb_motion_notify_event_t *e=(void *)ev;
            unsigned x=(e->event_x < 0 ? 0 : e->event_x)/q.scale, y=(e->event_y < 0 ? 0 : e->event_y)/q.scale;
            if (q.down && (abs((int)x-q.dx)>3 || abs((int)y-q.dy)>3)) q.moved=true;
            event(9,x,y,q.down); break;
        }
        case XCB_BUTTON_RELEASE: {
            xcb_button_release_event_t *e=(void *)ev;
            unsigned x=(e->event_x < 0 ? 0 : e->event_x)/q.scale, y=(e->event_y < 0 ? 0 : e->event_y)/q.scale;
            if (e->detail == 1) { if (q.down && !q.moved) event(2,x,y,0); event(11,x,y,0); q.down=false; }
            break;
        }
        case XCB_SELECTION_REQUEST: selection((void *)ev); break;
        case XCB_SELECTION_CLEAR: free(q.clip); q.clip=NULL; break;
        case XCB_SELECTION_NOTIFY: {
            xcb_selection_notify_event_t *e=(void *)ev;
            if (e->property == q.property) {
                xcb_get_property_reply_t *r=xcb_get_property_reply(q.c,xcb_get_property(q.c,1,q.win,q.property,q.utf8,0,16384),NULL);
                if (r && r->type == q.utf8 && r->format == 8 && !r->bytes_after)
                    replace(xcb_get_property_value(r),xcb_get_property_value_length(r));
                free(r);
            }
            break;
        }
        default: break;
        }
        free(ev);
    }
    if (xcb_connection_has_error(q.c)) event(1,0,0,0);
}
static lean_obj_res words(const uint32_t *v, size_t n) {
    lean_object *a=lean_mk_empty_array_with_capacity(lean_box(n));
    for (size_t i=0;i<n;i++) a=lean_array_push(a,lean_box_uint32(v[i]));
    return lean_io_result_mk_ok(a);
}
static void pixel(uint8_t *dst, const uint8_t *src) {
    dst[0]=src[2]; dst[1]=src[1]; dst[2]=src[0]; dst[3]=0;
}
lean_obj_res lq_screen(void) { init(); uint32_t v[]={q.w/q.scale,q.h/q.scale,0,0,160}; return words(v,5); }
lean_obj_res lq_desktop_frame(b_lean_obj_arg rows) {
    init(); memset(q.pixels,0,q.bytes);
    size_t h=lean_array_size(rows);
    for (unsigned y=0;y<q.h;y++) {
        if (y/q.scale >= h) continue;
        lean_object *row=lean_array_get_core(rows,y/q.scale);
        const uint8_t *p=lean_sarray_cptr(row); size_t w=lean_sarray_size(row)/4;
        for (unsigned x=0;x<q.w;x++) {
            if (x/q.scale >= w) continue;
            size_t i=((size_t)y*q.w+x)*4, j=(x/q.scale)*4;
            pixel(q.pixels+i,p+j);
        }
    }
    if (q.shm) {
        xcb_shm_put_image(q.c,q.win,q.gc,q.w,q.h,0,0,q.w,q.h,0,0,q.screen->root_depth,XCB_IMAGE_FORMAT_Z_PIXMAP,0,q.seg,0);
    } else {
        unsigned max=xcb_get_maximum_request_length(q.c)*4-128;
        unsigned chunk=max/(q.w*4); if (!chunk) fail("X request too small for a row");
        for (unsigned y=0;y<q.h;y+=chunk) {
            unsigned n=q.h-y < chunk ? q.h-y : chunk;
            xcb_put_image(q.c,XCB_IMAGE_FORMAT_Z_PIXMAP,q.win,q.gc,q.w,n,0,y,0,q.screen->root_depth,n*q.w*4,q.pixels+(size_t)y*q.w*4);
        }
    }
    /* The window manager's request is answered by the first frame shown
       after its configure: the one Lean painted at that size. */
    if (q.sync_pending && q.sync_configured) {
        xcb_sync_set_counter(q.c,q.counter,q.sync_value); q.sync_pending=q.sync_configured=false;
    }
    /* A round trip fences the shared segment before the next CPU write. */
    free(xcb_get_input_focus_reply(q.c,xcb_get_input_focus(q.c),NULL));
    struct pollfd fd={xcb_get_file_descriptor(q.c),POLLIN,0}; poll(&fd,1,16);
    events(); xcb_flush(q.c);
    lean_obj_res out=words(q.events,q.n); q.n=0; return out;
}
lean_obj_res lq_frame(b_lean_obj_arg list,uint32_t b,uint32_t over,b_lean_obj_arg top,
    b_lean_obj_arg bot,uint8_t pin,b_lean_obj_arg placement,b_lean_obj_arg hold) {
    (void)b; (void)over; (void)pin;
    init(); lq_slide_thread_init(); lq_slide_warm();
    uint32_t p[LQ_PLACEMENT_WORDS];
    for (unsigned i=0;i<LQ_PLACEMENT_WORDS;i++) p[i]=lean_unbox_uint32(lean_array_get_core(placement,i));
    unsigned h=q.h/q.scale;
    lean_object *rows=lean_mk_empty_array_with_capacity(lean_box(h));
    lean_object *layers[]={list,top,bot};
    for (unsigned y=0;y<h;y++) {
        lean_object *row=NULL;
        if (y>=p[7] && y<p[10]) {
            int64_t r=(int64_t)lq_slide_source(p[22],p[15],p[20],p[21],(int32_t)q.scroll,y);
            if (r>=0 && (uint64_t)r<lean_array_size(list)) row=lean_array_get_core(list,r);
            else {
                uint32_t f=lq_slide_fill_row(p[22],p[15],p[7],p[10],(int32_t)q.scroll,y);
                if (f<lean_array_size(hold)) row=lean_array_get_core(hold,f);
            }
        }
        for (unsigned k=1;k<3;k++) {
            uint32_t *r=p+4*k;
            if (y>=r[2] && y<r[3] && r[0]+y-r[2]<lean_array_size(layers[k]))
                row=lean_array_get_core(layers[k],r[0]+y-r[2]);
        }
        if (row) lean_inc(row); else row=lean_alloc_sarray(1,0,0);
        rows=lean_array_push(rows,row);
    }
    lean_object *result=lq_desktop_frame(rows); lean_dec(rows);
    // The desktop loop uses desktopFrame directly. Keep its phone-frame
    // adapter compatible too: desktop click events expand to raw samples.
    lean_object *raw=lean_io_result_get_value(result), *out=lean_mk_empty_array();
    struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts);
    uint64_t now=(uint64_t)ts.tv_sec*1000+ts.tv_nsec/1000000;
    for (size_t i=0;i+3<lean_array_size(raw);i+=4) {
        uint32_t k=lean_unbox_uint32(lean_array_get_core(raw,i));
        if (k!=1 && k!=2 && k!=3 && k!=4 && k!=5) continue;
        uint32_t x=lean_unbox_uint32(lean_array_get_core(raw,i+1));
        uint32_t y=lean_unbox_uint32(lean_array_get_core(raw,i+2));
        unsigned n=(k==2 || k==3) ? 2 : 1;
        for (unsigned j=0;j<n;j++) {
            uint64_t t=j==0 && n==2 ? now-(k==3 ? 500 : 30) : now;
            uint32_t v[8]={n==2 ? (j==0 ? 9 : 11) : k,k==5 ? 4 : 0,
                n==2 ? x : 0,n==2 ? y : 0,(uint32_t)t,(uint32_t)(t>>32),p[16],
                lq_slide_delta(p[22],p[15],(int32_t)q.scroll)};
            for (unsigned z=0;z<8;z++) out=lean_array_push(out,lean_box_uint32(v[z]));
        }
    }
    lean_dec(result); return lean_io_result_mk_ok(out);
}
lean_obj_res lq_scroll(uint32_t ch,uint32_t vh) { q.content=ch; q.view=vh; return lean_io_result_mk_ok(lean_box_float(q.scroll)); }
lean_obj_res lq_scroll_by(double d) { q.scroll+=d; return unit(); }
lean_obj_res lq_scroll_to(double b) { q.scroll=b; return unit(); }
lean_obj_res lq_motion(b_lean_obj_arg samples) { (void)samples; return unit(); }
lean_obj_res lq_text(void) {
    lean_object *p=lean_alloc_ctor(0,2,0), *a=lean_mk_empty_array();
    uint32_t v[]={count(q.anchor),count(q.caret),count(q.caret),count(q.caret)};
    for (int i=0;i<4;i++) a=lean_array_push(a,lean_box_uint32(v[i]));
    lean_ctor_set(p,0,lean_mk_string(q.text)); lean_ctor_set(p,1,a); return lean_io_result_mk_ok(p);
}
lean_obj_res lq_desktop_select(uint32_t a,uint32_t b) { q.anchor=byte_at(a); q.caret=byte_at(b); q.focused=true; event(4,0,0,0); return unit(); }
lean_obj_res lq_ime(uint8_t on) { q.focused=on; return unit(); }
/* The field becomes the string the app edits; one that already holds it
   is left alone, caret included, so the app's own echo changes nothing. */
lean_obj_res lq_set_text(b_lean_obj_arg s) {
    const char *t=lean_string_cstr(s);
    if (strcmp(t,q.text)) { snprintf(q.text,sizeof q.text,"%s",t); q.anchor=q.caret=strlen(q.text); }
    return unit();
}
lean_obj_res lq_copy(b_lean_obj_arg s) { init(); copy(lean_string_cstr(s),strlen(lean_string_cstr(s))); return unit(); }
lean_obj_res lq_ctl_poll(void) { return lean_io_result_mk_ok(lean_mk_empty_array()); }
lean_obj_res lq_ctl_reply(b_lean_obj_arg s) { puts(lean_string_cstr(s)); fflush(stdout); return unit(); }
lean_obj_res lq_scan(uint8_t on) { (void)on; return unit(); }
lean_obj_res lq_luma(void) { lean_object *p=lean_alloc_ctor(0,2,0); lean_ctor_set(p,0,lean_mk_empty_array()); lean_ctor_set(p,1,lean_alloc_sarray(1,0,0)); return lean_io_result_mk_ok(p); }
lean_obj_res lq_now_us(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts); return lean_io_result_mk_ok(lean_box_uint64((uint64_t)ts.tv_sec*1000000+ts.tv_nsec/1000)); }
lean_obj_res lq_tz_min(void) { time_t t=time(NULL); struct tm tm; localtime_r(&t,&tm); return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(int32_t)(tm.tm_gmtoff/60))); }
lean_obj_res lq_log(b_lean_obj_arg s) { fprintf(stderr,"%s\n",lean_string_cstr(s)); return unit(); }

/* Lifecycle polling shares the Linux frame's event pump. */
lean_obj_res lq_poll(void) { return lean_io_result_mk_ok(lean_mk_empty_array()); }
lean_obj_res lq_links(void) { return lean_io_result_mk_ok(lean_mk_empty_array()); }

/* Lean owns appearance; X11 has no mobile status/navigation bars. */
lean_obj_res lq_appearance(uint8_t dark, uint32_t background) {
    (void)dark; (void)background; return lean_io_result_mk_ok(lean_box(0));
}
