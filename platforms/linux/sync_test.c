/* What a window manager does when it resizes the window under
   _NET_WM_SYNC_REQUEST: ask for a counter value, resize, and wait for the
   app to set its counter to that value (it does so after showing the
   frame at the new size). Usage: sync_test WINDOW WIDTH HEIGHT VALUE.
   Exits 0 once the counter holds VALUE, 1 if it does not within 5 s. */
#include <xcb/xcb.h>
#include <xcb/sync.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static xcb_atom_t atom(xcb_connection_t *c, const char *s) {
    xcb_intern_atom_reply_t *r = xcb_intern_atom_reply(c, xcb_intern_atom(c, 0, strlen(s), s), NULL);
    xcb_atom_t a = r ? r->atom : XCB_NONE; free(r); return a;
}

int main(int argc, char **argv) {
    if (argc != 5) { fprintf(stderr, "usage: sync_test WINDOW WIDTH HEIGHT VALUE\n"); return 2; }
    xcb_window_t win = (xcb_window_t)strtoul(argv[1], NULL, 0);
    uint32_t size[2] = {(uint32_t)atoi(argv[2]), (uint32_t)atoi(argv[3])};
    uint32_t want = (uint32_t)strtoul(argv[4], NULL, 0);
    xcb_connection_t *c = xcb_connect(NULL, NULL);
    if (xcb_connection_has_error(c)) { fprintf(stderr, "sync_test: no display\n"); return 2; }
    free(xcb_sync_initialize_reply(c, xcb_sync_initialize(c, 3, 1), NULL));
    xcb_get_property_reply_t *p = xcb_get_property_reply(c,
        xcb_get_property(c, 0, win, atom(c, "_NET_WM_SYNC_REQUEST_COUNTER"), XCB_ATOM_CARDINAL, 0, 1), NULL);
    if (!p || xcb_get_property_value_length(p) != 4) { fprintf(stderr, "sync_test: no counter\n"); return 1; }
    xcb_sync_counter_t counter = *(uint32_t *)xcb_get_property_value(p); free(p);
    xcb_client_message_event_t ev = {0};
    ev.response_type = XCB_CLIENT_MESSAGE; ev.format = 32; ev.window = win;
    ev.type = atom(c, "WM_PROTOCOLS");
    ev.data.data32[0] = atom(c, "_NET_WM_SYNC_REQUEST");
    ev.data.data32[1] = XCB_CURRENT_TIME;
    ev.data.data32[2] = want; ev.data.data32[3] = 0;
    xcb_send_event(c, 0, win, XCB_EVENT_MASK_NO_EVENT, (const char *)&ev);
    xcb_configure_window(c, win, XCB_CONFIG_WINDOW_WIDTH | XCB_CONFIG_WINDOW_HEIGHT, size);
    xcb_flush(c);
    for (int i = 0; i < 500; i++) {
        xcb_sync_query_counter_reply_t *r = xcb_sync_query_counter_reply(c, xcb_sync_query_counter(c, counter), NULL);
        uint32_t lo = r ? r->counter_value.lo : 0; int32_t hi = r ? r->counter_value.hi : 0; free(r);
        if (hi == 0 && lo == want) { printf("sync_test: counter %u after the resize\n", lo); return 0; }
        nanosleep(&(struct timespec){0, 10000000}, NULL);
    }
    fprintf(stderr, "sync_test: counter never reached %u\n", want);
    return 1;
}
