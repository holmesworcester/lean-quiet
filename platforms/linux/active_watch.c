/* What a window manager hears of activation requests: every
   _NET_ACTIVE_WINDOW client message sent to the root window, one line each,
   "active WINDOW SOURCE". Runs until killed. Usage: active_watch. */
#include <xcb/xcb.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(void) {
    xcb_connection_t *c = xcb_connect(NULL, NULL);
    if (xcb_connection_has_error(c)) { fprintf(stderr, "active_watch: no display\n"); return 2; }
    xcb_window_t root = xcb_setup_roots_iterator(xcb_get_setup(c)).data->root;
    const char *name = "_NET_ACTIVE_WINDOW";
    xcb_intern_atom_reply_t *a = xcb_intern_atom_reply(c, xcb_intern_atom(c, 0, strlen(name), name), NULL);
    if (!a) return 2;
    uint32_t mask = XCB_EVENT_MASK_SUBSTRUCTURE_NOTIFY;
    xcb_change_window_attributes(c, root, XCB_CW_EVENT_MASK, &mask);
    xcb_flush(c);
    printf("ready\n"); fflush(stdout);
    xcb_generic_event_t *e;
    while ((e = xcb_wait_for_event(c))) {
        xcb_client_message_event_t *m = (void *)e;
        if ((e->response_type & 127) == XCB_CLIENT_MESSAGE && m->type == a->atom) {
            printf("active 0x%x %u\n", m->window, m->data.data32[0]); fflush(stdout);
        }
        free(e);
    }
    return 0;
}
