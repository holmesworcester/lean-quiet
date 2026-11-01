/* Call the production shell; only window availability and input pressure are
   controlled by this fixture. The publication code is not duplicated. */
#include "../../platforms/linux/shell.c"
lean_obj_res lq_test_desktop_visible(uint8_t visible) {
    init();
    if (visible) xcb_map_window(q.c,q.win); else xcb_unmap_window(q.c,q.win);
    xcb_flush(q.c);
    free(xcb_get_input_focus_reply(q.c,xcb_get_input_focus(q.c),NULL));
    events();
    return unit();
}
lean_obj_res lq_test_desktop_full_input(void) {
    q.n=4096;
    for (unsigned i=0;i<4096;i+=4) { q.events[i]=9; q.events[i+1]=q.events[i+2]=q.events[i+3]=0; }
    return unit();
}

lean_obj_res lq_test_desktop_valid_gc(uint8_t valid) {
    static xcb_gcontext_t saved;
    if (valid) q.gc=saved; else { saved=q.gc; q.gc=0; }
    return unit();
}

lean_obj_res lq_test_desktop_unmap_queued(void) {
    xcb_unmap_window(q.c,q.win); xcb_flush(q.c);
    free(xcb_get_input_focus_reply(q.c,xcb_get_input_focus(q.c),NULL));
    return lq_test_desktop_full_input();
}
