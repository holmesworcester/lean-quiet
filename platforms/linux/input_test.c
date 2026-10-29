/* Exercise the native editor and pixel conversion without an X server. */
#include "shell.c"
#include <assert.h>

static unsigned checks;
#define CHECK(p) do { assert(p); checks++; } while (0)

static void press(uint32_t sym, uint16_t state) {
    xcb_get_keyboard_mapping_keysyms(q.keys)[0]=sym;
    xcb_key_press_event_t e={0}; e.detail=8; e.state=state; key(&e);
}

int main(void) {
    q.focused=true; q.min_key=8;
    q.keys=calloc(1,sizeof(*q.keys)+8); q.keys->keysyms_per_keycode=2;
    replace("a\xc3\xa9\xf0\x9f\x8c\xb1",7);
    CHECK(count(q.caret)==3);
    CHECK(prev(q.caret)==3);
    CHECK(byte_at(2)==3);
    press(XK_Left,0); CHECK(q.caret==3 && q.anchor==3);
    press(XK_BackSpace,0); CHECK(strcmp(q.text,"a\xf0\x9f\x8c\xb1")==0);
    press(XK_Delete,0); CHECK(strcmp(q.text,"a")==0);
    press(XK_Home,0); CHECK(q.caret==0);
    press(XK_End,XCB_MOD_MASK_SHIFT); CHECK(q.anchor==0 && q.caret==1);
    replace("hello",5); CHECK(strcmp(q.text,"hello")==0);
    press('a',XCB_MOD_MASK_CONTROL); CHECK(q.anchor==0 && q.caret==5);
    replace("x",1); CHECK(strcmp(q.text,"x")==0);
    press(0x01004e2d,0); CHECK(strcmp(q.text,"x\xe4\xb8\xad")==0);
    press(XK_Return,XCB_MOD_MASK_SHIFT); CHECK(q.text[strlen(q.text)-1]=='\n');
    q.n=0; press(XK_Return,0); CHECK(q.n==4 && q.events[0]==5);
    size_t len=strlen(q.text);
    press(0x01a1,0); CHECK(strlen(q.text)==len);
    replace("\xff",1); CHECK(strlen(q.text)==len);
    replace("\xed\xa0\x80",3); CHECK(strlen(q.text)==len);
    replace("\xf0\x80\x80\x80",4); CHECK(strlen(q.text)==len);
    replace("a\0b",3); CHECK(strlen(q.text)==len);
    q.focused=false; press('z',0); CHECK(strlen(q.text)==len);
    /* Application zoom must work outside the native editor and must not
       insert +/-/0 into the draft. Test all accepted keyboard forms. */
    for (unsigned i=0;i<7;i++) {
        uint32_t symbols[]={XK_equal,XK_plus,XK_KP_Add,XK_minus,XK_KP_Subtract,XK_0,XK_KP_0};
        unsigned directions[]={1,1,1,2,2,0,0};
        q.n=0; q.down=true;
        press(symbols[i],XCB_MOD_MASK_CONTROL);
        CHECK(q.n==4 && q.events[0]==15 && q.events[1]==directions[i]);
        CHECK(!q.down && strlen(q.text)==len);
    }
    q.n=0; press(XK_minus,0); CHECK(q.n==0);
    /* The event-pump boundary protects focus and buffer ownership. Motion
       and text snapshots can coalesce; UI transitions and sends cannot. */
    const unsigned transitions[]={2,3,5,10,12,13,15};
    for (unsigned i=0;i<sizeof(transitions)/sizeof(*transitions);i++) {
        q.n=0; q.handoff=false; event(transitions[i],0,0,0);
        CHECK(q.handoff && q.events[0]==transitions[i]);
    }
    for (unsigned i=0;i<2;i++) {
        q.n=0; q.handoff=false; event(i==0 ? 4 : 9,0,0,0); CHECK(!q.handoff);
    }
    uint8_t src[]={118,71,199,255}, dst[4]; pixel(dst,src);
    CHECK(dst[0]==199 && dst[1]==71 && dst[2]==118 && dst[3]==0);
    free(q.keys);
    printf("native input: %u checks\n",checks);
    return 0;
}
