#include "input.h"
#include <assert.h>
#include <stdio.h>
int main(void) {
    /* The text actually passed between Win32's editor and the Lean composer:
       accent, Hebrew, CRLF, astral emoji, Japanese, LF and a trailing character. */
    const uint16_t s[]={'a',0xe9,0x5e9,'\r','\n',0xd83d,0xde42,0x65e5,'\n','z',0};
    const unsigned positions[]={0,1,2,3,5,7,8,9,10};
    for(unsigned i=0;i<sizeof(positions)/sizeof(*positions);i++) {
        assert(lq_utf16_at(s,i)==positions[i]);
        assert(lq_scalar_at(s,positions[i])==i);
    }
    assert(lq_utf16_at(s,10000)==10);
    assert(lq_scalar_at(s,10000)==8);
    const uint16_t lone[]={'\r','x',0};
    assert(lq_scalar_at(lone,2)==2);
    assert(lq_utf16_at(lone,1)==1);
    const uint16_t empty[]={0};
    assert(lq_utf16_at(empty,2)==0);
    assert(lq_scalar_at(empty,2)==0);
    puts("Windows editor: UTF-16/LF caret and selection boundaries pass");
}
