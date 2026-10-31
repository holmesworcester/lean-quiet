#ifndef LQ_WINDOWS_INPUT_H
#define LQ_WINDOWS_INPUT_H
#include <stdint.h>
/* Lean indices count Unicode scalar values and LF, Win32 uses UTF-16 and CRLF. */
static unsigned lq_scalar_at(const uint16_t *s,unsigned pos) {
    unsigned n=0;
    for(unsigned i=0;s[i]&&i<pos;i++) {
        if(s[i]=='\r'&&s[i+1]=='\n') continue;
        if(s[i]>=0xDC00&&s[i]<=0xDFFF&&i&&s[i-1]>=0xD800&&s[i-1]<=0xDBFF) continue;
        n++;
    } return n;
}
static unsigned lq_utf16_at(const uint16_t *s,unsigned pos) {
    unsigned i=0,n=0;
    while(s[i]&&n<pos) {
        if(s[i]=='\r'&&s[i+1]=='\n') i++;
        if(s[i]>=0xD800&&s[i]<=0xDBFF&&s[i+1]>=0xDC00&&s[i+1]<=0xDFFF) i++;
        i++; n++;
    } return i;
}
#endif
