/* Win32 only owns the window, Unicode editor, clipboard and presentation.
   All application state, networking, layout and pixels come from Lean. */
#define UNICODE
#define _UNICODE
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <windowsx.h>
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static struct {
    HWND win, edit;
    WNDPROC editProc;
    uint32_t events[4096]; size_t n;
    unsigned w,h,dpi,fw,fh,cursor;
    uint8_t *pixels;
    BOOL focused, muted, handoff, down, moved, systemDark;
    int dx,dy,wheel;
    double scroll;
} q;
static lean_obj_res unit(void) { return lean_io_result_mk_ok(lean_box(0)); }
static void event(uint32_t k,uint32_t a,uint32_t b,uint32_t c) {
    if(getenv("QUIET_INPUT_TRACE")) fprintf(stderr,"event %u %u %u %u down=%d moved=%d origin=%d,%d\n",k,a,b,c,q.down,q.moved,q.dx,q.dy);
    if(q.n+4>4096) { fprintf(stderr,"Windows input queue overflow\n"); abort(); }
    q.events[q.n++]=k; q.events[q.n++]=a; q.events[q.n++]=b; q.events[q.n++]=c;
    if(k==1||k==2||k==3||k==5||k==10||k==12||k==13||k==15||k==17) q.handoff=TRUE;
}
static lean_obj_res words(const uint32_t *v,size_t n) {
    lean_object *a=lean_mk_empty_array();
    for(size_t i=0;i<n;i++) a=lean_array_push(a,lean_box_uint32(v[i]));
    return lean_io_result_mk_ok(a);
}
static wchar_t *wide(const char *s) {
    int n=MultiByteToWideChar(CP_UTF8,MB_ERR_INVALID_CHARS,s,-1,NULL,0);
    wchar_t *w=calloc(n?n:1,sizeof(wchar_t));
    if(n) MultiByteToWideChar(CP_UTF8,MB_ERR_INVALID_CHARS,s,-1,w,n);
    return w;
}
static char *utf8(const wchar_t *w) {
    int n=WideCharToMultiByte(CP_UTF8,0,w,-1,NULL,0,NULL,NULL);
    char *s=calloc(n?n:1,1);
    if(n) WideCharToMultiByte(CP_UTF8,0,w,-1,s,n,NULL,NULL);
    return s;
}
static wchar_t *editor(void) {
    int n=GetWindowTextLengthW(q.edit);
    wchar_t *s=calloc(n+1,sizeof(wchar_t)); GetWindowTextW(q.edit,s,n+1); return s;
}
#include "input.h"
static BOOL shortcut(UINT key) {
    if(!(GetKeyState(VK_CONTROL)&0x8000)) return FALSE;
    if(key==VK_OEM_PLUS||key==VK_ADD) event(15,1,0,0);
    else if(key==VK_OEM_MINUS||key==VK_SUBTRACT) event(15,2,0,0);
    else if(key=='0'||key==VK_NUMPAD0) event(15,0,0,0);
    else return FALSE;
    return TRUE;
}
static LRESULT CALLBACK edit_proc(HWND w,UINT m,WPARAM a,LPARAM b) {
    if(m==WM_KEYDOWN) {
        if(shortcut((UINT)a)) return 0;
        if(a==VK_ESCAPE) { event(12,0,0,0); return 0; }
        if(a==VK_RETURN&&!(GetKeyState(VK_SHIFT)&0x8000)) { event(5,0,0,0); return 0; }
        if(a=='A'&&(GetKeyState(VK_CONTROL)&0x8000)) { SendMessageW(w,EM_SETSEL,0,-1); event(4,0,0,0); return 0; }
    }
    if(m==WM_CHAR&&(GetKeyState(VK_CONTROL)&0x8000)&&(a=='='||a=='+'||a=='-'||a=='0')) return 0;
    if(m==WM_CHAR&&((a=='\r'&&!(GetKeyState(VK_SHIFT)&0x8000))||a==27)) return 0;
    LRESULT r=CallWindowProcW(q.editProc,w,m,a,b);
    if(m==WM_KEYUP||m==WM_LBUTTONUP) event(4,0,0,0);
    return r;
}
static void paint(HDC dc) {
    if(!q.pixels) return;
    BITMAPINFO bi={0}; bi.bmiHeader.biSize=sizeof(BITMAPINFOHEADER);
    bi.bmiHeader.biWidth=q.fw; bi.bmiHeader.biHeight=-(LONG)q.fh;
    bi.bmiHeader.biPlanes=1; bi.bmiHeader.biBitCount=32; bi.bmiHeader.biCompression=BI_RGB;
    /* Keep the last complete frame while the shared renderer settles a resize. */
    StretchDIBits(dc,0,0,q.w,q.h,0,0,q.fw,q.fh,q.pixels,&bi,DIB_RGB_COLORS,SRCCOPY);
}
static BOOL system_dark(void) {
    DWORD light=1, size=sizeof(light);
    return RegGetValueW(HKEY_CURRENT_USER,L"Software\\Microsoft\\Windows\\CurrentVersion\\Themes\\Personalize",
        L"AppsUseLightTheme",RRF_RT_REG_DWORD,NULL,&light,&size)==ERROR_SUCCESS && light==0;
}
static LRESULT CALLBACK window_proc(HWND w,UINT m,WPARAM a,LPARAM b) {
    int x=GET_X_LPARAM(b), y=GET_Y_LPARAM(b);
    switch(m) {
    case WM_SETTINGCHANGE: case WM_THEMECHANGED: q.systemDark=system_dark(); return 0;
    case WM_CLOSE: EndMenu(); event(1,0,0,0); return 0;
    case WM_ERASEBKGND: return 1;
    case WM_PAINT: { PAINTSTRUCT ps; HDC dc=BeginPaint(w,&ps); paint(dc); EndPaint(w,&ps); return 0; }
    case WM_GETMINMAXINFO: ((MINMAXINFO*)b)->ptMinTrackSize=(POINT){336,519}; return 0;
    case WM_SIZE:
        if(a!=SIZE_MINIMIZED&&LOWORD(b)&&HIWORD(b)) {
            q.w=LOWORD(b); q.h=HIWORD(b); event(13,q.w,q.h,0);
        } return 0;
    case WM_DPICHANGED: {
        q.dpi=HIWORD(a); RECT *r=(RECT*)b;
        event(17,q.dpi*160/96,0,0);
        SetWindowPos(w,NULL,r->left,r->top,r->right-r->left,r->bottom-r->top,SWP_NOZORDER|SWP_NOACTIVATE); return 0;
    }
    case WM_COMMAND:
        if((HWND)b==q.edit&&HIWORD(a)==EN_CHANGE&&!q.muted) event(4,0,0,0);
        return 0;
    case WM_SETFOCUS: if(q.focused) SetFocus(q.edit); return 0;
    case WM_ACTIVATE:
        if(LOWORD(a)==WA_INACTIVE) { q.down=FALSE; ReleaseCapture(); event(16,0,0,1); }
        return 0;
    case WM_KEYDOWN: if(shortcut((UINT)a)) return 0; if(a==VK_ESCAPE) event(12,0,0,0); return 0;
    case WM_LBUTTONDOWN:
        SetFocus(q.focused?q.edit:w); SetCapture(w); q.down=TRUE; q.moved=FALSE; q.dx=x;q.dy=y;
        event(10,x,y,0); return 0;
    case WM_LBUTTONUP:
        ReleaseCapture(); if(q.down&&!q.moved) event(2,x,y,0);
        q.down=FALSE; event(11,x,y,0); return 0;
    case WM_RBUTTONUP: event(3,x,y,0); return 0;
    case WM_MOUSEMOVE: {
        TRACKMOUSEEVENT t={sizeof(t),TME_LEAVE,w,0}; TrackMouseEvent(&t);
        if(q.down&&(abs(x-q.dx)>3||abs(y-q.dy)>3)) q.moved=TRUE;
        event(9,x<0?0:x,y<0?0:y,q.down); return 0;
    }
    case WM_MOUSELEAVE: event(16,0,0,0); return 0;
    case WM_MOUSEWHEEL: {
        POINT p={x,y}; ScreenToClient(w,&p); q.wheel+=GET_WHEEL_DELTA_WPARAM(a);
        while(abs(q.wheel)>=WHEEL_DELTA) {
            int up=q.wheel>0; event(14,p.x<0?0:p.x,p.y<0?0:p.y,up?1:0);
            q.wheel+=up?-WHEEL_DELTA:WHEEL_DELTA;
        } return 0;
    }
    case WM_SETCURSOR:
        if(LOWORD(b)==HTCLIENT) { SetCursor(LoadCursorW(NULL,q.cursor==1?IDC_HAND:q.cursor==2?IDC_IBEAM:IDC_ARROW)); return TRUE; }
        break;
    }
    return DefWindowProcW(w,m,a,b);
}
static void init(void) {
    if(q.win) return;
    SetProcessDpiAwarenessContext(DPI_AWARENESS_CONTEXT_PER_MONITOR_AWARE_V2);
    wchar_t exe[32768]; GetModuleFileNameW(NULL,exe,32768);
    wchar_t *slash=wcsrchr(exe,L'\\'); if(slash) { *slash=0; SetCurrentDirectoryW(exe); }
    if(!getenv("QUIET_DB")) {
        wchar_t path[32768]; DWORD n=GetEnvironmentVariableW(L"LOCALAPPDATA",path,32000);
        if(!n||n>=32000) abort(); wcscat(path,L"\\LeanQuiet"); CreateDirectoryW(path,NULL);
        wcscat(path,L"\\quiet.db"); char *s=utf8(path); _putenv_s("QUIET_DB",s); free(s);
    }
    WNDCLASSW cls={0}; cls.lpfnWndProc=window_proc; cls.hInstance=GetModuleHandleW(NULL);
    cls.lpszClassName=L"LeanQuietWindow"; cls.hCursor=LoadCursorW(NULL,IDC_ARROW);
    RegisterClassW(&cls);
    q.w=1000; q.h=760; q.dpi=96; q.systemDark=system_dark();
    RECT r={0,0,q.w,q.h}; AdjustWindowRectEx(&r,WS_OVERLAPPEDWINDOW,FALSE,0);
    q.win=CreateWindowExW(0,cls.lpszClassName,L"Lean Quiet",WS_OVERLAPPEDWINDOW,
        CW_USEDEFAULT,CW_USEDEFAULT,r.right-r.left,r.bottom-r.top,NULL,NULL,cls.hInstance,NULL);
    if(!q.win) abort(); q.dpi=GetDpiForWindow(q.win);
    q.edit=CreateWindowExW(0,L"EDIT",L"",WS_CHILD|WS_VISIBLE|ES_MULTILINE|ES_AUTOVSCROLL|ES_AUTOHSCROLL|ES_WANTRETURN,
        -2,-2,1,1,q.win,(HMENU)1,cls.hInstance,NULL);
    SendMessageW(q.edit,EM_SETLIMITTEXT,65535,0);
    q.editProc=(WNDPROC)SetWindowLongPtrW(q.edit,GWLP_WNDPROC,(LONG_PTR)edit_proc);
    q.n=0; q.handoff=FALSE; ShowWindow(q.win,SW_SHOW); UpdateWindow(q.win);
}
lean_obj_res lq_screen(void) { init(); uint32_t v[]={q.w,q.h,0,0,q.dpi*160/96,q.systemDark}; return words(v,6); }
lean_obj_res lq_desktop_frame(b_lean_obj_arg rows) {
    init(); size_t h=lean_array_size(rows),w=h?lean_sarray_size(lean_array_get_core(rows,0))/4:0;
    if(w&&h) {
        if(w!=q.fw||h!=q.fh) { free(q.pixels); q.pixels=calloc(w*h,4); q.fw=w;q.fh=h; }
        for(size_t y=0;y<h;y++) {
            lean_object *row=lean_array_get_core(rows,y); size_t n=lean_sarray_size(row)/4;
            const uint8_t *p=lean_sarray_cptr(row);
            for(size_t x=0;x<w;x++) { uint8_t *d=q.pixels+4*(y*w+x);
                if(x<n) { d[0]=p[x*4+2];d[1]=p[x*4+1];d[2]=p[x*4];d[3]=0; }
                else memset(d,0,4);
            }
        }
        HDC dc=GetDC(q.win); paint(dc); ReleaseDC(q.win,dc);
    }
    q.handoff=FALSE;
    MsgWaitForMultipleObjects(0,NULL,FALSE,16,QS_ALLINPUT);
    MSG msg;
    while(!q.handoff&&q.n<4080&&PeekMessageW(&msg,NULL,0,0,PM_REMOVE)) {
        if(msg.message==WM_QUIT) { event(1,0,0,0); break; }
        TranslateMessage(&msg); DispatchMessageW(&msg);
    }
    lean_object *out=words(q.events,q.n); q.n=0; return out;
}
lean_obj_res lq_text(void) {
    wchar_t *w=editor(); DWORD a=0,b=0; SendMessageW(q.edit,EM_GETSEL,(WPARAM)&a,(LPARAM)&b);
    uint32_t v[]={lq_scalar_at((const uint16_t*)w,a),lq_scalar_at((const uint16_t*)w,b),lq_scalar_at((const uint16_t*)w,b),lq_scalar_at((const uint16_t*)w,b)};
    size_t j=0; for(size_t i=0;w[i];i++) if(!(w[i]=='\r'&&w[i+1]=='\n')) w[j++]=w[i]; w[j]=0;
    char *s=utf8(w); free(w);
    lean_object *p=lean_alloc_ctor(0,2,0), *arr=lean_mk_empty_array();
    for(int i=0;i<4;i++) arr=lean_array_push(arr,lean_box_uint32(v[i]));
    lean_ctor_set(p,0,lean_mk_string(s)); lean_ctor_set(p,1,arr); free(s);
    return lean_io_result_mk_ok(p);
}
lean_obj_res lq_set_text(b_lean_obj_arg s) {
    wchar_t *w=wide(lean_string_cstr(s)); size_t n=wcslen(w),j=0;
    wchar_t *native=calloc(2*n+1,sizeof(wchar_t));
    for(size_t i=0;i<n;i++) { if(w[i]=='\n'&&(i==0||w[i-1]!='\r')) native[j++]='\r'; native[j++]=w[i]; }
    q.muted=TRUE; SetWindowTextW(q.edit,native); SendMessageW(q.edit,EM_SETSEL,j,j); q.muted=FALSE;
    free(w);free(native);return unit();
}
lean_obj_res lq_desktop_select(uint32_t a,uint32_t b) {
    wchar_t *w=editor(); SendMessageW(q.edit,EM_SETSEL,lq_utf16_at((const uint16_t*)w,a),lq_utf16_at((const uint16_t*)w,b));free(w);
    q.focused=TRUE; SetFocus(q.edit);event(4,0,0,0);return unit();
}
lean_obj_res lq_ime(uint8_t on) { q.focused=on; SetFocus(on?q.edit:q.win); return unit(); }
lean_obj_res lq_desktop_cursor(uint32_t kind) {
    q.cursor=kind; POINT p; GetCursorPos(&p); ScreenToClient(q.win,&p);
    if(p.x>=0&&p.y>=0&&(unsigned)p.x<q.w&&(unsigned)p.y<q.h)
        SetCursor(LoadCursorW(NULL,kind==1?IDC_HAND:kind==2?IDC_IBEAM:IDC_ARROW));
    return unit();
}
lean_obj_res lq_copy(b_lean_obj_arg s) {
    wchar_t *w=wide(lean_string_cstr(s)); size_t n=(wcslen(w)+1)*sizeof(wchar_t);
    if(OpenClipboard(q.win)) { HGLOBAL h=GlobalAlloc(GMEM_MOVEABLE,n);
        if(h) { void *p=GlobalLock(h); if(p) { memcpy(p,w,n);GlobalUnlock(h);EmptyClipboard();if(!SetClipboardData(CF_UNICODETEXT,h))GlobalFree(h); } else GlobalFree(h); }
        CloseClipboard();
    } free(w);return unit();
}
lean_obj_res lq_scroll(uint32_t ch,uint32_t vh) { (void)ch;(void)vh;return lean_io_result_mk_ok(lean_box_float(q.scroll)); }
lean_obj_res lq_scroll_by(double d) { q.scroll+=d; return unit(); }
lean_obj_res lq_scroll_to(double b) { q.scroll=b; return unit(); }
lean_obj_res lq_motion(b_lean_obj_arg a) { (void)a;return unit(); }
lean_obj_res lq_frame(b_lean_obj_arg l,uint32_t b,uint32_t o,b_lean_obj_arg t,b_lean_obj_arg bot,uint8_t pin,b_lean_obj_arg p,b_lean_obj_arg h) {
    (void)l;(void)b;(void)o;(void)t;(void)bot;(void)pin;(void)p;(void)h;return words(NULL,0);
}
lean_obj_res lq_ctl_poll(void) { return words(NULL,0); }
lean_obj_res lq_ctl_reply(b_lean_obj_arg s) { (void)s;return unit(); }
lean_obj_res lq_scan(uint8_t on) { (void)on;return unit(); }
lean_obj_res lq_luma(void) {
    lean_object *p=lean_alloc_ctor(0,2,0);lean_ctor_set(p,0,lean_mk_empty_array());lean_ctor_set(p,1,lean_alloc_sarray(1,0,0));return lean_io_result_mk_ok(p);
}
lean_obj_res lq_pick_photo(uint32_t token) { (void)token;return lean_io_result_mk_ok(lean_box(0)); }
lean_obj_res lq_photo_result(void) { return lq_luma(); }
lean_obj_res lq_now_us(void) { LARGE_INTEGER n,f;QueryPerformanceCounter(&n);QueryPerformanceFrequency(&f);return lean_io_result_mk_ok(lean_box_uint64(n.QuadPart/f.QuadPart*1000000+(n.QuadPart%f.QuadPart)*1000000/f.QuadPart)); }
lean_obj_res lq_tz_min(void) { TIME_ZONE_INFORMATION t; DWORD state=GetTimeZoneInformation(&t); LONG bias=t.Bias+(state==TIME_ZONE_ID_DAYLIGHT?t.DaylightBias:state==TIME_ZONE_ID_STANDARD?t.StandardBias:0);return lean_io_result_mk_ok(lean_box_uint32((uint32_t)-bias)); }
lean_obj_res lq_log(b_lean_obj_arg s) { fprintf(stderr,"%s\n",lean_string_cstr(s));return unit(); }
lean_obj_res lq_poll(void) { return words(NULL,0); }
lean_obj_res lq_links(void) { return words(NULL,0); }
lean_obj_res lq_appearance(uint8_t dark,uint32_t bg) { (void)dark;(void)bg;return unit(); }
lean_obj_res lq_bars(uint32_t t,uint32_t b,uint8_t lt,uint8_t lb) { (void)t;(void)b;(void)lt;(void)lb;return unit(); }
lean_obj_res lq_desktop_native_scroll(void) { return lean_io_result_mk_ok(lean_box(0)); }
lean_obj_res lq_desktop_layers(b_lean_obj_arg l,b_lean_obj_arg h,b_lean_obj_arg p,b_lean_obj_arg v) { (void)l;(void)h;(void)p;(void)v;return unit(); }
