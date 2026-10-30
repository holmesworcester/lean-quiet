// AppKit supplies a window, OS text input and clipboard. The shared
// platforms.desktop.Main loop owns layout, queries, painting and actions.
#import <Cocoa/Cocoa.h>
#include <lean/lean.h>
#include <pthread.h>
#include <signal.h>
#include <time.h>
#include <unistd.h>

static NSWindow *window;
static NSBitmapImageRep *bitmap;
static NSImage *picture;
static NSMutableArray<NSNumber *> *events;
static double offset;
static bool focused, dragging, moved, snapshot;
static NSPoint downPoint;
static uint32_t width=1100, height=760, cursor;
static CGFloat backingScale=1;
static dispatch_source_t snapshotSource;
static int appArgc;
static char **appArgv;
int lean_app_main(int argc, char **argv);

static lean_obj_res unit(void) { return lean_io_result_mk_ok(lean_box(0)); }
static void onMain(dispatch_block_t f) {
  if (NSThread.isMainThread) f(); else dispatch_sync(dispatch_get_main_queue(), f);
}
static void event(uint32_t kind, uint32_t x, uint32_t y, uint32_t z) {
  if (getenv("QUIET_NATIVE_TRACE") && kind!=9)
    fprintf(stderr,"native event %u %u %u %u focused %d bounds %.0f %.0f\n",kind,x,y,z,focused,window.contentView.bounds.origin.x,window.contentView.bounds.origin.y);
  [events addObjectsFromArray:@[@(kind),@(x),@(y),@(z)]];
}
static lean_obj_res words(const uint32_t *v, size_t n) {
  lean_object *a=lean_mk_empty_array_with_capacity(lean_box(n));
  for (size_t i=0;i<n;i++) a=lean_array_push(a,lean_box_uint32(v[i]));
  return lean_io_result_mk_ok(a);
}
// Lean indices count Unicode scalars; Cocoa selection uses UTF-16 units.
static NSUInteger utf16(NSString *s, uint32_t scalar) {
  NSUInteger i=0;
  while (i<s.length && scalar--) {
    unichar c=[s characterAtIndex:i++];
    if (CFStringIsSurrogateHighCharacter(c) && i<s.length &&
        CFStringIsSurrogateLowCharacter([s characterAtIndex:i])) i++;
  }
  return i;
}
static uint32_t scalars(NSString *s, NSUInteger end) {
  uint32_t n=0;
  for (NSUInteger i=0;i<MIN(end,s.length);i++,n++) {
    if (CFStringIsSurrogateHighCharacter([s characterAtIndex:i]) && i+1<end &&
        CFStringIsSurrogateLowCharacter([s characterAtIndex:i+1])) i++;
  }
  return n;
}

@interface QuietView : NSTextView <NSTextViewDelegate>
@end
static QuietView *view;
@implementation QuietView
- (BOOL)isFlipped { return YES; }
- (BOOL)acceptsFirstResponder { return YES; }
- (void)drawInsertionPointInRect:(NSRect)r color:(NSColor*)c turnedOn:(BOOL)on {
  // Lean paints the composer caret at its actual desktop position.
}
- (void)resetCursorRects {
  [self addCursorRect:self.bounds cursor:(cursor==2?NSCursor.IBeamCursor:cursor==1?NSCursor.pointingHandCursor:NSCursor.arrowCursor)];
}
- (void)drawRect:(NSRect)dirty {
  if (picture) [picture drawInRect:self.bounds fromRect:NSZeroRect
    operation:NSCompositingOperationCopy fraction:1 respectFlipped:YES hints:nil];
}
- (void)updateTrackingAreas {
  for (NSTrackingArea *a in self.trackingAreas) [self removeTrackingArea:a];
  [self addTrackingArea:[[NSTrackingArea alloc] initWithRect:self.bounds
    options:NSTrackingMouseMoved|NSTrackingMouseEnteredAndExited|NSTrackingActiveInKeyWindow|NSTrackingInVisibleRect
    owner:self userInfo:nil]];
  [super updateTrackingAreas];
}
- (NSPoint)point:(NSEvent*)e {
  NSPoint p=[self convertPoint:e.locationInWindow fromView:nil];
  // This is a flipped view: convertPointToBacking uses a lower-left
  // backing origin. The Lean seam needs top-left device-pixel distances.
  p.x*=backingScale; p.y*=backingScale;
  p.x=MAX(0,MIN(width-1,p.x)); p.y=MAX(0,MIN(height-1,p.y)); return p;
}
- (void)mouseDown:(NSEvent*)e {
  [window makeFirstResponder:self]; downPoint=[self point:e]; dragging=true; moved=false;
  event(10,downPoint.x,downPoint.y,0);
}
- (void)mouseDragged:(NSEvent*)e {
  NSPoint p=[self point:e];
  moved |= fabs(p.x-downPoint.x)+fabs(p.y-downPoint.y)>3;
  event(9,p.x,p.y,1);
}
- (void)mouseUp:(NSEvent*)e {
  NSPoint p=[self point:e]; event(11,p.x,p.y,0); dragging=false;
  if (!moved) event(2,p.x,p.y,0);
}
- (void)rightMouseDown:(NSEvent*)e { NSPoint p=[self point:e]; event(3,p.x,p.y,0); }
- (void)mouseMoved:(NSEvent*)e { NSPoint p=[self point:e]; event(9,p.x,p.y,0); }
- (void)mouseExited:(NSEvent*)e { event(16,0,0,0); }
- (void)scrollWheel:(NSEvent*)e {
  NSPoint p=[self point:e];
  unsigned steps=MAX(1,MIN(8,(unsigned)ceil(fabs(e.scrollingDeltaY)/4)));
  for (unsigned i=0;i<steps;i++) event(14,p.x,p.y,e.scrollingDeltaY>0?1:0);
}
- (void)keyDown:(NSEvent*)e {
  NSString *key=e.charactersIgnoringModifiers;
  if (e.modifierFlags & NSEventModifierFlagCommand) {
    if ([key isEqual:@"+"] || [key isEqual:@"="]) { event(15,1,0,0); return; }
    if ([key isEqual:@"-"]) { event(15,2,0,0); return; }
    if ([key isEqual:@"0"]) { event(15,0,0,0); return; }
  }
  if (e.keyCode==53) { event(12,0,0,0); return; }
  if (focused) [super keyDown:e];
}
- (BOOL)performKeyEquivalent:(NSEvent*)e {
  if (!(e.modifierFlags & NSEventModifierFlagCommand)) return [super performKeyEquivalent:e];
  NSString *k=e.charactersIgnoringModifiers.lowercaseString;
  if ([k isEqual:@"q"]) { event(1,0,0,0); return YES; }
  if ([k isEqual:@"a"] && focused) { [self selectAll:nil]; event(4,0,0,0); return YES; }
  if ([k isEqual:@"c"]) { [self copy:nil]; return YES; }
  if ([k isEqual:@"x"] && focused) { [self cut:nil]; return YES; }
  if ([k isEqual:@"v"] && focused) { [self paste:nil]; return YES; }
  if ([@[@"+",@"=",@"-",@"0"] containsObject:k]) { [self keyDown:e]; return YES; }
  return [super performKeyEquivalent:e];
}
- (BOOL)textView:(NSTextView*)t doCommandBySelector:(SEL)sel {
  if (sel==@selector(insertNewline:)) {
    if (NSApp.currentEvent.modifierFlags & NSEventModifierFlagShift) return NO;
    event(5,0,0,0); return YES;
  }
  return NO;
}
- (void)textDidChange:(NSNotification*)note { event(4,0,0,0); }
- (void)textViewDidChangeSelection:(NSNotification*)note {
  if (focused) event(4,0,0,0);
}
@end

@interface QuietDelegate : NSObject <NSApplicationDelegate, NSWindowDelegate>
@end
@implementation QuietDelegate
- (BOOL)applicationShouldTerminateAfterLastWindowClosed:(NSApplication*)app { return YES; }
- (NSApplicationTerminateReply)applicationShouldTerminate:(NSApplication*)app {
  event(1,0,0,0); return NSTerminateCancel;
}
- (BOOL)windowShouldClose:(NSWindow*)w { event(1,0,0,0); return NO; }
- (void)windowDidResize:(NSNotification*)n {
  backingScale=window.backingScaleFactor;
  width=(uint32_t)lround(view.bounds.size.width*backingScale);
  height=(uint32_t)lround(view.bounds.size.height*backingScale);
  event(17,(uint32_t)lround(160*backingScale),0,0);
  event(13,width,height,0);
}
- (void)windowDidChangeBackingProperties:(NSNotification*)n { [self windowDidResize:n]; }
- (void)windowDidResignKey:(NSNotification*)n { event(16,0,0,1); }
@end

static void *runLean(void *arg) { lean_app_main(appArgc,appArgv); return NULL; }
int main(int argc,char **argv) {
  @autoreleasepool {
    appArgc=argc; appArgv=argv;
    events=[NSMutableArray new];
    [NSApplication sharedApplication];
    [NSApp setActivationPolicy:NSApplicationActivationPolicyRegular];
    QuietDelegate *delegate=[QuietDelegate new]; NSApp.delegate=delegate;
    window=[[NSWindow alloc] initWithContentRect:NSMakeRect(80,80,width,height)
      styleMask:NSWindowStyleMaskTitled|NSWindowStyleMaskClosable|NSWindowStyleMaskResizable|NSWindowStyleMaskMiniaturizable
      backing:NSBackingStoreBuffered defer:NO];
    window.title=@"Lean Quiet"; window.delegate=delegate; window.contentMinSize=NSMakeSize(320,480);
    window.contentMaxSize=NSMakeSize(4096,2160);
    view=[[QuietView alloc] initWithFrame:NSMakeRect(0,0,width,height)];
    view.delegate=view; view.richText=NO; view.automaticQuoteSubstitutionEnabled=NO;
    view.automaticDashSubstitutionEnabled=NO; view.automaticTextReplacementEnabled=NO;
    view.textContainerInset=NSZeroSize; view.drawsBackground=NO;
    window.contentView=view; [window makeFirstResponder:view];
    [delegate windowDidResize:nil];
    [window makeKeyAndOrderFront:nil]; [NSApp activateIgnoringOtherApps:YES];
    NSString *resources=NSBundle.mainBundle.resourcePath;
    if (resources && [[NSFileManager defaultManager] fileExistsAtPath:[resources stringByAppendingPathComponent:@"assets"]])
      chdir(resources.fileSystemRepresentation);
    if (!getenv("QUIET_DB")) {
      NSString *data=[NSSearchPathForDirectoriesInDomains(NSApplicationSupportDirectory,NSUserDomainMask,YES)[0]
        stringByAppendingPathComponent:@"LeanQuietDesktop"];
      [NSFileManager.defaultManager createDirectoryAtPath:data withIntermediateDirectories:YES attributes:nil error:NULL];
      setenv("QUIET_DB",[[data stringByAppendingPathComponent:@"quiet.db"] UTF8String],1);
    }
    // Snapshot only this app's final pixels, with no screen-capture privilege.
    if (getenv("QUIET_SNAPSHOT")) {
      signal(SIGUSR1,SIG_IGN);
      snapshotSource=dispatch_source_create(DISPATCH_SOURCE_TYPE_SIGNAL,SIGUSR1,0,dispatch_get_main_queue());
      dispatch_source_set_event_handler(snapshotSource,^{ snapshot=true; });
      dispatch_resume(snapshotSource);
    }
    setenv("LEAN_STACK_SIZE_KB","65536",0);
    pthread_t thread; pthread_attr_t attr; pthread_attr_init(&attr);
    pthread_attr_setstacksize(&attr,64<<20); pthread_create(&thread,&attr,runLean,NULL); pthread_attr_destroy(&attr);
    [NSApp run];
  }
  return 0;
}

lean_obj_res lq_screen(void) {
  __block uint32_t w,h,dark,dpi;
  onMain(^{ w=width; h=height; dpi=(uint32_t)lround(160*backingScale); dark=[view.effectiveAppearance.name containsString:@"Dark"]?1:0; });
  uint32_t v[]={w,h,0,0,dpi,dark}; return words(v,6);
}
lean_obj_res lq_desktop_frame(b_lean_obj_arg rows) {
  onMain(^{
    NSUInteger h=lean_array_size(rows), w=h?lean_sarray_size(lean_array_get_core(rows,0))/4:0;
    if (w && h) {
      bitmap=[[NSBitmapImageRep alloc] initWithBitmapDataPlanes:NULL pixelsWide:w pixelsHigh:h
        bitsPerSample:8 samplesPerPixel:4 hasAlpha:YES isPlanar:NO colorSpaceName:NSDeviceRGBColorSpace
        bitmapFormat:0 bytesPerRow:w*4 bitsPerPixel:32];
      for (NSUInteger y=0;y<h;y++) {
        lean_object *r=lean_array_get_core(rows,y); NSUInteger n=MIN(w,lean_sarray_size(r)/4);
        uint8_t *dst=bitmap.bitmapData+y*bitmap.bytesPerRow;
        memcpy(dst,lean_sarray_cptr(r),n*4);
        for (NSUInteger x=0;x<w;x++) dst[4*x+3]=255;
      }
      picture=[[NSImage alloc] initWithSize:NSMakeSize(w/backingScale,h/backingScale)]; [picture addRepresentation:bitmap];
      [view setNeedsDisplay:YES];
      if (snapshot) {
        snapshot=false;
        [[bitmap representationUsingType:NSBitmapImageFileTypePNG properties:@{}]
          writeToFile:[NSString stringWithUTF8String:getenv("QUIET_SNAPSHOT")] atomically:YES];
      }
    }
  });
  // Lean controls the frame rate; NSApp continues pumping native events.
  usleep(16000);
  __block NSArray<NSNumber*> *batch;
  onMain(^{ batch=[events copy]; [events removeAllObjects]; });
  size_t n=batch.count; uint32_t *v=malloc(n*sizeof(uint32_t));
  for (size_t i=0;i<n;i++) v[i]=batch[i].unsignedIntValue;
  lean_obj_res out=words(v,n); free(v); return out;
}
lean_obj_res lq_desktop_cursor(uint32_t kind) {
  onMain(^{ if (cursor!=kind) { cursor=kind; [window invalidateCursorRectsForView:view]; [(kind==2?NSCursor.IBeamCursor:kind==1?NSCursor.pointingHandCursor:NSCursor.arrowCursor) set]; } });
  return unit();
}
lean_obj_res lq_desktop_select(uint32_t a,uint32_t b) {
  onMain(^{ NSUInteger x=utf16(view.string,a),y=utf16(view.string,b); focused=true;
    view.selectedRange=NSMakeRange(MIN(x,y),MAX(x,y)-MIN(x,y)); event(4,0,0,0); });
  return unit();
}
lean_obj_res lq_text(void) {
  __block NSString *text; __block NSRange r, marked;
  onMain(^{ text=[view.string copy]; r=view.selectedRange; marked=view.markedRange; });
  uint32_t c=scalars(text,r.location+r.length);
  uint32_t v[]={scalars(text,r.location),c,c,c};
  if (marked.location!=NSNotFound) { v[2]=scalars(text,marked.location); v[3]=scalars(text,NSMaxRange(marked)); }
  lean_object *a=lean_mk_empty_array(); for(unsigned i=0;i<4;i++) a=lean_array_push(a,lean_box_uint32(v[i]));
  lean_object *p=lean_alloc_ctor(0,2,0); lean_ctor_set(p,0,lean_mk_string(text.UTF8String)); lean_ctor_set(p,1,a);
  return lean_io_result_mk_ok(p);
}
lean_obj_res lq_set_text(b_lean_obj_arg s) {
  NSString *text=[NSString stringWithUTF8String:lean_string_cstr(s)];
  onMain(^{ if (![view.string isEqual:text]) { view.string=text; view.selectedRange=NSMakeRange(text.length,0); } }); return unit();
}
lean_obj_res lq_ime(uint8_t show) { onMain(^{focused=show;}); return unit(); }
lean_obj_res lq_copy(b_lean_obj_arg s) {
  NSString *text=[NSString stringWithUTF8String:lean_string_cstr(s)];
  onMain(^{[NSPasteboard.generalPasteboard clearContents]; [NSPasteboard.generalPasteboard setString:text forType:NSPasteboardTypeString];});return unit();
}
lean_obj_res lq_scroll(uint32_t content,uint32_t viewport) { return lean_io_result_mk_ok(lean_box_float(offset)); }
lean_obj_res lq_scroll_by(double delta) { offset+=delta;return unit(); }
lean_obj_res lq_scroll_to(double value) { offset=value;return unit(); }
lean_obj_res lq_frame(b_lean_obj_arg list,uint32_t b,uint32_t over,b_lean_obj_arg top,b_lean_obj_arg bot,uint8_t pin,b_lean_obj_arg placement,b_lean_obj_arg hold) {
  // DesktopMain intercepts App's layer publications; the desktop picture
  // is the sole publication to this shell.
  return words(NULL,0);
}
lean_obj_res lq_ctl_poll(void) { return words(NULL,0); }
lean_obj_res lq_ctl_reply(b_lean_obj_arg s) { fprintf(stderr,"%s\n",lean_string_cstr(s));return unit(); }
lean_obj_res lq_poll(void) { return words(NULL,0); }
lean_obj_res lq_links(void) { return words(NULL,0); }
lean_obj_res lq_motion(b_lean_obj_arg a) { return unit(); }
lean_obj_res lq_scan(uint8_t on) { return unit(); }
static lean_obj_res emptyPair(void) {
  lean_object *p=lean_alloc_ctor(0,2,0); lean_ctor_set(p,0,lean_mk_empty_array());
  lean_ctor_set(p,1,lean_alloc_sarray(1,0,0));return lean_io_result_mk_ok(p);
}
lean_obj_res lq_luma(void) { return emptyPair(); }
lean_obj_res lq_pick_photo(uint32_t token) { return lean_io_result_mk_ok(lean_box(0)); }
lean_obj_res lq_photo_result(void) { return emptyPair(); }
lean_obj_res lq_appearance(uint8_t dark,uint32_t background) { return unit(); }
lean_obj_res lq_bars(uint32_t top,uint32_t bottom,uint8_t lightTop,uint8_t lightBottom) { return unit(); }
lean_obj_res lq_now_us(void) { struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return lean_io_result_mk_ok(lean_box_uint64((uint64_t)t.tv_sec*1000000+t.tv_nsec/1000)); }
lean_obj_res lq_tz_min(void) { time_t t=time(NULL);struct tm tm;localtime_r(&t,&tm);return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(int32_t)(tm.tm_gmtoff/60))); }
lean_obj_res lq_log(b_lean_obj_arg s) { fprintf(stderr,"%s\n",lean_string_cstr(s));return unit(); }
