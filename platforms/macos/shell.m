// AppKit supplies a window, OS text input and clipboard. The shared
// platforms.desktop.Main loop owns layout, queries, painting and actions.
#import <Cocoa/Cocoa.h>
#import <QuartzCore/QuartzCore.h>
#include "../native/thread.h"
#include <stdatomic.h>
#include <lean/lean.h>
#include <pthread.h>
#include <signal.h>
#include <time.h>
#include <unistd.h>

static NSWindow *window;
static NSImage *picture;
static NSMutableArray<NSNumber *> *events, *rawEvents;
static _Atomic double offset, pendingBy, pendingTo;
static _Atomic bool pendingJump;
static bool nativeActive, synchronizing;
static _Atomic bool nativeSupported;
static uint32_t scrollMeta[6], scrollPlacement[LQ_PLACEMENT_WORDS];
// Pending planes are owned by the Lean thread; only a complete root
// publication transfers their geometry/dimensions to the AppKit thread.
static uint32_t nextMeta[6], nextPlacement[LQ_PLACEMENT_WORDS];
static bool nextLayers, nextListChanged, nextHoldChanged;
static uint32_t shownListWidth, shownPlaneHeights[2];
static unsigned presentations, scrollUpdates, rawTouches;
static NSView *document;
static CALayer *desktopLayer, *listLayer, *holdLayer, *overlayLayer;
@class ConversationScroll;
static ConversationScroll *conversationScroll;
static CGImageRef overlayImage, shownRootImage;
typedef struct {
  lean_object *rows;
  CGImageRef image;
  const uint8_t *pixels;
  uint32_t w,h;
} PixelPlane;
static PixelPlane rootPlane, listPlane, holdPlane;
static void createNativeScroll(void);
static void translateNative(void);
static void nativeScrollTo(double value, bool stop);
static void writeScrollStats(void);
static void saveSnapshot(void);
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
- (void)viewDidEndLiveResize {
  [super viewDidEndLiveResize];
  [self setNeedsDisplay:YES];
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

// Only the list gets native scrolling. The sidebar, header, toolbar and
// composer are siblings painted in the fixed root view.
@interface ConversationDocument : NSView
@property BOOL rawTouch;
@property BOOL ignoreTouch;
@end
@interface ConversationScroll : NSScrollView
@property BOOL rejectMomentum;
- (void)boundsChanged:(NSNotification*)notification;
@end
@implementation ConversationDocument
- (BOOL)isFlipped { return YES; }
- (BOOL)acceptsFirstResponder { return NO; }
- (void)sample:(NSEvent*)e phase:(uint32_t)phase longPress:(BOOL)held {
  NSPoint point=[view point:e];
  struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts);
  uint64_t time=(uint64_t)ts.tv_sec*1000+ts.tv_nsec/1000000;
  if (held && phase==0) time-=600;
  int32_t slide=(int32_t)lq_slide_delta(scrollPlacement[22],scrollPlacement[15],(int32_t)llround(atomic_load(&offset)));
  uint32_t words[8]={9+phase,0,(uint32_t)MAX(0,point.x-scrollMeta[1]),(uint32_t)point.y,
    (uint32_t)time,(uint32_t)(time>>32),scrollPlacement[16],(uint32_t)slide};
  for (unsigned i=0;i<8;i++) [rawEvents addObject:@(words[i])];
  rawTouches++;
}
- (void)mouseDown:(NSEvent*)e {
  conversationScroll.rejectMomentum=YES;
  NSPoint point=[view point:e];
  self.ignoreTouch=(int64_t)lq_slide_source(scrollPlacement[22],scrollPlacement[15],scrollPlacement[20],
    scrollPlacement[21],(uint32_t)(int32_t)llround(atomic_load(&offset)),point.y)<0;
  if (self.ignoreTouch) return; // A hold tile is not an actionable message.
  self.rawTouch=fabs(atomic_load(&offset)-scrollPlacement[15])>.5;
  if (self.rawTouch) {
    [window makeFirstResponder:view];
    [self sample:e phase:0 longPress:NO];
  } else [view mouseDown:e];
}
- (void)mouseDragged:(NSEvent*)e {
  if (self.ignoreTouch) return;
  if (self.rawTouch) [self sample:e phase:1 longPress:NO]; else [view mouseDragged:e];
}
- (void)mouseUp:(NSEvent*)e {
  if (self.ignoreTouch) { self.ignoreTouch=NO; return; }
  if (self.rawTouch) [self sample:e phase:2 longPress:NO]; else [view mouseUp:e];
  self.rawTouch=NO;
}
- (void)rightMouseDown:(NSEvent*)e {
  conversationScroll.rejectMomentum=YES;
  if (fabs(atomic_load(&offset)-scrollPlacement[15])>.5) {
    [self sample:e phase:0 longPress:YES]; [self sample:e phase:2 longPress:NO];
  } else [view rightMouseDown:e];
}
- (void)mouseMoved:(NSEvent*)e { [view mouseMoved:e]; }
- (void)scrollWheel:(NSEvent*)e { [conversationScroll scrollWheel:e]; }
@end
@implementation ConversationScroll
- (void)scrollWheel:(NSEvent*)e {
  if (getenv("QUIET_NATIVE_TRACE")) fprintf(stderr,"native wheel %.0f momentum %lu reject %d active %d sync %d\n",e.scrollingDeltaY,(unsigned long)e.momentumPhase,self.rejectMomentum,nativeActive,synchronizing);
  if (e.momentumPhase!=NSEventPhaseNone && self.rejectMomentum) return;
  if (e.momentumPhase==NSEventPhaseNone) self.rejectMomentum=NO;
  // AppKit supplies trackpad precision, momentum and rubber-banding.
  [super scrollWheel:e];
}
- (void)boundsChanged:(NSNotification*)notification {
  if (!nativeActive || synchronizing) return;
  double total=MAX(scrollMeta[4],scrollMeta[5]);
  atomic_store(&offset,total-scrollMeta[4]-self.contentView.bounds.origin.y*backingScale);
  scrollUpdates++;
  if (events.count<4096) event(19,0,0,0);
  translateNative(); writeScrollStats();
}
@end

static void createNativeScroll(void) {
  if (conversationScroll) return;
  conversationScroll=[[ConversationScroll alloc] initWithFrame:NSZeroRect];
  conversationScroll.hidden=YES; conversationScroll.wantsLayer=YES;
  conversationScroll.borderType=NSNoBorder;
  conversationScroll.drawsBackground=YES;
  conversationScroll.layer.masksToBounds=YES;
  conversationScroll.automaticallyAdjustsContentInsets=NO;
  conversationScroll.hasVerticalScroller=YES;
  conversationScroll.hasHorizontalScroller=NO;
  conversationScroll.scrollerStyle=NSScrollerStyleOverlay;
  conversationScroll.autohidesScrollers=YES;
  conversationScroll.horizontalScrollElasticity=NSScrollElasticityNone;
  document=[[ConversationDocument alloc] initWithFrame:NSZeroRect];
  document.wantsLayer=YES; document.layer.geometryFlipped=YES; document.layer.masksToBounds=NO;
  conversationScroll.documentView=document;
  conversationScroll.contentView.postsBoundsChangedNotifications=YES;
  [NSNotificationCenter.defaultCenter addObserver:conversationScroll selector:@selector(boundsChanged:)
    name:NSViewBoundsDidChangeNotification object:conversationScroll.contentView];
  holdLayer=[CALayer layer]; listLayer=[CALayer layer]; overlayLayer=[CALayer layer];
  for (CALayer *layer in @[holdLayer,listLayer,overlayLayer]) {
    layer.actions=@{@"contents":[NSNull null],@"position":[NSNull null],@"bounds":[NSNull null]};
    layer.contentsScale=backingScale; layer.contentsGravity=kCAGravityResize;
    [document.layer addSublayer:layer];
  }
  [view addSubview:conversationScroll];
}
static void nativeScrollTo(double value, bool stop) {
  atomic_store(&offset,value);
  if (!nativeActive) return;
  if (stop) conversationScroll.rejectMomentum=YES;
  bool previous=synchronizing; synchronizing=true;
  CGFloat maximum=MAX(0,(double)MAX(scrollMeta[4],scrollMeta[5])-scrollMeta[4]);
  CGFloat sample=MAX(0,MIN(maximum,value));
  [conversationScroll.contentView scrollToPoint:NSMakePoint(0,(maximum-sample)/backingScale)];
  [conversationScroll reflectScrolledClipView:conversationScroll.contentView];
  atomic_store(&offset,sample);
  synchronizing=previous;
  translateNative();
}
static void translateNative(void) {
  if (!nativeActive) return;
  lq_slide_thread_init();
  int32_t sample=(int32_t)llround(atomic_load(&offset));
  CGFloat origin=conversationScroll.contentView.bounds.origin.y;
  [CATransaction begin]; [CATransaction setDisableActions:YES];
  CALayer *planes[2]={listLayer,holdLayer};
  uint32_t heights[2]={shownPlaneHeights[0],shownPlaneHeights[1]};
  for (int i=0;i<2;i++) {
    uint32_t r[4]; lq_slide_rect(scrollPlacement,sample,i,r);
    CALayer *layer=planes[i];
    layer.hidden=r[1]<=r[0] || !heights[i];
    layer.contentsRect=CGRectMake(0,heights[i]?(double)r[0]/heights[i]:0,1,heights[i]?(double)(r[1]-r[0])/heights[i]:0);
    layer.frame=CGRectMake(0,origin+((double)r[2]-scrollMeta[2])/backingScale,
      shownListWidth/backingScale,(r[3]-r[2])/backingScale);
  }
  // The cached full desktop crop retains hover/actions at rest. During
  // movement the raw overscan and hold planes slide independently of Lean.
  double shift=(double)sample-scrollPlacement[15];
  overlayLayer.frame=CGRectMake(0,origin+shift/backingScale,scrollMeta[3]/backingScale,scrollMeta[4]/backingScale);
  overlayLayer.hidden=fabs(shift)>.5;
  [CATransaction commit];
}
static void saveSnapshot(void) {
  const char *path=getenv("QUIET_SNAPSHOT"); if (!path) return;
  // Read the existing backing layers before cacheDisplay forces drawRect.
  // A repainting screenshot alone could conceal a blank resize backing.
  if (getenv("QUIET_COMPOSITOR_SNAPSHOT")) {
    size_t w=lround(view.bounds.size.width*backingScale), h=lround(view.bounds.size.height*backingScale);
    CGColorSpaceRef colors=CGColorSpaceCreateWithName(kCGColorSpaceSRGB);
    CGContextRef ctx=CGBitmapContextCreate(NULL,w,h,8,w*4,colors,(CGBitmapInfo)kCGImageAlphaPremultipliedLast);
    CGColorSpaceRelease(colors);
    if (ctx) {
      CGContextTranslateCTM(ctx,0,h); CGContextScaleCTM(ctx,backingScale,-backingScale);
      [view.layer renderInContext:ctx];
      CGImageRef image=CGBitmapContextCreateImage(ctx);
      NSBitmapImageRep *rep=[[NSBitmapImageRep alloc] initWithCGImage:image];
      [[rep representationUsingType:NSBitmapImageFileTypePNG properties:@{}]
        writeToFile:[[NSString stringWithUTF8String:path] stringByAppendingString:@".backing.png"] atomically:YES];
      CGImageRelease(image); CGContextRelease(ctx);
    }
  }
  [view displayIfNeeded]; [CATransaction flush];
  NSBitmapImageRep *shot=[view bitmapImageRepForCachingDisplayInRect:view.bounds];
  [view cacheDisplayInRect:view.bounds toBitmapImageRep:shot];
  NSString *file=[NSString stringWithUTF8String:path];
  [[shot representationUsingType:NSBitmapImageFileTypePNG properties:@{}] writeToFile:file atomically:YES];
  // Capture the exact immutable publication used by the compositor too.
  // Async photo decode can replace a placeholder between two frames even
  // at the same offset; pixel checks must compare one publication epoch.
  // Use the same AppKit colour conversion as the composited snapshot.
  // Both captures run in one main-thread turn; no new publication can
  // intervene, and the temporary visibility change is never presented.
  [CATransaction begin]; [CATransaction setDisableActions:YES];
  BOOL hidden=conversationScroll.hidden; conversationScroll.hidden=YES;
  NSBitmapImageRep *source=[view bitmapImageRepForCachingDisplayInRect:view.bounds];
  [view cacheDisplayInRect:view.bounds toBitmapImageRep:source];
  conversationScroll.hidden=hidden;
  [CATransaction commit];
  [[source representationUsingType:NSBitmapImageFileTypePNG properties:@{}]
    writeToFile:[file stringByAppendingString:@".source.png"] atomically:YES];
  NSDictionary *meta=@{@"sample":@(llround(atomic_load(&offset))),@"base":@(scrollPlacement[15]),
    @"presentations":@(presentations),@"scrollUpdates":@(scrollUpdates),
    @"native":@(nativeActive),@"liveResize":@(view.inLiveResize),@"planeWidth":@(shownListWidth),@"textureWidth":@(listLayer.contents?CGImageGetWidth((__bridge CGImageRef)listLayer.contents):0),@"publicationSize":@[@(CGImageGetWidth(shownRootImage)),@(CGImageGetHeight(shownRootImage))],@"viewport":@[@(scrollMeta[1]),@(scrollMeta[2]),@(scrollMeta[3]),@(scrollMeta[4])]};
  [[NSJSONSerialization dataWithJSONObject:meta options:0 error:NULL] writeToFile:[file stringByAppendingString:@".json"] atomically:YES];
}

static void writeScrollStats(void) {
  const char *path=getenv("QUIET_NATIVE_SCROLL_STATS"); if (!path) return;
  NSString *text=[NSString stringWithFormat:@"presentations %u scrollUpdates %u offset %.0f native %d box %u %u %u %u base %u rawTouches %u liveResize %d\n",
    presentations,scrollUpdates,atomic_load(&offset),nativeActive,scrollMeta[1],scrollMeta[2],scrollMeta[3],scrollMeta[4],scrollPlacement[15],rawTouches,view.inLiveResize];
  [text writeToFile:[NSString stringWithUTF8String:path] atomically:YES encoding:NSUTF8StringEncoding error:NULL];
}

@interface QuietDelegate : NSObject <NSApplicationDelegate, NSWindowDelegate>
@end
@implementation QuietDelegate
- (BOOL)applicationShouldTerminateAfterLastWindowClosed:(NSApplication*)app { return YES; }
- (NSApplicationTerminateReply)applicationShouldTerminate:(NSApplication*)app {
  event(1,0,0,0); return NSTerminateCancel;
}
- (BOOL)windowShouldClose:(NSWindow*)w { event(1,0,0,0); return NO; }
- (void)windowDidResize:(NSNotification*)n {
  CGFloat scale=window.backingScaleFactor;
  bool densityChanged=scale!=backingScale;
  backingScale=scale;
  width=MAX(1,(uint32_t)lround(view.bounds.size.width*scale));
  height=MAX(1,(uint32_t)lround(view.bounds.size.height*scale));
  // Never cover the last complete desktop with a viewport from a different
  // size. Keep that desktop visible until a matching publication arrives.
  nativeActive=false; conversationScroll.hidden=YES;
  [CATransaction begin]; [CATransaction setDisableActions:YES];
  desktopLayer.frame=view.bounds; desktopLayer.contentsScale=scale;
  [CATransaction commit];
  [view setNeedsDisplay:YES];
  if (densityChanged) event(17,(uint32_t)lround(160*scale),0,0);
  // A drag may produce many sizes before Lean gets its next turn. Only
  // the latest consecutive size matters; preserve intervening user input.
  NSUInteger count=events.count;
  if (count>=4 && events[count-4].unsignedIntValue==13) {
    events[count-3]=@(width); events[count-2]=@(height);
  } else event(13,width,height,0);
  writeScrollStats();
}
- (void)windowDidChangeBackingProperties:(NSNotification*)n { [self windowDidResize:n]; }
- (void)windowDidResignKey:(NSNotification*)n { event(16,0,0,1); }
@end

static void *runLean(void *arg) { lean_app_main(appArgc,appArgv); return NULL; }
int main(int argc,char **argv) {
  @autoreleasepool {
    appArgc=argc; appArgv=argv;
    events=[NSMutableArray new]; rawEvents=[NSMutableArray new];
    [NSApplication sharedApplication];
    [NSApp setActivationPolicy:NSApplicationActivationPolicyRegular];
    QuietDelegate *delegate=[QuietDelegate new]; NSApp.delegate=delegate;
    window=[[NSWindow alloc] initWithContentRect:NSMakeRect(80,80,width,height)
      styleMask:NSWindowStyleMaskTitled|NSWindowStyleMaskClosable|NSWindowStyleMaskResizable|NSWindowStyleMaskMiniaturizable
      backing:NSBackingStoreBuffered defer:NO];
    window.title=@"Lean Quiet"; window.delegate=delegate; window.contentMinSize=NSMakeSize(320,480);
    window.contentMaxSize=NSMakeSize(4096,2160);
    view=[[QuietView alloc] initWithFrame:NSMakeRect(0,0,width,height)];
    view.wantsLayer=YES;
    view.layerContentsRedrawPolicy=NSViewLayerContentsRedrawDuringViewResize;
    // NSTextView owns transient text/layout backing. Keep the actual desktop
    // in an independent retained layer so AppKit cannot clear it on resize.
    desktopLayer=[CALayer layer];
    desktopLayer.actions=@{@"contents":[NSNull null],@"position":[NSNull null],@"bounds":[NSNull null]};
    desktopLayer.contentsGravity=kCAGravityResize;
    desktopLayer.frame=view.bounds;
    [view.layer insertSublayer:desktopLayer atIndex:0];
    view.delegate=view; view.richText=NO; view.automaticQuoteSubstitutionEnabled=NO;
    view.automaticDashSubstitutionEnabled=NO; view.automaticTextReplacementEnabled=NO;
    view.textContainerInset=NSZeroSize; view.drawsBackground=NO;
    window.contentView=view; [window makeFirstResponder:view];
    [delegate windowDidResize:[NSNotification notificationWithName:NSWindowDidResizeNotification object:window]];
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
      dispatch_source_set_event_handler(snapshotSource,^{ if (picture) saveSnapshot(); else snapshot=true; });
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
static void freePixels(void *info, const void *data, size_t size) { free((void*)data); }
// Copy on Lean's thread, not the AppKit event thread. Immutable CGImages
// retain their pixels while Core Animation uses them; unchanged planes
// keep the old image/texture instead of re-uploading the entire window.
static bool capturePlane(PixelPlane *plane, b_lean_obj_arg rows) {
  if (plane->rows==rows) return false;
  size_t h=lean_array_size(rows), w=h?lean_sarray_size(lean_array_get_core(rows,0))/4:0;
  if (!w || !h) return false;
  bool changed=w!=plane->w || h!=plane->h;
  if (!changed) {
    for (size_t y=0;y<h;y++) {
      lean_object *r=lean_array_get_core(rows,y);
      if (lean_sarray_size(r)!=w*4 || memcmp(plane->pixels+y*w*4,lean_sarray_cptr(r),w*4)) { changed=true;break; }
    }
  }
  lean_inc(rows); if (plane->rows) lean_dec(plane->rows); plane->rows=rows;
  if (!changed) return false;
  if (h>SIZE_MAX/(w*4)) abort();
  uint8_t *pixels=calloc(h,w*4); if (!pixels) abort();
  for (size_t y=0;y<h;y++) {
    lean_object *r=lean_array_get_core(rows,y);
    memcpy(pixels+y*w*4,lean_sarray_cptr(r),MIN(w*4,lean_sarray_size(r)));
  }
  CGDataProviderRef provider=CGDataProviderCreateWithData(NULL,pixels,w*h*4,freePixels);
  CGColorSpaceRef colors=CGColorSpaceCreateWithName(kCGColorSpaceSRGB);
  CGImageRef image=CGImageCreate(w,h,8,32,w*4,colors,(CGBitmapInfo)kCGImageAlphaPremultipliedLast,provider,NULL,false,kCGRenderingIntentDefault);
  CGColorSpaceRelease(colors); CGDataProviderRelease(provider);
  if (!image) abort();
  if (plane->image) CGImageRelease(plane->image);
  plane->image=image; plane->pixels=pixels; plane->w=w; plane->h=h;
  return true;
}

lean_obj_res lq_desktop_native_scroll(void) { bool on=getenv("QUIET_DISABLE_NATIVE_SCROLL")==NULL; atomic_store(&nativeSupported,on); return lean_io_result_mk_ok(lean_box(on)); }
lean_obj_res lq_desktop_layers(b_lean_obj_arg list,b_lean_obj_arg hold,b_lean_obj_arg placement,b_lean_obj_arg viewport) {
  uint32_t metaStorage[6]={0}, pStorage[LQ_PLACEMENT_WORDS]={0};
  uint32_t *meta=metaStorage,*p=pStorage;
  if (lean_array_size(viewport)==6) for(unsigned i=0;i<6;i++) meta[i]=lean_unbox_uint32(lean_array_get_core(viewport,i));
  if (lean_array_size(placement)>=LQ_PLACEMENT_WORDS) for(unsigned i=0;i<LQ_PLACEMENT_WORDS;i++) p[i]=lean_unbox_uint32(lean_array_get_core(placement,i));
  else meta[0]=0;
  bool listChanged=false,holdChanged=false;
  if (meta[0]) { lq_slide_warm();listChanged=capturePlane(&listPlane,list);holdChanged=capturePlane(&holdPlane,hold); }
  memcpy(nextMeta,meta,sizeof nextMeta); memcpy(nextPlacement,p,sizeof nextPlacement);
  nextListChanged=listChanged; nextHoldChanged=holdChanged; nextLayers=true;
  return unit();
}

static void publishNativeLayers(void) {
  if (!nextLayers) return;
  nextLayers=false;
  createNativeScroll();
  nativeActive=nextMeta[0] && listPlane.image && holdPlane.image &&
    !view.inLiveResize && rootPlane.w==width && rootPlane.h==height;
  conversationScroll.hidden=!nativeActive;
  memcpy(scrollMeta,nextMeta,sizeof scrollMeta); memcpy(scrollPlacement,nextPlacement,sizeof scrollPlacement);
  bool jump=atomic_exchange(&pendingJump,false);
  double saved=(jump?atomic_load(&pendingTo):atomic_load(&offset))+atomic_exchange(&pendingBy,0.0);
  // Capture changes can arrive while resize temporarily hides the viewport.
  // Install their textures now: the next identical publication will no longer
  // have its changed bit set, so skipping this would retain an old-size plane.
  if (nextListChanged) listLayer.contents=(__bridge id)listPlane.image;
  if (nextHoldChanged) holdLayer.contents=(__bridge id)holdPlane.image;
  if (!nativeActive) { atomic_store(&offset,saved); return; }
  synchronizing=true;
  const uint32_t *meta=scrollMeta;
  conversationScroll.frame=NSMakeRect(meta[1]/backingScale,meta[2]/backingScale,meta[3]/backingScale,meta[4]/backingScale);
  document.frame=NSMakeRect(0,0,meta[3]/backingScale,MAX(meta[4],meta[5])/backingScale);
  if (listPlane.pixels) conversationScroll.backgroundColor=[NSColor colorWithSRGBRed:listPlane.pixels[0]/255.0
    green:listPlane.pixels[1]/255.0 blue:listPlane.pixels[2]/255.0 alpha:1];
  shownListWidth=listPlane.w; shownPlaneHeights[0]=listPlane.h; shownPlaneHeights[1]=holdPlane.h;
  nativeScrollTo(saved,jump);
  synchronizing=false;
}

lean_obj_res lq_desktop_frame(b_lean_obj_arg rows) {
  bool changed=capturePlane(&rootPlane,rows);
  onMain(^{
    presentations++;
    [CATransaction begin]; [CATransaction setDisableActions:YES];
    publishNativeLayers();
    if (changed) {
      if (shownRootImage) CGImageRelease(shownRootImage);
      shownRootImage=CGImageRetain(rootPlane.image);
      desktopLayer.contents=(__bridge id)shownRootImage;
      desktopLayer.frame=view.bounds;
      desktopLayer.contentsScale=backingScale;
      picture=[[NSImage alloc] initWithCGImage:rootPlane.image size:NSMakeSize(rootPlane.w/backingScale,rootPlane.h/backingScale)];
      [view setNeedsDisplay:YES];
    }
    if (nativeActive) {
      CGRect rect=CGRectMake(scrollMeta[1],scrollMeta[2],scrollMeta[3],scrollMeta[4]);
      if (CGRectGetMaxX(rect)<=rootPlane.w && CGRectGetMaxY(rect)<=rootPlane.h) {
        CGImageRef crop=CGImageCreateWithImageInRect(rootPlane.image,rect);
        if (overlayImage) CGImageRelease(overlayImage);
        overlayImage=crop; overlayLayer.contents=(__bridge id)crop;
      }
      translateNative();
    }
    if (changed) [view displayIfNeeded];
    [CATransaction commit];
    if (snapshot) {
      snapshot=false;
      saveSnapshot();
    }
    writeScrollStats();
  });
  const char *delay=getenv("QUIET_LEAN_FRAME_DELAY_MS");
  usleep(delay?MIN(1000,MAX(0,atoi(delay)))*1000:16000);
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
lean_obj_res lq_scroll(uint32_t content,uint32_t viewport) { return lean_io_result_mk_ok(lean_box_float(atomic_load(&offset))); }
lean_obj_res lq_scroll_by(double delta) {
  // Height/anchor corrections land with the new document extent, so an
  // old NSClipView bound cannot clamp away a newly measured row's move.
  if (!atomic_load(&nativeSupported)) {
    double old=atomic_load(&offset);
    while (!atomic_compare_exchange_weak(&offset,&old,old+delta)) {}
  } else {
    double old=atomic_load(&pendingBy);
    while (!atomic_compare_exchange_weak(&pendingBy,&old,old+delta)) {}
  }
  return unit();
}
lean_obj_res lq_scroll_to(double value) {
  atomic_store(&pendingTo,value); atomic_store(&pendingBy,0.0); atomic_store(&pendingJump,true);
  onMain(^{ nativeScrollTo(value,true); }); return unit();
}
lean_obj_res lq_frame(b_lean_obj_arg list,uint32_t b,uint32_t over,b_lean_obj_arg top,b_lean_obj_arg bot,uint8_t pin,b_lean_obj_arg placement,b_lean_obj_arg hold) {
  // DesktopMain intercepts App's layer publications; the desktop picture
  // is the sole publication to this shell.
  return words(NULL,0);
}
lean_obj_res lq_ctl_poll(void) { return words(NULL,0); }
lean_obj_res lq_ctl_reply(b_lean_obj_arg s) { fprintf(stderr,"%s\n",lean_string_cstr(s));return unit(); }
lean_obj_res lq_poll(void) {
  // Moving-message input uses the phones' existing eight-word ABI,
  // including displayed frame serial and the compiled Slide translation.
  __block NSArray<NSNumber*> *batch;
  onMain(^{ batch=[rawEvents copy]; [rawEvents removeAllObjects]; });
  size_t n=batch.count; uint32_t *v=malloc(n*sizeof(uint32_t));
  for(size_t i=0;i<n;i++) v[i]=batch[i].unsignedIntValue;
  lean_obj_res result=words(v,n);free(v);return result;
}
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
