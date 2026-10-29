// The app in the Simulator, end to end, through its real input: XCUITest's
// synthesized touches go through UIKit to Lean's raw-event classifier;
// accepted scroll samples drive native physics, and typing
// goes through the software keyboard into the twin's text field. Each step
// is checked in Lean's own state, and the twin's placement in the twin's
// own report (`twin`), both read over the control channel (ctl_ios.c: the
// runner is on the Mac's loopback too); screenshots are kept as artifacts,
// never as the check.
//
// Expects a community with the chaos data in the app's database (ship.sh
// sim seeds it). The runner's environment (TEST_RUNNER_x from xcodebuild):
// LEANQUIET_CTL_PORT (default 7417); LEANQUIET_CTL_TOKEN (the channel's
// token: the app is launched with it, and it is sent first);
// LEANQUIET_SHOTS, a directory on the Mac for the screenshots (also
// attached to the result bundle); and from
// Lean (test/Targets.lean), so the test computes no layout of its own:
// LEANQUIET_FIELD and LEANQUIET_CONTINUE (the Paste page's boxes, "x y w h"
// in page rows), LEANQUIET_COMPOSER ("height textRows") and LEANQUIET_LINK
// (a valid invite link).

#import <XCTest/XCTest.h>
#include <netinet/in.h>
#include <sys/socket.h>
#include <unistd.h>

@interface LeanQuietUITests : XCTestCase
@property (strong) XCUIApplication* app;
@property (nonatomic) int port;
@property (copy) NSString* token;
@end

@implementation LeanQuietUITests

// One control command and its one-line reply, or nil if the app is not
// listening.
- (NSString*)ctl:(NSString*)cmd {
  int s = socket(AF_INET, SOCK_STREAM, 0);
  struct sockaddr_in a = { 0 };
  a.sin_len         = sizeof a;
  a.sin_family      = AF_INET;
  a.sin_port        = htons((uint16_t)self.port);
  a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  struct timeval tv = { 30, 0 };
  setsockopt(s, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv);
  if (connect(s, (struct sockaddr*)&a, sizeof a) != 0) {
    close(s);
    return nil;
  }
  // the channel's token first (ctl_ios.c answers nothing without it)
  NSData* auth = [[NSString stringWithFormat:@"token %@\n", self.token] dataUsingEncoding:NSUTF8StringEncoding];
  write(s, auth.bytes, auth.length);
  char c;
  while (read(s, &c, 1) == 1 && c != '\n') {
  }
  NSData* line = [[cmd stringByAppendingString:@"\n"] dataUsingEncoding:NSUTF8StringEncoding];
  write(s, line.bytes, line.length);
  NSMutableData* got = [NSMutableData data];
  while (read(s, &c, 1) == 1 && c != '\n') {
    [got appendBytes:&c length:1];
  }
  close(s);
  return [[NSString alloc] initWithData:got encoding:NSUTF8StringEncoding];
}

// A number after key in a reply ("b 0 total 500 ... viewH 1983").
- (long)num:(NSString*)key in:(NSString*)reply {
  NSArray<NSString*>* ws = [reply componentsSeparatedByString:@" "];
  NSUInteger i = [ws indexOfObject:key];
  return i == NSNotFound || i + 1 >= ws.count ? -1 : ws[i + 1].integerValue;
}

- (NSString*)state {
  return [self ctl:@"state"] ?: @"";
}

- (NSString*)twin {
  return [self ctl:@"twin"] ?: @"";
}

// Polls a reply until ok holds (true), or gives up after secs (false).
- (BOOL)until:(double)secs ask:(NSString*)cmd that:(BOOL (^)(NSString*))ok {
  NSDate* end = [NSDate dateWithTimeIntervalSinceNow:secs];
  while ([end timeIntervalSinceNow] > 0) {
    if (ok([self ctl:cmd] ?: @"")) {
      return YES;
    }
    [NSThread sleepForTimeInterval:0.25];
  }
  return NO;
}

- (BOOL)until:(double)secs that:(BOOL (^)(NSString*))ok {
  return [self until:secs ask:@"state" that:ok];
}

// b, once it has stopped moving (a fling settled).
- (long)settledB {
  long last = -2;
  for (int i = 0; i < 40; i += 1) {
    long b = [self num:@"b" in:[self state]];
    if (b == last) {
      return b;
    }
    last = b;
    [NSThread sleepForTimeInterval:0.5];
  }
  return last;
}

// The twin's report once the keyboard's animation is over (the composer's
// top the same twice, 0.3 s apart).
- (NSString*)settledTwin {
  NSString* last = [self twin];
  for (int i = 0; i < 20; i += 1) {
    [NSThread sleepForTimeInterval:0.3];
    NSString* now = [self twin];
    if ([self num:@"composerTop" in:now] == [self num:@"composerTop" in:last]) {
      return now;
    }
    last = now;
  }
  return last;
}

- (void)shot:(NSString*)name {
  XCUIScreenshot* s = XCUIScreen.mainScreen.screenshot;
  XCTAttachment*  a = [XCTAttachment attachmentWithScreenshot:s];
  a.name     = name;
  a.lifetime = XCTAttachmentLifetimeKeepAlways;
  [self addAttachment:a];
  NSString* dir = NSProcessInfo.processInfo.environment[@"LEANQUIET_SHOTS"];
  if (dir.length > 0) {
    [s.PNGRepresentation writeToFile:[dir stringByAppendingFormat:@"/%@.png", name] atomically:YES];
  }
}

// Numbers from the environment ("x y w h").
- (NSArray<NSNumber*>*)env:(NSString*)key {
  NSString* v = NSProcessInfo.processInfo.environment[key];
  NSMutableArray* out = [NSMutableArray array];
  for (NSString* w in [v componentsSeparatedByString:@" "]) {
    if (w.length > 0) {
      [out addObject:@(w.integerValue)];
    }
  }
  return out;
}

// Pixels per point.
- (double)scale {
  return [self num:@"w" in:[self twin]] / self.app.frame.size.width;
}

// A point on the screen, given in pixels from its top left.
- (XCUICoordinate*)px:(double)x y:(double)y {
  double k = [self scale];
  XCUICoordinate* o = [self.app coordinateWithNormalizedOffset:CGVectorMake(0, 0)];
  return [o coordinateWithOffset:CGVectorMake(x / k, y / k)];
}

// A new simulator's keyboard first shows its slide-to-type tip.
- (void)skipKeyboardTip {
  XCUIElement* tip = self.app.buttons[@"Continue"];
  if ([tip waitForExistenceWithTimeout:2]) {
    [tip tap];
  }
}

- (void)setUp {
  self.continueAfterFailure = NO;
  NSString* p = NSProcessInfo.processInfo.environment[@"LEANQUIET_CTL_PORT"];
  self.port   = p.length > 0 ? p.intValue : 7417;
  self.token  = NSProcessInfo.processInfo.environment[@"LEANQUIET_CTL_TOKEN"] ?: @"";
  self.app    = [XCUIApplication new];
  self.app.launchEnvironment = @{ @"LEANQUIET_CTL_PORT": [NSString stringWithFormat:@"%d", self.port],
                                  @"LEANQUIET_CTL_TOKEN": self.token };
  [self.app launch];
  XCTAssertTrue([self until:30 ask:@"ping" that:^BOOL(NSString* s) { return [s isEqual:@"pong"]; }],
    @"the app does not answer on the control channel");
}

- (void)testScrollTapKeyboardSend {
  // The community's conversation, on the seeded data: its rows are read
  // and painted.
  [self ctl:@"channel"];
  XCTAssertTrue([self until:60 that:^BOOL(NSString* s) {
    return [self num:@"total" in:s] >= 100 && [self num:@"mounted" in:s] > 0;
  }], @"no chaos data on open: %@", [self state]);
  [NSThread sleepForTimeInterval:2];
  long total = [self num:@"total" in:[self state]];
  XCTAssertEqual([self settledB], 0, @"not pinned to the newest message on open");
  [self shot:@"1-open"];

  // A fling towards older messages (the finger moves down): UIKit's
  // physics raise the bottom-anchored offset.
  [self.app swipeDown];
  long b1 = [self settledB];
  XCTAssertGreaterThan(b1, 0, @"a swipe down did not scroll: %@", [self state]);
  [self.app swipeDown];
  long b2 = [self settledB];
  XCTAssertGreaterThan(b2, b1, @"a second swipe down did not scroll further");
  [self shot:@"2-scrolled"];
  [self ctl:@"bottom"];
  XCTAssertTrue([self until:10 that:^BOOL(NSString* s) { return [self num:@"b" in:s] == 0; }],
    @"did not go back to the newest: %@", [self state]);

  // A long press on a message opens the reaction sheet in the composer's
  // place (taller: the viewport shrinks); a header tap closes it.
  CGSize screen = self.app.frame.size;
  double k      = [self scale];
  long view     = [self num:@"viewH" in:[self state]];
  [[self px:screen.width * k / 2 y:screen.height * k * 0.6] pressForDuration:1.0];
  XCTAssertTrue([self until:10 that:^BOOL(NSString* s) { return [self num:@"viewH" in:s] < view; }],
    @"a long press opened no sheet: %@", [self state]);
  [self shot:@"3-sheet"];
  long top = [self num:@"top" in:[self twin]];
  [[self px:screen.width * k / 2 y:top / 2.0] tap];
  XCTAssertTrue([self until:10 that:^BOOL(NSString* s) { return [self num:@"viewH" in:s] == view; }],
    @"a header tap did not close the sheet: %@", [self state]);

  // A tap on the composer's text rows (Composer.layout's, from Lean) opens
  // the keyboard; the composer rides up on it (Lean is told its height).
  NSArray<NSNumber*>* comp = [self env:@"LEANQUIET_COMPOSER"];
  XCTAssertEqual(comp.count, 2u, @"LEANQUIET_COMPOSER not given");
  long ctop = [self num:@"composerTop" in:[self twin]];
  [[self px:screen.width * k / 2 y:ctop + comp[1].doubleValue / 2] tap];
  XCTAssertTrue([self until:10 that:^BOOL(NSString* s) { return [self num:@"ime" in:s] > 0; }],
    @"the keyboard did not open: %@", [self state]);
  [self skipKeyboardTip];
  [NSThread sleepForTimeInterval:1];
  [self shot:@"4-keyboard"];

  // Typing on the software keyboard reaches Lean's composer.
  [self.app typeText:@"Hello from the Simulator"];
  XCTAssertTrue([self until:10 that:^BOOL(NSString* s) {
    return [s containsString:@"text \"Hello from the Simulator\""];
  }], @"the typed text did not reach Lean: %@", [self state]);
  [self shot:@"5-typed"];

  // The keyboard's send: the message is written (one more) and the
  // composer empties; it is on screen at the bottom.
  [self.app typeText:@"\n"];
  XCTAssertTrue([self until:20 that:^BOOL(NSString* s) {
    return [self num:@"total" in:s] == total + 1 && [s containsString:@"text \"\""];
  }], @"send did not write the message: %@", [self state]);
  NSString* seen = [self ctl:@"visible"];
  XCTAssertTrue([seen containsString:@"Hello from the Simulator"], @"not on screen: %@", seen);
  [NSThread sleepForTimeInterval:1];
  [self shot:@"6-sent"];
}

// A page is pinned (Geometry.Seam.pinned; ios/Placement.lean): opening the
// keyboard on Paste must not move it, and a tap on it must reach the row
// drawn under the finger (Geometry.pinned_tap).
- (void)testSystemPhotoPicker {
  [self ctl:@"channel"];
  // Any previous test draft is sent before starting this selection.
  [self ctl:@"post"];
  XCTAssertTrue([[self ctl:@"photo-status"] hasPrefix:@"photos 0 pending false"]);
  [self ctl:@"pick-photo"];
  XCUIElement* cancel = self.app.buttons[@"Cancel"];
  if (![cancel waitForExistenceWithTimeout:10]) cancel = self.app.buttons[@"Close"];
  XCTAssertTrue([cancel waitForExistenceWithTimeout:10], @"native photo picker: %@", self.app.debugDescription);
  [cancel tap];
  XCTAssertTrue([self until:15 ask:@"photo-status" that:^BOOL(NSString* value) {
    return [value hasPrefix:@"photos 0 pending false"];
  }]);
  [self ctl:@"pick-photo"];
  XCUIElement* cell = [self.app.images matchingPredicate:[NSPredicate predicateWithFormat:@"label BEGINSWITH %@", @"Photo,"]].firstMatch;
  XCTAssertTrue([cell waitForExistenceWithTimeout:15], @"seeded native photo: %@", self.app.debugDescription);
  // Photos exposes each texture-backed thumbnail as an Image. Its
  // accessibility hit point is absent on iOS 26; tap its reported bounds.
  CGRect r = cell.frame;
  XCTAssertTrue(r.size.width > 0 && r.size.height > 0 && CGRectContainsRect(self.app.frame, r));
  [[[self.app coordinateWithNormalizedOffset:CGVectorMake(0, 0)]
      coordinateWithOffset:CGVectorMake(CGRectGetMidX(r), CGRectGetMidY(r))] tap];
  XCUIElement* add = self.app.buttons[@"Add"];
  if ([add waitForExistenceWithTimeout:2]) [add tap];
  XCTAssertTrue([self until:120 ask:@"photo-status" that:^BOOL(NSString* value) {
    return [value hasPrefix:@"photos 1 pending false"] && [value containsString:@"(1024, 2048)"];
  }], @"the native selection must be oriented and bounded: %@", [self ctl:@"photo-status"]);
  [self shot:@"system-photo-chip"];
  [self ctl:@"post Native iOS picker photo"];
  [self ctl:@"wait"];
  XCTAssertTrue([self until:60 ask:@"pics" that:^BOOL(NSString* value) {
    for (NSString* row in [value componentsSeparatedByString:@" | "])
      if ([row containsString:@"Native iOS picker photo"] && [row containsString:@" painted"]) return YES;
    return NO;
  }]);
  XCTAssertTrue([[self ctl:@"photo-status"] hasPrefix:@"photos 0 pending false"]);
  [self shot:@"system-photo-sent"];
}

- (void)testPinnedPaste {
  NSArray<NSNumber*>* field = [self env:@"LEANQUIET_FIELD"];
  NSArray<NSNumber*>* cont  = [self env:@"LEANQUIET_CONTINUE"];
  NSString* link = NSProcessInfo.processInfo.environment[@"LEANQUIET_LINK"];
  XCTAssertTrue(field.count == 4 && cont.count == 4 && link.length > 0, @"targets not given");
  XCTAssertTrue([[self ctl:@"open paste"] containsString:@"paste"], @"Paste did not open");

  // Lean crops the visible layer to the viewport. Its top is the header
  // bottom; the hidden physics view has the effective viewport height.
  XCTAssertTrue([self until:10 ask:@"twin" that:^BOOL(NSString* s) { return [self num:@"pin" in:s] == 1; }],
    @"the twin did not pin the page: %@", [self twin]);
  NSString* t0 = [self settledTwin];
  long top  = [self num:@"top" in:t0];
  long view = [self num:@"viewH" in:[self state]];
  long list0 = [self num:@"listY" in:t0];
  long svb0  = [self num:@"svBottom" in:t0];
  XCTAssertEqual(list0, top, @"page row 0 not at the viewport's top: %@", t0);
  XCTAssertEqual(svb0, view, @"the physics viewport is not Lean's viewport: %@", t0);
  XCTAssertEqual([self num:@"ime" in:[self state]], 0, @"the keyboard is already open");

  // A real tap on the field (Pages.paste's box) opens the keyboard.
  double fx = field[0].doubleValue + field[2].doubleValue / 2;
  double fy = top + field[1].doubleValue + field[3].doubleValue / 2;
  [[self px:fx y:fy] tap];
  XCTAssertTrue([self until:10 that:^BOOL(NSString* s) { return [self num:@"ime" in:s] > 0; }],
    @"a tap on the field did not open the keyboard: %@ / %@", [self state], [self twin]);
  [self skipKeyboardTip];

  // Keyboard open: the composer rode up, the page did not move.
  NSString* t1 = [self settledTwin];
  XCTAssertLessThan([self num:@"composerTop" in:t1], [self num:@"composerTop" in:t0], @"the composer was not lifted: %@", t1);
  XCTAssertEqual([self num:@"listY" in:t1], list0, @"the page moved with the keyboard: %@", t1);
  XCTAssertEqual([self num:@"svBottom" in:t1], [self num:@"composerTop" in:t1] - top,
    @"the physics viewport did not follow Lean's published height: %@", t1);
  NSLog(@"pinned: keyboard closed: %@", t0);
  NSLog(@"pinned: keyboard open:   %@", t1);
  [self shot:@"7-paste-keyboard"];

  // A link typed on the software keyboard reaches the field.
  [self.app typeText:link];
  XCTAssertTrue([self until:20 ask:@"twin" that:^BOOL(NSString* s) {
    return [s hasSuffix:[@"field " stringByAppendingString:link]];
  }], @"the typed link is not in the field: %@", [self twin]);
  XCTAssertEqual([self num:@"listY" in:[self twin]], list0, @"the page moved while typing");

  // A real tap on Continue (above the keyboard): Lean publishes what
  // pinned_tap reads (page row = view - 1 - report = the touch's row - top),
  // and Lean takes it as Continue: the link is accepted, the next page is
  // Choose a name.
  double cx = cont[0].doubleValue + cont[2].doubleValue / 2;
  double cy = top + cont[1].doubleValue + cont[3].doubleValue / 2;
  XCTAssertLessThan(cy, [self num:@"composerTop" in:t1], @"Continue is under the keyboard");
  // (the field's tap is the last reported until this one's arrives)
  NSString* (^lastTap)(NSString*) = ^NSString*(NSString* t) {
    NSArray<NSString*>* w = [t componentsSeparatedByString:@" "];
    NSUInteger i = [w indexOfObject:@"tap"];
    return i == NSNotFound || i + 3 >= w.count ? @"" : [[w subarrayWithRange:NSMakeRange(i + 1, 3)]
      componentsJoinedByString:@" "];
  };
  NSString* before = lastTap([self twin]);
  [[self px:cx y:cy] tap];
  XCTAssertTrue([self until:10 ask:@"twin" that:^BOOL(NSString* s) { return ![lastTap(s) isEqual:before]; }],
    @"no tap reported: %@", [self twin]);
  NSString* t2 = [self twin];
  NSArray<NSString*>* ws = [lastTap(t2) componentsSeparatedByString:@" "];
  XCTAssertEqual(ws[0].integerValue, 2, @"not a tap: %@", t2);
  long rep = ws[2].integerValue;
  long row = view - 1 - rep;
  long expect = lround(cy) - top;
  NSLog(@"pinned: tap at screen row %.0f; reported %ld; page row read %ld, drawn %ld (Continue %ld..%ld)", cy, rep,
    row, expect, cont[1].integerValue, cont[1].integerValue + cont[3].integerValue);
  XCTAssertLessThanOrEqual(labs(row - expect), 1, @"tap read at page row %ld, drawn at %ld: %@", row, expect, t2);
  XCTAssertTrue(row >= cont[1].integerValue && row < cont[1].integerValue + cont[3].integerValue,
    @"the tap's row %ld is not Continue's", row);
  XCTAssertTrue([self until:10 ask:@"page 0 99999" that:^BOOL(NSString* s) { return [s containsString:@"name"]; }],
    @"Continue did not take the link: %@", [self ctl:@"page 0 99999"]);
  [NSThread sleepForTimeInterval:1];
  [self shot:@"8-choose-name"];
}

@end
