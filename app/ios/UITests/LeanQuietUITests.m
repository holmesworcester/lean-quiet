// The app in the Simulator, end to end, through its real input: XCUITest's
// synthesized touches go through UIKit to the twin (the upside-down scroll
// view's physics, the chrome's taps and long press), and its typing goes
// through the software keyboard into the twin's text field. Each step is
// checked in Lean's own state, read over the control channel (ctl_ios.c:
// the runner is on the Mac's loopback too), and kept as a screenshot.
//
// Expects the app's database to hold the chaos data already (sim_e2e.sh
// seeds it). The runner's environment (TEST_RUNNER_x from xcodebuild):
// LEANQUIET_CTL_PORT (default 7417); LEANQUIET_SHOTS, a directory on the
// Mac for the screenshots (also attached to the result bundle).

#import <XCTest/XCTest.h>
#include <netinet/in.h>
#include <sys/socket.h>
#include <unistd.h>

@interface LeanQuietUITests : XCTestCase
@property (strong) XCUIApplication* app;
@property (nonatomic) int port;
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
  NSData* line = [[cmd stringByAppendingString:@"\n"] dataUsingEncoding:NSUTF8StringEncoding];
  write(s, line.bytes, line.length);
  NSMutableData* got = [NSMutableData data];
  char c;
  while (read(s, &c, 1) == 1 && c != '\n') {
    [got appendBytes:&c length:1];
  }
  close(s);
  return [[NSString alloc] initWithData:got encoding:NSUTF8StringEncoding];
}

// A number from `state`'s reply ("b 0 total 500 ... ime 0 text \"..\" ...").
- (long)num:(NSString*)key in:(NSString*)state {
  NSArray<NSString*>* ws = [state componentsSeparatedByString:@" "];
  NSUInteger i = [ws indexOfObject:key];
  return i == NSNotFound || i + 1 >= ws.count ? -1 : ws[i + 1].integerValue;
}

- (NSString*)state {
  return [self ctl:@"state"] ?: @"";
}

// Polls `state` until ok holds (true), or gives up after secs (false).
- (BOOL)until:(double)secs that:(BOOL (^)(NSString*))ok {
  NSDate* end = [NSDate dateWithTimeIntervalSinceNow:secs];
  while ([end timeIntervalSinceNow] > 0) {
    if (ok([self state])) {
      return YES;
    }
    [NSThread sleepForTimeInterval:0.25];
  }
  return NO;
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

// A point on the screen, in points from its top left.
- (XCUICoordinate*)at:(CGFloat)x y:(CGFloat)y {
  XCUICoordinate* o = [self.app coordinateWithNormalizedOffset:CGVectorMake(0, 0)];
  return [o coordinateWithOffset:CGVectorMake(x, y)];
}

- (void)setUp {
  self.continueAfterFailure = NO;
  NSString* p = NSProcessInfo.processInfo.environment[@"LEANQUIET_CTL_PORT"];
  self.port   = p.length > 0 ? p.intValue : 7417;
  self.app    = [XCUIApplication new];
  self.app.launchEnvironment = @{ @"LEANQUIET_CTL_PORT": [NSString stringWithFormat:@"%d", self.port] };
  [self.app launch];
}

- (void)testScrollTapKeyboardSend {
  // Cold open on the seeded data: the list's rows are read and painted.
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

  CGSize screen = self.app.frame.size;
  // A tap on the header jumps back to the newest message (App.onTap).
  [[self at:screen.width / 2 y:70] tap];
  XCTAssertTrue([self until:10 that:^BOOL(NSString* s) { return [self num:@"b" in:s] == 0; }],
    @"a header tap did not go back to the newest: %@", [self state]);

  // A long press on a message opens the reaction sheet in the composer's
  // place (taller: the viewport shrinks); a header tap closes it.
  long view = [self num:@"viewH" in:[self state]];
  [[self at:screen.width / 2 y:screen.height * 0.6] pressForDuration:1.0];
  XCTAssertTrue([self until:10 that:^BOOL(NSString* s) { return [self num:@"viewH" in:s] < view; }],
    @"a long press opened no sheet: %@", [self state]);
  [self shot:@"3-sheet"];
  [[self at:screen.width / 2 y:70] tap];
  XCTAssertTrue([self until:10 that:^BOOL(NSString* s) { return [self num:@"viewH" in:s] == view; }],
    @"a header tap did not close the sheet: %@", [self state]);

  // A tap on the composer's field opens the keyboard; the composer rides
  // up on it (Lean is told its height).
  [[self at:screen.width * 0.3 y:screen.height - 34 - 30] tap];
  XCTAssertTrue([self until:10 that:^BOOL(NSString* s) { return [self num:@"ime" in:s] > 0; }],
    @"the keyboard did not open: %@", [self state]);
  // A new simulator's keyboard first shows its slide-to-type tip.
  XCUIElement* tip = self.app.buttons[@"Continue"];
  if ([tip waitForExistenceWithTimeout:2]) {
    [tip tap];
  }
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

@end
