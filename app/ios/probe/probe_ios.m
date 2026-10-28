// An iOS app around NetProbe.lean: Lean's main (renamed lean_app_main) on
// a thread of its own with the process's arguments (simctl launch passes
// them), its stderr the report; the app exits with Lean's exit code.

#import <UIKit/UIKit.h>
#include <pthread.h>

int lean_app_main(int argc, char** argv);

static int    probe_argc;
static char** probe_argv;

static void* probe_run(void* arg) {
  // Lean's threads reserve 1 GB of stack each on 64-bit, more than an iOS
  // app's address space holds for a few (as in quiet_ios.m): 64 MB each.
  setenv("LEAN_STACK_SIZE_KB", "65536", 0);
  int code = lean_app_main(probe_argc, probe_argv);
  fflush(stderr);
  exit(code);
  return NULL;
}

@interface ProbeDelegate : UIResponder <UIApplicationDelegate>
@property (strong, nonatomic) UIWindow* window;
@end

@implementation ProbeDelegate

- (BOOL)application:(UIApplication*)app didFinishLaunchingWithOptions:(NSDictionary*)opts {
  self.window = [[UIWindow alloc] initWithFrame:UIScreen.mainScreen.bounds];
  self.window.rootViewController = [UIViewController new];
  [self.window makeKeyAndVisible];
  pthread_t      t;
  pthread_attr_t at;
  pthread_attr_init(&at);
  pthread_attr_setstacksize(&at, 64 << 20);
  pthread_create(&t, &at, probe_run, NULL);
  return YES;
}

@end

int main(int argc, char** argv) {
  probe_argc = argc;
  probe_argv = argv;
  @autoreleasepool {
    return UIApplicationMain(argc, argv, nil, NSStringFromClass([ProbeDelegate class]));
  }
}
