// An iOS app around NetProbe.lean: Lean's main (renamed lean_app_main) on
// a thread of its own with the process's arguments (simctl launch passes
// them), its stderr the report; the app exits with Lean's exit code.
//
// Beside it, the fallback for discovery where raw multicast is not allowed
// (an iPhone without the multicast entitlement): the system's DNS-SD
// (dns_sd.h, what NWBrowser is built on; it needs only NSBonjourServices
// and the local network permission). It registers <instance>-sd of type
// _leanquiet._udp and browses that type, resolving each service found to
// an IPv4 address and port, as Lean would then connect to them over TCP:
// `ok dnssd-found <name> host <host> port <port> addr <ip>`.

#import <UIKit/UIKit.h>
#include <arpa/inet.h>
#include <dns_sd.h>
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

// DNS-SD
// ------

static dispatch_queue_t sd_q;

typedef struct {
  char     name[256];
  char     host[1025];
  uint16_t port;
} SdFound;

static void sd_addr(DNSServiceRef ref, DNSServiceFlags flags, uint32_t ifi, DNSServiceErrorType err,
  const char* host, const struct sockaddr* a, uint32_t ttl, void* ctx) {
  SdFound* f = ctx;
  if (err != kDNSServiceErr_NoError) {
    fprintf(stderr, "fail dnssd-addr %s: error %d\n", f->name, err);
  } else if (a->sa_family == AF_INET) {
    char b[INET_ADDRSTRLEN];
    inet_ntop(AF_INET, &((const struct sockaddr_in*)a)->sin_addr, b, sizeof b);
    fprintf(stderr, "ok dnssd-found %s host %s port %u addr %s\n", f->name, f->host, f->port, b);
  } else {
    return;  // IPv6: wait for the IPv4 answer
  }
  DNSServiceRefDeallocate(ref);
  free(f);
}

static void sd_resolved(DNSServiceRef ref, DNSServiceFlags flags, uint32_t ifi, DNSServiceErrorType err,
  const char* full, const char* host, uint16_t port, uint16_t txtLen, const unsigned char* txt, void* ctx) {
  SdFound* f = ctx;
  DNSServiceRefDeallocate(ref);
  if (err != kDNSServiceErr_NoError) {
    fprintf(stderr, "fail dnssd-resolve %s: error %d\n", f->name, err);
    free(f);
    return;
  }
  snprintf(f->host, sizeof f->host, "%s", host);
  f->port = ntohs(port);
  DNSServiceRef a;
  if (DNSServiceGetAddrInfo(&a, 0, ifi, kDNSServiceProtocol_IPv4, host, sd_addr, f) == kDNSServiceErr_NoError) {
    DNSServiceSetDispatchQueue(a, sd_q);
  } else {
    free(f);
  }
}

static void sd_browsed(DNSServiceRef ref, DNSServiceFlags flags, uint32_t ifi, DNSServiceErrorType err,
  const char* name, const char* type, const char* domain, void* ctx) {
  if (err != kDNSServiceErr_NoError) {
    fprintf(stderr, "fail dnssd-browse: error %d\n", err);
    return;
  }
  if (!(flags & kDNSServiceFlagsAdd)) {
    return;
  }
  SdFound* f = calloc(1, sizeof *f);
  snprintf(f->name, sizeof f->name, "%s", name);
  DNSServiceRef r;
  if (DNSServiceResolve(&r, 0, ifi, name, type, domain, sd_resolved, f) == kDNSServiceErr_NoError) {
    DNSServiceSetDispatchQueue(r, sd_q);
  } else {
    free(f);
  }
}

static void sd_registered(DNSServiceRef ref, DNSServiceFlags flags, DNSServiceErrorType err,
  const char* name, const char* type, const char* domain, void* ctx) {
  if (err != kDNSServiceErr_NoError) {
    fprintf(stderr, "fail dnssd-register: error %d\n", err);
  } else {
    fprintf(stderr, "ok dnssd-registered %s\n", name);
  }
}

static void sd_start(const char* inst) {
  static DNSServiceRef reg, browse;  // held for the process's life
  char name[256];
  snprintf(name, sizeof name, "%s-sd", inst);
  sd_q = dispatch_queue_create("dnssd", DISPATCH_QUEUE_SERIAL);
  DNSServiceErrorType e = DNSServiceRegister(&reg, 0, 0, name, "_leanquiet._udp", NULL, NULL,
    htons(7401), 0, NULL, sd_registered, NULL);
  if (e == kDNSServiceErr_NoError) {
    DNSServiceSetDispatchQueue(reg, sd_q);
  } else {
    fprintf(stderr, "fail dnssd-register: error %d\n", e);
  }
  e = DNSServiceBrowse(&browse, 0, 0, "_leanquiet._udp", NULL, sd_browsed, NULL);
  if (e == kDNSServiceErr_NoError) {
    DNSServiceSetDispatchQueue(browse, sd_q);
  } else {
    fprintf(stderr, "fail dnssd-browse: error %d\n", e);
  }
}

@interface ProbeDelegate : UIResponder <UIApplicationDelegate>
@property (strong, nonatomic) UIWindow* window;
@end

@implementation ProbeDelegate

- (BOOL)application:(UIApplication*)app didFinishLaunchingWithOptions:(NSDictionary*)opts {
  self.window = [[UIWindow alloc] initWithFrame:UIScreen.mainScreen.bounds];
  self.window.rootViewController = [UIViewController new];
  [self.window makeKeyAndVisible];
  sd_start(probe_argc > 4 ? probe_argv[4] : "lean-ios-probe");
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
