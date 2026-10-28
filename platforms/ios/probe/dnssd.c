// DNS-SD for Lean on iOS
// =====================

// The system's mDNS (dns_sd.h, served by mDNSResponder; what NWBrowser is
// built on) for NetProbe.lean's Sd externs: register a service, browse a
// type, and for every service found resolve its host and port and then
// its IPv4 addresses. It needs NSBonjourServices and the local network
// permission, not the multicast entitlement raw sockets need. Nothing is
// decided here: each result is queued as an event and Lean takes them
// (Sd.poll) and decides what to do with them.
//
// Events, as Lean receives them: #[kind, name, host, port, addr], kind one
// of "registered" (name), "found" (name, host, port, one IPv4 address;
// one event per address), "error" (name = what failed, host = the code).

#include <arpa/inet.h>
#include <dispatch/dispatch.h>
#include <dns_sd.h>
#include <lean/lean.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct Ev {
  char*      f[5];
  struct Ev* next;
} Ev;

static pthread_mutex_t  sd_mu = PTHREAD_MUTEX_INITIALIZER;
static Ev*              sd_head;
static Ev**             sd_tail = &sd_head;
static dispatch_queue_t sd_q;

static void sd_event(const char* kind, const char* name, const char* host, unsigned port,
  const char* addr) {
  Ev*  e = calloc(1, sizeof *e);
  char p[8];
  snprintf(p, sizeof p, "%u", port);
  e->f[0] = strdup(kind);
  e->f[1] = strdup(name ? name : "");
  e->f[2] = strdup(host ? host : "");
  e->f[3] = strdup(p);
  e->f[4] = strdup(addr ? addr : "");
  pthread_mutex_lock(&sd_mu);
  *sd_tail = e;
  sd_tail  = &e->next;
  pthread_mutex_unlock(&sd_mu);
}

static void sd_error(const char* what, DNSServiceErrorType err) {
  char code[16];
  snprintf(code, sizeof code, "%d", (int)err);
  sd_event("error", what, code, 0, NULL);
}

static dispatch_queue_t sd_queue(void) {
  static dispatch_once_t once;
  dispatch_once(&once, ^{
    sd_q = dispatch_queue_create("lean.dnssd", DISPATCH_QUEUE_SERIAL);
  });
  return sd_q;
}

// A service being resolved: its name, then host and port.
typedef struct {
  char     name[256];
  char     host[1025];
  uint16_t port;
} Svc;

static void sd_addr(DNSServiceRef ref, DNSServiceFlags flags, uint32_t ifi, DNSServiceErrorType err,
  const char* host, const struct sockaddr* a, uint32_t ttl, void* ctx) {
  Svc* s = ctx;
  if (err != kDNSServiceErr_NoError) {
    sd_error("addr", err);
  } else if (a != NULL && a->sa_family == AF_INET) {
    char b[INET_ADDRSTRLEN];
    inet_ntop(AF_INET, &((const struct sockaddr_in*)a)->sin_addr, b, sizeof b);
    sd_event("found", s->name, s->host, s->port, b);
  }
  if (err != kDNSServiceErr_NoError || !(flags & kDNSServiceFlagsMoreComing)) {
    DNSServiceRefDeallocate(ref);
    free(s);
  }
}

static void sd_resolved(DNSServiceRef ref, DNSServiceFlags flags, uint32_t ifi, DNSServiceErrorType err,
  const char* full, const char* host, uint16_t port, uint16_t txt_len, const unsigned char* txt,
  void* ctx) {
  Svc* s = ctx;
  DNSServiceRefDeallocate(ref);
  if (err != kDNSServiceErr_NoError) {
    sd_error("resolve", err);
    free(s);
    return;
  }
  snprintf(s->host, sizeof s->host, "%s", host);
  s->port = ntohs(port);
  DNSServiceRef a;
  err = DNSServiceGetAddrInfo(&a, 0, ifi, kDNSServiceProtocol_IPv4, host, sd_addr, s);
  if (err != kDNSServiceErr_NoError) {
    sd_error("addr", err);
    free(s);
    return;
  }
  DNSServiceSetDispatchQueue(a, sd_queue());
}

static void sd_browsed(DNSServiceRef ref, DNSServiceFlags flags, uint32_t ifi, DNSServiceErrorType err,
  const char* name, const char* type, const char* domain, void* ctx) {
  if (err != kDNSServiceErr_NoError) {
    sd_error("browse", err);
    return;
  }
  if (!(flags & kDNSServiceFlagsAdd)) {
    return;
  }
  Svc* s = calloc(1, sizeof *s);
  snprintf(s->name, sizeof s->name, "%s", name);
  DNSServiceRef r;
  err = DNSServiceResolve(&r, 0, ifi, name, type, domain, sd_resolved, s);
  if (err != kDNSServiceErr_NoError) {
    sd_error("resolve", err);
    free(s);
    return;
  }
  DNSServiceSetDispatchQueue(r, sd_queue());
}

static void sd_registered(DNSServiceRef ref, DNSServiceFlags flags, DNSServiceErrorType err,
  const char* name, const char* type, const char* domain, void* ctx) {
  if (err != kDNSServiceErr_NoError) {
    sd_error("register", err);
  } else {
    sd_event("registered", name, NULL, 0, NULL);
  }
}

static lean_obj_res sd_result(const char* what, DNSServiceErrorType err, DNSServiceRef ref) {
  if (err != kDNSServiceErr_NoError) {
    char m[64];
    snprintf(m, sizeof m, "dns_sd %s: error %d", what, (int)err);
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(m)));
  }
  DNSServiceSetDispatchQueue(ref, sd_queue());  // held for the process's life
  return lean_io_result_mk_ok(lean_box(0));
}

lean_obj_res lq_sd_register(b_lean_obj_arg name, b_lean_obj_arg type, uint16_t port) {
  DNSServiceRef       ref;
  DNSServiceErrorType err = DNSServiceRegister(&ref, 0, 0, lean_string_cstr(name), lean_string_cstr(type),
    NULL, NULL, htons(port), 0, NULL, sd_registered, NULL);
  return sd_result("register", err, ref);
}

lean_obj_res lq_sd_browse(b_lean_obj_arg type) {
  DNSServiceRef       ref;
  DNSServiceErrorType err = DNSServiceBrowse(&ref, 0, 0, lean_string_cstr(type), NULL, sd_browsed, NULL);
  return sd_result("browse", err, ref);
}

lean_obj_res lq_sd_poll(void) {
  pthread_mutex_lock(&sd_mu);
  Ev* e   = sd_head;
  sd_head = NULL;
  sd_tail = &sd_head;
  pthread_mutex_unlock(&sd_mu);
  lean_object* out = lean_mk_empty_array();
  while (e != NULL) {
    lean_object* row = lean_mk_empty_array_with_capacity(lean_box(5));
    for (int i = 0; i < 5; i += 1) {
      row = lean_array_push(row, lean_mk_string(e->f[i]));
      free(e->f[i]);
    }
    out = lean_array_push(out, row);
    Ev* n = e->next;
    free(e);
    e = n;
  }
  return lean_io_result_mk_ok(out);
}
