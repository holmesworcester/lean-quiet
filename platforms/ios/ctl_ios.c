// The control channel on iOS
// ==========================

// Platform.ctlPoll and ctlReply, as android/twin/ctl.c does them, over TCP
// on 127.0.0.1 instead of an abstract unix socket (iOS has none): in the
// Simulator that is the Mac's own loopback, so a client on the Mac reaches
// the app directly (ios/ctl.py). A thread listens, one reader thread per
// connection splits what arrives into lines, and each line waits in a
// queue for Lean. A reply answers the oldest unanswered command and goes
// back on that command's connection. A connection is closed once its peer
// has hung up and every command it sent has been answered. The line
// `twin` is the twin's own report (lq_twin, for tests), answered at once;
// `twin local` puts the channel back on 127.0.0.1 alone; `twin shot`
// writes the app's window to Documents/screen.png.
//
// Who can reach it. TCP carries no peer uid (Android's SO_PEERCRED), and on
// a phone any other app can connect to 127.0.0.1 too. So a connection's
// first line must be the channel's token, `token <hex>` (128 random bits,
// compared in constant time); one that is not is closed, unread and
// unanswered. The token is the launch's LEANQUIET_CTL_TOKEN (a test
// harness makes one per run and launches with it, through simctl or
// devicectl: the Mac the phone is paired with), else one made at start and
// kept in the app's container (Documents/ctl.token, 0600; read it with
// devicectl device copy from). The channel listens on 127.0.0.1, and on
// every interface only for a launch with LEANQUIET_CTL_REMOTE=1 (a device
// test from the Mac over Wi-Fi), until `twin local`. And it exists only in
// development builds: build_ios.sh compiles it with LQ_CTL unless
// RELEASE=1. A release build has no listener at all, and ctlPoll answers
// nothing.

#include <lean/lean.h>

#ifdef LQ_CTL

#include <arpa/inet.h>
#include <fcntl.h>
#include <ifaddrs.h>
#include <netinet/in.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

typedef struct Conn {
  int  fd;
  int  pending;  // commands not yet answered
  bool hung;     // the peer hung up
  bool authed;   // its first line was the token
} Conn;

// The token, as hex (32 characters).
static char lq_token[65];

// Whether line (n bytes) is `token <the token>`, in constant time.
static bool lq_token_ok(const char* line, size_t n) {
  size_t t = strlen(lq_token);
  if (t == 0 || n != 6 + t || memcmp(line, "token ", 6) != 0) {
    return false;
  }
  unsigned char d = 0;
  for (size_t i = 0; i < t; i += 1) {
    d |= (unsigned char)(line[6 + i] ^ lq_token[i]);
  }
  return d == 0;
}

typedef struct Cmd {
  Conn*       conn;
  char*       line;
  bool        polled;
  struct Cmd* next;
} Cmd;

static pthread_mutex_t lq_ctl_mu = PTHREAD_MUTEX_INITIALIZER;
static Cmd*            lq_head;  // unanswered, oldest first
static Cmd**           lq_tail = &lq_head;

static void lq_release(Conn* c) {
  if (c->hung && c->pending == 0) {
    close(c->fd);
    free(c);
  }
}

void lq_twin(char* out, size_t n);       // quiet_ios.m
void lq_twin_shot(char* out, size_t n);

// `twin`: answered at once by the twin itself (lq_twin), not queued for Lean.
static void lq_twin_line(Conn* c) {
  char out[2048];
  lq_twin(out, sizeof out - 1);
  size_t n = strlen(out);
  out[n] = '\n';
  send(c->fd, out, n + 1, 0);
}

// Whether the channel listens on every interface (LEANQUIET_CTL_REMOTE=1
// at launch) until `twin local` puts it back on 127.0.0.1, and its port.
static _Atomic bool lq_any;
static int          lq_port;

// `twin local`: from now on the channel listens on 127.0.0.1 only (a test
// that asked for every interface at launch gives the LAN back without a
// relaunch). The listener is woken by a connection of its own.
static void lq_local(Conn* c) {
  bool was = atomic_exchange(&lq_any, false);
  if (was) {
    int s = socket(AF_INET, SOCK_STREAM, 0);
    struct sockaddr_in a;
    memset(&a, 0, sizeof a);
    a.sin_len         = sizeof a;
    a.sin_family      = AF_INET;
    a.sin_port        = htons((uint16_t)lq_port);
    a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    connect(s, (struct sockaddr*)&a, sizeof a);
    close(s);
  }
  const char* r = "control: 127.0.0.1 only\n";
  send(c->fd, r, strlen(r), 0);
}

static void lq_queue(Conn* c, const char* s, size_t n) {
  Cmd* m = calloc(1, sizeof *m);
  m->conn = c;
  m->line = strndup(s, n);
  pthread_mutex_lock(&lq_ctl_mu);
  c->pending += 1;
  *lq_tail = m;
  lq_tail  = &m->next;
  pthread_mutex_unlock(&lq_ctl_mu);
}

static void* lq_reader(void* arg) {
  Conn*  c = arg;
  char   buf[65536];
  size_t n = 0;
  for (;;) {
    ssize_t k = read(c->fd, buf + n, sizeof buf - n);
    if (k <= 0) {
      break;
    }
    n += (size_t)k;
    size_t start = 0;
    for (size_t i = 0; i < n; i += 1) {
      if (buf[i] == '\n') {
        size_t len = i - start;
        if (len > 0 && buf[i - 1] == '\r') {
          len -= 1;
        }
        if (!c->authed) {
          // the first line: the token, or the connection ends unanswered
          if (!lq_token_ok(buf + start, len)) {
            goto done;
          }
          c->authed = true;
          send(c->fd, "ok\n", 3, 0);
        } else if (len == 4 && memcmp(buf + start, "twin", 4) == 0) {
          lq_twin_line(c);
        } else if (len == 10 && memcmp(buf + start, "twin local", 10) == 0) {
          lq_local(c);
        } else if (len == 9 && memcmp(buf + start, "twin shot", 9) == 0) {
          char r[256];
          lq_twin_shot(r, sizeof r - 1);
          size_t k = strlen(r);
          r[k] = '\n';
          send(c->fd, r, k + 1, 0);
        } else if (len > 0) {
          lq_queue(c, buf + start, len);
        }
        start = i + 1;
      }
    }
    memmove(buf, buf + start, n - start);
    n -= start;
    if (n == sizeof buf) {
      n = 0;  // a line longer than the buffer is dropped
    }
  }
done:
  pthread_mutex_lock(&lq_ctl_mu);
  c->hung = true;
  lq_release(c);
  pthread_mutex_unlock(&lq_ctl_mu);
  return NULL;
}

static void* lq_listen(void* arg) {
  int  port = lq_port;
  bool any  = atomic_load(&lq_any);
  int  s    = socket(AF_INET, SOCK_STREAM, 0);
  int one  = 1;
  setsockopt(s, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
  struct sockaddr_in a;
  memset(&a, 0, sizeof a);
  a.sin_len         = sizeof a;
  a.sin_family      = AF_INET;
  a.sin_port        = htons((uint16_t)port);
  a.sin_addr.s_addr = htonl(any ? INADDR_ANY : INADDR_LOOPBACK);
  if (s < 0 || bind(s, (struct sockaddr*)&a, sizeof a) != 0 || listen(s, 8) != 0) {
    fprintf(stderr, "control: cannot listen on port %d\n", port);
    return NULL;
  }
  fprintf(stderr, "control: listening on %s:%d\n", any ? "every interface" : "127.0.0.1", port);
  struct ifaddrs* ifs;
  if (any && getifaddrs(&ifs) == 0) {
    for (struct ifaddrs* i = ifs; i != NULL; i = i->ifa_next) {
      if (i->ifa_addr != NULL && i->ifa_addr->sa_family == AF_INET) {
        char b[INET_ADDRSTRLEN];
        inet_ntop(AF_INET, &((struct sockaddr_in*)i->ifa_addr)->sin_addr, b, sizeof b);
        fprintf(stderr, "control: address %s %s\n", i->ifa_name, b);
      }
    }
    freeifaddrs(ifs);
  }
  for (;;) {
    int fd = accept(s, NULL, NULL);
    if (fd < 0) {
      continue;
    }
    if (atomic_load(&lq_any) != any) {
      // `twin local` (its wake-up connection): listen again, on loopback
      close(fd);
      close(s);
      return lq_listen(arg);
    }
    setsockopt(fd, SOL_SOCKET, SO_NOSIGPIPE, &one, sizeof one);
    Conn* c = calloc(1, sizeof *c);
    c->fd   = fd;
    pthread_t t;
    if (pthread_create(&t, NULL, lq_reader, c) != 0) {
      close(fd);
      free(c);
      continue;
    }
    pthread_detach(t);
  }
  return NULL;
}

// Starts the channel on port: the launch's token, or a new one kept at
// token_file (see the top).
void lq_ctl_start(int port, const char* token_file) {
  const char* given  = getenv("LEANQUIET_CTL_TOKEN");
  const char* remote = getenv("LEANQUIET_CTL_REMOTE");
  if (given != NULL && strlen(given) >= 32 && strlen(given) < sizeof lq_token) {
    strcpy(lq_token, given);
  } else {
    unsigned char r[16];
    arc4random_buf(r, sizeof r);
    for (int i = 0; i < 16; i += 1) {
      snprintf(lq_token + 2 * i, 3, "%02x", r[i]);
    }
    int fd = open(token_file, O_WRONLY | O_CREAT | O_TRUNC, 0600);
    if (fd >= 0) {
      write(fd, lq_token, strlen(lq_token));
      close(fd);
    }
  }
  atomic_store(&lq_any, remote != NULL && strcmp(remote, "1") == 0);
  lq_port = port;
  pthread_t t;
  if (pthread_create(&t, NULL, lq_listen, NULL) == 0) {
    pthread_detach(t);
  }
}

lean_obj_res lq_ctl_poll(void) {
  lean_object* out = lean_mk_empty_array();
  pthread_mutex_lock(&lq_ctl_mu);
  for (Cmd* m = lq_head; m != NULL; m = m->next) {
    if (!m->polled) {
      m->polled = true;
      out = lean_array_push(out, lean_mk_string(m->line));
    }
  }
  pthread_mutex_unlock(&lq_ctl_mu);
  return lean_io_result_mk_ok(out);
}

lean_obj_res lq_ctl_reply(b_lean_obj_arg s) {
  pthread_mutex_lock(&lq_ctl_mu);
  Cmd* m = lq_head;
  if (m != NULL && m->polled) {
    lq_head = m->next;
    if (lq_head == NULL) {
      lq_tail = &lq_head;
    }
  } else {
    m = NULL;
  }
  pthread_mutex_unlock(&lq_ctl_mu);
  if (m == NULL) {
    return lean_io_result_mk_ok(lean_box(0));
  }
  const char* str = lean_string_cstr(s);
  size_t      n   = strlen(str);
  char*       out = malloc(n + 1);
  memcpy(out, str, n);
  for (size_t i = 0; i < n; i += 1) {
    if (out[i] == '\n') {
      out[i] = ' ';  // one line per reply
    }
  }
  out[n] = '\n';
  size_t off = 0;
  while (off < n + 1) {
    ssize_t k = send(m->conn->fd, out + off, n + 1 - off, 0);
    if (k <= 0) {
      break;
    }
    off += (size_t)k;
  }
  free(out);
  pthread_mutex_lock(&lq_ctl_mu);
  m->conn->pending -= 1;
  lq_release(m->conn);
  pthread_mutex_unlock(&lq_ctl_mu);
  free(m->line);
  free(m);
  return lean_io_result_mk_ok(lean_box(0));
}

#else  // a release build: no channel; Lean's externs answer nothing

lean_obj_res lq_ctl_poll(void) {
  return lean_io_result_mk_ok(lean_mk_empty_array());
}

lean_obj_res lq_ctl_reply(b_lean_obj_arg s) {
  (void)s;
  return lean_io_result_mk_ok(lean_box(0));
}

#endif
