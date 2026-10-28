// The control socket
// ==================

// Platform.ctlPoll and ctlReply on Android: a thread listens on the
// abstract unix socket "leanquiet" (reach it from the host with
// `adb forward tcp:N localabstract:leanquiet`), one reader thread per
// connection splits what arrives into lines, and each line waits in a
// queue for Lean. A reply answers the oldest unanswered command and goes
// back on that command's connection. A connection is closed once its
// peer has hung up and every command it sent has been answered.

#include <android/log.h>
#include <lean/lean.h>
#include <pthread.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <unistd.h>

typedef struct Conn {
  int  fd;
  int  pending;  // commands not yet answered
  bool hung;     // the peer hung up
} Conn;

typedef struct Cmd {
  Conn*       conn;
  char*       line;
  bool        polled;
  struct Cmd* next;
} Cmd;

static pthread_mutex_t lq_mu = PTHREAD_MUTEX_INITIALIZER;
static Cmd*            lq_head;  // unanswered, oldest first
static Cmd**           lq_tail = &lq_head;

static void lq_release(Conn* c) {
  if (c->hung && c->pending == 0) {
    close(c->fd);
    free(c);
  }
}

static void lq_queue(Conn* c, const char* s, size_t n) {
  Cmd* m = calloc(1, sizeof *m);
  m->conn = c;
  m->line = strndup(s, n);
  pthread_mutex_lock(&lq_mu);
  c->pending += 1;
  *lq_tail = m;
  lq_tail  = &m->next;
  pthread_mutex_unlock(&lq_mu);
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
        if (len > 0) {
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
  pthread_mutex_lock(&lq_mu);
  c->hung = true;
  lq_release(c);
  pthread_mutex_unlock(&lq_mu);
  return NULL;
}

static void* lq_listen(void* arg) {
  int s = socket(AF_UNIX, SOCK_STREAM, 0);
  struct sockaddr_un a;
  memset(&a, 0, sizeof a);
  a.sun_family = AF_UNIX;
  const char* name = "leanquiet";
  memcpy(a.sun_path + 1, name, strlen(name));  // abstract: a leading NUL
  socklen_t len = (socklen_t)(offsetof(struct sockaddr_un, sun_path) + 1 + strlen(name));
  if (s < 0 || bind(s, (struct sockaddr*)&a, len) != 0 || listen(s, 8) != 0) {
    __android_log_write(ANDROID_LOG_ERROR, "lean", "control: cannot listen on @leanquiet");
    return NULL;
  }
  __android_log_write(ANDROID_LOG_INFO, "lean", "control: listening on @leanquiet");
  for (;;) {
    int fd = accept(s, NULL, NULL);
    if (fd < 0) {
      continue;
    }
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

void lq_ctl_start(void) {
  pthread_t t;
  if (pthread_create(&t, NULL, lq_listen, NULL) == 0) {
    pthread_detach(t);
  }
}

lean_obj_res lq_ctl_poll(void) {
  lean_object* out = lean_mk_empty_array();
  pthread_mutex_lock(&lq_mu);
  for (Cmd* m = lq_head; m != NULL; m = m->next) {
    if (!m->polled) {
      m->polled = true;
      out = lean_array_push(out, lean_mk_string(m->line));
    }
  }
  pthread_mutex_unlock(&lq_mu);
  return lean_io_result_mk_ok(out);
}

lean_obj_res lq_ctl_reply(b_lean_obj_arg s) {
  pthread_mutex_lock(&lq_mu);
  Cmd* m = lq_head;
  if (m != NULL && m->polled) {
    lq_head = m->next;
    if (lq_head == NULL) {
      lq_tail = &lq_head;
    }
  } else {
    m = NULL;
  }
  pthread_mutex_unlock(&lq_mu);
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
    ssize_t k = send(m->conn->fd, out + off, n + 1 - off, MSG_NOSIGNAL);
    if (k <= 0) {
      break;
    }
    off += (size_t)k;
  }
  free(out);
  pthread_mutex_lock(&lq_mu);
  m->conn->pending -= 1;
  lq_release(m->conn);
  pthread_mutex_unlock(&lq_mu);
  free(m->line);
  free(m);
  return lean_io_result_mk_ok(lean_box(0));
}
