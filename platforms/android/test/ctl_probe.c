// Connects to the abstract socket @leanquiet, sends "ping", prints the reply (or nothing).
#include <stdio.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <unistd.h>
int main(void) {
  int s = socket(AF_UNIX, SOCK_STREAM, 0);
  struct sockaddr_un a = { .sun_family = AF_UNIX };
  const char* n = "leanquiet";
  memcpy(a.sun_path + 1, n, strlen(n));
  socklen_t len = (socklen_t)(offsetof(struct sockaddr_un, sun_path) + 1 + strlen(n));
  if (connect(s, (struct sockaddr*)&a, len) != 0) { puts("connect failed"); return 1; }
  write(s, "ping\n", 5);
  struct timeval tv = { 2, 0 };
  setsockopt(s, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv);
  char buf[64] = {0};
  ssize_t k = read(s, buf, sizeof buf - 1);
  printf("reply: %s\n", k > 0 ? buf : "(none: closed)");
  return 0;
}
