/*
  L0: the minimal honest socket FFI.  TRUSTED CODE (design/36 §3).

  Each entry point is one syscall (sys_listen: a fixed straight-line
  sequence) with some arguments FIXED, and an honest encoding of its
  result.  There is no retry, no loop other than the fixed 8-byte number
  codecs, and no decision that depends on errno except the error table.  Everything
  else (write loops, retries, what to do on reset or when out of fds)
  is verified CakeML (L1).

  The model: async/honest-l0/ (the L0 world), a sound over-approximation:
  every behaviour of this file plus the kernel must be a behaviour of
  the model.

  RESULT HEADER: every call's output buffer a, except sys_fdok's, starts
  with 13 bytes
      a[0]      code  : 0 = success, else err_code(errno); 255 = an errno
                        the table does not list (never disguised)
      a[1..8]   value : big-endian (fd, count); on error 0, or for
                        sys_listen the failing step 1..5
      a[9..12]  errno : the raw errno, big-endian (0 on success)

  | entry           | syscall, FIXED arguments                             | conf             | a after the header  |
  |-----------------|------------------------------------------------------|------------------|---------------------|
  | sys_listen      | socket(AF_INET, SOCK_STREAM, 0); setsockopt          | port (2 bytes)   | -                   |
  |                 | SO_REUSEADDR=1; bind 127.0.0.1:port; listen 128;     |                  |                     |
  |                 | fcntl F_SETFL O_NONBLOCK (accept never blocks)       |                  |                     |
  | sys_poll        | poll((struct pollfd *)(a + 16), k, block ? -1 : 0)   | block (0/1)      | 3 pad bytes, then   |
  |                 | on the caller's buffer, in place (no copy, no cap)   |                  | k struct pollfd     |
  |                 |                                                      |                  | (see below)         |
  | sys_accept      | accept(l, NULL, NULL)                                | listener fd      | -                   |
  | sys_recv        | recv(fd, buf, n, MSG_DONTWAIT)                       | fd               | n-byte data area    |
  | sys_send        | send(fd, data, len, MSG_DONTWAIT [| MSG_NOSIGNAL])    | fd ++ data       | -                   |
  | sys_shutdown    | shutdown(fd, SHUT_WR)                                | fd               | -                   |
  | sys_close       | close(fd)                                            | fd               | -                   |
  | sys_connect     | socket(AF_INET, SOCK_STREAM, 0); fcntl F_SETFL       | port (2 bytes)   | -                   |
  |                 | O_NONBLOCK; connect 127.0.0.1:port                   |                  |                     |
  | sys_connerr     | getsockopt(fd, SOL_SOCKET, SO_ERROR)                 | fd               | -                   |
  | sys_fdok        | fcntl(fd, F_GETFD)                                   | fd (1 byte)      | NO header: 1 byte,  |
  |                 |                                                      |                  | 1 open / 0 closed   |

  sys_poll (design/36 §9 D20): the caller's buffer a holds, after the
  13-byte header and 3 pad bytes (untouched), k = (alen - 16) / 8 entries
  in the platform's struct pollfd layout: fd (int32), events (int16),
  revents (int16), native (little-endian) byte order, the kernel writing
  revents in place.  The layout and the flag values POLLIN 1, POLLOUT 4,
  POLLERR 8, POLLHUP 16, POLLNVAL 32 are a BUILD-TIME-CHECKED ABI
  assumption (_Static_assert below; Linux and macOS agree).  If a + 16 is
  not aligned for struct pollfd (CakeML byte arrays are word-aligned, so
  it never is), the call fails with EINVAL without polling.

  sys_connect's value is the new fd as soon as socket() succeeded, also
  when connect then fails (EINPROGRESS: pending; ECONNREFUSED etc.:
  failed); the fd stays open until the program closes it.  Value 0: no fd
  (socket or fcntl failed; a program that has seen sys_fdok report fd 0
  open, and never closes it, never gets 0 as a new fd).
  sys_connerr: code 0 and value 0: no pending error; code e and value 1:
  the socket's pending error e (reading it clears it); code e and value
  0: getsockopt itself failed with e.

  What the fixed arguments rule out: blocking I/O (MSG_DONTWAIT; the
  socket's own O_NONBLOCK state is then irrelevant), other address
  families and addresses (IPv4 loopback only), UDP, other backlogs,
  peer addresses, MSG_PEEK/OOB/WAITALL, SHUT_RD, poll timeouts other
  than 0 and infinity.

  sys_fdok (D33, design/50 (c2)): a[0] = 1 if fd c[0] is open, 0 if not.
  [P fcntl]: F_GETFD fails (EBADF) exactly when the fd is not an open file
  descriptor.  The programs call it on 0, 1 and 2 first and stop if any is
  closed, so the check is in the verified program, not here.

  STARTUP CONTRACT (the constructor, before cml_main): SIGPIPE is ignored
  (a write to a gone peer is the EPIPE result, not a kill; macOS has no
  MSG_NOSIGNAL).

  MISUSE (exit 3; the model's call fails, FFI_failed): buffer lengths
  other than the above, a poll block flag other than 0/1, an fd above
  INT_MAX.  UNCHECKED (the model's call fails; the verified caller never
  does it): poll entries requesting events other than POLLIN, POLLOUT.
*/
#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <netinet/in.h>
#include <poll.h>
#include <signal.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

#define HDR 13
#define POLL_OFF 16  /* the pollfd entries' offset in sys_poll's buffer */

/* The struct pollfd ABI the model assumes (design/36 §9 D20) */
_Static_assert(sizeof(struct pollfd) == 8, "struct pollfd is 8 bytes");
_Static_assert(offsetof(struct pollfd, fd) == 0, "pollfd.fd at 0");
_Static_assert(offsetof(struct pollfd, events) == 4, "pollfd.events at 4");
_Static_assert(offsetof(struct pollfd, revents) == 6, "pollfd.revents at 6");
_Static_assert(sizeof(int) == 4 && sizeof(short) == 2, "int32 fd, int16 events");
_Static_assert(POLLIN == 1 && POLLOUT == 4 && POLLERR == 8 && POLLHUP == 16 && POLLNVAL == 32,
               "poll flag values");
#if !defined(__BYTE_ORDER__) || __BYTE_ORDER__ != __ORDER_LITTLE_ENDIAN__
#error "the L0 model assumes little-endian struct pollfd fields"
#endif
#ifdef MSG_NOSIGNAL
#define SEND_FLAGS (MSG_DONTWAIT | MSG_NOSIGNAL)
#else
#define SEND_FLAGS MSG_DONTWAIT
#endif

static void die(const char *msg) {
  fprintf(stderr, "socket_ffi_l0: %s\n", msg);
  exit(3);
}

static uint64_t get_be8(const unsigned char *b) {
  uint64_t n = 0;
  for (int i = 0; i < 8; i++) n = (n << 8) | b[i];
  return n;
}

static void put_be(unsigned char *b, int len, uint64_t n) {
  for (int i = len - 1; i >= 0; i--) { b[i] = n & 0xff; n >>= 8; }
}

static int get_fd(const unsigned char *b) {
  uint64_t n = get_be8(b);
  if (n > INT_MAX) die("fd out of range");
  return (int)n;
}

/* The error table: total; anything unlisted is 255 with its raw errno */
static unsigned char err_code(int e) {
  switch (e) {
  case EAGAIN: return 1;
#if EWOULDBLOCK != EAGAIN
  case EWOULDBLOCK: return 1;
#endif
  case EINTR: return 2;          case EINPROGRESS: return 3;
  case ECONNREFUSED: return 4;   case ECONNRESET: return 5;
  case EPIPE: return 6;          case ECONNABORTED: return 7;
  case ETIMEDOUT: return 8;      case ENOTCONN: return 9;
  case EMFILE: return 10;        case ENFILE: return 11;
  case ENOBUFS: return 12;       case ENOMEM: return 13;
  case EADDRINUSE: return 14;    case EACCES: return 15;
  case EBADF: return 16;         case ENOTSOCK: return 17;
  case EINVAL: return 18;        case ENETUNREACH: return 19;
  case EHOSTUNREACH: return 20;  case ENETDOWN: return 21;
  case EPROTO: return 22;
  default: return 255;
  }
}

/* The header for a syscall result r (r < 0: failed, with errno) */
static void put_res(unsigned char *a, long r) {
  int e = r < 0 ? errno : 0;
  a[0] = r < 0 ? err_code(e) : 0;
  put_be(a + 1, 8, r < 0 ? 0 : (uint64_t)r);
  put_be(a + 9, 4, (uint32_t)e);
}

__attribute__((constructor)) static void l0_startup(void) {
  signal(SIGPIPE, SIG_IGN);
}

/* sys_listen's failure at step k (1..5): the socket, if made, is closed */
static void listen_fail(unsigned char *a, int k, int s) {
  int e = errno;
  if (s >= 0) close(s);
  errno = e;
  put_res(a, -1);
  put_be(a + 1, 8, (uint64_t)k);
}

void ffisys_listen(unsigned char *c, long clen, unsigned char *a, long alen) {
  if (clen != 2 || alen != HDR) die("sys_listen: lengths");
  int one = 1;
  struct sockaddr_in ad;
  memset(&ad, 0, sizeof ad);
  ad.sin_family = AF_INET;
  ad.sin_port = htons((uint16_t)((c[0] << 8) | c[1]));
  ad.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  int s = socket(AF_INET, SOCK_STREAM, 0);
  if (s < 0) { listen_fail(a, 1, -1); return; }
  if (setsockopt(s, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one) < 0) { listen_fail(a, 2, s); return; }
  if (bind(s, (struct sockaddr *)&ad, sizeof ad) < 0) { listen_fail(a, 3, s); return; }
  if (listen(s, 128) < 0) { listen_fail(a, 4, s); return; }
  if (fcntl(s, F_SETFL, O_NONBLOCK) < 0) { listen_fail(a, 5, s); return; }
  put_res(a, s);
}

void ffisys_poll(unsigned char *c, long clen, unsigned char *a, long alen) {
  if (clen != 1 || c[0] > 1 || alen < POLL_OFF || (alen - POLL_OFF) % 8 != 0)
    die("sys_poll: lengths");
  unsigned char *p = a + POLL_OFF;
  if ((uintptr_t)p % _Alignof(struct pollfd) != 0) {
    errno = EINVAL;
    put_res(a, -1);
    return;
  }
  put_res(a, poll((struct pollfd *)(void *)p, (nfds_t)((alen - POLL_OFF) / 8), c[0] ? -1 : 0));
}

void ffisys_accept(unsigned char *c, long clen, unsigned char *a, long alen) {
  if (clen != 8 || alen != HDR) die("sys_accept: lengths");
  put_res(a, accept(get_fd(c), NULL, NULL));
}

void ffisys_recv(unsigned char *c, long clen, unsigned char *a, long alen) {
  if (clen != 8 || alen <= HDR) die("sys_recv: lengths");
  put_res(a, recv(get_fd(c), a + HDR, (size_t)(alen - HDR), MSG_DONTWAIT));
}

void ffisys_send(unsigned char *c, long clen, unsigned char *a, long alen) {
  if (clen < 8 || alen != HDR) die("sys_send: lengths");
  put_res(a, send(get_fd(c), c + 8, (size_t)(clen - 8), SEND_FLAGS));
}

void ffisys_shutdown(unsigned char *c, long clen, unsigned char *a, long alen) {
  if (clen != 8 || alen != HDR) die("sys_shutdown: lengths");
  put_res(a, shutdown(get_fd(c), SHUT_WR));
}

/* A result with error e and value v (sys_connect's fd, sys_connerr's flag) */
static void put_err_val(unsigned char *a, int e, uint64_t v) {
  a[0] = err_code(e);
  put_be(a + 1, 8, v);
  put_be(a + 9, 4, (uint32_t)e);
}

void ffisys_connect(unsigned char *c, long clen, unsigned char *a, long alen) {
  if (clen != 2 || alen != HDR) die("sys_connect: lengths");
  struct sockaddr_in ad;
  memset(&ad, 0, sizeof ad);
  ad.sin_family = AF_INET;
  ad.sin_port = htons((uint16_t)((c[0] << 8) | c[1]));
  ad.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  int s = socket(AF_INET, SOCK_STREAM, 0);
  if (s < 0) { put_res(a, -1); return; }
  if (fcntl(s, F_SETFL, O_NONBLOCK) < 0) {
    int e = errno; close(s); put_err_val(a, e, 0); return;
  }
  if (connect(s, (struct sockaddr *)&ad, sizeof ad) < 0) { put_err_val(a, errno, (uint64_t)s); return; }
  put_res(a, s);
}

void ffisys_connerr(unsigned char *c, long clen, unsigned char *a, long alen) {
  if (clen != 8 || alen != HDR) die("sys_connerr: lengths");
  int err = 0;
  socklen_t len = sizeof err;
  if (getsockopt(get_fd(c), SOL_SOCKET, SO_ERROR, &err, &len) < 0) { put_res(a, -1); return; }
  if (err == 0) put_res(a, 0);
  else put_err_val(a, err, 1);
}

void ffisys_close(unsigned char *c, long clen, unsigned char *a, long alen) {
  if (clen != 8 || alen != HDR) die("sys_close: lengths");
  put_res(a, close(get_fd(c)));
}

void ffisys_fdok(unsigned char *c, long clen, unsigned char *a, long alen) {
  if (clen != 1 || alen != 1) die("sys_fdok: lengths");
  a[0] = fcntl(c[0], F_GETFD) >= 0;
}
