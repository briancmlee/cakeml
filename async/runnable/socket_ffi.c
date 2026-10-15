/*
  The socket FFI for the verified echo server: TRUSTED CODE.

  The CakeML program (async/runnable/echo_server.sexp) calls four FFI
  functions, one per operation of the socket model
  (async/ffi-spike/ffiSpikeSocketFFIScript.sml).  Each C function below
  must behave as the model's ffi_sock_* function on the byte arrays:

  | FFI name    | model function   | conf (input)          | a (in/out)                     |
  |-------------|------------------|-----------------------|--------------------------------|
  | sock_poll   | ffi_sock_poll    | k fds, 8 bytes each   | k flags: 1 ready, 0 not        |
  | sock_accept | ffi_sock_accept  | listener fd (8 bytes) | 9 bytes: status (1 accepted,   |
  |             |                  |                       |   0 would block), new fd       |
  | sock_read   | ffi_sock_read    | connection fd (8)     | status (0 data, 1 would block, |
  |             |                  |                       |   2 EOF), 8-byte count, data   |
  | sock_write  | ffi_sock_write   | fd (8) ++ data        | unused                         |
  | sock_select | ffi_sock_select  | k fds, 8 bytes each   | empty (length 0)               |
  |             | (asyncM4BlkLoop) |                       |                                |

  sock_select is used only by the blocking echo program
  (async/m4-blocking, run_b).  The model's ffi_sock_select lets rounds of
  the world pass (sock_wait) until a poll of the fds would report one of
  them ready, and returns nothing; if that never happens it diverges
  (FFIdiverge).  Here: block in poll(2) with no timeout until one of the
  fds is ready (POLLIN/POLLHUP/POLLERR, as for sock_poll), consuming
  nothing.  The sock_poll that follows reports the ready set.  With no fd
  ready ever (or an empty list) this blocks forever, which is the model's
  divergence.  TRUST ITEM: this function behaves as ffi_sock_select.

  fds are 8-byte big-endian numbers (fd_bytes).  The model's readiness
  (is_ready): a listener with a pending connection, or a connection with
  unread data or EOF; in POSIX terms, POLLIN (or POLLHUP/POLLERR, on which
  a read returns EOF or an error, reported as EOF).

  The model's world starts with one listener.  It has no operation that
  creates listeners, so this file creates it before cml_main runs (a
  constructor function) as fd LFD = 3, the fd the program's main passes to
  the server.  Port: the CAKE_ECHO_PORT environment variable (default 7777),
  on 127.0.0.1.

  Where the real world is outside the model (each is a trust assumption):
   - errors: the model has none beyond EOF.  A read error (e.g. ECONNRESET)
     is reported as EOF; a write error (e.g. EPIPE: the peer has gone) drops
     the data; accept errors other than "would block" are reported as
     "would block".  Misuse that the model rejects (an fd that is not a
     socket) aborts the program, as the FFI call would fail in the model.
   - writes: the model's writes always succeed in full.  Accepted sockets
     are blocking, and sock_write loops until everything is sent.  A client
     that never reads can therefore stall the server.
   - time: the model's poll delivers one step of an arbitrary schedule of
     arrivals.  How long the real poll waits is therefore unobservable in
     the model.  This file waits only when the program is idle: no socket
     operation since the last poll and the same ready set for IDLE_ROUNDS
     polls in a row.  Then it waits (at most IDLE_WAIT_MS) for an fd that
     was not ready to become ready.  Otherwise the loop would spin.
     Compiling with -DNO_IDLE_WAIT turns this wait off: sock_poll then
     never waits, exactly as the model's poll (one round per call).  The
     blocking program does not need the wait (it sleeps in sock_select).
   - closing: the model has no close, so fds are never closed.  A closed
     connection stays ready (EOF) and stays in the loop's interest list.
*/
#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <poll.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

#define LFD 3
#define IDLE_ROUNDS 2
#define IDLE_WAIT_MS 50
#define MAX_FDS 4096

static void die(const char *msg) {
  fprintf(stderr, "socket_ffi: %s (errno %d: %s)\n", msg, errno, strerror(errno));
  exit(3);
}

/* fd_bytes / bytes_fd: 8 bytes, big-endian */
static long get_fd(const unsigned char *b) {
  uint64_t n = 0;
  for (int i = 0; i < 8; i++) n = (n << 8) | b[i];
  return (long)n;
}

static void put_be8(unsigned char *b, uint64_t n) {
  for (int i = 7; i >= 0; i--) { b[i] = n & 0xff; n >>= 8; }
}

/* The model's initial world: one listener, LFD, with an empty queue */
__attribute__((constructor)) static void make_listener(void) {
  const char *p = getenv("CAKE_ECHO_PORT");
  int port = p ? atoi(p) : 7777;
  signal(SIGPIPE, SIG_IGN);
  int s = socket(AF_INET, SOCK_STREAM, 0);
  if (s < 0) die("socket");
  int one = 1;
  setsockopt(s, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
  struct sockaddr_in a;
  memset(&a, 0, sizeof a);
  a.sin_family = AF_INET;
  a.sin_port = htons(port);
  a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  if (bind(s, (struct sockaddr *)&a, sizeof a) < 0) die("bind");
  if (listen(s, 128) < 0) die("listen");
  if (s != LFD) {
    if (dup2(s, LFD) < 0) die("dup2");
    close(s);
  }
  /* accept must not block: the model's accept reports "would block" */
  fcntl(LFD, F_SETFL, fcntl(LFD, F_GETFL) | O_NONBLOCK);
  fprintf(stderr, "echo server: listening on 127.0.0.1:%d\n", port);
}

/* Set by accept/read/write, cleared by poll: did the program do anything
   since the last poll? */
static int busy = 1;
static int idle_polls = 0;
static unsigned char last_ready[MAX_FDS];
static long last_n = -1;

/* The ready flags of fds[0..n), without waiting */
static void ready_now(struct pollfd *pfds, long n, unsigned char *flags) {
  if (poll(pfds, n, 0) < 0 && errno != EINTR) die("poll");
  for (long i = 0; i < n; i++) {
    if (pfds[i].revents & POLLNVAL) { errno = EBADF; die("poll: not an fd"); }
    flags[i] = (pfds[i].revents & (POLLIN | POLLHUP | POLLERR)) ? 1 : 0;
  }
}

/* ffi_sock_poll: one flag per given fd, 1 iff it is ready */
void ffisock_poll(unsigned char *c, long clen, unsigned char *a, long alen) {
  if (clen != 8 * alen || alen > MAX_FDS) { errno = EINVAL; die("sock_poll: lengths"); }
  long n = alen;
  struct pollfd pfds[MAX_FDS];
  for (long i = 0; i < n; i++) { pfds[i].fd = (int)get_fd(c + 8 * i); pfds[i].events = POLLIN; }
  ready_now(pfds, n, a);
  int same = (n == last_n) && memcmp(a, last_ready, n) == 0;
  idle_polls = (!busy && same) ? idle_polls + 1 : 0;
#ifdef NO_IDLE_WAIT
  if (0) {
#else
  if (idle_polls >= IDLE_ROUNDS) {
#endif
    /* idle: wait for one of the fds that are not ready to become ready */
    struct pollfd wait[MAX_FDS];
    long m = 0;
    for (long i = 0; i < n; i++) if (!a[i]) wait[m++] = pfds[i];
    if (poll(wait, m, IDLE_WAIT_MS) < 0 && errno != EINTR) die("poll");
    ready_now(pfds, n, a);
  }
  memcpy(last_ready, a, n);
  last_n = n;
  busy = 0;
}

/* ffi_sock_accept: a[0] = 1 and a[1..8] = the new fd, or a[0] = 0 */
void ffisock_accept(unsigned char *c, long clen, unsigned char *a, long alen) {
  if (clen != 8 || alen != 9) { errno = EINVAL; die("sock_accept: lengths"); }
  busy = 1;
  int fd = accept((int)get_fd(c), NULL, NULL);
  if (fd < 0) {
    if (errno == EBADF || errno == ENOTSOCK || errno == EINVAL) die("sock_accept");
    a[0] = 0;                     /* would block (or a transient error) */
    return;
  }
  /* reads are non-blocking per call (MSG_DONTWAIT); writes block */
  fcntl(fd, F_SETFL, fcntl(fd, F_GETFL) & ~O_NONBLOCK);
  int one = 1;
#ifdef SO_NOSIGPIPE
  setsockopt(fd, SOL_SOCKET, SO_NOSIGPIPE, &one, sizeof one);
#endif
  a[0] = 1;
  put_be8(a + 1, (uint64_t)fd);
}

/* ffi_sock_read: at most alen - 9 bytes */
void ffisock_read(unsigned char *c, long clen, unsigned char *a, long alen) {
  if (clen != 8 || alen <= 9) { errno = EINVAL; die("sock_read: lengths"); }
  busy = 1;
  ssize_t r = recv((int)get_fd(c), a + 9, alen - 9, MSG_DONTWAIT);
  if (r > 0) { a[0] = 0; put_be8(a + 1, (uint64_t)r); }
  else if (r == 0) a[0] = 2;                              /* EOF */
  else if (errno == EAGAIN || errno == EWOULDBLOCK || errno == EINTR) a[0] = 1;
  else if (errno == EBADF || errno == ENOTSOCK) die("sock_read");
  else a[0] = 2;                       /* e.g. ECONNRESET: reported as EOF */
}

/* ffi_sock_write: all of c[8..clen) to the fd in c[0..8) */
void ffisock_write(unsigned char *c, long clen, unsigned char *a, long alen) {
  if (clen < 8) { errno = EINVAL; die("sock_write: lengths"); }
  busy = 1;
  int fd = (int)get_fd(c);
  long off = 8;
  while (off < clen) {
    ssize_t w = send(fd, c + off, clen - off, 0);
    if (w > 0) off += w;
    else if (w < 0 && errno == EINTR) continue;
    else if (w < 0 && (errno == EBADF || errno == ENOTSOCK)) die("sock_write");
    else break;                    /* e.g. EPIPE: the peer has gone */
  }
}

/* ffi_sock_select: block until one of the fds c[0..clen) is ready; the
   buffer is empty and nothing is consumed.  (The model: sock_wait, then
   the next sock_poll reports the ready set.) */
void ffisock_select(unsigned char *c, long clen, unsigned char *a, long alen) {
  if (clen % 8 != 0 || alen != 0 || clen / 8 > MAX_FDS) {
    errno = EINVAL; die("sock_select: lengths");
  }
  long n = clen / 8;
  struct pollfd pfds[MAX_FDS];
  for (long i = 0; i < n; i++) { pfds[i].fd = (int)get_fd(c + 8 * i); pfds[i].events = POLLIN; }
  for (;;) {
    int r = poll(pfds, n, -1);       /* no timeout: n = 0 blocks forever */
    if (r < 0 && errno == EINTR) continue;
    if (r < 0) die("sock_select: poll");
    for (long i = 0; i < n; i++)
      if (pfds[i].revents & POLLNVAL) { errno = EBADF; die("sock_select: not an fd"); }
    return;
  }
}
