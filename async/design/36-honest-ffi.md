# 36: An honest, minimal socket FFI, with verified wrappers (AUDIT + DESIGN, for review)

Status: **design accepted (§9); implementation started (§8 phases, stacked branches).** Branch `spike/honest-ffi`
(from `spike/endpoint-world`). Statement-only HOL drafts are in
`async/honest-ffi/` (§10). No existing file, spec or proof is changed.

## 0. Summary

**The principles** (the user's):

1. **Honesty.** The trusted C must not hide what the kernel does.
   Precisely: *every behaviour of the real C + kernel must be a behaviour
   of the HOL model* (the model is a sound over-approximation). A model may
   allow more than reality does; that only costs proof effort. A model that
   allows less is a lie: a theorem about it says nothing about some real
   runs.
2. **Minimality.** Each FFI entry point is (ideally) one syscall. Some
   arguments are fixed by the C to restrict behaviour. The result is
   encoded honestly. There are no loops, no retries and no policy in C.
3. **Layering.**
   - **L0**: the minimal honest FFI.
   - **L1**: verified CakeML wrappers, proved once against L0's model.
   - **L2**: the servers and the async library, proved only against L1's
     spec.
   Enriching L0 later touches only L1's proofs.

**The audit (§2).** Today's C has these lies:

- **11 lies (L)**, among them:
  - the four known ones (blocking `sock_write`, reset reported as EOF,
    accept errors reported as would-block, POLLERR/POLLHUP);
  - 7 more:
    - L5: fd exhaustion. **The deployed v1 echo server stops serving new
      clients after about 250 connections on macOS (`ulimit -n` is 256)
      and then busy-spins.** Its liveness theorem is proved in a world
      with 2^64 fds;
    - L6, L7: arrivals between calls, and short reads. The model lets
      time pass only at `sock_poll`;
    - L8: close with unread input sends RST, so data the program wrote
      can be lost;
    - L9: closed or unopened fds 0–2 at startup;
    - L10: fd truncation to `int`;
    - L11: recv errors other than reset (ENOBUFS etc.) are reported as
      EOF.
- **4 model-level lies** in the endpoint world (M1–M4), which the honest
  C would expose.
- The C's `die`s are crashes on misuse (C). They are fine when the model
  makes the same calls fail. One of them (POLLNVAL) is not matched by the
  model.

**The design.**

- **L0 (§3)** has 7 entry points: `sys_listen`, `sys_poll`, `sys_accept`,
  `sys_recv`, `sys_send`, `sys_shutdown`, `sys_close`, plus `sys_connect`
  and `sys_connerr` when clients land.
  - Every result is the same 13-byte header: a status code from a total
    errno table, an 8-byte value, and the raw errno.
  - About **90 lines of C** (today: about 140 lines of code), with no
    loops other than array marshalling.
  - The startup contract shrinks to one line, `signal(SIGPIPE, SIG_IGN)`,
    plus a documented precondition (fds 0–2 are open).
- **L1 (§5)** is one verified layer, an extension of close-v2's handle
  layer (`asyncHL`). It has:
  - per-fd outboxes (write_all);
  - read pausing at a high-water mark;
  - error absorption: reset ↦ end of stream, peer-gone ↦ drop the outbox;
  - out-of-fds handling (listener interest suppressed until a close);
  - EINTR retry;
  - graceful close;
  - the **round discipline** that lets the honest, time-anywhere L0 world
    look like the existing round-based worlds.
- **The key result:** **L1's spec is the existing version-1/version-2
  socket world, unchanged.**
  - The refinement theorem (§6) says that every run of
    (L1 loop + server) in an L0 world is a run of (old loop + server) in
    *some* version-2 (resp. version-1) world.
  - So **every existing server theorem is reused as is**, and **no
    server proof is touched**: not even for the general theorems under
    backpressure and errors.
  - What changes is the headline statements: they move to the raw trace,
    with per-guarantee antecedents (§7).

**Cost (§8).** About 3–4 weeks of agent time. The bulk is L1's CakeML
loop with its CF proof, and the regrouping simulation.

**Decisions: §9** (taken 2026-10-16).

---

## 1. What the specs trust today

The proofs end at a HOL socket model:

- version 1: `ffiSpikeSocketFFI`;
- version 2: `socketV2FFI`;
- the blocking select: `asyncM4BlkLoop.ffi_sock_select`, and QuietSpec's
  `ffi_select`;
- the endpoint world (draft): `endpointWorld`.

`async/runnable/socket_ffi.c` (review/12-close-v2 version; 210 lines,
about 140 of code) is assumed to implement it. The tester (design/29) found
0 divergences in 20177 calls, but by construction it avoided every case
below (§3 of design/29 lists several of them).

## 2. The audit

The classes:

- **L**: a real behaviour the model does not have (a lie);
- **A**: an acceptable abstraction (the model over-approximates, or the
  difference cannot be observed by any program; the reason is given);
- **C**: a crash (`die`, exit 3) on misuse, where the model's call fails
  too (`NONE`, so `FFI_failed`); a proved program never does it.

### 2.1 The constructor `make_listener` (runs before `cml_main`)

| syscall behaviour | model | class |
|---|---|---|
| `socket`/`bind`/`listen` fail (port in use, EACCES) → `die` before main | the initial world has the listener | **A**: no run of the program exists, so the theorem is about runs that got past setup. Documented as a startup contract. Under L0 this becomes a program-visible error (§3) |
| `setsockopt(SO_REUSEADDR)` and `fcntl(O_NONBLOCK)` results unchecked | listener is non-blocking (accept never blocks) | **L (latent)**: if `fcntl` failed, `accept` could block forever. Practically unreachable, but unchecked |
| `dup2(s, 3)`: the listener is fd 3 | `lfd = 3w` | A (contract). L0 drops it: the kernel's fd is returned to the program |
| fds 0, 1, 2 assumed open | v2/endpoint `reserved = [0;1;2]`; `alloc_ok` never returns a reserved fd | **L9**: started with fd 0/1/2 closed (e.g. by a daemoniser), `socket()` returns 0, `dup2` moves it, and fd 0 is now free. `accept` returns 0, which the model says it never does. Worse, the basis' stdout/stderr writes would go to a client socket |
| `signal(SIGPIPE, SIG_IGN)` | — | A: needed so that EPIPE is a result, not a kill. Kept as the one-line startup contract |
| port from `CAKE_ECHO_PORT`, 127.0.0.1 only | addresses are abstract | A |

### 2.2 `ffisock_poll` (v1/v2 `ffi_sock_poll`, `poll(2)` with timeout 0)

| syscall behaviour | model | class |
|---|---|---|
| POLLIN/POLLHUP/POLLERR → flag 1 | `is_ready`: pending connection, unread data, or EOF | **L4**, in combination with L2: POLLERR (reset) is shown as "ready", and the read then says EOF. The flag alone is defensible: "a read will not would-block" is true under POLLERR/POLLHUP. The lie is in the read. Under L0 the raw `revents` are passed through (§3) |
| POLLNVAL (fd not open) → `die` | unknown fd → flag 0 (not a failure) | **C, unmatched**: the model answers, the C crashes. A v2 program that polls a closed fd is fine in the model and dies for real (if the fd was not reused); if the fd was reused, it polls someone else's connection, which the model also does. Fix in L0: report NVAL honestly; L1 proves it never happens |
| `poll` fails with EINTR → flags from stale `revents` | — | **L (small)**: on EINTR `revents` are unspecified, and the C reads them anyway. Impossible with timeout 0 in practice, but not handled |
| `poll` fails with ENOMEM/EINVAL (nfds > RLIMIT_NOFILE) → `die` | always answers | **C (unmatched)** for >RLIMIT fds; unreachable before L5 bites |
| `MAX_FDS` 4096 → `die` | no limit | C (unmatched); unreachable before L5 |
| returns at once (timeout 0) | one tick of the schedule | A: the schedule is an arbitrary grouping of arrivals into steps. **But** see L6 |

### 2.3 `ffisock_accept` (`ffi_sock_accept`, `accept(2)` on a non-blocking listener)

| syscall behaviour | model | class |
|---|---|---|
| a connection → fd; then `fcntl(~O_NONBLOCK)` and `setsockopt(SO_NOSIGPIPE)`, results unchecked | accepted, `fd` is the client's (v1: chosen by the schedule; v2: `alloc`) | A (the extra syscalls are policy; L0 removes them) |
| EAGAIN → status 0 | queue empty → 0 | ✓ |
| **ECONNABORTED** (BSD/macOS: a pending connection was reset before accept), Linux's pending network errors (ENETDOWN, EPROTO, EHOSTUNREACH, ...), EPERM (firewall) → status 0 | 0 only if the queue is empty | **L3**: "would block" while other connections may be pending. The listener stays readable, so a select-based loop re-polls at once |
| **EMFILE/ENFILE** → status 0 | `ep_alloc` fails only at 2^64 fds (v2/endpoint); v1 has no limit at all | **L5**: the connection stays queued and the listener stays readable. Every round, accept fails. A polling loop (echo v1) burns CPU and never serves a new client again. The blocking loop (`run_b`) busy-spins in `sock_select`, which QuietSpec's quiescence claim denies. **v1 programs never close, so they hit this after `RLIMIT_NOFILE − 4` clients (macOS default 256, Linux 1024).** The proved `echo_live` ("every client is served") is false for real for client 253 on a default macOS |
| ENOBUFS/ENOMEM → status 0 | — | L3 (transient) |
| EBADF/ENOTSOCK/EINVAL → `die` | not a listener → `NONE` | C ✓ |
| EINTR → status 0 | — | A: impossible on a non-blocking socket |

### 2.4 `ffisock_read` (`ffi_sock_read`, `recv(MSG_DONTWAIT)`)

| syscall behaviour | model | class |
|---|---|---|
| r > 0: data, at most `alen − 9` bytes | `TAKE n incoming` (all available, up to n) | **L7**: `recv` may return fewer bytes than are available (segment boundaries, a real network). A second read in the same round then returns more. In the model, without a tick, the second read returns would-block. design/29 §3.4 calls this "covered by the schedule", but it is not: the schedule only changes at polls. Unobservable on loopback, real on a network |
| r = 0: EOF | `peer_closed` and nothing unread | ✓ |
| EAGAIN → 1 | nothing unread, no EOF | ✓ |
| **EINTR → 1** (would block) | would-block only with nothing unread | A: impossible with MSG_DONTWAIT. But if it happened, it would be a lie (data present). L0 reports it honestly |
| **ECONNRESET, ETIMEDOUT, ENOTCONN, EHOSTUNREACH → 2 (EOF)** | no errors | **L2**: a broken connection looks like an orderly close. The specs' liveness clauses then speak of a client that "closed" when it crashed |
| **ENOBUFS/ENOMEM → 2 (EOF)** | — | **L11**: a transient resource error is reported as the end of the stream; the program drops a live client |
| EBADF/ENOTSOCK → `die` | not a connection → `NONE` | C ✓ (v2: a closed fd fails in both) |

### 2.5 `ffisock_write` (`ffi_sock_write`: all bytes appended to `outgoing`, instantly)

| syscall behaviour | model | class |
|---|---|---|
| the socket is **blocking**; the C loops `send` until everything is sent | instant, complete | **L1**: a client that stops reading stalls the whole single-threaded server for ever (slow-reader DoS). Every other client's liveness is proved in the model and false for real. Also: time passes inside the call (the peer reads), which the model forbids |
| **EPIPE/ECONNRESET → stop, report success** | all bytes in `outgoing` | **L1′**: the rest of the data is silently dropped; the model says it was written. The specs' `bytes_written_to` counts bytes that never left |
| `send` returns 0 → stop | — | A: does not happen for len > 0 |
| EINTR → retry | — | A (policy in C; L0 moves it to CakeML) |
| EBADF/ENOTSOCK → `die` | `NONE` | C ✓ |

### 2.6 `ffisock_select` (`ffi_sock_select`/QuietSpec `ffi_select`: block until a poll would report one fd ready)

| syscall behaviour | model | class |
|---|---|---|
| `poll(-1)`, returns when any fd has POLLIN/HUP/ERR | `sock_wait`: the first tick at which some fd `is_ready` | ✓, except L4/L2 as for poll |
| EINTR → retry | — | A (policy in C; L0 reports it) |
| POLLNVAL → `die` | `asyncM4BlkLoop`'s version: unknown fds never ready (no failure), **unmatched** C; QuietSpec's `sel_ok`: fails, C ✓ | C (one of two models unmatched) |
| fd exhaustion (L5) → listener POLLIN for ever → `sock_select` returns at once, accept fails, repeat | `sock_wait` never returns for a listener whose queue is not served... | **L5 again**: a 100% CPU spin that the model (and QuietSpec) excludes |

### 2.7 `ffisock_close` (`ffi_sock_close2`)

| syscall behaviour | model | class |
|---|---|---|
| `close(fd)`; EINTR ignored | the fd is free; the client's stream stays | A (on Linux the fd is closed even on EINTR; on macOS likewise for sockets) |
| **closing with unread input sends RST**: the peer may lose data still in flight that the program wrote | nothing is lost; `outgoing` is what the client gets | **L8**: a server that writes a response and closes while the client has pipelined more data can destroy its own response. (EchoSpec2's server closes after EOF, when nothing is unread, so it is safe. HTTP's planned close-after-response is not, without a lingering close) |
| EBADF → `die` | not an open connection → `NONE` | C ✓ |

### 2.8 Across all calls

- **L6, time.**
  - The models let time pass only at `sock_poll` (and `select`). The
    kernel changes state at any moment.
  - A program that sees "not ready" or "would block" and then, before
    the next poll, calls again on the same fd can get data. The model
    says that is impossible.
  - This is the same root cause as L7. It is a lie of the model, not of
    the C.
  - **Mitigation (§5.3):** our servers call `read`/`accept` only on fds
    the last poll reported ready, once per round (`asyncServer`'s
    `handler` waits `readable` before each read). L1 enforces this
    discipline for every server, and the refinement theorem turns it
    into a proof.
- **L10, fd truncation.** `get_fd` casts a 64-bit fd to `int`, so fd
  2^32 + 3 acts on the listener. The model treats it as unknown. A proved
  program never does this (fds come from the world), but the C should
  check.
- **Endpoint world, model level** (would become visible once the C is
  honest):
  - **M1**: when no fd is free, `ep_accept` returns "would block" while
    the queue is non-empty, which is L5 inside the model;
  - **M2**: `ep_send` on a shut or refused channel accepts 0 bytes, which
    means would-block for ever. Really it is EPIPE/ECONNREFUSED;
  - **M3**: a refused connect reads as EOF. Really it is an error;
  - **M4**: `takes j b n` is a fixed function and `Drain` is all-or-nothing.
    In reality the kernel's acceptance varies with time (autotuned
    buffers, partial reads by the peer). So some real sequences of partial
    sends are not model sequences (decision 1 of design/35).

## 3. L0: the minimal honest FFI

### 3.1 The result header (all calls)

Every call's output buffer starts with 13 bytes:

    out[0]      code   : 0 = OK, else the error (table below)
    out[1..8]   value  : 8 bytes big-endian (an fd, a count, ...); 0 on error
    out[9..12]  errno  : the raw errno, 4 bytes (0 on success)

**The error table** is **total**: an errno the table does not list is
code 255 (OTHER), with the raw value. Nothing is ever folded into
success, EOF or would-block.

| code | errno | code | errno |
|---|---|---|---|
| 1 | EAGAIN, EWOULDBLOCK | 12 | ENOBUFS |
| 2 | EINTR | 13 | ENOMEM |
| 3 | EINPROGRESS | 14 | EADDRINUSE |
| 4 | ECONNREFUSED | 15 | EACCES |
| 5 | ECONNRESET | 16 | EBADF |
| 6 | EPIPE | 17 | ENOTSOCK |
| 7 | ECONNABORTED | 18 | EINVAL |
| 8 | ETIMEDOUT | 19 | ENETUNREACH |
| 9 | ENOTCONN | 20 | EHOSTUNREACH |
| 10 | EMFILE | 21 | ENETDOWN |
| 11 | ENFILE | 22 | EPROTO |
| 255 | anything else | | |

(EAGAIN and EWOULDBLOCK are the same number on Linux and macOS.) The
table is a `switch`: one function, about 25 lines.

In the model, `errno` is opaque. The model fixes which **codes** a call
may return in which state (§4); the raw errno is the world's choice.

**Misuse that the model rejects** still fails, with `die`:

- buffer lengths;
- an fd ≥ 2^31 (fixes L10).

These are class C: the model's call returns `NONE`. **Not misuse any
more:**

- EBADF and ENOTSOCK are reported as codes 16/17. The model returns them
  for unknown fds;
- POLLNVAL is reported as a flag.

So the C has only two kinds of `die`, both length/range checks.

### 3.2 The entry points

All socket calls fix `MSG_DONTWAIT`. So **no call ever blocks**, except
`sys_poll` with its block flag set. The socket's own `O_NONBLOCK` state
is then irrelevant: macOS's accepted sockets inherit it, Linux's don't.
That removes `fcntl` from accept.

| call | syscall (fixed args) | conf | out after the header | what the fixed args rule out |
|---|---|---|---|---|
| `sys_listen` | `socket(AF_INET, SOCK_STREAM, 0)`; `setsockopt(SO_REUSEADDR, 1)`; `bind(127.0.0.1:port)`; `listen(fd, 128)`; `fcntl(F_SETFL, O_NONBLOCK)`: a straight line that stops at the first failure and reports it (value: the failing step, 1..5) | port, 2 bytes | — (value: the listener fd) | other families, other addresses (loopback only), UDP, other backlogs. The non-blocking listener makes `accept` never block, even when a pending connection vanishes between poll and accept |
| `sys_poll` | `poll((struct pollfd *)(a + 16), k, block ? -1 : 0)`, in place on the caller's buffer (D20, §3.6) | 1 byte block flag | 3 pad bytes (untouched), then k `struct pollfd` (fd int32, events int16, revents int16, native byte order), the kernel writing `revents` | priority bands, timeouts other than 0 and ∞ (no timers yet) |
| `sys_accept` | `accept(l, NULL, NULL)` | listener fd | — (value: the new fd) | peer addresses |
| `sys_recv` | `recv(fd, buf, n, MSG_DONTWAIT)` | fd | value: count (0 = EOF); then the n-byte data area | blocking, MSG_PEEK, OOB, MSG_WAITALL |
| `sys_send` | `send(fd, buf, len, MSG_DONTWAIT \| MSG_NOSIGNAL`(Linux)`)` | fd ++ data | value: the count accepted | blocking; SIGPIPE (with the startup contract on macOS); OOB |
| `sys_shutdown` | `shutdown(fd, SHUT_WR)` | fd | — | SHUT_RD/SHUT_RDWR (no use for them) |
| `sys_close` | `close(fd)` | fd | — | — |
| *later:* `sys_connect` | `socket(AF_INET, SOCK_STREAM, 0)`; `fcntl(O_NONBLOCK)`; `connect(127.0.0.1:port)`: a straight line | port | value: the fd once `socket` succeeded (the fd is returned even when connect fails; closing it is the program's job). Code 0 = connected; 3 (EINPROGRESS) = pending; 4 (ECONNREFUSED) etc. = failed | other addresses |
| *later:* `sys_connerr` | `getsockopt(fd, SOL_SOCKET, SO_ERROR)` | fd | code = the pending error (0: none) | — |

**On `sys_listen` and `sys_connect`.** These are straight-line sequences,
not single syscalls. The alternative was 4–5 L0 calls (socket, setsockopt,
bind, listen, fcntl) and a model of unbound/bound/listening sockets that
no program needs. Recommended: keep each as **one restricted call**, "make
a non-blocking loopback listener on this port", with honest failure
reporting (which step failed, and its errno). Each step is one `if`
that returns the error. That is result encoding, not policy. **Decision
D2.**

### 3.3 The startup contract: what stays outside the model

**Recommendation (D2):** move listener creation into the program
(`sys_listen`), and keep only this as a documented contract:

1. **`signal(SIGPIPE, SIG_IGN)` in a constructor.** On Linux,
   `MSG_NOSIGNAL` would suffice. macOS has no `MSG_NOSIGNAL`, and the
   alternative is a second syscall in every accept (`SO_NOSIGPIPE`).
   Ignoring SIGPIPE only turns a process kill into the EPIPE result the
   model already has, so it hides nothing.
2. **Precondition: fds 0, 1, 2 are open at start** (fixes L9 by contract).
   The alternative is a check in the constructor (`fcntl(F_GETFD)` on 0–2,
   exit if closed). Recommended: do the check. It is three syscalls in
   straight line, and it makes the model's `reserved` true.

The port moves into CakeML: the program reads it from its command line
(basis `CommandLine`), or uses a constant.

**Consequence for the specs:** the world starts **without** a listener.
The first event of every trace is `sys_listen`.

- The old specs (listener `3w` at the start) are recovered by a view that
  starts after a successful `sys_listen`. With fds 0–2 open, `alloc` is
  the lowest free fd, which is 3 when nothing else is open (that is a
  property of `lowest_free`, not an assumption).
- A failed listen is a normal outcome: the wrapper exits with a message.
  The spec says "if listen succeeds, then ...".

The fallback, if you'd rather not touch the initial world now: keep
today's constructor without `dup2`, with checked syscalls. It is a
documented contract, 15 lines, with everything else as above.

### 3.4 Size

Estimated, excluding comments:

| part | lines of code |
|---|---|
| fd/number helpers (get_fd with a range check, put_be8, put_be4) | 15 |
| the errno table | 25 |
| the result header writer | 5 |
| the constructor (SIGPIPE, fds 0–2 check) | 8 |
| listen | 14 |
| poll (a pass-through since D20: length and alignment checks) | 8 |
| accept | 4 |
| recv | 5 |
| send | 5 |
| shutdown, close | 6 |
| **total** | **≈ 100** estimated; **130 as written** (`socket_ffi_l0.c`, two error cases per line), of which the error table is a quarter |

Today it is about 140 lines of code. More important than the count:

- **no loops** except the fixed 8-byte number codecs (since D20, poll
  has no marshalling loop and no cap);
- **no retries;**
- **no decision depends on errno**, except the table.

The C is one screen of "call the syscall, encode the result". connect
adds about 15 lines later.

### 3.5 Size against effort: four points on the curve

**The main finding.** Most of the verification cost does not come from
how small the C is. It comes from **being honest about writes and
errors**:

- an honest `send` is partial, so some verified code must buffer and
  retry: that is L1's outbox;
- an honest `recv`/`accept` has errors, so some verified code must decide
  what to do with them.

Every point below therefore needs the L1 core. Shrinking the C further
adds only small, local CakeML work.

Separately from the C, design decision D3 (time, L6) adds about 3 days to
any point; it is a model question, not a C question.

Effort is in agent-days at our observed pace (CF-heavy days ≈ 6–8 worker
hours; e.g. close-v2's handle layer, about 500 lines of HOL+CF, took about
2 days).

| point | trusted C (code lines / `if`s / loops) | what the C still decides | moves into CakeML (L1), and its cost | world model | tester | existing proofs needing refinement work |
|---|---|---|---|---|---|---|
| **(a) lies-only patch** of today's file | ≈ 150 / ≈ 26 / 3 (marshalling + select's EINTR retry) | the constructor (incl. `dup2` → 3); retries on EINTR; the errno → status mapping per call (ad hoc, but honest: reset, exhausted and aborted get their own status) | write buffering (partial sends, OUT interest), reset ↦ EOF policy, exhausted ↦ drop listener interest, graceful close. **≈ 15–16 days** (§8 phases 3–8 minus the EINTR and listen parts) | the endpoint extensions of §4, minus EINTR/transient choices | new scenarios: slow reader, RST, EMFILE, aborted | none of the servers; the loop and FFI CF specs are new (new encodings); the specs' initial world is unchanged |
| **(b) medium**: one syscall per call, fixed args, the §3.1 header and total table; **setup kept as a documented constructor** (socket/bind/listen/`dup2` → 3, SIGPIPE, fds 0–2 check) | ≈ 110 / ≈ 12 + one `switch` / 2 (marshalling only) | the constructor only | (a) + EINTR retry and transient codes in every wrapper: **+0.5 day ≈ 16 days** | (a) + `transient` choices | (a) + EINTR is hard to provoke (signal storms); test via `SA_RESTART` off | as (a) |
| **(c) minimal** (recommended): (b), with setup as the program's `sys_listen` call; the constructor keeps only SIGPIPE and the fds 0–2 check | ≈ 100 / ≈ 12 + `switch` / 2 | nothing beyond encoding | (b) + the listen sequence, port parsing and exit on failure, plus the raw specs' "starts with a successful `sys_listen`" view: **+1.5 days ≈ 17–18 days** | (b) + listeners created by a call (`ep_listen`, which may fail) | (b) + port-in-use, EACCES | as (a), plus the trace view drops `sys_listen` (inside the transfer lemmas, not the servers) |
| **(d) raw errno**: (c) without the errno table; the C returns the raw errno, and CakeML decodes it with a per-platform table | ≈ 75 / ≈ 8 / 2 | nothing at all: every call is "syscall, then copy the result out" | (c) + a CakeML decoder, but **the two platform tables (Linux, macOS errno numbers) become trusted HOL constants**: **+1 day ≈ 18–19 days** | (c), parameterised by the platform table | (c) + run on both platforms | as (c) |

A generic "syscall with fixed arguments" shim (one entry point that
dispatches on a call number) was considered and is **not recommended**:

- it saves about 20 more lines;
- it moves the per-call meaning into a dispatch table that must be
  trusted just the same;
- it makes the FFI names in the trace less readable, and readable traces
  are what the specs are stated on.

**Recommendation: (c).** It has the "nothing but encode/decode" property
for about 1.5 days more than (b). (d) only moves trust from C into HOL
constants.

### 3.6 `sys_poll` on CakeML's `struct pollfd` buffer (D20)

The C used to copy k × 9 bytes into a stack array of at most 4096
`struct pollfd` (`MAX_FDS`, a `die` beyond) and copy the revents back,
and L1 polled in chunks of 4096 (`poll_chunks`). Now CakeML lays out the
entries itself (`poll_buf`, `pfd_bytes` in `honestL1Model`) and the C
passes the buffer to `poll` as it is: no loop, no copy, no cap. L1 polls
once per round.

**The trusted surface for `sys_poll` after D20:**

| item | what | how it is justified |
|---|---|---|
| ABI layout | `struct pollfd` is 8 bytes: `int fd` at 0, `short events` at 4, `short revents` at 6; little-endian; POLLIN 1, POLLOUT 4, POLLERR 8, POLLHUP 16, POLLNVAL 32 | **build-time checked**: `_Static_assert`s and an endianness `#error` in the C. Linux and macOS agree. The L0 model (`pollfd_entries`, `pe_fd`, `abi_rev`, `abi_revents`) reads the same layout |
| alignment | `a + 16` aligned for `struct pollfd`; otherwise EINVAL without polling | **runtime checked** in the C; the model allows the failure (any error, [P 2.3]). CakeML byte arrays are word-aligned, so it never fires: `make align` runs 64 real polls from a CakeML program at varying heap positions |
| events | each entry requests POLLIN, POLLOUT, both or nothing | **unchecked precondition** on the caller: the model's call fails (`pe_ok`) otherwise, and L1 never does it (proved: `poll_set_small`, `e < 4`, so `pfd_bytes` writes 0, 1, 4 or 5) |
| fds | the 4-byte field is a C `int`; a negative one is ignored by poll [P poll] | model: an fd field ≥ 2^31 gets revents 0 (`pfd_revents`). L1 only polls fds < 2^31 (`psmall`, proved along runs) |
| bytes left alone | the header's 3 pad bytes and each entry's fd and events | the model returns them unchanged; the tester checks it |
| failed poll | revents unspecified | `poll_junk`, a world choice per byte |

## 4. L0's world model

**As built (phase 3):** a new theory, `async/honest-l0/honestL0WorldScript.sml`
(trusted). It sits beside close-v2's `endpointWorld`, which stays the
idealised world (agreed with close-v2: they fix M2/M3 there; M1, M4 and
D3's time are fixed here). It is anchored on the standards (§4.2) and
checked by conformance tests (§4.3). The rely is in
`honestL0RelyScript.sml`; `honestL0WorldPropsScript.sml` proves that
buffers keep their length and that the rely holds along a run. The text
below is the original proposal; where they differ, §4.2 and the theory
win.

The design rule: **over-approximate**.
Wherever platforms differ or timing is uncontrollable, the model lets the
world choose (a field of the world, ∀-quantified in specs), and L1 must
handle every choice.

**Channel state** (added to `chan`):

- `err : errcode option`: the pending socket error (`sk_err`/`so_error`),
  set by a reset or a refused connect, and cleared when a call reports it;
- `broken : bool`: sticky; set once an error has occurred;
- `aborted : bool`: the program closed with unread input (RST sent).

**World fields:**

- `fd_limit : num`: RLIMIT_NOFILE (fixes M1/L5). `ep_alloc` fails when
  `LENGTH (ep_used w) ≥ fd_limit`;
- `takes` becomes history-dependent: `takes j hist b n` (fixes M4; this
  resolves design/35's decision 1 the honest way);
- `short : num -> call list -> num -> num`: how many of the available
  bytes `recv` returns, at least 1 (fixes L7);
- `transient : call list -> mlstring -> errcode option`: the world may
  make any call fail with EINTR, ENOBUFS or ENOMEM (over-approximation;
  covers L11 and EINTR);
- `abort_on_accept : bool`: whether a reset pending connection is
  returned by accept (Linux) or dropped with ECONNABORTED (BSD).

**Arrivals.**

- Existing: `Incoming a`, `PData j bs`, `PEof j`, `Drain j`.
- New: `PReset j e` (the connection breaks: `err := SOME e`,
  `broken := T`; the world may also discard the unread input), and
  `Drain j k` (partial drain).
- **Time (fixes L6):** the environment may deliver arrivals before
  *every* call, not only at polls. The model: `ep_ffi_fn` runs
  `w.env_mid w.hist` before the call.
- The simple instance: `env_mid = K []`.

**Per call, which results are possible:**

| call | possible results |
|---|---|
| `sys_poll` | IN iff (listener with a queue, or channel with inbox ≠ [] or `peer_eof` or `err ≠ NONE` or `broken`); OUT iff (Up, ¬shut, `takes j hist inflight 1 > 0`) or `broken`; ERR only if `err ≠ NONE`; HUP only if `broken` or (`peer_eof` ∧ `shut`); the world chooses within these "only if"s (macOS and Linux differ on HUP); NVAL iff the fd is not open. With the block flag set: ticks until some revents ≠ 0, or diverges (`FFIdiverge`, as `ffi_sock_select`). EINTR: world's choice |
| `sys_accept` | an fd (alloc) when the queue is non-empty and `fd_limit` permits; EMFILE (ENFILE: world's choice) when not, with the connection staying queued; EAGAIN when the queue is empty; ECONNABORTED (pops a reset pending connection) if `¬abort_on_accept`; transient codes |
| `sys_recv` | data (`short` of `TAKE n inbox`) if inbox ≠ []; else the pending `err` (and clear it) if set; else count 0 (EOF) if `peer_eof` or `broken`; else EAGAIN. Unknown fd: EBADF. Transient codes |
| `sys_send` | `err` if pending (cleared); EPIPE if `shut` or `broken`; else count = `takes j hist inflight n`, or EAGAIN if that is 0. Unknown fd: EBADF |
| `sys_close` | frees the fd; sets `aborted` if inbox ≠ [] (the peer's view: in-flight bytes may be lost) |
| `sys_shutdown` | `shut := T` |
| *connect* (for close-v2) | see §4.1 |

**The simple instance** `simple0 w` is:

- `takes` = full;
- `short` = all;
- `transient = K NONE`;
- no `PReset` arrivals;
- `fd_limit` = ∞ (`dimword`);
- `env_mid = K []`.

The design keeps "the simple worlds are instances" (design/35 §3).

**The rely gains nothing progress-like.** Progress assumptions stay
per-guarantee:

- `reads_fair` (§7) is redefined as "channel c is writable infinitely
  often";
- `no_reset w io c`;
- `fd_room` (for v2 programs: free fds keep reappearing).

### 4.1 Refused connects: the encoding for close-v2

So that the endpoint world's draft and L0 agree (close-v2 implements
this; settled here):

- **`sys_connect` result:**
  - code 0: connected at once;
  - code 3 (EINPROGRESS): pending;
  - code 4 (ECONNREFUSED) or another code: failed at once.
  The value is always the fd, if one was allocated.
- **A refused channel keeps its fd until the program closes it**, whether
  it was refused at once (code 4) or after pending (settled at a tick).
  This is POSIX: a failed connect leaves the socket open. So the fd is
  never reused before `sys_close`, and fd discipline and `alloc` are
  unchanged. Closing it is L1's job (the connect wrapper closes on
  failure).
- **In the endpoint world:** `status = Connecting | Up | Refused`. A
  refusal settled at a tick sets `err := SOME ECONNREFUSED` and
  `broken := T` (a pending error, as the kernel's `so_error`).
- **poll** on a refused channel: IN, OUT and ERR (Linux reports
  POLLERR|POLLHUP|POLLIN|POLLOUT; the world may choose any superset of
  {ERR} ∪ {OUT}).
- **`sys_connerr`:** ECONNREFUSED the first time, then 0. As the kernel,
  reading the pending error clears it.
- **`sys_recv`:** ECONNREFUSED if the error is still pending, then EOF
  (count 0).
- **`sys_send`:** ECONNREFUSED if still pending, then EPIPE.
- **Legacy `«sock_*»` calls** (v1/v2 encodings, kept for the v1/v2
  instances as close-v2 requires): `«sock_read»` on a refused channel
  returns a new status byte **3 = error**, with the error code in byte 1,
  not EOF (fixes M3). `«sock_send»` (endpoint draft) gets the L0 header.
- **`«sock_write»` stays** in the endpoint world's call set as v1/v2's
  idealised full write, because the v1/v2 instance theorems use it. The
  honest C no longer provides it (§8 phase 1).

### 4.2 Anchored on the standards (user decision, 2026-10-16)

The L0 world (`async/honest-l0/honestL0WorldScript.sml`, trusted) is
written from the standards, not from one platform. Sections are cited in
its comments.

- **[P]** POSIX.1-2024 (IEEE Std 1003.1-2024, Issue 8), XSH:
  - `send`, `recv`, `accept`, `poll`, `close`, `shutdown`, `listen`,
    `bind`, `socket`;
  - 2.3 Error Numbers;
  - 2.6 File Descriptor Allocation;
  - 2.10.7 Socket I/O Mode;
  - 2.10.14 Signals.
- **[T]** RFC 9293 (TCP), and RFC 1122 §4.2.2.13.

The citations were checked against the primary texts. The rules:

1. **Where a standard is specific**, the model follows it.
2. **Where it is loose or silent**, the model is nondeterministic: a world
   choice (`lchoices`), with every permitted behaviour allowed.
3. **Where a real platform does what the standard forbids**, the model
   allows it too, as a documented **platform extension [X]**.
4. **Constraints the standards don't give but the model assumes** are
   marked **[A]**. The conformance tests check them on every platform.

| topic | standard | model | platforms |
|---|---|---|---|
| fd of a new socket | [P 2.6]: the **lowest** available fd (accept, socket) | follows it: `lowest_fd`; EMFILE if it is not below the limit | macOS conforms (tested) |
| partial send | [P 2.10.7]: "transfer only as much as is available"; EAGAIN only if nothing fits | `takes` (the room is the kernel's) | macOS: a partial 15708 of 65536, then EAGAIN |
| counts below 2^64 (D24) | [P send], [P recv]: the result is an `ssize_t`, so a count is at most SSIZE_MAX | rely: `takes` and `short` are below 256^8 (`l0_rely`) | **build-time checked**: `_Static_assert(sizeof(ssize_t) <= 8)` in the C |
| non-blocking per call | `MSG_DONTWAIT` is **not** in Issue 8 | treated as O_NONBLOCK for one call ([P 2.10.7]) | **[X4]** a non-standard flag, in macOS and Linux |
| SIGPIPE | [P send, 2.10.14]: EPIPE is returned "regardless of whether the generation of the signal is suppressed"; `MSG_NOSIGNAL` is standard | EPIPE is a result | macOS lacks `MSG_NOSIGNAL`: the startup contract ignores SIGPIPE (standard behaviour, not an extension) |
| short recv | [P recv]: data "as soon as it becomes available" | `short` (≥ 1 byte, ≤ available) | macOS: short reads seen (261 times in the random test) |
| arrivals between calls | none | the environment delivers before **every** call (D3) | macOS: data after an EAGAIN with no poll (P7) |
| errors at other times | [P 2.3]: implementations "may generate errors ... under circumstances other than those described" | `transient`: any error at any call, **except** EAGAIN (**[A2]**) | none seen (0 warnings in the random test) |
| reset, unread input | [T §3.10.7.4]: "All segment queues should be flushed" (lowercase: not BCP 14) | `LBreak j e keep`: kept or flushed | macOS keeps it (P3) |
| reset, how reported | [T §3.10.7.4]: "reset" responses; [P recv/send]: ECONNRESET, EPIPE "no longer connected" | a pending error, reported once (`err`); then `broken_recv`/`broken_send` | macOS: recv ECONNRESET once, then 0; send EPIPE, leaving the error pending (P2, P4) |
| reset after the peer's EOF (D21) | [P recv] 0 when "no messages are available to be received and the peer has performed an orderly shutdown"; [P 2.10.10] the pending error "is returned in response to a subsequent send(), recv(), or getsockopt()"; [P 2.10.11] "The receive queue is logically terminated if an end-of-file indication has been received" | `eof_first`: recv may return 0 and leave the error pending | Linux: 0 for ever; the error is reported by send (P4) |
| close, unread input | [T §3.6.1]: SHOULD send RST (SHLD-3) | `aborted` (the peer *may* lose data) | macOS: the client lost the response (P6) |
| close, interrupted | [P close]: EINTR with the fd open, EINPROGRESS with it closed, or 0 (unspecified which) | `close_intr` | none seen (no signal handlers) |
| sending after the peer's FIN | [T §3.6.1]: permitted | permitted | macOS (P4) |
| accept, EMFILE | [P accept]: shall fail; the pending connection's fate is **unspecified** | `emfile_drops`: queued, or dropped with the peer reset | macOS drops and resets (P5); Linux keeps it queued (documented) |
| accept, broken pending | [P accept]: ECONNABORTED (shall), EPROTO (may) | `accept_aborts`: dropped with an error, or returned | macOS returns it (P8); BSDs: ECONNABORTED; **[X3]** Linux also returns network errors not in the list |
| shutdown when not connected | [P shutdown]: ENOTCONN | `shut_err` on a broken or already-shut channel | macOS: ENOTCONN once both sides have sent FIN (**found by the random test**) |
| shutdown of a pending connect (D22) | [P shutdown]: shall fail with ENOTCONN "The socket is not connected"; [P connect]: a pending connection is "established asynchronously" | `pending_err`; the observed success is explained by environment choices (`LConnUp`, then `LBreak`; the two ends are not linked, D1), so no rule of its own. Verified L1 never calls `sys_shutdown` | **[X5]** Linux succeeds, aborts the connect and leaves ECONNRESET pending (P13) |
| POLLERR | [P poll]: **required** for every condition a read or write would report with −1 | `show_err`, **only if** an error is pending or the channel is broken or shut | **[X1]** macOS never shows it (P2) |
| POLLHUP | [P poll]: defined for devices, pipes and FIFOs; **not for sockets** | `show_hup`; **[A1]** only after the peer's EOF, a break, or our own shutdown | macOS shows it after our SHUT_WR alone (**found by the random test**; [A1] widened) |
| POLLHUP with POLLOUT | [P poll]: "mutually-exclusive" | not excluded | **[X2]** Linux sets both after a reset (documented) |
| POLLERR/HUP/NVAL not requested | [P poll]: reported "even if the application did not set the corresponding bit" | yes | conforms |
| negative fd in an entry (D20) | [P poll]: "If the value of fd is less than 0, events shall be ignored, and revents shall be set to 0" | `pfd_revents`: an fd field ≥ 2^31 (negative as an `int`) gets revents 0 | not probed (L1 never polls one) |
| revents of a failed poll (D20) | [P poll]: unspecified | `poll_junk`: any bytes | — |
| accepted socket and O_NONBLOCK | [P accept]: implementation-defined | irrelevant: every call uses MSG_DONTWAIT | — |

**Fairness assumptions (used only by R1-live, §6; approved, D11 and D12).**
R1-safe and every safety result use none of them.

- **[F1] Transient failures are not permanent.** For each call kind
  (recv, accept, send, poll) and each fd or listener: if the call is
  attempted infinitely often, it succeeds infinitely often.
  - [P 2.3] lets errors happen "under circumstances other than those
    described", so the model allows `transient` at any call.
  - No standard promises progress. [F1] is therefore an assumption, in
    the sense of [A].
  - EINTR additionally needs a caught signal [P 2.10.14], and the
    startup contract installs none.
- **[F2] An empty send buffer takes a byte.** With nothing in flight, a
  send of n > 0 bytes accepts at least one.
  - [P 2.10.7]: send transfers "as much as is available", and with
    nothing in flight the space is the whole buffer.
  - [T §3.8.6] (flow control): the window is not the obstacle once the
    peer has taken everything.

### 4.3 The probes and tests are conformance tests

- **The checker** (`runnable/l0/tester/l0check.py`) replays a logged run
  against a transcription of the L0 world. It reads the run's choices off
  the observations, and keeps the set of possible states for choices that
  are only visible later. It delivers each client action at the latest
  moment that still explains every observation.
- **Any observation no state explains is a finding.** One explained only
  through POSIX 2.3's "any error at any time" escape is a warning, for
  review.
- **Mutation test** (`mutants.py`): 8 forbidden observations planted in
  real logs (wrong bytes, a non-lowest fd, a false EAGAIN, NVAL on an
  open fd, ...). **All 8 caught.**

| run | result |
|---|---|
| the 10 probes, macOS 26 (Darwin 25.6, arm64): `probes-darwin.txt` / `.json` | **10/10 conform** |
| random test (`random_test.py`): 100 scenarios × 200 steps, 12146 calls. Exercised: 195 partial sends, 237 resets seen, 100 EMFILEs, 261 short reads, 1080 EOFs, 273 closes without reading first | **0 findings, 0 warnings** |

**The five macOS corrections of the first probe round, reclassified:**

| observation | under the standards |
|---|---|
| HUP on a peer FIN alone | permitted: POLLHUP is unspecified for sockets |
| send gives EPIPE and leaves the reset pending | permitted: [P send] EPIPE "no longer connected"; when the pending error is reported is not specified |
| EMFILE drops and resets the pending connection | permitted: its fate is unspecified |
| accept returns a reset pending connection | permitted reading of [P accept] (Linux does the same) |
| no POLLERR | **forbidden** by [P poll]: platform extension [X1] |

**Three model gaps found by the random test, all fixed before freezing:**

1. **EMFILE is about fd numbers, not a count of open fds** (as first
   written). [P]: no fd *below the limit* is free.
2. **shutdown → ENOTCONN once both sides have sent FIN** (a second
   shutdown). This is now `shut_err` on an already-shut channel. Before
   the fix, the checker had to invent a reset to explain it, which a
   later EOF then contradicted.
3. **POLLHUP after our own SHUT_WR**, so [A1] was widened.

Plus one checker limitation, found and fixed: a cap on the number of
candidate states. The checker now warns when the cap is reached.

**Linux has not been tested yet:** no Linux machine is available here.
`make probes` and `random_test.py` on Linux are the **conformance check**
to run before a release. [X2], [X3] and Linux's EMFILE behaviour are
expected; anything else would be a finding.

**Conformance run on Linux (Sisyphus), 2026-10-17** (Linux 6.18, x86_64,
after D20; `probes-linux.txt` / `.json`). This records a run; it is not
a Linux platform claim.

| run | result |
|---|---|
| the 13 probes | 11/13 conform. **P4:** after the peer's FIN and then its RST, recv returns 0 (EOF), never ECONNRESET. **P13:** the pending connect state *was* observed (no revents; recv and send EAGAIN), but shutdown on the pending socket returned OK and connerr then reported ECONNRESET |
| mutants | 11/11 caught |
| random test: 100 scenarios × 200 steps, 12461 calls | **80 findings**, all of P4's kind (recv → EOF after a reset); 6 warnings (accept EMFILE explained only as transient) |

The pre-D20 C and tester (`41dffdd16`) give the same results on the same
machine (the same 80 findings and the same probe findings), so neither
comes from D20. *Resolved by D21 and D22 (§9):* P4 and the 80 random
findings are [P] looseness the model now has (`eof_first`); P13 is a
platform extension [X5] the model already admitted (the checker could
not see it).

**Conformance run on Linux (Sisyphus), 2026-10-17, after D21/D22** (a
run, not a Linux platform claim):

| run | result |
|---|---|
| the 13 probes | **13/13 conform** |
| mutants | **11/11 caught** |
| random test: 100 scenarios × 200 steps, 12461 calls. Exercised: 106 partial sends, 54 resets seen, 223 EMFILEs, 263 short reads, 1356 EOFs, 277 closes without reading first | **0 findings**; 10 warnings, all accept EMFILE explained only as transient ([P 2.3]) |

## 5. L1: the verified wrapper layer

L1 is **one CakeML module plus its loop**: the honest-world version of
close-v2's handle layer (`asyncHLProg`: a verified table and auto-close,
the server unchanged). It sits between the event loop's `perform` and L0.
**The server (L2) sees exactly today's vocabulary:**

- actions `Accept l | Read c n | Write c bs` (+ `Close c` in v2);
- responses `Accepted (fd option) | Got (data | EOF | would-block) |
  Wrote`;
- readiness: the set of readable fds.

### 5.0 As built (phase 4, `async/honest-l1/`, branch `spike/honest-l1`)

- **`honestL1Model`**: L1 over the L0 world, for version 2 only (D5).
  - It follows close-v2's handle layer (`asyncHLModel`; the interface
    is unchanged and imported read-only later). The computation emits
    today's actions on handles.
  - Every action and every round becomes concrete L0 calls through
    `l0_ffi_fn`, so its event trace **is** the raw trace.
  - `l1do` covers:
    - buffered writes (one send at once if the outbox is empty);
    - the round discipline;
    - auto-close on EOF, deferred while the outbox flushes;
    - a broken connection ends its episode;
    - accept errors, with `exhausted`.
  - `l1_tail` is the round's poll (IN for the interest, unless paused or
    an exhausted listener; OUT for non-empty outboxes), then flush, then
    reap. `lrounds` is the run, as `hrounds`.
  - `l1hdl`/`l1hdln` restate `hdl`/`hdln`, so this theory needs none of
    `asyncHLModel`'s CF ancestors.
- **`honestL1Props`** (8 theorems):
  - `read_no_syscall`, `recv_found_empty`: the round discipline;
  - `gone_is_eof`;
  - `stall_local`: a slow reader stalls only itself;
  - `write_buffered`;
  - `exhausted_quiet`: no listener input polling while out of fds;
  - `paused_quiet`.
- **`honestL1Simple`** (13 theorems): the simple L0 world `simple0`, and
  R3 in it. Each wrapper is one L0 call answering exactly as today's
  call:
  - `write_simple`: one `sys_send` of exactly bs, fully taken, and the
    outbox stays empty;
  - `read_simple`: one `sys_recv`, answering `TAKE n` of the input;
  - `accept_simple`: one `sys_accept`, returning the lowest free fd under
    a fresh handle.
- **`honestL1Inv`** (phase 4b, 34 theorems): **L1 never makes a failing
  L0 call.**
  - The invariant `small_fds`: every fd L1 holds is below 2^31.
  - **Found and fixed:** the C allows at most 4096 fds per poll, and L1
    polled its whole interest in one call. A server with more than 4096
    connections would have aborted. L1 now polls in chunks of at most
    4096 (`poll_chunks`); the C is unchanged. *Superseded by D20 (§3.6):*
    the C has no cap and L1 polls once per round.
  - Each L0 call succeeds and keeps the rely (`sys_*_ok`).
  - `l1do_ok`, then `l1round_ok`: a round completes and keeps the rely
    and the invariant.
  - `lrounds_ok` and `lrun_ok_thm`: the run never fails, given `l2_ok`.
    `l2_ok` asks only what the handle layer's `hrun_ok` asks: well-formed
    reads, and no handle-number overflow.
- **Next (phase 6):** R1/R2 against `asyncHLModel`: the regrouping
  simulation, and in `simple0` worlds the round-by-round renaming of
  `hrounds`.

### 5.1 The wrappers: spec, what each absorbs, and how

The **L1 state** per fd:

- `outbox` (bytes written by L2, not yet accepted by the kernel);
- `paused` (L2 is not shown its input);
- `gone` (broken: reset or peer-gone);
- `closing` (L2 closed it; L1 drains before closing).

Globally: `exhausted` (the last accept said EMFILE/ENFILE).

| wrapper | L2-visible spec (today's vocabulary) | raw behaviours absorbed, and how |
|---|---|---|
| **write** (write_all, buffered) | `Write c bs` → `Wrote` in the next round, as today. The bytes are appended to c's outbox | **Partial send:** keep the rest in the outbox. **EAGAIN:** declare OUT interest on c and send again when writable, so **only c waits** (fixes L1). **EPIPE/ECONNRESET:** mark `gone` and drop the outbox; the next read of c reports EOF (fixes L1′). **EINTR/ENOBUFS:** retry when next writable |
| **read** (read-or-closed) | `Read c n` → `Got (SOME d)` / `Got (SOME [])` (EOF) / `Got NONE` (would-block) | **Errors (reset, ETIMEDOUT, ...):** become EOF for L2, recorded as `gone`. It is not a lie, because the **raw trace** shows the error and the spec is stated on the raw trace (§7). **EINTR/ENOBUFS/ENOMEM:** `Got NONE` (would-block); retry next round (fixes L11). **Round discipline:** recv is called only if c was reported readable at this round's poll and no earlier call this round said EAGAIN; otherwise `Got NONE` without a syscall. **Pausing:** if c's outbox is above the high-water mark H, c is not reported readable to L2 |
| **accept** (accept-or-skip) | `Accept l` → `Accepted (SOME f)` / `Accepted NONE` | **ECONNABORTED and Linux's pending network errors:** `Accepted NONE`. Each pops one pending connection, so this is finite. **EMFILE/ENFILE:** `Accepted NONE` and set `exhausted`; **the listener is then not reported readable** to L2, and not polled, until a close frees an fd (fixes L5's spin). ENOBUFS/ENOMEM/EINTR: `Accepted NONE` |
| **readiness** (select-on-interest) | the set of readable fds among L2's interest, as today's `sock_poll` (or the blocking `sock_select` + poll) | It polls L2's interest (IN) **minus** paused fds and the listener while exhausted, **plus** OUT on every fd with a non-empty outbox. IN, HUP or ERR mean "readable" for L2, since the following recv reports what happened. OUT flushes the outbox (one send per writable fd per round). NVAL: proved impossible (L1 polls only fds it owns). EINTR: an empty round |
| **close** (v2) | `Close c` → done, as `«sock_close»` today | **Graceful close:** if the outbox is non-empty, `shutdown` after it drains, then close. With unread input, `shutdown(SHUT_WR)`, then read and discard to EOF, then close (lingering close, fixes L8). A `gone` fd is closed at once. Every close clears `exhausted` |
| **listen** (startup) | none: L2 starts with listener `lfd` | `sys_listen port`. On failure, print the step and errno, and exit (`FFI_failed`-free: a clean `Terminate`) |

*Running out of fds, in the prefetching L1 (D17, supersedes the
`exhausted` rows above).* ENFILE is retried in the next round, like a
transient error. EMFILE **pauses** the listener: L1 leaves it out of the
poll for `pf_backoff` rounds (a named constant in the model; no proof
uses its value) and then retries the accept, as real servers pause
accepting and retry. A close does **not** end the pause early: the pause
only counts down. That is simpler than the lazy L1's "every close clears
`exhausted`", and still live: the retry comes at most `pf_backoff` rounds
later. At a real fd limit, each retry's EMFILE may reset one queued
connection (`emfile_drops`, permitted by [P accept]); live-conn's
"dropped" case covers that.

**Memory.** The outbox makes a slow reader cost memory, not time:

- **pausing** at H bounds each outbox to H + one read's worth for
  servers that write only in response to reads (echo, HTTP and KV all do);
- a server that writes without reading could still grow it. The L1 spec
  states the bound as a theorem about `outbox ≤ H + n` under that
  property;
- CakeML out-of-memory remains the compiler theorem's caveat, as today.

### 5.2 L1's spec is the existing round world

What L2 can observe through L1 is exactly a run of today's
version-2 (resp. version-1) world, under a **regrouped schedule**:

- **Data read at round r** on a fd last reported readable without a read
  since poll p is placed in the schedule step of poll p.
  - This is consistent: inbox only grows between reads; poll reports
    only a flag; and L1 never calls recv after a "no".
- **An EOF or a raw error read by L1** becomes `Eof2 j` in the same way.
- **A connection accepted at round r** is placed at the poll that first
  showed the listener readable, after the previous accept.
  - Exhausted periods show the listener not ready, so the connection
    "arrives" when L1 accepts it.
- **Writes** are complete at once from L2's point of view (into the
  outbox).
- **Paused input** reaches L2 later. That is just a later step of the
  schedule, which the ∀-schedule specs already cover.
- **The fd an accept returns** is the kernel's.
  - v2 world: `alloc` is the kernel's choice, which is free in the v2
    world because the v2 world's open fds ⊆ the real ones.
  - v1 world: `Connect l c` names the real fd post hoc. v1 programs never
    close, so it is fresh.

So **no new abstract world is needed**, and **L2's theorems apply
unchanged**. Backpressure, resets, fd limits and arrival timing exist
only below L1.

### 5.3 Why the discipline is needed and enough

**Without it** (a server that reads a fd the poll said was not ready),
some L0 runs have no v2 counterpart (L6).

**L1 imposes it**, whatever the server asks. A `Read` outside the
discipline gets `Got NONE` without a syscall, which is a correct
would-block in the regrouped world. Our servers never ask, so in the
simple instance L1 makes exactly one recv per server Read.

### 5.4 Shaped by what our servers need

| server | today's world | what it needs from L1 | covered by the L1 of §5.1? |
|---|---|---|---|
| echo (v1), echo2 (v2) | v1 / v2 | read, write in response to reads, accept; v2: close on EOF | yes; pausing bounds memory, because writes follow reads on the same fd |
| HTTP (headers, bodies) | v1 | as echo; responses can be large (files) | yes. A large file response sits in one outbox (bounded by the file). The planned close-after-response needs the graceful close |
| KV | v1 (`with_store` inside the computation) | as HTTP | yes |
| chat (`spike/chat-spec`, `chat_spec` as `echo_spec`) | v1 | **broadcast**: writes to fds it is *not* reading from | **partly.** Pausing does not bound a slow client's outbox, since other clients' lines fill it. Options (decision D7): unbounded (memory grows with a non-reading client; liveness intact under `reads_fair`), or a hard limit after which L1 drops the client (it becomes `gone`; the raw spec then owes it only "the episode ends"). Real chat servers do the latter |
| proxy / client (endpoint drafts) | endpoint | connect; **cross-fd backpressure** (stop reading A while B's outbox is full) | **no.** Per-fd pausing cannot express it. A proxy needs a richer L1 interface: write completion, or an outbox level as a readiness event. That is design/35's `write_all` with `Writable` interest (D4's alternative). It is an *additional* L1 interface, so the servers above do not change |

So the L1 of §5.1 (whose spec is today's v1/v2 worlds) serves every
server we have. The proxy is the first program that needs a second,
richer L1 spec. Designing that one now would be premature.

## 6. Refinement theorem statements

These are drafts. Names are tentative; `(*claim*)` marks a definition
of the proposition. Throughout:

- `loopV2 m` is today's CakeML handle-layer loop running server
  computation `m`;
- `loopL1 m` is the L1 loop running the **same** `m`;
- `P = prog loopV2 server` and `P' = prog loopL1 server` share the
  server's code.

**(R1) Generic refinement, one theorem for all servers:**

    l1_refines_v2 : ∀m w0 io0.
        l0_world w0 ∧ l0_rely w0 ∧
        semantics_prog (init_state (l0_ffi w0)) init_env (P' m) (Diverge io0) ⇒
        ∃sk io. server_world2 lfd sk ∧
                semantics_prog (init_state (socket2_ffi sk)) init_env (P m) (Diverge io) ∧
                l1_rel w0 io0 sk io

- `l1_rel` relates the raw trace and the abstract trace, per episode:
  - **reads:** at every raw prefix there is an abstract prefix with the
    same bytes read per episode, and conversely;
  - **writes:** the raw bytes sent are a prefix of the abstract bytes
    written, at corresponding prefixes;
  - **flush:** whatever is abstractly written is eventually raw-sent, if
    `reads_fair` and `¬gone` hold for the channel;
  - **closes, accepts:** the same episodes, in the same order;
  - **listen:** the raw trace starts with a successful `sys_listen`
    returning `lfd`, or the program terminated after a failed one.
- Plus the same for v1 (`l1_refines_v1`, with the L1 variant that never
  closes) and for the blocking loops (`run_b`, with a QuietSpec-style
  `asleep` outcome mapped to `asleep`).

**(R2) The simple instance.** In a simple world nothing is regrouped,
nothing is buffered beyond the round, and the raw trace **is** the
abstract one, renamed:

    l1_simple : simple0 w0 ∧ ... (as R1) ⇒ ∃sk io. ... ∧ io = l0_view io0 ∧ sk = sk_of w0

- `l0_view` renames:
  - each `sys_send` that sends all of a write ↦ a `«sock_write»` event;
  - `sys_recv` ↦ `«sock_read»`;
  - `sys_poll` (no block) ↦ `«sock_poll»`;
  - `sys_accept` ↦ `«sock_accept»`;
  - `sys_close` ↦ `«sock_close»`;
  - and drops `sys_listen`.
- `sk_of w0` is the v2 world with w0's schedule.

**R2, made precise by phase 4** (the plan for phase 6). The simple-world
refinement holds round by round under four side conditions, each found
while building L1:

1. **Open loop.** `simple0` plus `open_loop`: the environment ignores the
   calls, as version 2's schedule does. The version-2 world `sk_of w0` takes
   its `future` from the environment's arrivals at successive polls.
2. **One poll per round:** at most 4096 polled fds. L1 chunks larger
   polls, and each chunk is a step of time that the handle layer's single
   poll does not have. (*Old R2 only.* Since D20 L1 polls once per round;
   the old `honestL1Round` keeps the bound because its decoding lemma
   uses it.)
3. **Reads within the interest.** A server Read of a handle outside the
   round's polled interest gets "would block" from L1 with no syscall, but
   possibly data from version 2. Our servers read only after waiting for
   readiness (`asyncServer`'s `handler`). R2 assumes this (`reads_interest`),
   and it is proved per server. R1 (general) needs no such hypothesis,
   because regrouping covers it.
4. **No outbox, no closing.** In `simple0` every send is taken whole
   (`write_simple`), so flush and reap never act. EOF closes at once, as
   the handle layer's auto-close does.

Under these, R2's relation is: the handle tables agree (`l1hdl` = `hdl`);
L1's outboxes are empty and its `closing` list is empty; L0 channel j is
version-2 client j (inbox = incoming, peer_eof = peer_closed, sent =
outgoing, open fds and listeners the same). The events then rename
one-to-one:
- `sys_recv` ↦ `sock_read`;
- `sys_send` ↦ `sock_write`;
- `sys_accept` ↦ `sock_accept`;
- `sys_close` ↦ `sock_close`;
- `sys_poll` ↦ `sock_poll`, where the flag is IN, and HUP/ERR imply IN in
  `simple0`.

**R2, as built (phase 6, `async/honest-l1/`, branch `spike/honest-refine`).**
R2 is proved as a run theorem against close-v2's handle layer
(asyncHLModel, unchanged), at the model level:

    l1_refines_hl :
      simple_v2 p lfd sched w0 ∧ l0_rely w0 ∧ fds_lt w0 ∧ w2n lfd < 2^31 ∧
      l1v2_rel p lfd sched (w0, l1init) (s0, hinit) ∧ hl_ok lfd ifds m s0 ⇒
      ∀n. ∃w st evs.
        lrounds lfd hw ifds m (w0, l1init) n = SOME (hhist lfd ifds m s0 n, (w, st), evs) ∧
        l1v2_rel p lfd sched (w, st) (hst lfd ifds m s0 n) ∧
        drops (MAP l0_v2_event evs) (FLAT (GENLIST (hround_events lfd ifds m s0) n)) ∧
        simple_v2 p lfd sched w ∧ l0_rely w ∧ fds_lt w ∧
        rdy_ok lfd (polp_at lfd ifds m s0 n) w st

L1 and the handle layer give **the same history** (the snapshots the
server sees). The relation between their I/O traces is weaker than the
one-to-one renaming that the draft above expected.

- **Traces, `drops`.** L1's renamed events (`l0_v2_event`) are the
  handle layer's events with some would-block events deleted. When the
  discipline (below) says a Read or Accept would block, L1 answers
  without a syscall, but the handle layer logs a `sock_read` or
  `sock_accept` with an empty result. `drops` is inductive, and
  `drops_APPEND` lets it compose round by round.
- **The relation `l1v2_rel`** (honestL1Refine). It holds the table facts:
  - L1's handle table equals the handle layer's;
  - every handle has the form `l1hdl lfd i` with i < nxt.

  It also holds `core_rel`, which says L0 channel j is v2 client j and
  includes four invariants found while proving:
  - the accept queue has no duplicates;
  - queued channels are not open;
  - open fds map to distinct channels;
  - the listener is not a client fd.
- **The discipline, per polled (handle, fd) pair: `rdy_ok`, `polp_at`.**
  The draft's condition 3 ("reads within the interest") is not enough
  as stated. The discipline must be tracked per (handle, fd) pair
  polled at the end of the previous round, because a handle's fd can
  be reused after a close.
- **Polling with an empty interest.** L1 must poll even when the
  interest is empty. `poll_chunks` now gives `[l]` for any l of at
  most 4096 entries, including `[]` (since D20 there is no chunking:
  `l1_polls [fes]`). Otherwise the handle layer's poll
  of no fds would tick the world's clock and L1's would not.
- **Side conditions, `hl_ok`.** These are assumptions about the server
  running on the handle layer, round by round, in the style of
  `hrun_ok`:
  - the round discipline (`hacts_disc`: reads and accepts only on pairs
    polled at the last poll);
  - fewer than 2^31 − 1 fds in use;
  - handle numbers that fit in 64 bits;
  - at most 4096 polled fds.
- **Proof structure.**
  - Steps: `act_step` covers one action (accept, write, read; skip,
    data, empty, EOF).
  - Rounds: `acts_step` covers a round's actions; `tail_step` covers the
    flush, reap and poll (no-ops in simple_v2 except the poll);
    `round_step` covers a whole round.
  - The run: `l1_refines_hl` follows by induction on n, using
    `hround_SUC` to unfold one handle-layer round.
  - Theories: honestL1Refine, honestL1Steps, honestL1Round. There are
    no cheats.

Still open:
- connecting this to `semantics_prog`;
- R1 for general worlds, with regrouping;
- the per-server proofs of `hl_ok`.

**R1: a finding before proving (phase 7, 2026-10-16). R1 is false for
the current L1, and the fix (for decision) is a prefetching L1.**

R1 asks for exact history equality with *some* v2 world. The v2 world's
readiness is **exact and sticky**:
- a listener is ready iff a client is pending, and then an accept
  succeeds;
- a connection is ready iff it has unread data or EOF, and stays ready
  until it is read.

The current L1 reports what the kernel's poll said and learns the truth
only at the later syscall. Each of these runs has no v2 counterpart,
whatever the regrouping:

| # | L0 run | L1 tells L2 | v2 must say |
|---|---|---|---|
| C1 | listener reported ready; `accept` gives ECONNABORTED, EMFILE or a transient error | `Accepted NONE` | `Accepted (SOME _)`, because ready means pending |
| C2 | fd reported ready; `recv` gives EINTR, ENOBUFS or EAGAIN | `Got NONE` | data or EOF |
| C3 | ready; `Read h 100` gets 10 bytes (fewer than available, or more arrive later); a second `Read h 100` in the same round gets new bytes | data twice | the first short read emptied `incoming`, so the second is `Got NONE` |
| C4 | ready and unread; L2 then writes past the high-water mark, so the next poll leaves the fd out | not ready | ready (its data is still there) |
| C5 | the poll fails (EINTR) | nothing ready | the previous ready fds are still ready |

§5.2's regrouping argument overlooked stickiness and failing accepts.
C3 also defeats "place the data at the poll", because v2's `TAKE n`
pins down where each short read ends.

**Options:**

- **(A) A prefetching L1. Recommended.** L1 pulls input into its own
  buffers in the round's tail, then reports from the buffers.
  - After the poll, for each fd reported IN/HUP/ERR, not paused, and with
    an empty buffer, L1 makes one `recv` of a fixed chunk:
    - data goes into the fd's inbox;
    - 0 bytes, or a hard error, sets `eof` (the episode ends, as now);
    - a transient error does nothing.
  - For a readable listener (not exhausted), L1 makes one `accept`;
    success appends the fd to L1's accept queue.
  - L2 is told: ready iff the inbox is non-empty, `eof` is set, or the
    accept queue is non-empty.
  - `Read h n` is `TAKE n` of the inbox; `Accept` pops the queue; neither
    makes a syscall.
  - This is v2's semantics exactly. R1 becomes a plain forward
    simulation, with no regrouping and no discipline:
    - v2 client j = the j-th connection L1 accepted;
    - `incoming` = its inbox; `peer_closed` = `eof`;
    - the schedule's step n = what round n's tail fetched (the world is
      defined from L1's deterministic run, which does not depend on
      it);
    - `alloc j used` = the kernel's fd for j if it is not in `used`,
      else `lowest_free used`. This satisfies `alloc_ok`, and in the
      run the kernel's fd is never in v2's `used`, since v2's open fds
      are among the kernel's.
  - C1–C5 are absorbed below the buffers. Each inbox is bounded by one
    chunk, because L1 fetches only into an empty inbox.
  - Pausing becomes "don't fetch", and in v2 terms that is just a later
    arrival.
  - Cost: the L1 model, honestL1Props/Simple/Inv, and R2 must be
    re-proved. R2 should get easier: the history is equal as before, and
    the raw trace is the tail's fetches.
- **(B) A weaker abstract world**, v2 plus spurious readiness and
  failing accepts. L2's existing theorems would not apply unchanged,
  which is the point of §5.2. Rejected.
- **(C) Keep the lazy L1 and assume C1–C5 away.** That gives R2-plus,
  not R1.

**Decision (user, 2026-10-16): (A).** "If this is what a real server
would do, we should do it." Prefetching buffered readers are the norm:
OCaml Async's `Reader`, libuv's `uv_read_start`, Netty. The prefetching
L1 becomes *the* L1.
- It is built additively in new theories (`honestL1PF*`, starting with
  `honestL1PFModel`), and the servers then switch over to it.
- The lazy L1 (`honestL1Model`…`honestL1Round`, PRs #107/#110/#132)
  stays for the record and is superseded.

**The prefetching L1, precisely** (`honestL1PFModel`):

- **Backpressure.** L1 fetches only within the program's current poll
  interest.
  - A connection fd is fetched only if its handle is in the interest,
    its inbox is empty, it has no EOF, and it is not paused (outbox ≤
    hw, D4).
  - The listener is fetched only if it is in the interest, its accept
    queue is empty, and it is not exhausted. So there is **at most one
    accept per round per listener**, and a server that stops polling its
    listener stops accepting: there are no eager accepts behind its
    back.
  - An fd that the poll asked about only for output (paused, or
    closing) is never fetched, even if it reports HUP/ERR.
- **Bounds.**
  - Each inbox holds at most one chunk (`pf_chunk` = 64 KiB), because a
    fetch fills only an empty inbox.
  - Each listener's accept queue holds at most one fd.
  - L1's input memory is therefore at most `pf_chunk` × (connections in
    the interest). With 4096 connections that is 256 MiB in the worst
    case. The chunk is a constant of the model and can be lowered.
  - **Relation to D4 pausing:** pausing stops *fetching*. A paused fd
    keeps its at most one chunk, and stays ready until the server reads
    it. For servers that write only in response to reads, the outbox is
    still bounded by hw plus the responses to one chunk.
- **Reset vs EOF.** L1 keeps the distinction.
  - The fetch log records `FEof f` (an orderly FIN: recv returned 0)
    separately from `FReset f` (a hard error such as ECONNRESET), and
    the raw error is in the trace.
  - The server's vocabulary, `Got`, has only EOF, so both read as EOF,
    and both are `Eof2` in the version-2 world.
  - A richer L1 interface can expose the difference later at no cost to
    this one.
- **Syscall-level cost** (what differs from the lazy L1, on the wire and
  in the trace):
  - **Extra calls.** L1 makes at most one recv per round per
    interest-readable connection with an empty inbox, and at most one
    accept per round per listener. A recv happens whether or not the
    server reads that round; the server's Reads make no syscalls. When
    the server keeps up, the recv count is about the same as before (one
    per chunk received, plus the final 0 or error).
  - **Prefetched, never served.** A connection L1 accepted but the
    server never Accepted is visible only as an fd in L1's queue. The
    client already saw an established connection before any accept,
    since the kernel completes the handshake, so the wire is unchanged.
    If the program exits, the kernel closes the fd like any other: FIN,
    or RST if unread bytes remain in the kernel. Without the prefetch,
    the connection would have been reset from the backlog at exit.
  - **FIN, not RST.** Fetched bytes leave the kernel's receive buffer.
    If the program exits, or an fd is closed while L1's inbox still
    holds unread bytes, the kernel's receive buffer may be empty. The
    close then sends **FIN** where the lazy L1 (bytes still in the
    kernel) would have caused an **RST** (RFC 1122 §4.2.2.13; RFC 9293
    §3.6). This is documented behaviour; both are within the standards.
  - **EMFILE (D17).** The listener pauses for `pf_backoff` rounds after
    a failing accept, then L1 retries. Meanwhile the pending connection
    waits in the kernel's backlog, unless it is reset (`emfile_drops`,
    which [P accept] permits). ENFILE is retried in the next round. The
    server is told
    "ready" only when L1's queue holds an fd, so it never sees a failed
    Accept.

**R1's two halves.** The v2 world `sk` is built from the run's own fetch
log:
- the schedule's step n is round n's fetches;
- `alloc` returns the kernel's fd for each client;
- `reserved = []`.

So R1 splits into two halves.

- **R1-safe (forward simulation).** L1's history equals the handle
  layer's in `sk`, round by round. `sk` is well formed (`sched_wf2`,
  `alloc_ok`), so it satisfies `server_world2`, and L2's *safety*
  theorems transfer as they are.
- **R1-live (fetch completeness).** L2's liveness is relative to `sk`.
  For example, `echo_live2 sk io` promises to echo what client j sent
  *in `sk`*, which here means what L1 fetched. To transfer liveness to
  the real clients, R1 must show that L1 eventually fetches what the
  kernel delivers:
  - **(data)** for an accepted connection: every byte its peer delivered
    that a recv could return is eventually in some round's `FData`, and
    its EOF or break eventually gives `FEof`/`FReset`;
  - **(connections)** every connection pending on the listener is
    eventually `FConn`. The exceptions: it is aborted (ECONNABORTED: the
    peer reset it, so no service is owed), or it is reset under EMFILE
    (`emfile_drops`, macOS).

  Where starvation could come from, and what removes it:

  | source | removed by | kind |
  |---|---|---|
  | the server never polls the handle or listener | **S1:** the interest covers every open handle and the listener (asyncServer's `ifds` does by construction) | server obligation, proved per server like `hl_ok` |
  | the inbox stays full (no fetch while it is non-empty) | the server reads what it is shown. This follows from L2's own v2 liveness: what `sk` delivers is eventually read | free |
  | the accept queue stays full | the server accepts when the listener is ready (asyncServer does); one accept per round then drains the backlog first in, first out | server obligation (S1) |
  | **transient errors forever:** the model lets EINTR/ENOBUFS/ENOMEM/ENFILE happen "at any time", so recv, accept or poll could fail on every try | **[F1] (approved, weak form, D11):** per call kind and per fd/listener, a call attempted infinitely often succeeds infinitely often (§4.2) | **L0 fairness assumption (trusted)** |
  | **pausing forever:** the outbox never drops below hw | the client keeps reading its responses (LDrain), **and [F2] (approved, D12):** with nothing in flight, the kernel accepts at least one byte (`0 < n ⇒ 0 < takes j h 0 n`) | client hypothesis per episode, plus an **L0 assumption (trusted)** |
  | **EMFILE forever:** the process sits at the fd limit | **[F3]:** liveness for *new* connections assumes fds free up, e.g. the open connections stay below the limit. Otherwise connections wait in the backlog, which is the real behaviour | hypothesis of the connection half |
  | the round stops | the loop runs forever (`Diverge`), and every round polls (`poll_chunks` polls at least once) | free |

  The resulting L0-level liveness is L2's v2 liveness, restricted to
  episodes whose client keeps reading. For servers that never pause (the
  outbox stays ≤ hw), it applies to every episode. That is the honest
  statement: a client that never reads is backpressured, by design (D4).

  R1-live comes after R1-safe. [F1] (weak form) and [F2] are approved
  additions to the trusted L0 surface (§4.2; D11, D12). If R1-live
  cannot go through with the weak [F1], the reason will be reported
  before any change of form.

**R1-safe, as built (`async/honest-l1/honestL1PFRefine`, branch
`spike/honest-r1`).** The theorems, model level, no cheats:

    l1pf_refines_hl :
      l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
      (∀n. SND (pcm lfd hw ifds m w0 n) + 1 < 2^64) ⇒
      ∀n h ws evs logs.
        prounds lfd hw ifds m (w0, pinit) n = SOME (h, ws, evs, logs) ⇒
        hhist lfd ifds m (psk lfd hw ifds m w0) n = h ∧ …(the relation and invariants)

    psk_server_world : (same hypotheses) ⇒
      (psk …).listening = [(lfd, [])] ∧ (psk …).clients = [] ∧
      (psk …).open_fds = [] ∧ alloc_ok (psk …).alloc ∧ sched_wf2 (psk …)

In words: in **any** L0 world, every run of the prefetching L1 is
round-for-round the handle layer's run (asyncHLModel, unchanged) in one
version-2 world `psk`. That world satisfies `server_world2`, the
hypothesis of the v2 server theorems.

- **The world `psk`** is built from L1's own run, which does not depend
  on it:
  - client j is the j-th connection L1 fetched (`pcm`, the client map);
  - the schedule's step n is what round n fetched (`parr`: `FConn` ↦
    `Connect2 lfd`, `FData f bs` ↦ `Data2 j bs`, `FEof`/`FReset f` ↦
    `Eof2 j`, where j is f's client);
  - `alloc` returns the kernel's fd for each client (`run_alloc`; else
    `lowest_free`, so `alloc_ok` holds);
  - `reserved = []`.
- **The relation `pv_rel`:**
  - L1's inbox and EOF flag for an open handle's fd are its client's
    `incoming` and `peer_closed`;
  - L1's accept queue is the listener's pending clients;
  - the v2 open fds are the handles' fds.
- **Invariants:**
  - `pown`: L1's fds (listener, handles, closing, queued) are distinct,
    handles are distinct and issued, and only open handles have input;
  - `l0own`: those fds are open in the L0 world. With `fds_lt` and the
    rely's fd limit, this makes **every accepted fd fresh**
    (`sys_accept_fresh`).
- **Proof structure:**
  - actions: `pdo_hdo`; Accept is a pop from the queue, Read is TAKE n,
    and EOF auto-close maps to a lingering close against v2's immediate
    close;
  - the fetch: `fetch_rel`, and `step_ok2` for its arrivals;
  - the snapshot: `ready_eq`;
  - the round's tail: `tail_rel`;
  - one round: `round_rel`;
  - the run: induction.
  - `sched_wf2` concerns the world *left alone*. It agrees with the
    handle layer's world on all that `step_ok2` reads (`wagree`), since
    the program's actions never change listeners, counts or
    `peer_closed`.
- **Hypotheses beyond the L0 rely:**
  - the listener is open;
  - fewer than 2^64 − 1 connections over the run. This is v2's own
    fairness bound (`arrival_ok2`), restated on L1's run.
- **Not yet:** R1-live (fetch completeness; [F1] weak, [F2]); connecting
  to `semantics_prog`; the switch-over of the servers to this L1.

**R1-live, the statement (for review; not yet proved).** R1-safe makes
L2's liveness theorems true *of `psk`*: what client j sent in `psk` is
served. R1-live says `psk` misses nothing the kernel delivered, so the
promise reaches the real peers.

*Setting.* An infinite L1 run in L0 world w0. A prerequisite, not yet
built, is the PF analogue of `lrun_ok_thm`: the run never fails, given
the handle-layer conditions. Each channel c that L1 accepted has an fd f
and is client j of `psk`. The fetch log is `plog`.

*Hypotheses:*
- **[F1] (D11, weak fairness, trusted):** for each call kind (recv,
  accept, send, poll) and each fd or listener, if the run makes that
  call infinitely often, it succeeds (no transient error) infinitely
  often.
- **[F2] (D12, trusted):** `0 < n ⇒ 0 < w0.ch.takes j h 0 n`.
- **S1 (server, interest):** at every round, the poll interest contains
  every open handle and the listener. This is the asyncServer shape,
  proved per server.
- **S2 (server, accepting):** if the listener is reported ready at some
  round, the server issues `Accept lfd` at some later round. Also
  proved per server.
- **D(c) (the peer of c drains):** whenever c has bytes in flight, an
  `LDrain` for c eventually arrives. This is per episode, not trusted:
  it is the condition under which service is owed (D4 backpressure).
- **[F3] (fds free up):** infinitely often, an accept attempt finds the
  lowest fd below the limit. This is needed only for the connection
  part.

*Conclusions:*
- **(live-data)** If D(c) holds, then for every L0 step k there is a
  round n such that `peer_sent` of c at step k, less any bytes flushed
  by a break (`LBreak … F`), is a prefix of client j's data in the
  first n steps of `psk`. If c's peer closes or c breaks, then `Eof2 j`
  is eventually in `psk`.
  *Formal shape (agreed, in two parts).* **(A) kernel → L1:** for round
  n0, open handle h with fd f bound to channel c, no EOF recorded by L1
  on f, and B = c's kernel inbox at n0: eventually B is a prefix of the
  FData payloads L1 fetched on f from n0 on, or the episode ended (L1
  logged FEof f or FReset f). An orderly peer EOF cannot end the episode
  before B is fetched, because recv returns the inbox's data before it
  reports EOF; only a break (`LBreak … F`, which flushes the inbox) can,
  whether L1 then reads it as FReset or as FEof. So "episode ended" never
  hides lost data on a clean close. **(B) L1 → `psk`:** the FData
  payloads on f from its accept round on are exactly client j's `Data2`
  bytes in `psk` (j = `cl (pcm a) f`), and FEof/FReset on f become
  `Eof2 j` (R1-safe's `arrs`/`pv_rel`). Together they give the text above.
  *Done:* `fetch_progress` (honestL1PFLive): L1 eventually fetches on an
  open handle's fd with input pending. (A): `live_data_kernel`
  (honestL1PFStream). (A)+(B): **`live_data`** (honestL1PFClient): for an
  open handle on fd f with no EOF recorded by L1, bound to channel c, and
  j = `cl (pcm n0) f`: eventually `Eof2 j` is among `psk`'s arrivals from
  step n0 on, or c's kernel inbox at n0 is a prefix of client j's `Data2`
  bytes there. Hypotheses: the run's side conditions, `winv w0`, [F1]
  (D11′), S1, S3, S4 for f. The D16 corollary and live-conn are proved
  too (below and honestL1PFConnRun).
  **D16 corollary (proved, honestL1PFD16, fd75f3319):** hypothesis HD16 f
  (`HD16_def`, on the fetch log and f's channel at round boundaries): if
  round k's fetch log has `FReset f`, f's channel at the end of round k
  is broken with an empty inbox (`flushed`). Then `live_data_d16`: f's
  kernel input R at round n0 is eventually a prefix of what L1 fetched
  on f, or ∃k ≥ n0 with f flushed. `live_data_psk_d16` gives the same in
  psk, as client data. An orderly EOF needs no hypothesis (`recv_zero`:
  L0 returns 0 only with an empty inbox). *Wording refined (agreed with
  the coordinator, 2026-10-17):* the approved wording "every byte c's peer
  delivered is eventually in psk" is refined to "... unless the
  connection genuinely broke and the kernel discarded unread data". Real
  TCP may discard received-but-unread data on an RST (the model's LBreak
  with keep = F), so the unrefined statement is false for real
  connections. The corollary still excludes exactly what D16 is about:
  a spurious hard error ending the episode early.
  *Formal shapes for live-conn (agreed).* **[F3]:** infinitely often some
  fd below the limit is free (`∀n. ∃n' ≥ n. ∃x < fd_limit. n2w x ∉
  l0_used (rworld n')`). It is a condition on the run, on what the process
  holds, so it partly depends on the server closing connections. It is not
  trusted; it is discharged per server. For our servers the plan is to
  discharge it from facts like S4 and from reply-and-close behaviour, or,
  more simply, from a bound on concurrent connections (the open
  connections stay below the limit). That discharge is planned with the
  per-server obligations (item 5 of the whole-program list), not inside
  R1-live. **S2:** `(rstate n).acq ≠ [] ⇒` the server issues `Accept lfd`
  at some later round (the listener is reported ready exactly when acq ≠
  []). **Statement (D18):** a channel j0 in the listener's accept queue
  at round n0 is eventually (a) accepted (a `Connect2 lfd` in `parr k`
  matched to j0; the FConn form is a lemma), or (b) dropped (it left the
  queue broken, by ECONNABORTED or by an EMFILE reset), or (c) L1's
  accepts on lfd fail infinitely often. Disjunct (c) is the honest cost
  of D11′. The L0 model lets the world answer an accept with any error
  but EAGAIN as a transient failure ([P 2.3]), leaving the queue
  unchanged, and L1 retries every failed accept. [F1] constrains only
  the `l1_transient` errors, and on the observed trace a spurious
  ECONNABORTED looks the same as a real one, which pops a broken
  connection. **Corollary:** with the explicit hypothesis "every
  ECONNABORTED from L1's accepts on lfd really dropped a queued
  connection" (stated on the run's observed events and the listener's
  queue where possible), (c) is gone: j0 is accepted or dropped.
  *Refinement while proving (agreed with the coordinator):* the main
  form needs no [F3]. If j0 is never resolved, pops stop after finitely
  many (j0's position is finite), and L1 keeps accepting (S1, S2, the
  pause countdown, [F1] on lfd's poll), so every later accept fails,
  which is (c). [F3] moves to the corollary, whose hypotheses are:
  (H1) every failed accept on lfd whose error is not `l1_transient`,
  EMFILE or ENFILE removed a connection from the queue (the observed
  event plus the queue before and after); this covers ECONNABORTED and
  Linux's pending network errors. (H2) [F3]. (H3) the weak, **joint**
  form: if L1 attempts accept on lfd infinitely often, infinitely many
  attempts fail neither with an `l1_transient` error nor with ENFILE
  (this is [F1]'s accept clause with ENFILE added, as a hypothesis). It
  must be joint: two separate weak forms ("infinitely many accepts not
  transient", from [F1], and "infinitely many not ENFILE") are both
  met by a run alternating EINTR, ENFILE, EINTR, ..., where every accept
  fails and j0 waits forever. It is still a weak form, which allows
  recurring ENFILE and EINTR (the user's rule: fairness only in weak
  "infinitely often" forms that do not exclude realistic runs).
  *Correction (2026-10-17, before proving the corollary):* the
  paragraph that stood here said "EMFILE needs no new assumption ... in
  L0, EMFILE comes only when `l0_alloc` finds no fd below the limit".
  That was wrong. L0's world choice `transient` may return any error
  but EAGAIN, EMFILE included, and it cannot be limited to accepts
  because it does not see the call kind. So the model allows spurious
  EMFILE, and H1 + [F3] + H3 would not imply the corollary (a run where
  every accept gets a spurious EMFILE). **The corollary's hypotheses
  are now (agreed with the coordinator, no new trust):** (H1) as above,
  stated on the observed event plus the listener's queue at round
  boundaries: if round k has an accept on lfd that fails with an error
  outside {`l1_transient`, EMFILE, ENFILE} and the queue is not empty,
  some channel queued at round k is no longer queued at round k+1.
  (H3′) the joint weak form with EMFILE added: if L1 attempts accept on
  lfd infinitely often, infinitely many attempts fail with none of
  `l1_transient`, ENFILE, EMFILE. [F3] is dropped from the corollary:
  H3′ excludes only runs where j0 cannot be accepted anyway (the process
  at its limit forever, or spurious EMFILE forever). [F3] together with
  "no spurious EMFILE forever" implies H3′.
  **Proved (honestL1PFConnRun, 5d0d1c269):** `live_conn`, the main form,
  from [F1], S1, S2 (L1's accepted fds are eventually asked for) and
  the run's hypotheses, with `linv lfd w0` (lfd is a listener and no
  connection's fd); and `live_conn_psk`, where an accepted j0 is a
  `Connect2 lfd` in its round's arrivals under a new client number;
  and `live_conn_cor` (255d198d7), the corollary from H1 (`H1_def`) and
  H3′ (`H3_def`, errors in `kept_err`): accepted or dropped. All in
  honestL1PFConnRun, Holmake green, no cheats.
- **(live-conn)** Assume [F3]. Every connection that reaches the
  listener's backlog (`LIncoming` on its port) is eventually a
  `Connect2` in `psk`, unless it is dropped. It is dropped only if it
  broke while pending (ECONNABORTED: its peer reset it) or was reset
  under EMFILE (`emfile_drops`, macOS).

*Amendment (approved, D15).* L1 fetches on f only if f's inbox is empty and f is not paused.
Two per-server obligations make that hold, and the theorem must state
them:
- **S3, the server reads what it is shown:** a handle that is ready with
  inbox data is eventually read. It follows from the server's own v2
  liveness, but it appears as a hypothesis of the generic theorem.
- **S4, writes don't outrun the client:** if D(c) holds, f's outbox
  eventually falls to ≤ hw.
  - It holds for servers that write only in response to reads (echo,
    HTTP, KV): while f is paused nothing new is read, so nothing new is
    written.
  - For a broadcast server, D7's slow-client drop is what makes it hold.

*Formal shape of S4 (as the proof needs it; the same meaning as D15):*
eventually, until f is next fetched, the server issues no Write on f's
handle and f's outbox stays within hw. Reply-only servers satisfy it:
while nothing new is read on f, nothing new is written to f.

*Corollary shape (per server, for example echo):* from `echo_live2 psk
io` with R1-safe and R1-live, every byte delivered by a peer that
drains is eventually written to that peer on the wire. The writes reach
the wire because flushes progress under [F2] and D(c).

**Correction (2026-10-17, moonshot step 8): S4 was not discharged.** D15
says S4 is "discharged per server from v2 liveness and reply-only
writes". That discharge needs L1's *output* liveness: if the peer drains,
f's outbox shrinks. Nothing proved it; no PF theory used [F2] at all.
So every R1-live result that assumes S4 (fetch_progress, live_data,
the D16 corollary) rested on an unproved per-server obligation. The
missing piece is the L1 lemma `flush_progress` (inflight falls to 0
under D(c); then [F2] makes POLLOUT shown; then [F1] makes a send go
through, so the outbox shrinks). With it, S4 is *derived* from the L2
obligation `writes_follow_feeds` (design/45 §2.3) plus S3, not assumed.
D(c) is made precise as `drains` (the peer's in-flight bytes eventually
fall; an `LDrain` of 0 bytes does not count). Under construction on
`spike/moonshot-s4g`.

**Correction (2026-10-17, found by async-spike): S3 as stated is false**
for any server whose peer always has data ready: a round's actions empty
f's inbox and the same round's fetch refills it, so the inbox is never
empty at a round boundary although the server reads everything. The proofs
use S3 only once f is no longer fetched, so S3 is replaced by **S3w**
("if f is no longer fetched, its inbox eventually empties"), and S4 by
**S4w** (the same premise; then f's outbox stays within hw and nothing is
written to it). S3 ⇒ S3w and S4 ⇒ S4w are proved, so fetch_progress,
live_data_kernel, live_data and the D16 corollary only got stronger.

*Why it should hold:*
- A byte in c's kernel inbox makes c's next unpaused poll report IN.
- L1 then recvs, or retries after a transient failure ([F1]).
- c is unpaused eventually because its outbox drains ([F2] with D(c)).
- The inbox is emptied by L2's reads. Under S1, the v2 liveness
  forces those reads, because `psk` delivered the data.
- The accept queue is emptied by S2.

**sys_connect (phase 8, branch `spike/honest-connect`).**

*Done (L0):*
- **The C:** `sys_connect` (socket + O_NONBLOCK + connect 127.0.0.1:port).
  Its value is the fd as soon as `socket()` succeeded, also when connect
  then fails; value 0 means no socket. `sys_connerr` reads `SO_ERROR`:
  value 1 is the socket's pending error, value 0 a failed getsockopt.
- **The L0 world (trusted, for review):**
  - a channel may be `connecting`;
  - `connect_now` (EINPROGRESS / at once / failed at once) and
    `pending_err` (recv, send, shutdown while pending) are world
    choices, cited to [P connect];
  - arrivals `LConnUp` / `LConnFail e` settle a pending connect;
  - a pending socket shows no revents.
- **Conformance (macOS):** probes 13/13 conform (P11 connect, P12
  refused, P13 pending), mutants 11/11 caught, and the random test has 0
  findings. On P12, macOS shows IN|HUP and no ERR for a refused connect,
  which [X1] allows. On P13 the pending state was not observed: macOS
  completed every connect, even with backlog 0.

*The L1 wrapper: a decision first.* A client's abstract world is close-v2's
endpoint world (`spike/refused-connect`, PR #104):
- Connecting settles to Up or Refused at the next tick, by the world's
  `accepts a j`;
- a refused channel's read reports the error (status 3, code 4), then
  the channel is Failed;
- `sock_send` takes 0 while Connecting.

There is **no endpoint handle layer** (no asyncHLModel counterpart with a
Connect action). The options:

- **(E1) Recommended: an endpoint handle layer**, close-v2-style, over
  `endpointWorld`.
  - Actions: Accept, Read, Write (buffered, complete), Connect a, and
    Close. Connect returns a handle or none. Refused and Failed read as
    the endpoint world says.
  - The prefetching L1 refines it exactly as R1-safe does: a world
    built from L1's run, with fetches as arrivals, and connect outcomes
    observed by L1 (sys_connerr after poll OUT/ERR) as the settle choices
    `accepts`. Writes are complete in the abstract world, using the
    no-backpressure instance `takes j b n = n`, since L1 buffers.
  - The proxy's cross-fd backpressure (§5.4) needs a write-completion
    event, which is an addition to this layer, not a change.
- **(E2) Refine the endpoint FFI calls directly.** L1's buffering and its
  answering would-block without a syscall mean the call-level traces
  differ. This would need a weaker relation, so I don't recommend it.

**Decision (coordinator, 2026-10-16): (E1).**
- I build the endpoint handle layer in new theories, modelled on
  asyncHLModel. `endpointWorld` is unchanged, and close-v2 confirms the
  encoding.
- **Deferred:** a write-completion event (or an outbox level as a
  readiness event) for the proxy's cross-fd backpressure (§5.4). It will
  be an addition to this layer later, not a change.
- **Connect outcomes known at once take effect at the round's tail**
  (close-v2, for the E1 refinement, 2026-10-17; agreed with honest-ffi).
  - In honestL1EPModel, a connect that succeeds or fails at once keeps its
    handle pending until the tail. The outcome is held in the model state
    `early` (no syscall). This matches the layer, where Settle arrives at
    the next tick.
  - Without it, ERead or EWrite on a fresh refused handle in the same round
    would answer before the layer could. Handle names are predictable, so
    the refinement would need a hypothesis on the computation.
  - An implementation of this layer must keep the same timing.
- **E1's world is built from L1's run, so its rely is run-local**
  (coordinator, 2026-10-17). A spec meant to transfer through E1 is stated
  with the rely for the calls the program makes (`rely_on Q`), not plain
  `ep_rely` (see design/45 §2.5).
- **The weakening (a), pending the user:** E1 holds for runs in which no
  connect returned without a socket (no `EConnected NONE`), a condition on
  the observed events. (b), a world choice "connect failed, no socket" in
  `endpointWorld`, would remove it.

**New trusted items (L0 connect), for the user's review**
(`honestL0WorldScript.sml`):

| item | what | cited |
|---|---|---|
| channel state | `connecting : bool` (a connect is pending) | [P connect] |
| world choice | `connect_now`: EINPROGRESS (pending) / connected at once / failed at once with e (the socket then broken, its state "unspecified") | [P connect]: EINPROGRESS with O_NONBLOCK, ECONNREFUSED, "the state of the socket is unspecified" |
| world choice | `pending_err`: the error of recv, send or shutdown on a pending socket | [P send, shutdown] ENOTCONN; [P recv] "not connected"; Linux EAGAIN |
| arrivals | `LConnUp j` (the pending connect completes); `LConnFail j e` (it fails: e becomes the pending socket error, read by `sys_connerr`) | [P connect]: "established asynchronously"; SO_ERROR |
| readiness | a pending socket shows no revents; it is "ready for writing" only once established | [P connect], [P poll] |
| calls | `l0_connect`: the lowest free fd [P 2.6], EMFILE at the limit, value 0 when there is no socket. `l0_connerr`: getsockopt(SO_ERROR), reading clears it | [P 2.6], [P getsockopt] |
| not linked | a connect to the program's own listener also arrives there as `LIncoming`, by the environment's choice. The two ends are not linked: an over-approximation, so every real pairing is a behaviour | D1 |

**Not tested on macOS:** macOS conformance never observed the pending
state. Every connect completed (P13, even with backlog 0). *Observed on
Linux (Sisyphus, 2026-10-17, P13; a run, not a platform claim):* a
pending connect shows no revents, and recv and send give EAGAIN
(`pending_err`), as the model says. shutdown on it succeeds, which
[P shutdown] forbids: **[X5]** (D22), explained by environment choices
and unreachable from L1.

**R2/R3/R4 for the prefetching L1 (restated; statements first, nothing
proved yet).** The R2/R3/R4 above were written for the lazy L1, with one
syscall per server action and a raw trace that renames the abstract one.
For the prefetching L1 they are **false as written**:
- a recv takes up to 64 KiB, so one fetch can merge several schedule
  steps' data;
- there is at most one accept per round, so two connects in one tick land
  one round apart;
- reads make no syscall.

They are restated through `psk` (R1-safe) and transfer lemmas:
- **R2′ `l1pf_simple`:**
  - In `simple0 ∧ open_loop` worlds with at most one connect per tick and
    at most `pf_chunk` bytes per client per tick, `psk = sk_of w0`.
  - Otherwise `psk` is a **delay** of `sk_of w0`, under an explicit
    `delays` relation: the same per-client streams, each arrival at a
    tick no earlier than in `sk_of w0`.
- **R3′:** the PF wrappers.
  - Read is `TAKE n` of the inbox, with no syscall.
  - A fetch is one recv of at most `pf_chunk` bytes, or one accept.
  - A write is one send when the outbox is empty.
- **R4′, per server.** The template, for echo2:

      l0_echo2_spec : ∀w0. l0_world_hyps w0 ⇒
        (listen fails ∧ the program terminates) ∨
        ∃io0. semantics_prog (… l0_ffi w0) … echo2_prog_l1 (Diverge io0) ∧
              raw_safe io0 ∧
              (∀c. F1 ∧ F2 ∧ D c ∧ ¬hard_err c ⇒ raw_live c io0) ∧ …

  It goes through `psk` (R1-safe) and per-predicate **transfer lemmas**
  between raw and abstract prefixes. The instant map they need comes from
  the per-round `prounds`/`hrounds` correspondence.

**The formal [F1] (D11′'s form, as built).** Calls are keyed by the fds they
involve: the single fd for recv, accept, send and connerr; *every listed fd*
for poll (`call_fds`). Calls are read off the run's IO-event trace, with
their observed results. If calls of a kind involving fd f are made
infinitely often, then infinitely many of them do not return a retried
outcome (D11′). The world-choice form (D11) was replaced before any proof
used it. Under D11, a broken channel whose recv kept returning EINTR (the
world's `broken_recv`) would have starved L1 with no assumption violated.
An earlier draft keyed on the whole configuration, which gave poll nothing
because a poll's fd set changes; this form replaced it before any proof
used it.

**Open item (client side; proposed, not added): connect fairness.** Each
connect attempt makes a new fd, so no per-fd [F1] covers connect.
Moreover, repeated connects can fail with EADDRNOTAVAIL when ephemeral
ports are exhausted, for example by TIME_WAIT on the side that closes
first. A client-side liveness claim needs either a **connect fairness
assumption per address** (connects to a are attempted infinitely often ⇒
infinitely many of them are not failed by resource exhaustion) or a
**connection-rate bound** as a hypothesis. To be decided with the client
and moonshot specs.

**Whole-program obligations** (between the model-level theorems and a
statement about the real binary):
1. **The `semantics_prog` link.** R1-safe and R1-live are model level.
2. **The L1 CakeML loop**, in the same translation chain as the servers.
   "No server proof changes" holds at the model level only. The L1 code
   needs its own CF spec, and the servers are relinked against it.
3. **The listener fd.** `main2` hard-codes `lfd = 3`, but under D2 the
   program calls `sys_listen`, which returns the lowest *free* fd. If fd
   3 is inherited (a reserved fd), the listener is elsewhere, and polling
   fd 3 is misuse in the model. Either the server uses the returned fd,
   or the startup contract checks that fds ≥ 3 are closed (D2 checks only
   0–2).
4. **Fewer than 2^64 − 1 connections.** R1-safe states this on L1's run.
   A corollary about all L0 worlds needs it as a world hypothesis (as
   `v1_instance_disc`'s `sched_connects_le`).
5. **The per-server obligations:** S1–S4, `pl2_ok`/`hl_ok` (interest,
   ≤ 4096 fds per poll chunk, handle numbers < 2^64: since D25, each
   round `nxt + naccepts acts < 2^64`, counting only Accept actions), and D16's
   qualification of live-data.
6. **Listen failure.** Headline statements of the form `Diverge io` need
   the disjunct "listen failed and the program terminated" (`l1_rel`
   already allows it).
7. **Memory.** L1's input buffers take up to 64 KiB × the connections in
   the interest (256 MiB at 4096), plus outboxes (for HTTP, up to the
   file size). The machine-code theorem's heap must cover that, or the
   statement becomes "diverges or runs out of memory".

**(R3) Per-wrapper lemmas** (model level, on L1's functional core; the
cheap part). For example:

    write_simple : outbox_step (simple sends) (Write c bs) st = (Wrote, st with outbox unchanged) ∧
                   the raw calls of the round = [sys_send c bs ↦ full]

Draft in `async/honest-ffi/honestL1Script.sml` (§10).

**(R4) Corollaries: the old headline predicates hold for the relinked
programs in simple worlds.** For each existing theorem:

- `echo_spec 3w echo_prog`;
- `echo_spec2 3w echo2_prog`;
- `http_spec_h 3w files http_prog_h`;
- `http_spec_b 3w files http_prog_b`;
- `kv_spec 3w kv_prog`.

From R2 and the old theorem:

    echo_spec2_l0_simple : ∀w0. simple0 w0 ∧ l0_server_world w0 ∧ l0_rely w0 ⇒
        ∃io0. semantics_prog (init_state (l0_ffi w0)) init_env echo2_prog' (Diverge io0) ∧
              echo_safe2 (l0_view io0) ∧ echo_live2 (sk_of w0) (l0_view io0) ∧ echo_closes2 (l0_view io0)

Existence comes from the program's totality in the L0 world (its CF
spec). Uniqueness comes from determinism (`same_answers_semantics`, as
in endpointSemantics). That is the user's "existing programs keep their
theorems as corollaries via refinement". The v1 programs need R1's v1
variant; see §7 for their fd-limit hypothesis.

## 7. Spec consequences

**The real headlines move to the raw trace in general L0 worlds.** They
are proved from R1 + the old theorem + **transfer lemmas** for each
predicate shape, and **no server proof changes**:

- **safety** (`always`: raw written ≼ f(raw read)). Raw sent ≼ abstract
  written ≼ f(abstract read) = f(raw read). True for prefix-closed
  safety predicates, which all of ours are (echo: written ≼ read; HTTP:
  responses ≼ answers to requests read; KV: linearizable prefixes).
  - KV's `precedes` (real-time order) needs care: regrouping can only
    move abstract events later than raw reads and earlier than raw
    sends. That shrinks intervals the wrong way for one direction, so
    the transfer lemma for `kv_safe` is the one non-trivial check.
    Statement drafted; **risk flagged**.
- **liveness, per connection,** gains antecedents. These are
  per-guarantee hypotheses, never in the rely:
  - `reads_fair w0 io0 c`: the client of c keeps reading (writable
    infinitely often);
  - `¬gone c`: no reset or peer-gone on c (after one, the server only
    owes "the episode ends");
  - **v1 programs:** `clients_below w0 (fd_limit − |reserved| − 1)`.
    **This is the honest price of never closing**: liveness for the first
    L clients only;
  - **v2 programs:** `fd_room`: if fds are exhausted, some client
    eventually closes.
- **New guarantee clauses:**
  - `ends_on_gone`: after a reset or peer-gone on c, the episode is
    closed eventually (v2). It comes from L1 (EOF to L2) plus the
    server's close-on-EOF (EchoSpec2's `echo_closes2`);
  - `graceful`: no close happens with unread input pending, unless the
    peer was gone. This makes L8 a spec obligation; it is L1's lingering
    close;
  - **no busy-wait under exhaustion** (blocking/quiet programs): while
    exhausted, the listener is not in the wait set. This is QuietSpec's
    quiescence, re-proved through R1's blocking variant.

**New bites** (each a refutation of a broken server, as the existing
`*_bite` files):

1. **`stall_bite`**: a server that writes with the old blocking
   semantics, modelled honestly as "a write ticks until fully accepted",
   violates per-connection liveness. Client A never reads, client B
   sends 1 byte, and B is never answered. This is L1 made visible.
   design/35's `starve_bite` claim is the endpoint-world version; this
   one is stated against the raw L0 trace.
2. **`reset_bite`**: a server that treats a raw reset as data, or never
   ends the episode, fails `ends_on_gone`.
3. **`leak_bite`**: a v2 server that keeps broken connections open fails
   liveness for client L+1 under `fd_limit` L.
4. **`spin_bite`**: a blocking server that keeps the listener in its
   wait set while exhausted never quiesces (it is not `asleep`).
5. **`rst_bite`**: a server that closes with unread input pending
   violates `graceful`. A run exists where the peer loses the response.
6. **v1 honesty, a fact rather than a bite:** `echo_live` (v1) is false
   in L0 worlds with `fd_limit = 256` and 300 clients. This states for
   the README that the v1 server is not robust.

## 8. Cost and phases

Agent-days, at -j1 with holslot, from experience with M3/M4/close-v2.

| phase | content | estimate | proof risk |
|---|---|---|---|
| 0 | this design; user decisions §9 | done | — |
| 1 | **C**: `socket_ffi_l0.c` (≈ 100 lines). Old `socket_ffi.c` kept, with its header changed to "IDEALISED: documents its lies (§2)", for rebuilding the archive binaries. `Makefile`s get an L0 target | 0.5 | — |
| 2 | **Tester** (design/29), on L0 calls. Python transcription of the L0 model. New scenarios: a client that never reads (partial sends, EAGAIN); RST from the client (`SO_LINGER 0`); EMFILE (`setrlimit` low in the child); a vanishing pending connection (ECONNABORTED on macOS); short reads (TCP_NODELAY drip-feed); refused connects; NVAL. **Its first job:** confirm or refute the platform claims in §4 (pending-error semantics after reset/refusal, HUP on macOS vs Linux) before phase 3 freezes them | 1.5 | low |
| 3 | **World model**: the L0 world (§4) as a new theory beside `endpointWorld` (or as its extension, if close-v2 agrees); rely; simple instance; `v2_instance` still holds for `simple0` with the legacy calls | 1.5 | low |
| 4 | **L1 functional core** (HOL): state, wrappers, regrouping, outbox and pause invariants, R3 | 2 | low–medium |
| 5 | **L1 CakeML loop + CF** (`loopL1`, extending `asyncHLProg`; L0 call specs ×7, new; loop spec in the style of `asyncHLLoop`) | 4–5 | medium (CF is slow; memory-heavy) |
| 6 | **R1/R2**: the regrouping simulation, raw ↔ abstract traces. The heart of it, and pure HOL | 3–4 | **medium–high** (the accept-placement and v1 post-hoc fd naming are fiddly) |
| 7 | **Transfer lemmas** + raw headlines: echo, echo2, HTTP-H, HTTP-B, KV (KV's `precedes`, §7) | 3 | medium (KV) |
| 8 | **Bites** 1–5 | 2 | low |
| 9 | **Relink + runnable**: exports, demos; a new demo with a non-reading client next to a normal one (today it stalls; with L1 it doesn't); CPU table under EMFILE (today it spins) | 1 | low |
| 10 | **Blocking/quiet variants** through R1 (`run_b`, QuietSpec) | 2 | medium |
| | **total** | **≈ 21–24 agent-days** (3–4 weeks wall clock alongside other workers) | |

**What moves into CakeML** (now verified, previously trusted C or absent):

- the write loop;
- EINTR retries;
- accept error policy;
- reset handling;
- graceful close;
- listener setup sequencing;
- port parsing;
- the round discipline.

Its verification cost is phases 4–7: about 12–14 days, against a C that
loses about 40% of its code and all of its policy.

**Order of value:** 1–2 (honest C + tester) give real evidence quickly.
Phases 1–2 can ship first only as an **unused** build target, because
an L0 C without L1 runs no proved program. 4–6 are the core. 7 gives the
headlines. 8 gives the bites.

## 9. Decisions (user, 2026-10-16)

Guiding rule (the user's): **for every L0 decision, do the honest thing,
even if it is more work.**

| # | decision | status |
|---|---|---|
| D1 | Honesty criterion: the model is a sound over-approximation (every real behaviour is a model behaviour; never under-approximate). Platform differences are ∀-quantified world choices | **agreed** |
| D2 | `sys_listen` is made by the program (straight-line, restricted). The constructor **checks** that fds 0–2 are open, and sets SIGPIPE to ignored | **decided** |
| D3 | **Time is fixed in the model:** arrivals and state changes may happen before **any** call. L1's round discipline + the regrouping simulation prove our programs unaffected | **decided** |
| D4 | Buffered outboxes with read pausing (no server proof changes) | taken on the agents' recommendation; **revisable** |
| D5 | Retire the v1 runnables in favour of v2, and move HTTP onto the v2 handle layer | **approved** (see D5′) |
| D6 | `«sock_write»` stays model-only (for the v1/v2 instance theorems); the honest C drops it | **agreed** |
| D7 | Chat: drop a slow client at a hard outbox limit | taken on the agents' recommendation; **revisable** |
| D8 | Point (c) of §3.5 | **decided** |
| D5′ | (D5 approved later the same day) the v1 runnables are retired; L1 and the refinement target the version-2 world for every shipped program (echo2, HTTP on the v2 handle layer, KV); the v1 programs stay as model-level theorems | **approved** |
| D9 | The L0 model is anchored on the standards (POSIX.1-2024, RFC 9293/1122), with cited sections. Where they are loose: nondeterminism. A platform behaviour they forbid is a documented extension [X]. The probes are conformance tests (§4.2–4.3) | **decided** |
| D10 | L1 prefetches (§6, option (A)): it fetches input into its own buffers in the round's tail and reports what they hold. It becomes *the* L1, built additively and then switched to; the lazy L1 is superseded. "If this is what a real server would do, we should do it" | **approved** |
| D11 | **[F1]**, for R1-live only. A fairness assumption on transient failures, **per call kind and per fd/listener**: a call that is attempted infinitely often succeeds (does not fail transiently) infinitely often. Transient failures may recur forever, but never refuse permanently. The stronger "finitely many failures" was rejected as unrealistic for a long-running server (occasional ENOMEM/ENOBUFS forever). Using the stronger form needs a fresh decision | **approved (weak form); restated by D11′** |
| D12 | **[F2]**, for R1-live only. With nothing in flight, send accepts at least one byte (`0 < n ⇒ 0 < takes j h 0 n`) | **approved** |
| D13 | The L0 connect model is trusted surface: the `connecting` state; the world choices `connect_now` and `pending_err`; the arrivals `LConnUp` / `LConnFail`; no revents while pending. Cited to [P connect]. Untested on macOS: the pending state was never observed (§6) | **approved** |
| D14 | The R1-live statement (§6), with hypotheses [F1] (weak), [F2], S1, S2, D(c) and [F3]. [F3] (fds free up infinitely often) is an explicit hypothesis of the connection half of the theorem | **approved** |
| D15 | R1-live gains S3 (the server reads what it is shown) and S4 (if the peer drains, the outbox eventually falls to ≤ hw) as per-server obligations, not trusted. They are discharged per server: echo, HTTP and KV from their v2 liveness and reply-only writes; chat via D7 | **approved** |
| D16 | Spurious hard errors (the L0 model allows any error but EAGAIN as a transient failure, [P 2.3]): (live-data) holds **unless L1 observed a hard error on c**, in which case the episode ended (`Eof2 j`). No new trust. Plus a corollary with the condition as an explicit **hypothesis**: if hard errors on c occur only when the connection really broke, every byte c's peer delivered is eventually in `psk` | **approved** |
| D11′ | **[F1] restated on observed outcomes** (replaces D11's world-choice form; does not add to it). Per call kind and per fd: a call on f made infinitely often does not return a *retried* outcome infinitely often. Retried = an `l1_transient` error (EAGAIN, EINTR, ENOBUFS, ENOMEM) for recv, accept and send; any failure for poll (L1 retries every failed poll next round). Reason: the weakest single assumption, and no extra narrowing of POSIX. It covers both the world's transient choice and a broken channel's transient-looking errors (`broken_recv`, an `LBreak` error), with no trusted "broken errors are never transient" fact. Stated on the run's IO-event trace (the observed results) | **approved (user, via coordinator)** |
| D17 | Running out of fds at accept. **ENFILE is retried** (only EMFILE pauses). **While the process is out of fds, L1 retries accept after a backoff** of `pf_backoff` rounds (a model constant; no proof uses its value), as real servers pause accepting and retry, instead of waiting for a close. No "no spurious EMFILE" hypothesis. In the model: `pause` in the PF state; L1 polls the listener only when `pause = 0`. Stated honestly in §5/§6: at a real fd limit on macOS, each retry's EMFILE may reset one queued connection (`emfile_drops`), which live-conn's "dropped" case covers. *Corrected 2026-10-17:* this row said EMFILE needs no new assumption; that was wrong, because L0's `transient` may be a spurious EMFILE (§6). The corollary uses H3′ (EMFILE in the joint weak set) instead of [F3]. The CakeML L1 loop and its CF spec follow the model | **decided (user, via coordinator)** |
| D18 | Spurious accept errors (the analogue of D16 for the listener). **live-conn, main form (no new trust):** j0 is (a) accepted, (b) dropped (broken or aborted, or an EMFILE reset), or (c) L1's accepts on lfd fail (retried) infinitely often. **Corollary** under the explicit hypothesis "every ECONNABORTED on lfd's accept really dropped a queued connection" (on observed events plus the queue where possible; otherwise on world choices, with the reason): accepted or dropped. [F1]'s retried set for accept stays as in D11′. Rationale, for consistency with D11′/D16/D17: never add trusted kernel facts that narrow POSIX's looseness; weaken the main theorem honestly, and give the strong form as a corollary under an explicit hypothesis | **decided (user, via coordinator)** |

| D19 | Hung-up fds (user decision, option 2; via async-spike's L3-00 Q-L3-1). On POLLHUP for a connection fd L1 holds, L1 fetches what is left. (a) If the input ends with a hard error (`FReset`: the connection really broke), its outbox is dropped and the fd is marked gone, so it is closed. (b) If it ends with EOF (a half-close; the fd may still be writable), L1 keeps flushing and closes when drained, but after `pf_hupwait` consecutive rounds with a non-empty outbox and no send progress (a named constant, like `pf_backoff`) the outbox is dropped. An empty outbox or any progress resets the count. Model: `hups` in the PF state, `hup_step` between the fetch and the reap. No HUP disjunct anywhere: no hung-up fd is polled forever. The cost on the output side: liveness assumes the peer reads within `pf_hupwait` rounds of the hang-up. *Correction:* the first framing said a hung-up fd is always unwritable. That is wrong for a half-close: the L0 model, like platforms, may report POLLHUP after the peer's FIN alone, and the fd stays writable, so dropping at once would lose replies to half-closing clients *Superseded in part by D23:* (b)'s timeout now applies to every fd, not only hung-up ones (`stall_step`, `stalls`, `pf_sendwait`); (a) is kept | **decided (user, via coordinator)** |
| D20 | **sys_poll on CakeML's `struct pollfd` buffer** (§3.6). The C is a pass-through: `poll` runs in place on the caller's buffer from offset 16, with no copy loop and no cap (`MAX_FDS` 4096 is gone, and with it `poll_chunks`: L1 polls once per round). The layout is a **build-time-checked ABI assumption** (static asserts); a misaligned buffer gets EINVAL (runtime check); events other than POLLIN/POLLOUT are an **unchecked precondition** on callers, which L1 meets (proved). The L0 model reads the entries (`pollfd_entries`), allows fds ≥ 2^31 (revents 0), and has `poll_junk` for a failed poll's revents. Conformance rerun on Linux (§4.3). R1/R1-live are unchanged in wording; internally, `psmall` (polled fds < 2^31) is a new invariant along runs | **decided (user, via coordinator)** |
| D21 | **Reset after the peer's EOF** (a Linux conformance finding, P4 and the random test). After the peer's EOF, with an empty inbox and a reset's error pending, recv may return 0 and leave the error pending (`eof_first`), as well as report it. Labelled **[P] POSIX looseness**, consistent with the model's reading of recv's ECONNRESET as the once-reported pending error ([P 2.10.10], [P 2.10.11], [P recv] RETURN VALUE; §4.2). No statement changes: a flushed break read as EOF was already reachable, and the D16 corollary already allows it (`flushed`) | **decided (user, via coordinator)** |
| D22 | **shutdown of a pending connect** (Linux, P13). [P shutdown] forbids the success: platform extension **[X5]**. **No model change** (option A): the observed trace is a behaviour of the model through environment choices (`LConnUp`, then `LBreak`), and verified L1 never calls `sys_shutdown`. The checker may draw a break no client action logged when connerr reports one | **decided (user, via coordinator)** |
| D23 | **Write timeout** (Finding 2, option (ii-b); generalises D19). A peer that stops reading for good is indistinguishable, through poll and send, from a slow one: a receiver that keeps its window closed while it acknowledges the probes keeps the connection open indefinitely ([T] RFC 1122 §4.2.2.17), so no error is ever reported. So L1 times out every fd, not only hung-up ones: after `pf_sendwait` consecutive rounds with a non-empty outbox and no send progress, L1 drops f's outbox and marks it gone (closed at the reap or the auto-close, as for D19). A round with progress or an empty outbox resets the count. A hard input error (`FReset`) still drops at once (D19 (a)). Model: D19's counters absorbed into one per-fd stall count, `stalls` in the PF state, `stall_step` between the fetch and the reap, now tracking every fd L1 holds (`pf_held`); `pf_hupwait` becomes `pf_sendwait` (8). POLLHUP no longer plays a part. Statements: R1-safe, R1-live and the D16 corollary are unchanged (dropping is the existing `gone` path, which acct already allows as a prefix; nothing on the input side reads `gone`). Output liveness (flush_progress, S4w, flush_live) reads "unless L1 timed f out", an observed disjunct, with a strong form under "the peer reads within `pf_sendwait` rounds of a stall" | **decided (user, via coordinator)** |
| D24 | **counts below 2^64** (from m4-server's B2 work). `l0_rely` gains `(∀j h b n. w.ch.takes j h b n < 256 ** 8) ∧ (∀j h a. w.ch.short j h a < 256 ** 8)`: [P send/recv] return `ssize_t`, so a count is at most SSIZE_MAX; the C checks `sizeof(ssize_t) <= 8` at build time (with D20's asserts, §3.6). A stronger rely: no existing proof changes | **decided (user, via coordinator)** |
| D25 | **Handle-room guard counts only Accept actions** (echo liveness cut-off). Handles are the 2^64 − 1 word64 values other than lfd's (`l1hdln` skips it), and `l1hdln lfdn j < 2^64 ⇔ j + 1 < 2^64` (`l1hdln_lt`). Only an Accept action takes one (and only when a prefetched connection is waiting: an unhanded prefetched accept takes none). The round's guard was `l1hdln (nxt + LENGTH acts) < 2^64`, counting every action and stricter by one; it is now `nxt + naccepts acts < 2^64` (`pl2_ok`, `pround_ok`): exactly what the round's accepts can need, so a server issuing one Accept a round is served while fewer than 2^64 − 1 connections have been handed out. Statements: only the room hypothesis of R1-live (`pl2_ok`) changes, and it gets weaker; R1-safe's own hypotheses are unchanged | **decided (user, via coordinator)** |

**Principle (user):** OS assumptions are justified by POSIX and the RFCs
only, never by any platform's behaviour. The probes are tests, not
justification.

§4.1 (the refused/error encoding) is approved with D1/D3, and close-v2
implements it in the endpoint world.

## 10. Statement-only HOL drafts (this branch)

`async/honest-ffi/`, built with holslot -j1, no cheats. Claims are
definitions of propositions:

- `honestL0Script.sml`: the error codes, the result header encoding and
  decoding (proved inverse), the readiness flags, and the L0 result types
  (`acc_res`, `recv_res`, `send_res`).
- `honestL1Script.sml`: the L1 per-fd state and the wrappers' functional
  core in today's vocabulary, including the round discipline and the
  poll set. Proved:
  - R3's per-wrapper simple-world lemmas: `write_simple`, `read_simple`,
    `accept_simple`, `poll_simple`;
  - three first facts beyond the simple world:
    - `stall_local`: a failed or partial send on c touches no other fd;
    - `gone_is_eof`;
    - `exhausted_quiet`: while out of fds, the listener is not polled
      for input.

  R1/R2 (the run-level statements) are not drafted in HOL. They need the
  L0 world, whose shape waits for D1–D3.

Both files build (`Holmake`, holslot -j1). 11 theorems, no cheats.

## 11. The boundary is pragmatic: what we expect to revise

The user asked for a boundary that is easy to change. Here is what is
meant to be stable, and what is expected to move:

- **Stable: L1's spec.** It is today's v1/v2 socket worlds, unchanged.
  That is the most stable choice available: the servers' theorems already
  rest on it. New needs (the proxy's backpressure, timers) are met by
  **adding** L1 interfaces with their own specs. The existing one is not
  changed.
- **Expected to change: L0 and its model.**
  - connect/connerr (with close-v2's refused connects);
  - the HUP/ERR rules per platform, once the tester has measured them;
  - the set of transient errors;
  - `sys_listen`'s shape (IPv6, other addresses);
  - poll vs kqueue/epoll for many fds (today `MAX_FDS` 4096);
  - a poll timeout, once timers exist;
  - possibly D3's time model.

  Each change re-proves L1 (phases 4–6) and nothing above it.
- **Expected to be tuned: L1's policies.**
  - the high-water mark H;
  - lingering close or immediate close;
  - the chat slow-client limit (D7);
  - what a reset means for the episode.

  These live in verified CakeML. They change L1's proofs and,
  where they are visible in the raw specs (`ends_on_gone`, `graceful`),
  those clauses. They never change the servers.
- **Deliberately not decided now:**
  - the richer L1 interface the proxy will need;
  - whether the endpoint world and the L0 world merge (close-v2 owns the
    former; §4 is written as a proposal to extend it, but a separate L0
    theory beside it works too).
