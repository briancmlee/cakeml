# 36: An honest, minimal socket FFI, with verified wrappers (AUDIT + DESIGN, for review)

Status: **design only; nothing implemented.** Branch `spike/honest-ffi`
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

**Decisions for the user: §9.**

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
| `sys_poll` | `poll(fds, k, block ? -1 : 0)` | 1 byte block flag; k × (fd 8 bytes ++ events 1 byte: bit0 IN, bit1 OUT) | k bytes of `revents`: bit0 IN, bit1 OUT, bit2 ERR, bit3 HUP, bit4 NVAL | priority bands, timeouts other than 0 and ∞ (no timers yet) |
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
| poll (marshalling loops) | 14 |
| accept | 4 |
| recv | 5 |
| send | 5 |
| shutdown, close | 6 |
| **total** | **≈ 100**, of which the error table is a quarter |

Today it is about 140 lines of code. More important than the count:

- **no loops except array marshalling;**
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

## 4. L0's world model: an extension of the endpoint world

L0 is modelled as a variant of `endpointWorld` (close-v2's file; this is
a **proposal**, not an edit). The design rule: **over-approximate**.
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

## 5. L1: the verified wrapper layer

L1 is **one CakeML module plus its loop**: the honest-world version of
close-v2's handle layer (`asyncHLProg`: a verified table and auto-close,
the server unchanged). It sits between the event loop's `perform` and L0.
**The server (L2) sees exactly today's vocabulary:**

- actions `Accept l | Read c n | Write c bs` (+ `Close c` in v2);
- responses `Accepted (fd option) | Got (data | EOF | would-block) |
  Wrote`;
- readiness: the set of readable fds.

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

## 9. Decisions for you

1. **D1, honesty criterion.** "Every real behaviour is a model behaviour"
   (over-approximation allowed, never under-approximation), with platform
   differences as ∀-quantified world choices. Agree?
2. **D2, setup.** `sys_listen` as one restricted straight-line call made
   by the program (recommended), or keep a minimal documented constructor
   contract? Also: check fds 0–2 in the constructor (recommended), or
   state it as a precondition only?
3. **D3, time (L6).** Fix it in the model (arrivals before any call;
   L1's discipline + regrouping prove our programs unaffected), as
   recommended? Or keep "time only at poll" as a documented abstraction?
   The latter is cheaper (phase 6 shrinks by about half), but it is a
   statement the kernel does not satisfy.
4. **D4, write semantics for L2.** Buffered writes with pausing (L1
   outboxes, `Wrote` at once; **no server proof changes**; recommended),
   or a `write_all` computation that L2 waits on? The latter gives
   natural flow control, but needs a new response timing in the Level-1
   model and therefore re-proved server liveness.
5. **D5, v1 programs.** Keep v1 relinked programs, with the honest
   `clients_below` hypothesis? Or retire the v1 runnables in favour of v2
   (close + handle layer), keeping `echo_spec` only as the model-level
   theorem it is today?
6. **D6, `«sock_write»`.** It stays as an idealised model call for the
   v1/v2 instance theorems (close-v2's request), and the honest C drops
   it. OK?
7. **D7, slow clients under broadcast (chat).** Unbounded outbox, or drop
   the client at a hard limit (recommended, as real chat servers do)?
8. **D8, the point on the size/effort curve** (§3.5). (c) is
   recommended.

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
