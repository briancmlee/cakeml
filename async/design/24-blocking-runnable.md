# 24: The blocking echo server, running

Branch `spike/blocking-runnable`, stacked on `spike/m4-blocking` (PR #27).
It merges `spike/runnable` (PR #23) and uses it read-only, except for one
addition to the trusted `socket_ffi.c` (§1).

- New directory: `async/blocking-runnable/`.
- `Holmake` there exports `echo_blocking.sexp`; `make` builds three
  servers.

**Headline status (user decision).** EchoSpec stays unchanged, and the
polling program remains the headline. `echo_blocking_spec`
(`async/m4-blocking`, 17) is the official refinement/companion theorem,
presented directly under it.

## 1. The C side of `«sock_select»` (TRUST ITEM)

`ffisock_select` is added to `async/runnable/socket_ffi.c`, with a row in
the file's mapping table. The model is `ffi_sock_select`
(`asyncM4BlkLoop`):

- **config:** k fds, 8 bytes each (`fds_bytes`, as for `sock_poll`);
- **buffer:** empty, and nothing is consumed;
- **behaviour:** block until a poll of the fds would report one ready, or
  forever if that never happens (`FFIdiverge`).

The C function calls `poll(2)` with no timeout on the fds, for
`POLLIN`, `POLLHUP` or `POLLERR` (the same readiness as `sock_poll`). It
retries on `EINTR`, and aborts on `POLLNVAL` or bad lengths, as the model
rejects those. With k = 0 it blocks forever.

**Trust item:** `ffisock_select` behaves as `ffi_sock_select`. The
following `sock_poll` reports the ready set, as in the model.

#23's idle-wait heuristic in `sock_poll` has since been **removed**
(§4, `spike/no-idle-wait`): `sock_poll` never waits, exactly as the
model's poll, in every build.

## 2. The program, compiled and running

`asyncEchoBlkExportScript.sml` exports exactly the program that
`echo_blocking_semantics` and `echo_blocking_spec` are about:
`SNOC (main_call «main») echo_b_prog`, with
`fun main u = run_b ([3], server 3)`. It is compiled with release v3479
(arm8, native), as #23 does.

The demo (`make demo`, `demo-transcript.txt`) has three concurrent clients
and a late one. Each gets back exactly its own lines, as with the polling
server.

## 3. CPU usage (indicative)

`make cpu` (`cpu_bench.py`) runs each server through three 30 s phases:

1. **idle-fresh:** no client has ever connected;
2. **light load:** one client sends a 64-byte line every 100 ms and reads
   the echo;
3. **idle-after:** that client has disconnected.

CPU% = process CPU time / wall time, from `ps -o cputime`.

**Caveat about the environment.** These runs were made from a background
session whose processes are niced (nice 10, background QoS), and
`taskpolicy` cannot lift that. A pure C busy loop (`spin.c`, the
calibration row) measures only 16% there. So compare the servers with the
calibration row, not with 100%. Run `make cpu` in a normal terminal for
absolute numbers.

```
calibration: a C busy loop measures 13.6% here (= one core fully busy in this environment)
phases of 30 s each; CPU% = process CPU time / wall time (100% = one core)
server                  idle-fresh  light-load  idle-after  rtt median
echo_blocking                 0.0%        0.1%       65.8%       315us
echo_polling                 26.0%       15.9%       67.3%       718us
```

(Re-measured after the idle wait was removed, §4; the same niced session,
so compare with the calibration row. Before the removal, `echo_polling`
measured 0.1% / 0.2% / 0.1% with the heuristic, and the model-faithful
build without it, then called `echo_polling_nowait`, measured
24.4% / 27.3% / 82.5% against a 16.2% calibration.)

| build | what it is |
|---|---|
| `echo_blocking` | the blocking program (this PR) |
| `echo_polling` | #23's polling program; `sock_poll` exactly as the model's (no wait) |

What the numbers show:

- **The polling server busy-polls** whenever it runs: it is at or above
  the busy-loop calibration in every phase. This is the honest cost of a
  `sock_poll` that returns at once, as the model's does.
- **The blocking server sleeps** while no client has ever connected, and
  under light load.
- **But it spins once a client has disconnected.** The loop's interest
  list only grows, and a closed connection stays ready forever (EOF). The
  model has no `close`. So a model-faithful `select` on the whole list
  returns at once, every round.
  - This is a property of the verified loop, not of the C side.
  - The fix (select only on the live connections) is in
    `spike/m4-blocking-live`.

## 4. #23's idle-wait heuristic in `sock_poll`: removed

#23's `sock_poll` waited up to 50 ms when the program looked idle: no
socket operation since the last poll, and the same ready set for 2 polls
in a row. The wait was unobservable in the model (its poll delivers one
step of an arbitrary arrival schedule, with no time inside a poll), but
it was a scheduling heuristic in trusted code, not a refinement of
anything proved, and it added up to 50 ms of latency when a quiet period
ended.

**It has been removed** (`spike/no-idle-wait`, a user decision): `sock_poll`
is a single `poll` with timeout 0, so the trusted C now matches the
model's poll directly. The cost is that the polling program busy-polls
while idle (§3); the blocking program, which sleeps in `sock_select`, is
the one to run.

## 5. Connections are never closed (limitation, future work)

The socket model has no `close`, so the server never closes a finished
connection's fd. A long-running server therefore leaks one fd per
connection, and its interest list grows with every connection.

Future work: add `close` to the socket model and the server (and remove
the fd from the interest list), with the matching C call.
