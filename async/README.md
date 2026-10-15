> **DRAFT for your voice.** Every claim names its theorem. The sections
> marked **[Your voice]** are yours to write; the facts elsewhere should
> stay checkable.

# A verified asynchronous echo server (and HTTP server) in CakeML

```
(* spec/EchoSpecScript.sml *)
echo_spec lfd prog ⇔
  ∀sk. server_world lfd sk ⇒
       ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog
              (Diverge io) ∧
            echo_safe io ∧ echo_live sk io

(* headline/asyncM4EchoSpecScript.sml *)
Theorem echo_prog_spec:
  echo_spec 3w echo_prog
```

In plain English: **in every fair world** with one listening socket and
any future pattern of connections and data, **the echo program runs
forever**. At every moment, **on every connection, what it has sent back
is a prefix of what that client sent** (safety). **Everything a client
sends is eventually sent back** (liveness).

`echo_prog` is the actual CakeML program: the basis library, a socket
module, an async library, an event loop and a concurrent server. It
compiles and runs (below).

Alongside:
- **a blocking version** that sleeps in `select`, proved to refine the
  headline (`echo_blocking_spec`);
- **an HTTP server** that tolerates request headers. It meets the safety
  half of a header-tolerant HTTP specification (`http_prog_h_safe`).

## What you have to trust

| file | what it says |
|---|---|
| `spec/EchoSpecScript.sml` | the sockets-only FFI oracle, per-connection projections of raw I/O events, `echo_safe`, `echo_live`, `echo_spec` |
| `spec/HttpSpecHeadersScript.sml` (with HttpSpec's paths, files and response printer from `spec/HttpSpecScript.sml`) | requests with any headers, `http_safe_h`, `http_live_h`, `http_spec_h` |
| `world/sockets/ffiSpikeSocketFFIScript.sml` | the socket world: listeners, connections, a schedule of future arrivals; the byte-level FFI functions |
| `world/sockets/ffiSpikeSocketFairScript.sml` | fairness of schedules (`sched_wf`, used by `server_world`) |
| CakeML | the source semantics (`semantics_prog`) and its I/O events |
| `runnable/socket_ffi.c` | the C side of the socket calls, which must implement the socket model (a mapping table is in the file) |

Nothing else is trusted. The async library's model, its CakeML
implementation, the event loop and the scheduler are all proved, and none
of them appears in the statement.

## Why you should believe it

- **No cheats.** There are 115 theory files and about 29,000 lines of
  HOL4. None contains a `cheat`, and each directory builds with `Holmake`
  on top of CakeML's basis.
- **The spec bites.** `spec/EchoSpecBiteScript.sml` proves that the
  traces of plausible broken servers violate the spec:
  - swapping clients' data (`broken_swaps_clients`);
  - dropping or duplicating a byte (`broken_drops_a_byte`,
    `broken_duplicates_a_byte`);
  - writing before reading (`broken_writes_before_reading`);
  - never echoing (`broken_never_echoes`).

  `spec/HttpSpecHeadersBiteScript.sml` does the same for HTTP. It covers
  letting a header change the response, answering before the blank line,
  and never answering. It also shows that curl's default request is a
  valid request (`curl_request`).
- **The spec is not vacuous.** A fair world exists
  (`server_world_exists`). In it, an ideal trace satisfies safety and
  liveness together (`ideal_trace_safe_and_live`).
- **The spec came first.** EchoSpec was written and reviewed before the
  final proofs, and they had to meet it as stated.

## It runs

```
$ make demo          # runnable/echo: 3 concurrent clients and a late 4th
[  0.000s] alice    sent     'hello from alice'
[  0.001s] alice    received 'hello from alice'
...
[  0.466s] check    alice: received exactly its own lines: True

$ curl -s -i http://127.0.0.1:7840/        # runnable/http: plain curl, default headers
HTTP/1.0 200 OK
Content-Length: 42

Hello from a verified CakeML HTTP server!
```

- **Build route.** The verified programs are exported from HOL as
  S-expressions (`programs/*/…sexp`). The official CakeML release
  compiler (v3479) compiles them natively for arm64, and they are linked
  with the release's `basis_ffi.c` and `runnable/socket_ffi.c`.
- **Speed.** The echo server reaches 60–70% of the throughput of a
  trivial Python asyncio server (`runnable/echo/bench-results.txt`). This
  is not a careful benchmark.
- **CPU** (`runnable/echo-blocking/cpu-results.txt`):
  - the blocking server sleeps (0.0%) while idle and under light load;
  - a polling server faithful to the model busy-waits.

## The key design idea

**Pull-based polling is also the verification-friendly design.**

- A computation is a function from the *history of world snapshots* it
  has been polled with to its action log and optional result
  (`model/core/asyncCore`).
- There are no callbacks, no mutable promise cells and no scheduler state
  for the proofs to track.
- So the library's laws are **equalities of computations**:
  - the monad laws;
  - `choose` loses nothing: `bind (choose m1 m2) rejoin = both m1 m2`.

**Level 1 → Level 2 gives provable no-busy-waiting.**

- Level 2 records the events a computation waits for. A computation is
  *quiet* if rounds in which none of them is ready can be deleted without
  changing anything. Every combinator and the echo server are quiet.
- So a scheduler may block, and it behaves exactly like one that polls
  (`model/sched/asyncSched2`).
- The same holds for CakeML's event loop: the `select` loop is equivalent
  to polling (`loop/blocking-l2`), and the blocking echo program refines
  the polling one (`echo_blocking_spec`).

## Honest limitations

- **HTTP liveness is in progress.** HTTP has the safety half
  (`http_prog_h_safe`); `http_live_h` is being proved.
- **The blocking server spins after a client disconnects.** The loop's
  interest list only grows, and a closed connection stays ready (EOF). A
  fix that selects only on live connections is in progress.
- **No `close`.** The socket model has no `close`, so finished
  connections are never closed and a long-running server leaks fds. A v2
  with `close` and fd reuse is in progress.
- **The machine-code theorem is pending.** The program-level theorem is in
  the form CakeML's compiler correctness theorem consumes, and the
  composition scripts are written (`runnable/machine-code/`). Running them
  needs CakeML's compiler proofs built in-logic. Until then the release
  compiler and the S-expression export (cross-checked against the
  official printer) are in the trusted base.
- **The socket model is idealized.** It has no errors besides EOF, and
  writes always succeed in full. `socket_ffi.c` documents how reality is
  mapped onto it.
- An earlier, strict HTTP spec (`GET <path> HTTP/1.0` with no headers) and
  its results are archived on the spike branches.

## How it was built

**[Your voice.]**
- You designed and reviewed the specifications and the design decisions,
  and set the policy: specs first, no cheats, readable lemmas, additive
  changes.
- AI agents (Claude) wrote the proofs, the CakeML code and the design
  notes. They worked as parallel workers on stacked branches,
  coordinated by an orchestrating session.
- Every theorem was checked by HOL4.

## Where to read next

- `REVIEW-START-HERE.md` gives the reading path through the 11 review PRs.
- `design/README.md` indexes the design notes by layer.
