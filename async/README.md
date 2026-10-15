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
- **a blocking version** that sleeps in `select` on the listener and the
  live connections only. It is proved to refine the headline
  (`echo_live_spec`), and it idles at 0.0% CPU;
- **an HTTP server** that tolerates request headers. It meets a
  header-tolerant HTTP specification **in full**, safety and liveness:

  ```
  (* headline/asyncHttpSpecHScript.sml *)
  Theorem http_prog_h_spec:
    http_spec_h 3w demo_files http_prog_h
  ```

  The HTTP server is also proved quiet (no busy-waiting at Level 2,
  `servers/http-quiet`).

**Polling and blocking.** The trusted C (`runnable/socket_ffi.c`) does
exactly what the model says: `sock_poll` is one `poll(2)` with timeout 0.
So the polling headline busy-polls while idle, and the verified blocking
refinement idles at 0.0%:

| server | idle, before any client | light load | idle, after a client left |
|---|---|---|---|
| `echo_live` (blocking, `echo_live_spec`) | 0.0% | 0.1% | 0.0% |
| `echo_polling` (the headline program) | 26.0% | 15.9% | 67.3% |

CPU% is process CPU time over wall time, in 30 s phases, from a background
session that throttles busy polling (a C busy-polling loop measures
13–16% there). The blocking row is from
`runnable/echo-blocking/cpu-results.txt` (#46), and the polling row is
from `cpu-results-no-idle-wait.txt` (#50, the C as it is now).

## What you have to trust

| file | what it says |
|---|---|
| `spec/EchoSpecScript.sml` | the sockets-only FFI oracle, per-connection projections of raw I/O events, `echo_safe`, `echo_live`, `echo_spec` |
| `spec/HttpSpecHeadersScript.sml` (with HttpSpec's paths, files and response printer from `spec/HttpSpecScript.sml`) | GET requests with any headers except body-framing ones (no request bodies), `http_safe_h`, `http_live_h`, `http_spec_h` |
| `world/sockets/ffiSpikeSocketFFIScript.sml` | the socket world: listeners, connections, a schedule of future arrivals; the byte-level FFI functions |
| `world/sockets/ffiSpikeSocketFairScript.sml` | fairness of schedules (`sched_wf`, used by `server_world`) |
| CakeML | the source semantics (`semantics_prog`) and its I/O events |
| `runnable/socket_ffi.c` | the C side of the socket calls, which must implement the socket model (a mapping table is in the file) |

Nothing else is trusted. The async library's model, its CakeML
implementation, the event loop and the scheduler are all proved, and none
of them appears in the statement.

## Why you should believe it

- **No cheats.** There are 129 theory files and about 34,000 lines of
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
  answering a request that carries a body (`broken_answers_body_request`),
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
- **CPU:** see the table above.

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
  to polling (`loop/blocking-l2`, `brun_two_outcomes`), and the blocking
  echo program refines the polling one (`echo_live_spec`).

## Honest limitations

- **This HTTP subset has no request bodies.** Requests with
  Content-Length or Transfer-Encoding are not answered.
- **Proofs establish values, not running time.** An exponential-time
  parser passed all proofs until a long header exposed it: the translated
  code of a recursive split made its recursive call twice per character,
  so a 165-character User-Agent got no answer in 10 s. It was fixed with
  proved-equal linear definitions (`split_at2`, `split_path2`), and now
  takes 1.5 ms. The parsers' definitions and theorems are unchanged.
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
