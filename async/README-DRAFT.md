> **DRAFT, to be rewritten in your own voice.** Written by an agent from
> what is proved on `spike/presentation` (2026-10-15). Every claim below
> names its theorem, and the pending ones are marked **PENDING**. Tone,
> order and emphasis are yours to change; the facts should stay checkable.

# A verified asynchronous echo server (and HTTP server) in CakeML

```
(* spec/EchoSpecScript.sml: the theorem to prove is  echo_spec 3w echo_prog *)
echo_spec lfd prog ⇔
  ∀sk. server_world lfd sk ⇒
       ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog
              (Diverge io) ∧
            echo_safe io ∧ echo_live sk io
```

In plain English: **in every fair world** with one listening socket and
any future pattern of connections and data, **the compiled echo program
runs forever**. At every moment, **on every connection, what it has sent
back is a prefix of what that client sent** (safety). **Everything a
client sends is eventually sent back** (liveness).

**Status:**
- **Proved:** the safety half, for the real program
  (`asyncHeadline.echo_prog_safe`: `echo_spec 3w echo_prog` without
  `echo_live sk io`).
- **PENDING:** `echo_live` for the program. It is in progress on
  `spike/m4-liveness`; liveness is already proved in the model (see
  Honest limitations).

`echo_prog` is the actual CakeML program: the basis library, a socket
module, an async library, an event loop and a concurrent server. It is
compiled and running (below). The same safety result holds for an HTTP
server against an HTTP specification (`http_prog_safe`).

### A stricter implementation, and what it buys you: the blocking server

The headline program *polls*: each round it asks the sockets which fds
are ready and carries on. A second program, `echo_b_prog`, runs the same
server under an event loop that **sleeps in `select`** whenever the
server is waiting. It is proved against the *same* `echo_safe` and
`echo_live`, reused verbatim (`asyncM4BlkMain`, PR #27):

```
echo_blocking_spec:
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ⇒
  (∃io. semantics_dec_list (init_state (ssel_ffi sk)) init_env
          (SNOC (main_call «main») echo_b_prog) (Diverge io) ∧
        echo_safe io ∧
        (echo_live sk (poll_io [3w] echo_m sk) ⇒ echo_live sk io)) ∨
  (∃c io. semantics_dec_list (init_state (ssel_ffi sk)) init_env
            (SNOC (main_call «main») echo_b_prog)
            (Terminate (FFI_outcome (Final_event (ExtCall «sock_select») c []
                                       FFI_diverged)) io) ∧
          echo_safe (fromList io) ∧
          (echo_live sk (poll_io [3w] echo_m sk) ⇒ echo_live sk (fromList io)))
```

- **The world** (`ssel_ffi sk`) is EchoSpec's socket world plus one
  call, `«sock_select»`.
- **Two outcomes.**
  - The blocking program either runs forever, with an `echo_safe` trace
    that is `echo_live` whenever the polling program's is;
  - or it ends **asleep in `select`** after a finite trace that is
    `echo_safe`, and `echo_live` whenever polling's is. This happens
    only once the polling program would never act again, i.e. after it
    has done everything polling would do.
- **Safety is unconditional.**

This is the program-level counterpart of the model's Level 1 → Level 2
story (below). The stricter implementation buys an idle server that
consumes no CPU, and the price is one more FFI call and one more possible
outcome. **[Idle-CPU comparison table: being produced on
`spike/blocking-runnable`.]**

**Why is the verified headline the polling program?**
- Its specification is the simplest one to read and trust: a socket world
  without `select`, and one outcome, "runs forever".
- The blocking program is not a weaker result hidden behind it. It is
  proved to *refine* the headline: same properties, the same trace modulo
  polls and selects, plus an explicit "asleep in select" ending.
- In the polling build that runs below, the waiting is done by trusted C
  code (an idle wait in `socket_ffi.c`, which the model cannot observe).
  The blocking program moves the sleeping into verified code.

---

## What you have to trust

The statement uses only these definitions:

| file | lines | what it says |
|---|---|---|
| `spec/EchoSpecScript.sml` | 155 | the sockets-only FFI oracle, the per-connection projections of raw I/O events, `echo_safe`, `echo_live`, `echo_spec` |
| `spec/HttpSpecScript.sml` | 115 | the HTTP subset (printer for requests, responses, the file map), `http_safe`, `http_live`, `http_spec` |
| `ffi-spike/ffiSpikeSocketFFIScript.sml` | 426 | the socket world: listeners, connections, a schedule of future arrivals; the byte-level FFI functions |
| `ffi-spike/ffiSpikeSocketFairScript.sml` | 402 | fairness of schedules (`sched_wf`, used by `server_world`) |
| CakeML | n/a | the source semantics (`semantics_prog`) and its I/O events |
| `runnable/socket_ffi.c` | 189 | the C side of the four socket calls, which must implement the socket model; a mapping table is in the file |

Nothing else is trusted. The async library's model, its CakeML
implementation, the refinement layer, the event loop and the scheduler
are all proved, and none of them appears in the statement.

## Why you should believe it

- **No cheats.** There are 94 theory files and about 25,000 lines of HOL4
  on this branch, and none contains a `cheat`. Each part builds with
  `Holmake` on top of CakeML's basis.
  - **TODO (measure):** one-command build time on a clean checkout. The
    estimate is ~20 minutes at `-j2` on an M1.
- **The spec bites.** `spec/EchoSpecBiteScript.sml` proves that concrete
  traces of plausible broken servers violate the spec:
  - swapping two clients' data (`broken_swaps_clients`);
  - dropping a byte (`broken_drops_a_byte`);
  - duplicating a byte (`broken_duplicates_a_byte`);
  - writing before reading (`broken_writes_before_reading`);
  - never echoing (`broken_never_echoes`).

  `spec/HttpSpecBiteScript.sml` does the same for HTTP:
  - the wrong order (`broken_wrong_order`);
  - a 200 for a missing file (`broken_200_for_missing_file`);
  - a wrong Content-Length (`broken_wrong_content_length`);
  - answering a half-arrived request (`broken_answers_partial_request`);
  - never answering (`broken_never_answers`).
- **The spec is not vacuous.** A fair world exists (`server_world_exists`,
  `server_world_one_client`). In it, an ideal trace satisfies safety and
  liveness together (`ideal_trace_safe_and_live`,
  `ideal_http_trace_safe_and_live`).
- **The spec came first.** EchoSpec and HttpSpec were written and
  reviewed before the final proofs. The proofs had to meet them as
  stated, and HttpSpec was never edited to make a proof go through.

## It runs

```
$ make demo          # async/runnable: 3 concurrent clients and a late 4th
[  0.000s] alice    sent     'hello from alice'
[  0.000s] bob      sent     'bob says hi'
[  0.001s] alice    received 'hello from alice'
[  0.001s] bob      received 'bob says hi'
...
[  0.466s] check    alice: received exactly its own lines: True
```

```
$ curl --http1.0 -H Host: -H User-Agent: -H Accept: -i http://127.0.0.1:7830/
HTTP/1.0 200 OK
Content-Length: 42

Hello from a verified CakeML HTTP server!
```

- **How it is built.** The verified program is exported from HOL as an
  S-expression and compiled by the official CakeML release compiler
  (v3479), natively for arm64 on an M1 Mac. It is linked with the
  release's `basis_ffi.c` and the 189-line socket FFI.
- **The demo transcripts** are `runnable/demo-transcript.txt` (echo) and
  `http-safety/http-demo-transcript.txt`. The HTTP one covers concurrent
  and pipelined requests.
- **Indicative numbers.** On an M1 Pro over loopback, with a threaded
  Python client, the verified echo server reaches 60–70% of the
  throughput of a trivial Python asyncio echo server. For example:

  | clients × lines | verified CakeML | Python asyncio |
  |---|---|---|
  | 10 × 1000 | 32,204 lines/s | 52,900 lines/s |

  Median round trips are tens to hundreds of µs
  (`runnable/bench-results.txt`). These are not careful benchmarks.

## The key design idea

**Pull-based polling is also the verification-friendly design.**

- A computation is a function from the *history of world snapshots* it
  has been polled with to its action log and optional result
  (`model/asyncCore`).
- There are no callbacks, no mutable promise cells and no scheduler
  state for the proofs to track. `bind`, `both` and Async-style `choose`
  are pure functions on histories.
- So the library's laws are **equalities of computations**:
  - the monad laws;
  - `choose` loses nothing: `bind (choose m1 m2) rejoin = both m1 m2`.

  Recursive servers are admitted by a guarded-recursion rule.

**Level 1 → Level 2 gives provable no-busy-waiting.**

- Level 2 adds, to each computation, the set of events it is waiting for,
  and *erases* to Level 1 (`model/asyncLevel2`).
- A computation is *quiet* if snapshots in which none of its events are
  ready can be deleted without changing anything. Every combinator, the
  echo server and the idle-deadline loop are quiet.
- Hence a scheduler may **block** until an awaited event is ready, and it
  behaves exactly like one that polls every round (`model/asyncSched2`).
- The same transfer has been carried to CakeML's event loop: the
  select-based loop is proved equivalent to polling (`l2-blocking`), and
  the blocking echo program refines the polling one (`echo_blocking_spec`,
  above).

## Honest limitations

- **PENDING: liveness at the program level.** `echo_live` ("everything a
  client sends is eventually echoed") and `http_live` are not yet proved
  for the CakeML program, so the full `echo_spec 3w echo_prog` is not yet
  a theorem (and `echo_blocking_spec`'s liveness is conditional on it). Liveness is proved in the model's closed loop: every byte
  that arrives is written back within n + 3q + 5 rounds (`asyncLiveness`).
  The program-level proof is in progress (`m4-liveness`).
- **PENDING: the machine-code theorem.** The program-level theorem is in
  the form CakeML's compiler correctness theorem consumes, and the
  composition scripts are written (`machine-code/`). Running them needs
  CakeML's compiler proofs built in-logic (~10 GB peak), which has not
  been done yet. Until then, the release compiler (verified, but a
  different version of CakeML) and the S-expression export (unverified,
  but cross-checked) are in the trusted base.
- **The socket model is idealized.** It has no errors besides EOF, writes
  always succeed in full, and there is no `close`. `socket_ffi.c`
  documents how reality is mapped onto it, and each mapping is a trust
  assumption. A client that never reads can stall the server, because
  writes block.
- **HTTP is a tiny subset.** Requests must be exactly
  `GET <path> HTTP/1.0\r\n\r\n`, so curl needs its default headers
  removed. A header-tolerant variant of the spec is drafted for decision
  (`spec/HttpSpecHeaders`).
- **Performance** was not a goal (see above).

## How it was built

**[Your voice. The facts are below.]**

- You designed and reviewed the specifications (EchoSpec, HttpSpec) and
  the design notes' decisions, and you set the policy: specs first, no
  cheats, readable lemmas, additive changes.
- AI agents (Claude) wrote the proofs, the CakeML code and the design
  notes. They worked as parallel workers on stacked branches,
  coordinated by an orchestrating session, with each step recorded in
  `design/` and in PRs.
- Every theorem was checked by HOL4. The agents' own claims were never
  taken on trust.

## From 2024 to 2026

**[Your voice.]** In March 2024 you wrote an *unverified* Promise library
and busy-polling scheduler in CakeML, with hand-written C FFI for
timers and non-blocking `select`. It ran under Rosetta, on a fake
timer-driven file system. In 2026 the same idea was redone as a
*verified* development:

- the promise library became a pure model with proved laws;
- busy polling became a provably-equivalent blocking scheduler;
- the `select` FFI became a socket model in the trusted spec;
- the program now runs natively on arm64.

## Where to read next

- `design/` is the numbered design notes. `01-semantics.md` covers the
  model; `16-final-spec.md` covers the specs; `21`–`23` cover the
  runnable programs and the program-level theorems.
- `PRESENTATION-PLAN.md` proposes the final repository layout.
