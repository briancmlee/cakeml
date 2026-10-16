> **DRAFT for your voice.** Every claim names its theorem. The sections
> marked **[Your voice]** are yours to write. The facts elsewhere should
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

In plain English, **in every fair world** (one listening socket, and any
future pattern of connections and data) **the echo program runs
forever**. Two things hold throughout:
- **safety:** at every moment, **on every connection, what it has sent
  back is a prefix of what that client sent**;
- **liveness:** **everything a client sends is eventually sent back**.

`echo_prog` is the actual CakeML program: the basis library, a socket
module, an async library, an event loop and a concurrent server. It
compiles and runs (see "It runs" below).

## The headline theorems

| theorem | what it says | where |
|---|---|---|
| `echo_prog_spec : echo_spec 3w echo_prog` | the echo server: safe and live, in every fair world | `headline/asyncM4EchoSpec` |
| `http_prog_pb_spec : http_spec_b 3w demo_files http_prog_pb` | an HTTP server (GET and POST, any headers, Content-Length bodies; `POST /echo` answers the body): safe and live **in full** | `programs/http-pb/asyncProtoSemB` |
| `echo_l_quiet : echo_quiet 3w echo_l_main` | the blocking echo server goes to **sleep** when the world goes quiet (QuietSpec), while staying safe and live | `quiet/echo/asyncEchoQuiet` |
| `http_q_quiet : http_quiet_b 3w demo_files (SNOC (main_call «main») http_q_prog)` | the same for the HTTP server, on the loop that selects on the declared interest (option C) | `programs/http-quiet/asyncOCQuietFinal` |
| `echo2_prog_spec : echo_spec2 3w echo2_prog` | an echo server that **closes** connections and **reuses** fds: safe and live per connection, even across fd reuse, and it closes every connection whose EOF it read | `headline/asyncHLEchoSpec2` |

How the HTTP server is built: it is an *instance* of one generic protocol
server (`servers/proto`). Safety, liveness and the CakeML program are
proved once, for any framing protocol that meets four conditions
(`proto_ok`). The HTTP-bodies parser meets them (`proto_ok_b`), and the
trusted HTTP spec is the generic one for that protocol
(`http_spec_b_proto`). Liveness itself comes from a library theorem
(`server_with_live`, `servers/library-liveness`): each handler proves one
per-connection obligation.

**Quiescence.** EchoSpec and HttpSpecBodies say nothing about CPU: a
server that busy-polls meets them. QuietSpec (`spec/QuietSpec`) adds a
blocking `select` to the world and asks for more. In every fair world in
which only finitely many things arrive, the program's run must be
**finite**: it ends blocked forever in `select`, having answered
everything. A busy-polling server fails this (`broken_runs_forever`), and
so does one that spins in `select` on an fd it never reads.

## What you have to trust

| file | what it says |
|---|---|
| `spec/EchoSpecScript.sml` | the sockets-only FFI oracle, per-connection projections of raw I/O events, `echo_safe`, `echo_live`, `echo_spec` |
| `spec/HttpSpecBodiesScript.sml` (plus the vocabulary of `spec/HttpSpecScript.sml` and `spec/HttpSpecHeadersScript.sml`: paths, files, the response and header printers) | GET and POST requests with headers and a Content-Length body; RFC character sets for header names (tokens), paths and field values; `http_safe_b`, `http_live_b`, `http_spec_b` |
| `spec/QuietSpecScript.sml` | the blocking `select` call (`ffi_select`; selecting on a non-socket fails), quiet worlds (`arrivals_finite`), sleeping (`asleep`), `echo_quiet`, `http_quiet_b` |
| `world/sockets/ffiSpikeSocketFFIScript.sml` | the socket world: listeners, connections, a schedule of future arrivals, and the byte-level FFI functions |
| `world/sockets/ffiSpikeSocketFairScript.sml` | fairness of schedules (`sched_wf`, used by `server_world`) |
| `spec-v2/EchoSpec2Script.sml`, `world/sockets-v2/` | for `echo2_prog_spec` only: the version-2 world with `close` and fd reuse (`sched_wf2`, `alloc_ok`) and the per-episode spec |
| CakeML | the source semantics (`semantics_prog`) and its I/O events |
| `runnable/socket_ffi.c` | the C side of the socket calls, which must implement the socket model (a mapping table is in the file); see "Honest limitations" |

**Checked against the RFC.** `spec-rfc/` holds an independent reference
for RFC 9112 request framing (`rfc9112Framing`), which cites the RFC
clause by clause, and proves that HttpSpecBodies agrees with it:
- the RFC frames every printed valid request, followed by anything, as
  exactly that request (`rfc_frames_exactly_valid`; for lists and on the
  wire, `rfc_frames_list_exactly_valid` and
  `rfc_octets_frames_exactly_valid`);
- our subset is exactly the RFC messages with method GET or POST, version
  1.0 or 1.1, a space right after every field colon, and a canonical
  Content-Length value (`rfc_subset_exact`).

The reference is a reading aid. You need not trust it, but if you do, the
agreement is checked.

**Stricter than the RFC, on purpose:**
- a space is required after each field colon;
- Content-Length must be canonical (no leading zeros, no OWS);
- Transfer-Encoding makes a request invalid;
- only GET and POST are accepted.

The examples are `host_no_space_rfc` and `host_no_space_not_ours`.

Nothing else is trusted. The async library's model, its CakeML
implementation, the event loops, the scheduler and the protocol pipeline
are all proved, and none of them appears in the statements.

## Why you should believe it

- **No cheats.** There are 209 theory files and about 55,600 lines of
  HOL4, and none contains a `cheat`. Each directory builds with `Holmake`
  on top of CakeML's basis.
- **The specs bite.** `spec/EchoSpecBiteScript.sml` proves that the
  traces of plausible broken servers violate the spec:
  - swapping clients' data (`broken_swaps_clients`);
  - dropping or duplicating a byte (`broken_drops_a_byte`,
    `broken_duplicates_a_byte`);
  - writing before reading (`broken_writes_before_reading`);
  - never echoing (`broken_never_echoes`).

  `spec/HttpSpecBodiesBiteScript.sml` does the same for HTTP:
  - answering a body that looks like a request as if it were one
    (`broken_body_as_request`);
  - answering before the last body byte (`broken_answers_before_body`);
  - reading `"Content-Length\t:"` as a header (`broken_tab_header`);
  - accepting a tab in a path or a NUL in a field value
    (`rfc_chars_bites`);
  - never answering (`broken_never_answers_b`).

  It also shows that the framing is unique (`print_brequest_unique`), and
  that `curl -d` sends a valid request (`curl_post_request`).

  `spec/QuietSpecBiteScript.sml`:
  - any program that runs forever in a quiet fair world fails
    (`broken_runs_forever`, `_b`);
  - the worlds in which earlier blocking servers spun are quiet fair
    worlds (`spin_worlds_quiet`);
  - sleeping too early fails liveness (`broken_sleeps_early`);
  - selecting on stdin fails (`select_stdin_fails`).

  `spec-v2/EchoSpec2BiteScript.sml`:
  - data leaking to a later connection on a reused fd
    (`broken_leaks_across_reuse`), which EchoSpec alone misses
    (`v1_misses_leak`);
  - never closing (`broken_never_closes`).
- **The specs are not vacuous.** Fair worlds exist (`server_world_exists`,
  `hello_world_quiet`, `server_world2_exists`). In them, ideal traces meet
  every clause together: `ideal_trace_safe_and_live`,
  `ideal_b_trace_safe_and_live`, `ideal_quiet_b`, `ideal2_trace_spec`.
- **The specs came first.** EchoSpec, QuietSpec and EchoSpec2 were
  written and reviewed before the final proofs, and the proofs had to
  meet them as stated.

## It runs

```
$ make demo          # runnable/echo: 3 concurrent clients and a late 4th
[  0.000s] alice    sent     'hello from alice'
[  0.001s] alice    received 'hello from alice'
...
[  0.466s] check    alice: received exactly its own lines: True

$ curl -s -i -d hello http://127.0.0.1:7850/echo    # runnable/http-bodies: plain curl
HTTP/1.0 200 OK
Content-Length: 5

hello
```

- **Build route.** The verified programs are exported from HOL as
  S-expressions (`…sexp`). The official CakeML release compiler (v3479)
  compiles them natively for arm64, and they are linked with the
  release's `basis_ffi.c` and `runnable/socket_ffi.c`.
- **Speed.** The echo server reaches 60–70% of the throughput of a
  trivial Python asyncio server (`runnable/echo/bench-results.txt`). This
  is not a careful benchmark.

**CPU.** The trusted C does exactly what the model says: `sock_poll` is
one `poll(2)` with timeout 0. So the polling programs busy-poll while
idle, and the verified blocking programs sleep:

| server | idle, before any client | light load | idle, after a client left | after an invalid request |
|---|---|---|---|---|
| `echo_live` (blocking echo, `echo_l_quiet`) | 0.0% | 0.1% | 0.0% | — |
| `echo_polling` (`echo_prog`) | 26.0% | 15.9% | 67.3% | — |
| `http_quiet` (option C, `http_q_quiet`) | 0.0% | 0.1% | 0.0% | 0.0% |
| `http_server_pb` (polling, `http_prog_pb`) | 21.9% | 26.0% | 76.8% | 89.2% |

CPU% is process CPU time over wall time, in 30 s phases, from a
background session that throttles busy polling (a C busy-polling loop
measures 13–16% there). The sources are:
- `runnable/echo-blocking/cpu-results.txt` and
  `cpu-results-no-idle-wait.txt`;
- `runnable/http-quiet/cpu-results.txt`.

## The key design ideas

**Pull-based polling is also the verification-friendly design.**
- A computation is a function from the *history of world snapshots* it
  has been polled with to its action log and optional result
  (`model/core/asyncCore`).
- There are no callbacks, no mutable promise cells, and no scheduler
  state for the proofs to track.
- So the library's laws are **equalities of computations**:
  - the monad laws;
  - `choose` loses nothing: `bind (choose m1 m2) rejoin = both m1 m2`.

**Level 1 → Level 2 gives provable no-busy-waiting.**
- Level 2 records the events a computation waits for. A computation is
  *quiet* if rounds in which none of them is ready can be deleted without
  changing anything. Every combinator, and the echo server, is quiet.
- So a scheduler may block, and it behaves exactly like one that polls
  (`model/sched/asyncSched2`).
- The same holds for CakeML's event loops: the `select` loop is
  equivalent to polling (`loop/blocking-l2`, `brun_two_outcomes`).

**Select on what the computation declares (option C).** The earlier
blocking loops guessed their select set from the trace: the whole
interest list, or the connections not yet at EOF. A handler that stops
early, for example on an invalid request, then leaves an fd in the set
that nobody reads, and the loop spins. The option C loop
(`loop/select-interest`) instead asks the Level 2 computation what it
waits for (`qsel c`, its declared interest). The select set is then right
by construction, and a finished handler drops out of it by itself
(`quiet/README.md`).

## Honest limitations

- **Known gap in the trusted C (`socket_ffi.c`), being fixed.** Five
  behaviours of the C are not in the model:
  - writes block until all bytes are sent, so a client that stops
    reading can stall the whole server;
  - a write to a departed peer silently drops data;
  - connection resets are reported as end-of-file;
  - accept failures such as running out of file descriptors are reported
    as "would block";
  - socket errors are reported as "readable".

  The model has none of these behaviours, so the theorems don't see them.
  A redesign is in progress: a minimal, honest FFI (about one syscall per
  call), verified CakeML wrappers that absorb the raw semantics, and
  refinement proofs so the theorems about the lifetimes world (close and
  fd reuse) carry over (design/36, in PR
  #94; the L0 C and world in #96 and #98; the verified L1 wrapper core in
  #107 and #110; the refinement is in progress).
- **Only the version-2 echo closes connections.** The echo server of
  layer 13 (`echo2_prog_spec`) closes finished connections and reuses
  their fds. The other programs use the version-1 socket model, which has
  no `close`: they never close a connection. On macOS the version-1
  runnables run out of fds after about 250 clients (honest-FFI audit,
  design/36). They will be retired in favour of the version-2 world, and
  HTTP is being moved onto it (#105).
- **The HTTP subset is small.** It has GET and POST only, and bodies
  framed by one Content-Length header with a canonical decimal value.
  Chunked Transfer-Encoding is not supported: such requests are invalid
  and get no answer.
- **No `Expect: 100-continue`.** Safety forbids interim 1xx responses. A
  client that sends this header (curl does, for large bodies) waits about
  a second and then sends the body anyway.
- **Quiescence is qualitative.** QuietSpec says nothing about CPU while
  arrivals keep coming, nor about *how soon* the server sleeps after the
  last arrival. Only `echo_live` and `http_quiet` are proved quiet; the
  polling programs are not, and are not meant to be.
- **Proofs establish values, not running time.** An exponential-time
  parser passed every proof until a long header exposed it. The
  translated code of a recursive split made its recursive call twice per
  character, so a 165-character User-Agent got no answer in 10 s. It was
  fixed with proved-equal linear definitions (`split_at2`,
  `split_path2`), and the request now takes 1.5 ms. The parsers'
  definitions and theorems are unchanged.
- **The machine-code theorem is pending.** The program-level theorem is in
  the form CakeML's compiler correctness theorem consumes, and the
  composition scripts are written (`runnable/machine-code/`). Running them
  needs CakeML's compiler proofs built in-logic. Until then, the release
  compiler and the S-expression export (cross-checked against the
  official printer) are in the trusted base.
- **The socket model is idealized.** It has no errors besides EOF, and
  writes always succeed in full. `socket_ffi.c` documents how reality is
  mapped onto it, and the first item above lists where the C falls short.

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

- `REVIEW-START-HERE.md`: the reading paths through the 14 review PRs
  (one hour, or in full).
- `REVIEW-SERIES-PLAN.md`: the layer map, and what feeds each layer.
- `design/README.md`: the design notes, indexed by layer.
