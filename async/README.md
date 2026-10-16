# Verified asynchronous I/O in CakeML: servers that are safe, live and quiet

**Start with `HEADLINES.md`.** It states every end-product theorem in full,
with the trusted definitions it mentions expanded next to it, before any
proof. This README is the map: the levels, what you have to trust, the
reading paths, and the honest limitations.

```
(* spec/EchoSpecScript.sml *)
echo_spec lfd prog ⇔
  ∀sk. server_world lfd sk ⇒
       ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog (Diverge io) ∧
            echo_safe io ∧ echo_live sk io

(* headline/echoHeadlineScript.sml *)
Theorem echo_prog_spec:
  echo_spec 3w echo_prog
```

In every fair world (one listening socket, and any future pattern of
connections and data), the echo program runs forever. On every
connection, what it has sent back is always a prefix of what that client
sent (safety). Everything a client sends is eventually sent back
(liveness).

## The series: headlines first, then zoom levels

The review series is organised by *concept*, and names carry no version
numbers. Each level opens with the theorem that links it to the level
above. A reader can stop after any level and still know exactly what was
proved.

| level | branches | what it adds | links to the level above |
|---|---|---|---|
| **H**, headlines | `final/00-headlines` | every end-product theorem, stated in full; this README; `design/NAMES.md` | — |
| **L0**, core | `final/01` … `final/11` | simple sockets, with no close, no peers, and the model's C. The specs, the async library, Level 2, the scheduler, isolation, liveness from the library, protocols as instances (HTTP, KV), quiescence, and it runs | — |
| **L1**, lifetimes | `final/L1-01` … `L1-03` | close and fd reuse; per-connection (episode) specs; the echo server with close | `lifetime_core_link_thm`: conservativity (adding close changes nothing for programs that never close) |
| **L2**, peers | `final/L2-00` … `L2-04` | connect, refusal and half-close; clients and proxies; rely/guarantee specs; buffer closure; the four servers' peer-world specs over the simple class | `v2_instance_thm`, `echo_episodes_peer_equiv_thm` (to L1); `v1_instance_disc_thm` and `*_peer_equiv_disc_thm` (to L0, for fd-disciplined programs) |
| **L3**, the real kernel | planned | an honest C FFI (one syscall per call), verified wrappers, and the refinement to the lifetimes world | design/36's R1–R4 (in progress) |

### L0 layers (core)

| # | branch | PR | layer |
|---|---|---|---|
| 01 | `final/01-trusted-surface` | #118 | the trusted surface: socket world, fairness, EchoSpec, HttpSpec, QuietSpec, KvSpec, bites; the RFC 9112 agreement |
| 02 | `final/02-model-core` | #119 | the async model: the monad laws, `both`, `choose` |
| 03 | `final/03-loops-level2-sched` | #120 | recursion, Level 2 (declared interest), the scheduler: no busy-waiting |
| 04 | `final/04-servers-model` | #121 | servers in the model, with isolation |
| 05 | `final/05-cakeml-library` | #122 | the library in CakeML (CF specs) |
| 06 | `final/06-sockets-loops` | #123 | sockets in CakeML, divergence, the event loops |
| 07 | `final/07-echo-program` | #124 | **`echo_prog_spec`**, and the blocking refinement |
| 08 | `final/08-library-liveness` | #125 | liveness proved once, from the library |
| 09 | `final/09-protocols` | #126 | protocols as instances: **`http_prog_spec`**, **`kv_prog_spec`** |
| 10 | `final/10-quiescence` | #127 | quiescence: select on the declared interest; **`echo_blocking_quiet`**, **`http_blocking_quiet`**; stateful quiescence (model level) |
| 11 | `final/11-it-runs` | #128 | it runs: `runnable/socket_ffi.c`, the exports, demos, CPU tables |

### L1 layers (lifetimes)

| # | branch | PR | layer |
|---|---|---|---|
| 01 | `final/L1-01-trusted-surface` | #142 | the lifetimes world (`lifetimeWorld`, `lifetimeFair`) and `EchoEpisodesSpec` |
| 02 | `final/L1-02-link` | #143 | **`lifetime_core_link_thm`**, the link to L0 (a leaf) |
| 03 | `final/L1-03-echo-episodes` | #144 | **`echo_episodes_prog_spec`**: the echo server with close and fd reuse |

### L2 layers (peers)

| # | branch | PR | layer |
|---|---|---|---|
| 00 | `final/L2-00-statements` | #151 | the headline claims, stated first, over the simple class (`simple_class`: no backpressure, open loop, `nonsat1`) |
| 01 | `final/L2-01-world` | #148 | the peer world (`peerWorld`, `peerFair`), rely/guarantee spec forms, the servers' peer-world specs, buffer closure (`relay_safety`) |
| 02 | `final/L2-02-lifetimes` | #149 | the link to L1: **`v2_instance_thm`**, **`echo_episodes_peer_equiv_thm`** |
| 03 | `final/L2-03-core` | #150 | the link to L0: **`v1_instance_disc_thm`**; `echo_`/`http_`/`kv_peer_equiv_disc_thm` |
| 04 | `final/L2-04-claims` | #152 | fd discipline of the three L0 programs; the four claims **proved** |

## The headline theorems

| theorem | level | theory |
|---|---|---|
| `echo_prog_spec : echo_spec 3w echo_prog` | L0 | `headline/echoHeadline` |
| `http_prog_spec : http_spec 3w demo_files http_prog` | L0 | `programs/http-pb/httpSemantics` |
| `kv_prog_spec : kv_spec 3w kv_prog` (linearizable and live) | L0 | `programs/kv/kvHeadline` |
| `echo_blocking_quiet : echo_quiet 3w echo_blocking_main` | L0 | `quiet/echo/echoQuiet` |
| `http_blocking_quiet : http_quiet 3w demo_files (SNOC (main_call «main») http_blocking_prog)` | L0 | `programs/http-quiet/httpQuietHeadline` |
| `lifetime_core_link_thm : lifetime_core_link` | L1 | `lifetimes/link/lifetimeCoreProof` |
| `echo_episodes_prog_spec : echo_episodes_spec 3w echo_episodes_prog` | L1 | `headline/echoEpisodesHeadline` |
| `peer_echo_prog_spec`, `peer_http_prog_spec`, `peer_kv_prog_spec`, `peer_echo_episodes_spec` (the four servers in the peer world, simple class) | L2 | `peers/statements/peerStatements` |

Each is stated in full in `HEADLINES.md`, with its bites. The chat server
is an appendix: it is not part of the series until its revised spec has
had an independent review.

## What you have to trust

| file | what it says |
|---|---|
| `spec/EchoSpec` | the sockets-only FFI oracle; per-connection projections of raw I/O events; `echo_safe`, `echo_live`, `echo_spec` |
| `spec/HttpSpec`, plus the vocabulary of `spec/HttpGetSpec` and `spec/HttpHeadersSpec` | GET and POST requests with headers and a Content-Length body; RFC character sets; `http_safe`, `http_live`, `http_spec` |
| `spec/KvSpec` | the key-value store's linearizable safety (`kv_safe`) and liveness (`kv_live`) |
| `spec/QuietSpec` | the blocking `select` (selecting on a non-socket fails); quiet worlds; sleeping; `echo_quiet`, `http_quiet` |
| `world/sockets/socketWorld`, `socketFair` | the socket world and the fairness of schedules (`sched_wf`) |
| L1 only: `lifetimes/world/lifetimeWorld`, `lifetimeFair`, `lifetimes/spec/EchoEpisodesSpec` | the world with close and fd reuse, and the per-episode spec |
| CakeML | the source semantics (`semantics_prog`) and its I/O events |
| `runnable/socket_ffi.c` | the C side of the socket calls, which must implement the socket model (see "Honest limitations") |

**Checked against the RFC.** `spec-rfc/` holds an independent reference
for RFC 9112 request framing and proves that HttpSpec agrees with it:
`rfc_frames_exactly_valid` and `rfc_subset_exact`. Our subset is stricter
than the RFC, on purpose:
- a space is required after each field colon;
- Content-Length must be canonical;
- Transfer-Encoding is not accepted;
- the only methods are GET and POST.

Nothing else is trusted. The async library, its CakeML implementation, the
event loops, the scheduler and the protocol pipeline are all proved.

## Reading paths

- **15 minutes:** `HEADLINES.md` only. Every end-product theorem, with its
  trusted definitions inlined, its bites and the trust list.
- **One hour:**
  1. `HEADLINES.md`;
  2. L0 01, the trusted surface;
  3. L0 03's Level 2 idea (declared interest, `quiet`, `no_busy_waiting`);
  4. L0 10's design note (`quiet/README.md`: the two spins, and select on
     the declared interest);
  5. the opening theorem of each later level (L1 02; L2 02 and 03).
- **The core in full (about 8 hours):** H, then L0 01 → 11. L0 is complete
  on its own.
- **Everything:** H → L0 → L1 → L2 (→ L3 as it lands). Each level starts
  with its linking theorem, then its trusted surface, then its proofs.

In each PR, read only the definitions and the ≤ 5 statements its
description lists, and skip the proofs.

## Why you should believe it

- **No cheats.** Every layer builds with `Holmake` on top of CakeML's
  basis, and no theory has a cheat.
- **The specs bite.** Each spec has a `*Bite` theory proving that the
  traces of plausible broken servers violate it, for example:
  - swapping clients' data;
  - answering a body as a request;
  - answering early;
  - spinning in `select`;
  - leaking data across fd reuse;
  - never closing.
- **The specs are not vacuous.** Fair worlds exist, and ideal traces meet
  every clause.
- **The specs came first.** They were written and reviewed before the
  final proofs.

## Honest limitations

- **Known gap in the trusted C (`socket_ffi.c`), being fixed.** The C
  behaves in five ways the model doesn't:
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
  fd reuse) carry over (design/36; L3).
- **What reaches the real kernel, and in what form** (`HEADLINES.md` §8):
  - the L1 (lifetimes) headlines are planned to transfer, with safety and
    *eventual* liveness;
  - the L0 headlines are not; their runnables are retired, because
    without close they run out of fds after about 250 clients on macOS;
  - "within N rounds" bounds become "eventually";
  - quiescence on the kernel is open.
- **L2's peer-world specs hold in the simple class only** (no
  backpressure, open loop, not filling the fd space). Our servers use full
  writes, which are a misuse under backpressure.
- **The HTTP subset is small.** It has GET and POST only, bodies framed by
  one canonical Content-Length, and no chunked encoding.
- **No `Expect: 100-continue`.** A client that sends it waits about a
  second before sending the body.
- **Quiescence is qualitative.** QuietSpec says nothing about how soon a
  server sleeps, nor about CPU while arrivals keep coming. Stateful
  (KV) quiescence is proved at model level; its CakeML instance is still
  to come.
- **Proofs establish values, not running time.** An exponential-time
  parser passed every proof until a long header exposed it. It was fixed
  with proved-equal linear definitions.
- **The machine-code theorem is pending.** The composition scripts are
  written (`runnable/machine-code/`). Until they run, the release compiler
  and the S-expression export are in the trusted base.

## Names

The spike branches use older names, such as `asyncM4*`, `asyncOC*`,
`EchoSpec2` and `ffiSpikeSocketFFI`. `design/NAMES.md` maps every theory
and renamed constant from its spike name to its final name. The design
notes `design/NN-*.md` are kept as written, so use that table to read them.

## How it was built

**[Your voice.]** You designed and reviewed the specifications and the
design decisions, and set the policy: specs first, no cheats, readable
lemmas, additive changes. AI agents (Claude) wrote the proofs, the CakeML
code and the design notes, as parallel workers on stacked branches,
coordinated by an orchestrating session. HOL4 checked every theorem.
