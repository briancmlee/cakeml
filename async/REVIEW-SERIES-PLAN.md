# Review series plan (v2): the async I/O work as 14 layered PRs

**Purpose.** About 30 stacked spike PRs record the order in which things
were *discovered*. This series presents the same results in the order
they would have been *designed*: the trusted statement first, then each
layer that proves it. Every PR is one coherent layer that builds on its
own (`Holmake -j1` green, no cheats). You read the definitions and the ≤ 5
statements each PR lists, never the proofs.

**v2.** This is the second cut of the series. The first, `review/01…12`
(#34–#44, #68), is tagged `archive/review-v1-01` … `-12`; its PRs are
annotated "Superseded by …" and left open. The v2 changes:
- layer 01 gains QuietSpec, the tchar and RFC-character-set spec changes,
  and the RFC 9112 agreement (`spec-rfc/`);
- layers 09–11 are new: liveness from a library, HTTP as a protocol
  instance, and quiescence with option C;
- the copied HTTP pipelines are retired.

The approved proposal is `REVIEW-SERIES-V2-PROPOSAL.md` (async-spike,
outside the repository).

**What it is made of.** Branches `review-v2/01-…` to `review-v2/14-…`,
each stacked on the previous one.
- Files are moved into one layout (below), and theory names are unchanged.
- Nothing is re-proved except where a layer had to be rewired off a
  retired theory; the PR says so where that happens.
- Holmakefile `INCLUDES` are computed from each theory's ancestors.
- The spike branches and PRs stay untouched as the archive.

**Presentation, next.** By the user's decision, the final series will be
organised by *concept*, with no version numbers. It will open with the
headline theorems stated in full, followed by zoom levels: core,
lifetimes, peers, real kernel. This v2 series is the snapshot that cut
starts from; the proposal for it is separate.

## The layout

```
async/
  spec/                 TRUSTED: EchoSpec, HttpSpecBodies (+ HttpSpec, HttpSpecHeaders vocabulary), QuietSpec, bites (01)
  spec-rfc/             the RFC 9112 reference and the agreement proofs (01)
  world/sockets/        TRUSTED: socket model + fairness (01); CakeML Socket module (06); select (08)
  world/clock/, world/composed/   the modular FFI world and whole-program divergence (06)
  model/core|level2|sched|examples   the async library's semantics, pure HOL (02–03)
  servers/echo|closed-loop|relabel   the echo server in the model (04)
  cakeml/library|approx|level2   the library in CakeML with CF specs (05, 08)
  loop/polling|blocking|blocking-l2   the event loops (06, 08)
  programs/echo|echo-live|echo-blocking   the echo programs and their trace theorems (07–08)
  servers/skeleton|library-liveness|http   liveness from the library (09)
  servers/proto|proto-inst, programs/proto|http-pb   the generic protocol pipeline and the HTTP instance (10)
  quiet/ffi|echo        quiescence: FFI agreement, the blocking echo (11)
  servers/level2-proto|proto-stable, programs/http-level2|http-quiet, loop/select-interest   option C (11)
  headline/             the final theorems, in the specs' own terms (07, 13)
  runnable/             socket_ffi.c (TRUSTED), exports, Makefiles, demos, CPU tables (12)
  spec-v2/, world/sockets-v2(-cf)/, loop/handles/, programs/echo-v2/
                        close and fd reuse: TRUSTED EchoSpec2 and the v2 world, then its proof (13)
  design/, README.md, REVIEW-*.md   notes and reading guides (14)
```

## The series

| # | branch | PR | headline / content | from |
|---|---|---|---|---|
| 01 | `review-v2/01-spec` | #84 | the trusted surface; SPEC CHANGE commits: tchar 718c53c8d, H-CHARS 821f833cc; QuietSpec 330e59aef; spec-rfc 9840a1788 | v1 01; #55, #57 |
| 02 | `review-v2/02-model-core` | #85 | the async model | v1 02 |
| 03 | `review-v2/03-model-loops-level2-sched` | #86 | recursion, Level 2, no busy-waiting | v1 03 |
| 04 | `review-v2/04-servers-model` | #87 | the echo server in the model | v1 04 |
| 05 | `review-v2/05-cakeml-library` | #88 | the library in CakeML | v1 05 |
| 06 | `review-v2/06-loop-and-plumbing` | #89 | sockets in CakeML, divergence, the event loop | v1 06 |
| 07 | `review-v2/07-echo-program` | #90 | `echo_spec 3w echo_prog` | v1 07 |
| 08 | `review-v2/08-blocking` | #91 | the blocking refinement; the Level 2 CF library (`cakeml/level2`) | v1 08; #81 |
| 09 | `review-v2/09-library-liveness` | #92 | `server_with_live`, `server_v_live`, `server_v_live_ans` | #62, #70, #71, spike/proto-kv |
| 10 | `review-v2/10-http-proto` | #100 | `http_spec_b 3w demo_files http_prog_pb` | #58, #74, #64, spike/proto-kv |
| 11 | `review-v2/11-quiet-option-c` | #109 | `echo_quiet 3w echo_l_main`; `http_quiet_b 3w demo_files (SNOC (main_call «main») http_q_prog)` | #77, #81, #82, #93, spike/option-c-int |
| 12 | `review-v2/12-runnable` | #112 | it runs; the option C server at 0% idle CPU | v1 10; spike/option-c-int |
| 13 | `review-v2/13-close-v2` | #113 | `echo_spec2 3w echo2_prog` | v1 12 (#63) |
| 14 | `review-v2/14-docs` | — | README, design notes, START-HERE, this plan | v1 11 |

### 01. `review-v2/01-spec`: the trusted surface (45–60 min)
- **Claims:** what the servers must do, on raw socket I/O, CPU included,
  and that this bites.
- **Own:**
  1. the socket world: `sockets`, `deliver1`, `tick`, the four
     operations and their byte encodings (`ffiSpikeSocketFFI`), and fairness
     `sched_wf` (`ffiSpikeSocketFair`);
  2. `echo_spec` = `server_world` + `echo_safe` + `echo_live` (`EchoSpec`);
  3. `http_spec_b` (`HttpSpecBodies`):
     - GET and POST, with Content-Length bodies;
     - header names are RFC tokens (`tchar`), paths are RFC 3986
       characters, and field values are RFC 9110 field characters;
     - `POST /echo` answers the body;
  4. `echo_quiet`, `http_quiet_b` (`QuietSpec`): the blocking `select`,
     quiet worlds, and sleeping;
  5. the bites and non-vacuity (`*Bite`), and the RFC agreement
     (`rfc_frames_exactly_valid`, `rfc_subset_exact`).
- **Skip:** the proofs of the bite lemmas, the fairness lemmas, and
  `spec-rfc`'s proofs.

### 02. `review-v2/02-model-core`: the async model (≈2,690 lines; 45 min)
- **Claims:** computations on histories form a lawful monad, and `both`
  and `choose` lose nothing.
- **Own** (REVIEW-GUIDE H1–H7):
  1. the monad laws (`bind_left_identity`, `bind_right_identity`,
     `bind_assoc`);
  2. `bind_continues` and `bind_settled_continues`;
  3. `both_result`;
  4. `choose_rejoin`;
  5. `choose_losers`.
- **Skip:** the `wf_*`/`settled_*` closure lemmas (one line each in the
  guide) and `resume_*`.
- **From:** model/asyncCore, asyncLevel1, asyncChoose (#1, #3).

### 03. `review-v2/03-model-loops-level2-sched`: recursion, no busy-waiting (≈3,040 lines; 45 min)
- **Claims:** recursive computations are well-defined, Level 2 refines
  Level 1, everything is quiet, and the scheduler never busy-waits.
- **Own:**
  1. `fix_unfold` with the recursion rule (H8–H10);
  2. Level 2 erasure (`erase_bind2`, `erase_both2`, `erase_choose2`; H11);
  3. quietness (`quiet_bind2`, `quiet_both2`, `quiet_fix2`; H12);
  4. `no_busy_waiting` and `blocked_sound` (scheduler);
  5. the echo/idle examples end to end (H14).
- **Skip:** the `wf2_*`, `guarded*`, `status_*`, `trans_*` helpers and the
  examples' unfolding lemmas.
- **From:** model/ (#3, #6, #8).

### 04. `review-v2/04-servers-model`: the echo server in the model (≈3,770 lines; 40 min)
- **Claims:** the concurrent echo server gives every client back exactly
  its own bytes, never busy-waits, and in a closed loop with fair clients
  echoes everything in bounded time.
- **Own:**
  1. `server_unfold` (the server's definition);
  2. `echo_server_safety`;
  3. `server_no_busy_waiting`;
  4. `closed_loop_liveness`;
  5. relabelling preserves meaning (`relabel_bind`, `relabel_both`).
- **Skip:** `handler_progress`, `server_accept_progress`, the closed-loop
  accounting (they are reused by PR 7, which states their payoff), and
  `server_uses_accepted`.
- **From:** model/ (#9, #19), m4-server/asyncM4ServerUses and
  asyncM4Relabel (#17), m4-common/asyncM4RelabelDist (#25).

### 05. `review-v2/05-cakeml-library`: the library in CakeML (≈2,470 lines; 30 min)
- **Claims:** the CakeML library implements the model, with no
  step-indexing: each poll returns a residual, and `STEPA`/`COMP` relate
  a value to a model computation.
- **Own:**
  1. the representation and `COMP`/`STEPA` (`asyncCfActModel`);
  2. `bind_spec`;
  3. `both_spec`;
  4. `choose_spec`;
  5. depth-indexed specs for recursion: `app_COMP_of_approxd`, `bind_spec_d`.
- **Skip:** `asyncCfDet` (determinism lemma), the one-poll model lemmas,
  and the generic worlds `asyncCfActWorld`/`asyncCfReactWorld` (used later).
- **From:** cf-actions (#10), cf-reactive (#14), cf-spike/asyncCfDet
  (#2/#5), m4-server/asyncM4Approx (#17).

### 06. `review-v2/06-loop-and-plumbing`: sockets in CakeML, divergence, the event loop (≈4,940 lines; 40 min)
- **Claims:** a CakeML program that loops forever on sockets has a
  `Diverge` semantics whose trace is the event loop's rounds. The loop's
  trace is the computation's action log on the history the socket world
  generates, with a dynamic interest list.
- **Own:**
  1. the Socket module's specs (`Socket_*_spec`);
  2. `call_main_thm_div` (whole-program divergence, sockets-only world)
     and the multi-part rule `IMP_app_POSTd_FFI_part_filter`;
  3. `run_spec` (fixed interest);
  4. `run_i_spec` (dynamic interest);
  5. `rounds_LPREFIX` / `bytes_written_to_rounds` (traces as rounds).
- **Skip:** the clock world (it is the template the socket world follows),
  `serve_*`, the replayed `Async_*_spec`, `sinv`/`sock_do_ok` (no-misuse
  plumbing).
- **From:** ffi-spike (#4, #11, #13), m3-assembly (#16), m4-common
  (#25, #30).

### 07. `review-v2/07-echo-program`: **`echo_spec 3w echo_prog`** (≈3,250 lines; 40 min)
- **Claims:** the headline. The concrete CakeML echo program meets
  EchoSpec, unamended.
- **Own:**
  1. `echo_prog_spec : echo_spec 3w echo_prog` (headline/asyncM4EchoSpec);
  2. `sserver_spec` (the CakeML server implements the model server);
  3. `echo_semantics_prog` (divergence; the trace is the run; `echo_safe`);
  4. `echo_live_rounds` (`echo_live` of the run);
  5. `conn_accepted` and `accepted_live` (the two halves of liveness).
- **Skip:** the round-by-round world lemmas (`grounds_*`, `quiet_rounds_s`,
  `round_queued`, …) and the relabelling/TREL bridges.
- **From:** m4-common, m4-safety (#25), runnable/asyncEchoMain (#23),
  machine-code/asyncEchoSemantics (#24), m4-liveness (#30),
  m4-echospec, m4-echospec-live.

### 08. `review-v2/08-blocking`: the blocking refinement (≈5,640 lines; 35 min)
- **Claims:**
  - an event loop that sleeps in `select` is equivalent to polling
    (Level 2);
  - the blocking echo program selects only on the fds the server waits
    on (the listener and live connections), so it idles at 0% CPU, also
    after clients disconnect;
  - it is safe, and live whenever the polling one is; it can block
    forever only when the polling program would never act again.
- **Own:**
  1. `sock_select_polls` (the model of select; trusted with socket_ffi.c);
  2. `brun_two_outcomes` (the generic blocking loop: it runs as the
     polling loop would, or it ends asleep in `select` only once polling
     would never act again; `brun_spec` is its first outcome);
  3. `sel_covers` and the select-set loop's two outcomes
     (`asyncM4BlkSelWorld`, `asyncM4LiveLoop`);
  4. `echo_live_spec` (the companion theorem, directly under the headline).
- **Skip:**
  - the `brounds`/`bgrounds` invariants and the replayed Level 2 specs;
  - `echo_blocking_spec` (the first version, which selects on the whole
    interest list and spins after a disconnect; it is kept because the
    live-fd version builds on it).
- **From:** l2-blocking (#21) and asyncL2BlkStuck (#49), m4-blocking (#27), m4-blocking-live (#46;
  its `asyncM4LiveWorld` is renamed `asyncM4BlkSelWorld` here, because
  the liveness proof already has a theory of that name),
  ffiSpikeSocketSelect.


### 09. `review-v2/09-library-liveness`: liveness from a library (40 min)
See #92: a server proves one per-handler obligation (`handler_live`), and
`server_with_live` / `server_v_live` give every connection its owed
output. Echo's liveness is re-derived through it (`echo_live_via_lib`).

### 10. `review-v2/10-http-proto`: HTTP as a protocol instance (45 min)
See #100:
- `proto_ok P` (four conditions on a framing protocol) and `proto_spec`;
- `http_spec_b_proto`: HttpSpecBodies is `proto_spec` for `P_b`;
- `proto_live_rounds`, and `proto_spec_of_semantics`;
- the headline `http_prog_pb_spec`.

The copied HTTP pipelines (strict, headers, bodies) are retired to
`archive/http-copies`.

### 11. `review-v2/11-quiet-option-c`: quiescence, and option C (45 min)
See #109 and `quiet/README.md`:
- `run_q_two_outcomes` (select on the declared interest);
- `proto_stable`;
- `echo_l_quiet`;
- the headline `http_q_quiet`.

### 12. `review-v2/12-runnable`: it runs (15 min)
See #112. Read `runnable/socket_ffi.c` (TRUSTED). It has a known gap,
which is being fixed (design/36, #94). The CPU tables are in
`runnable/*/cpu-results.txt`.

### 13. `review-v2/13-close-v2`: close and fd reuse (45 min)
See #113: EchoSpec2 and the v2 world (TRUSTED for this layer),
`echo2_prog_spec`, the bites, and `hrun_sim`.

### 14. `review-v2/14-docs`: README, design notes, START-HERE (15 min)


## Retired to `archive/` tags (not deleted)

| tag | what | replaced by |
|---|---|---|
| `archive/review-v1-01` … `-12` | the first series | this series |
| `archive/http-copies` (b0e77dbc7) | the copied HTTP pipelines: strict GET (`http_spec`), header-tolerant (`http_prog_h_spec`), bodies (`http_prog_b_spec`) | layer 10's instances |
| `archive/http-quiet-53` | #53: the header-tolerant server at Level 2 | layer 11 (`server_with2` is lifted into `asyncServerWith2`) |
| `archive/http-blocking-56` | #56: live-list HTTP select. It spins after an invalid request (85.4% CPU) | layer 11's option C (0.0%) |

The first series' list of dropped scaffolding still applies:

## Dropped (superseded scaffolding; still on the spike branches)

| dropped | why | replaced by |
|---|---|---|
| cf-spike: asyncCfModel/Prog/Snap/Loop, smoke | results-only `STEP`, the feasibility test | PR 5's `STEPA`/`COMP` (asyncCfDet is kept) |
| cf-actions/asyncCfActLoop, cf-reactive/asyncCfReactLoop | event loops over toy worlds | PR 6's socket loops |
| ffiSpikeClockExample, ffiSpikeSocketExample, ffiSpikeSocketLogDiv | demos of the FFI recipe and the multi-part rule | the real programs (the rule itself is kept) |
| m3-assembly/asyncM3Example(Model) | `accept3` demo | the echo program |
| m4-server/asyncM4ServerSpec, http-impl/asyncHttpImplSpec | specs in the model's vocabulary | the socket-vocabulary specs (`sserver_spec`, `sserver_with_spec`) |
| strict HttpSpec as a headline (`http_spec`, `http_prog_safe`) | superseded by the header-tolerant spec (your decision) | `http_spec_h`, `http_prog_h_safe` (files kept as build support in PR 9) |
| world-async/* (experimental #12, #15) | the world as an async program: a side experiment | — (archive) |
| design/HANDOFF-*, conventions, heap-measurements, PRESENTATION-PLAN | process notes | this plan |

Kept but not headline: the clock world (the socket world is built on its
lemmas), `asyncM4ServerProg` (the HTTP translation reuses its code).


## After the series

- **Next-steps PR** (statements for review, not in the series):
  - the endpoint world (#67, #104);
  - fd discipline (#78);
  - buffer closure (#79);
  - KV (#52, #73, #80, #95).
- **Appendix** (linked, not reviewed): the chat server (#66, #72, #75, #76,
  #83; bounded latency #97, #106).

**Mechanics of folding in.** A late result is committed on its layer's
branch, then merged forward up the stack (`review-v2/N` into `N+1`, …).
That adds merge commits and never rewrites history, so each PR's diff stays
its own layer.
