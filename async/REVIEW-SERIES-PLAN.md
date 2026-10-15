# Review series plan: the async I/O work as 11 layered PRs

**Purpose.** About 30 stacked spike PRs record the order things were
*discovered*. This series presents the same results in the order they
would have been *designed*. The trusted statement comes first, then each
layer that proves it. Every PR is one coherent layer that builds on its
own (`Holmake -j2` green, no cheats). You read the definitions and the ≤ 5
statements each PR lists, and never the proofs.

**What it is made of.** Branches `review/01-…` to `review/11-…`, each
stacked on the previous one; `review/01` starts from `async-io`.
- Files are moved into one layout (below). Theory names and statement
  text are unchanged.
- Dead ends are left out (see "Dropped").
- Nothing is re-proved. Every theory is the latest spike version, moved
  as-is; only Holmakefile `INCLUDES` change.
- The spike branches and PRs stay untouched as the archive. You decide
  later whether to close them.

## The layout

```
async/
  spec/                 TRUSTED: EchoSpec, HttpSpec, their bite (PR 1)
  world/sockets/        TRUSTED: socket model + fairness (PR 1); CakeML Socket module (PR 6); select (PR 8)
  world/clock/, world/composed/   the modular FFI world and whole-program divergence (PR 6)
  model/core|level2|sched|examples   the async library's semantics, pure HOL (PRs 2–3)
  servers/echo|closed-loop|relabel|http   servers written with the library, model-level properties (PRs 4, 9)
  cakeml/library|approx  the library in CakeML with CF specs (PR 5)
  loop/polling|blocking|blocking-l2   the event loops (PRs 6, 8)
  programs/echo|echo-live|echo-blocking|http   whole programs and their trace theorems (PRs 7–9)
  headline/             the final theorems, in the specs' own terms (PRs 7, 9)
  runnable/             socket_ffi.c (TRUSTED), export, Makefiles, demos (PR 10)
  design/               notes, reading guide (PR 11)
```

## The series

Sizes are the lines of HOL moved; reading time covers the listed
statements only.

### 1. `review/01-spec`: the trusted surface (≈2,000 lines; 30–45 min)
- **Claims:** what the servers must do, on raw socket I/O, and that this
  bites.
- **Own:**
  1. the socket world: `sockets`, `deliver1`, `tick`, the four
     operations and their byte encodings (`ffiSpikeSocketFFI`);
  2. fairness: `sched_wf` (`ffiSpikeSocketFair`);
  3. `echo_spec` = `server_world` + `echo_safe` + `echo_live` (`EchoSpec`);
  4. `http_spec_h` (`HttpSpecHeaders`, the HTTP spec: header-tolerant;
     it reuses HttpSpec's paths, files and response printer);
  5. bite and non-vacuity: `broken_*`, `server_world_exists`,
     `ideal_trace_safe_and_live`, `plain_requests`, `curl_request`,
     `broken_*_h`, and `body_headers_invalid` /
     `broken_answers_body_request` (the subset has no request bodies:
     `valid_header` rejects Content-Length and Transfer-Encoding).
- **Skip:** the proofs of the bite lemmas, and the fairness lemmas
  (`ticks_*`, `*_shape`). Of `HttpSpec`, read only the vocabulary
  (`valid_path`, `handle`, `print_response`). Its strict request subset
  and `http_spec` are the earlier, archived statement.
- **From:** ffi-spike (socket FFI, Fair), spec/ (#18), HttpSpecHeaders
  (#28, spike/http-headers).

### 2. `review/02-model-core`: the async model (≈2,690 lines; 45 min)
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

### 3. `review/03-model-loops-level2-sched`: recursion, no busy-waiting (≈3,040 lines; 45 min)
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

### 4. `review/04-servers-model`: the echo server in the model (≈3,770 lines; 40 min)
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

### 5. `review/05-cakeml-library`: the library in CakeML (≈2,470 lines; 30 min)
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

### 6. `review/06-loop-and-plumbing`: sockets in CakeML, divergence, the event loop (≈4,940 lines; 40 min)
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

### 7. `review/07-echo-program`: **`echo_spec 3w echo_prog`** (≈3,250 lines; 40 min)
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

### 8. `review/08-blocking`: the blocking refinement (≈5,640 lines; 35 min)
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

### 9. `review/09-http`: HTTP, `http_spec_h 3w demo_files http_prog_h` (≈6,350 lines; 40 min)
- **Claims:**
  - a header-tolerant parser, proved against the spec's own printer;
  - a generic accept/fork skeleton, verified once;
  - the whole HTTP program meets HttpSpecHeaders in full: it runs
    forever, is safe, and answers every complete request.
- **Own:**
  1. `http_prog_h_spec : http_spec_h 3w demo_files http_prog_h` (headline,
     `headline/asyncHttpSpecH`); `http_prog_h_safe` is its safety half;
  2. the parser against the printer (`asyncHttpParseH`);
  3. `server_with_isolates` and `sserver_with_spec` (the skeleton, once);
  4. `hmachine_live` (the handler as a machine answers every complete
     request);
  5. `http_live_h_rounds` (`http_live_h` of the loop's trace).
- **Skip:**
  - `gen_*` (the generic no-misuse argument), the depth specs, and the
    translation plumbing;
  - the generic socket-level accept progress (`asyncSWSock`, the
    `server_with` analogue of the echo program's `conn_accepted`) and the
    drain lemmas;
  - the strict-subset files (`asyncHttpParse`, `asyncHttpServer`,
    `asyncHttpSafe`, `asyncHttpSock*`, `asyncHttpMain`,
    `asyncHttpSemantics`, `headline/asyncHeadline`). The header-tolerant
    proofs build on them, but they are not for review.
- **From:** http-model (#20), http-impl/asyncHttpImplProg (#22),
  http-safety (#26), http-headers, http-liveness (http-liveness-h and
  asyncSWProgress), m4-server/asyncM4ServerProg (code reused by the
  translation).

### 10. `review/10-runnable`: it runs (no HOL to review; 15 min)
- **Claims:** both servers compile with the release compiler and run, and
  the blocking one idles at 0% CPU.
- **Own:** `socket_ffi.c` (TRUSTED: the C side of the four calls plus
  `select`; one mapping table to check against `ffiSpikeSocketFFI`). It
  does exactly what the model says: `sock_poll` is one `poll(2)` with
  timeout 0 (the earlier idle-wait heuristic is gone, #50).
- **Skip:** the Makefiles, demo clients, the printer cross-check, the
  generated `.sexp` files, and the machine-code scripts (`compile/`, not
  built by default; blocked on memory, see note 22).
- **From:** runnable (#23), blocking-runnable (#29), m4-blocking-live (#46),
  no-idle-wait (#50), http-headers' and http-nobody's demo (#48),
  machine-code/compile (#24).

### 11. `review/11-docs`: README, design notes, START-HERE (15 min)
- `async/README.md` (from README-DRAFT, updated: the headline is now
  proved in full), `REVIEW-START-HERE.md`, and design notes 01–24, kept as
  the "why" behind each layer, with a per-layer index.
- HANDOFF notes, worker conventions and heap measurements stay on the
  spike branches.

**Total:** ≈30,000 lines of HOL; about 6.5 hours of reading at the listed
depth.

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

## In-flight work: where each lands

- **HTTP liveness**: folded in. PR 9's headline is
  `http_prog_h_spec : http_spec_h 3w demo_files http_prog_h`.
- **header-tolerant HttpSpec**: adopted (your decision). It is PR 1's HTTP
  spec. The strict HttpSpec's statement and results are archived; its
  file stays as shared vocabulary.
- **blocking fix**: folded in (`echo_live_spec`, PR 8).
- **no request bodies** (HttpSpecHeaders, user-approved): folded into PR 1
  (spec and bite) and PR 9 (the program and its proofs).
- **`brun_two_outcomes`** (#49): folded into PR 8.
- **no idle wait in the trusted C** (#50): folded into PR 10.
- **close / fd reuse (close-v2)**: a new PR 12 (`review/12-close-v2`) on
  top. It holds EchoSpec2 (spec first), the v2 world and the handle layer,
  and touches nothing below it.

Mechanics of folding in: a late result is committed on the layer's
branch, then merged forward up the stack (`review/N` into `N+1`, …). That
adds merge commits, never rewrites; each PR's diff stays its own layer.

## Decisions for you (defaults used unless you say otherwise)

1. **Theory names unchanged** (default). This keeps EchoSpec/HttpSpec
   byte-identical (they import `ffiSpikeSocketFFI`), and every note and
   spike reference stays valid. Renames (e.g. `ffiSpikeSocket*` →
   `socket*`, `asyncM3*`/`asyncM4*` → layer names) can be one mechanical
   commit at the end if you want them.
2. **Dropped files**: not carried into the series (default). The
   alternative is an `async/archive/` folder that is not built.
3. **Close the spike PRs** after review, or leave them open: yours to
   decide; nothing is touched.
