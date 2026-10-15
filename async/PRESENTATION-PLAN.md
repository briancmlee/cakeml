# Presentation plan: from ~25 stacked spikes to one development

**DRAFT, a proposal for you to shape. Nothing has been moved.** Every
file stays where it is until you approve a layout. This note proposes:

1. a final layout;
2. a mapping from today's files to it;
3. what is headline, what is support, and what is scaffolding;
4. a merge strategy that keeps all history.

## 1. Proposed final layout

```
async/
  README.md            the front page (draft: README-DRAFT.md)
  spec/                TRUSTED: what the servers do (EchoSpec, HttpSpec), their bite and
                       non-vacuity lemmas
  headline/            the final theorems, stated in spec/'s own terms
  model/               the async library's semantics (pure HOL, no CakeML)
    core/              snapshots, Level 1 combinators, choose, recursion rule, transcripts
    level2/            declared interest, erasure, quietness (no busy-waiting)
    sched/             the scheduler (M2) and its no-busy-waiting theorem
    examples/          echo / idle loops at both levels
  servers/             servers written with the library, and their model-level properties
    generic/           server_with (accept/fork skeleton), isolation, no misuse
    echo/              the concurrent echo server: safety, Level 2, closed loop, liveness
    http/              parser (against HttpSpec's printer), HTTP handler, safety
  cakeml/              the library and servers in CakeML, with CF specs
    library/           Async in CakeML: return/bind/emit/wait/both/map/choose; STEPA/COMP
    approx/            depth-indexed specs (STEPAd) for recursive servers
    servers/           socket-vocabulary echo and HTTP servers, sserver_with_spec
  world/               the outside world
    sockets/           socket model and FFI, fairness, cfDiv rules for multi-part FFIs
  loop/                the event loops in CakeML and their traces
    polling/           M3 fixed-interest loop, M4 dynamic-interest loop (run_i)
    blocking/          select-based loops proved equivalent to polling
  programs/            whole programs: main, semantics (Diverge + spec), the trace bridges
    echo/              echo_semantics_prog, EchoRunOk/EchoSafe (generic: RunOkGen)
    http/              http_semantics_prog, http_comp_safe
  runnable/            export to S-expression, socket_ffi.c (TRUSTED), Makefiles, demos
  machine-code/        in-logic compilation + compile_correct (pending the compiler build)
  design/              numbered design notes (kept); review guide
    archive/           HANDOFF-* notes, worker conventions, heap measurements
  archive/             scaffolding, kept buildable or frozen (see §3)
```

The order of the sections is also a reading order. It runs from what you
must trust (spec) to what is proved (headline), then down through the
layers that prove it.

## 2. Mapping from today's files

The status column uses: **H** = headline (shown on the front page), **S** =
support (needed by a headline), **X** = scaffolding (superseded; archive).

| today | files | proposed | status |
|---|---|---|---|
| `spec/` | EchoSpec, HttpSpec | `spec/` | H (trusted) |
| `spec/` | EchoSpecBite, HttpSpecBite | `spec/` | H (bite / non-vacuity) |
| `spec/` | HttpSpecHeaders, HttpSpecHeadersBite | `spec/` if you adopt it, else `archive/` | draft (your decision) |
| `headline/` | asyncHeadline | `headline/` | H |
| `model/` | asyncCore, asyncLevel1, asyncChoose, asyncLoop, asyncTranscript | `model/core/` | H (monad laws, choose, recursion rule) / S |
| `model/` | asyncLevel2, asyncLoop2 | `model/level2/` | H (erasure, quietness) |
| `model/` | asyncSched, asyncSched2 | `model/sched/` | H (no busy-waiting) |
| `model/` | asyncEcho, asyncIdle, asyncEcho2, asyncIdle2 | `model/examples/` | S |
| `model/` | asyncServer, asyncServerSafety, asyncServer2 | `servers/echo/` | S |
| `model/` | asyncWorld, asyncClosedLoop, asyncProgress, asyncLiveness | `servers/echo/closed-loop/` | S (model-level liveness) |
| `http-model/` | asyncServerWith | `servers/generic/` | S |
| `http-model/` | asyncHttpParse, asyncHttpServer | `servers/http/` | S |
| `http-safety/` | asyncServerWithUses | `servers/generic/` | S |
| `m4-server/` | asyncM4ServerUses, asyncM4Relabel | `servers/echo/`, `cakeml/approx/` | S |
| `cf-actions/` | asyncCfActModel, asyncCfActProg, asyncCfActSpec, asyncCfActBoth(Model) | `cakeml/library/` | S |
| `cf-actions/` | asyncCfActLoop, asyncCfActWorld | `loop/polling/` | S |
| `cf-reactive/` | asyncCfChoose(Model) | `cakeml/library/` | S |
| `cf-reactive/` | asyncCfReactLoop, asyncCfReactWorld | `loop/polling/` | S |
| `m4-server/` | asyncM4Approx | `cakeml/approx/` | S |
| `m4-server/` | asyncM4ServerProg, asyncM4ServerSpec | `archive/` | X (model vocabulary; superseded by the socket vocabulary) |
| `http-impl/` | asyncHttpImplProg, asyncHttpImplSpec | `archive/` | X (model vocabulary; superseded by http-safety's Sock*) |
| `ffi-spike/` | ffiSpikeSocketFFI, ffiSpikeSocketFair, ffiSpikeSocketProg, ffiSpikeSocketProof, ffiSpikeSocketDiv, ffiSpikeSocketWorld, ffiSpikeDivMain, ffiSpikeDivMulti | `world/sockets/` (drop the `ffiSpike` prefix) | S (FFI model is trusted via EchoSpec) |
| `ffi-spike/` | ffiSpikeClock*, ffiSpikeSocketExample, ffiSpikeSocketLogDiv | `archive/` | X (first FFI experiments) |
| `m3-assembly/` | asyncM3Prog, asyncM3Loop, asyncM3World | `loop/polling/` | S |
| `m3-assembly/` | asyncM3Example(Model) | `archive/` | X (accept3 demo) |
| `m4-common/` | asyncM4GRounds, asyncM4Loop, asyncM4GTrans, asyncM4SockInv | `loop/polling/` | S |
| `m4-common/` | asyncM4RelabelDist, asyncM4SockModel | `cakeml/servers/` | S |
| `m4-common/` | asyncM4EchoRunOk, asyncM4EchoSafe | `programs/echo/` | S |
| `m4-safety/` | asyncM4SockApprox, asyncM4SockServer | `cakeml/approx/`, `cakeml/servers/` | S |
| `http-safety/` | asyncRunOkGen | `programs/` (shared) | S |
| `http-safety/` | asyncHttpSockModel, asyncHttpSockProg, asyncHttpSockSpec | `cakeml/servers/` | S |
| `http-safety/` | asyncHttpSafe, asyncHttpMain, asyncHttpSemantics | `programs/http/` | H (http_comp_safe, http_semantics_prog) |
| `runnable/` | asyncEchoMain, sexpV3479Lib, socket_ffi.c, Makefile, demo files | `runnable/` | H (it runs) |
| `machine-code/` | asyncEchoSemantics | `programs/echo/` | H (echo_semantics_prog) |
| `machine-code/compile/` | echoServerCompile, echoServerProof | `machine-code/` | pending |
| `cf-spike/` | asyncCf* (feasibility) | `archive/` | X (superseded by cf-actions) |
| branch `spike/l2-blocking` | `l2-blocking/`, ffiSpikeSocketSelect | `loop/blocking/` | H (blocking ≡ polling) |
| branch `spike/m4-blocking` (in progress) | `m4-blocking/` | `loop/blocking/` | H when done |
| branch `spike/m4-liveness` (in progress) | `m4-liveness/` | `programs/echo/` | H when done (echo_live) |
| branches `spike/world-as-async`, `world-async-multi` | `world-async/` | `archive/experimental/` | X (experimental) |
| branch `spike/infra` | design/conventions, heap-measurements | `design/archive/` | X |
| `design/` | 01–23 notes, REVIEW-GUIDE | `design/` (renumber optional) | S |
| `design/` | HANDOFF-*.md, shared-base-build, new-experiment-worktree.sh | `design/archive/` | X |

The **front page** should show only a handful of things:

- the trusted specs (EchoSpec, HttpSpec, ~270 lines);
- the headline theorem: `echo_spec 3w echo_prog` for the polling program,
  as written. Its safety half is proved (`echo_prog_safe`) and the
  liveness half is pending. `http_prog_safe` sits alongside;
- directly under it, the blocking server as a refinement theorem
  (`echo_blocking_spec`, PR #27), with the idle-CPU comparison;
- the library's laws (monad laws, `choose` loses nothing);
- no busy-waiting (Level 2, and blocking ≡ polling);
- "it runs".

Everything else is support, reachable from `design/`.

## 3. Scaffolding: archive or delete?

Option A, recommended: **`async/archive/`, frozen.** Move the X rows there
with their Holmakefiles, but remove them from the default build. Every
superseded idea stays readable next to the design note that explains why
it was replaced. Cost: nothing, except that archive/ is not rebuilt.

Option B: **delete, with a tag.** Tag the consolidated tree before the
layout commit (e.g. `async-spikes-2026-10`), then delete the X rows. The
history and the tag keep them. The tree is smaller, but readers must know
about the tag.

## 4. Merge strategy (keeps all history; no rebases, no force-pushes)

In hg terms: merge every head into one, then `hg mv` into the new layout,
in one reviewable commit.

1. **Consolidation branch** `async-consolidated` from `async-io`.
2. **Merge the heads, not the stack.** Most spikes are ancestors of
   `spike/http-safety`, so merging that tip brings in #1–#11, #13, #14,
   #16–#18, #20, #22–#26 at once. Then merge the side heads
   `spike/l2-blocking`, `spike/m4-blocking`, `spike/m4-liveness` (when
   done), `spike/async-closed-loop`, `spike/world-async-multi` and
   `spike/infra`, each with `--no-ff`. Expect conflicts only in
   `design/HANDOFF.md`-style shared notes and `async/README.md`, both
   resolvable by keeping both sides.
3. **Tag** the merged tree: `async-spikes-2026-10`.
4. **One layout commit**: `git mv` per the table. Renames are tracked, and
   `git log --follow` sees through them. Update each Holmakefile's
   `INCLUDES`, then build. This is the only commit whose diff is large,
   and it is mechanical: nothing but moves and INCLUDES changes.
5. **One README commit**: README-DRAFT.md, in your voice, becomes
   README.md.
6. **One PR** `async-consolidated → async-io`. Close the stacked spike PRs
   with a link to it. Their branches and the tag keep every intermediate
   state. Alternatively merge them bottom-up, retargeting each to
   `async-io`. That works too, but it means ~25 merges for the same
   result.
7. **Upstream** (later, your call): the consolidated `async/` directory
   is self-contained except for its dependency on the basis heap. That
   suits a single upstream PR, or an `examples/`-style contribution.

Estimated effort: steps 1–3 take an hour. Step 4 takes half a day,
mostly INCLUDES and a full rebuild of about 40 minutes at `-j2`. Steps
5–6 depend on your editing.

## 5. Decisions for you

1. The layout (§1). In particular: `cakeml/` versus `cf/` for the CakeML
   layer, and whether `loop/` and `programs/` should merge.
2. Archive or delete the scaffolding (§3).
3. Whether to adopt `HttpSpecHeaders` (B of this PR) as the HTTP spec,
   keep both, or drop it.
4. Whether `ffiSpike*` names get renamed. This is a large mechanical
   rename of theory names, so constants keep their names but theory
   prefixes change.
5. Close the stacked PRs, or merge them bottom-up (§4.6).
