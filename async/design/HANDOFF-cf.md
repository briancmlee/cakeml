# Handoff: CF feasibility spike (spike/cf-feasibility)

Kept current at every commit. A fresh agent should be able to continue from
this file plus the coordinator's original brief.

## Where things are

- Worktree: `~/Programming/cakeml-worktrees/cf-spike`, branch
  `spike/cf-feasibility` (from `async-io` f73189499). It is a **sparse**
  worktree: only `async/` (and `.gitignore`) is checked out, plus a
  gitignored `async/holproject.toml` pointing at the base. See
  `async/design/shared-base-build.md`.
- Spike sources: `async/cf-spike/`
  - `asyncCfModelScript.sml`: the HOL history model (`mret`, `mwait`,
    `mbind`, `after`, `finished`) and one lemma per implementation step.
  - `asyncCfDetScript.sml`: a general CF lemma, `app_basic_forall`
    (determinism lets you conjoin infinitely many pure postconditions).
  - `asyncCfProgScript.sml`: the CakeML `step` datatype and
    `return`/`poll`/`wait`/`bind`, the coinductive representation predicate
    `STEP`, its approximations `STEPn`, and the CF specs.
  - `smokeScript.sml`: smoke test for the shared-base recipe.
- Docs: `async/design/02-cf-feasibility.md` (the result),
  `async/design/shared-base-build.md` (the recipe),
  `async/design/new-experiment-worktree.sh` (the recipe as a script).
- The base `~/Programming/cakeml` is frozen: never Holmake there.

## State (done)

- Step 0: base build finished 01:39:53 (exit 0).
- Step 1: the shared-base recipe works. A sparse worktree + gitignored
  `async/holproject.toml` with `[projects.cakeml] path = <base>` builds
  only the experiment's theories. The base's build products, heap and git
  status are unchanged; the first run added 65 missing make-deps cache files
  in the base, and nothing after that. Holmake's fixed overhead is ~6.5 s per run.
- Step 2: **Option A works.** `return_spec`, `poll_spec`, `wait_spec`,
  `bind_spec`, `bind_Done_spec` (MAIN) are proved, with no cheats.
  `Holmake -j2` in `async/cf-spike` succeeds (asyncCfProgTheory 62 s).
- Option B: not tried (not needed).

## Decisions

- Option A (residuals, no refs).
- `STEP` is coinductive. Recursive code (wait, bind) is proved via finite
  approximations `STEPn` (induction on n), then `STEPn_IMP_STEP` (coinduction
  + `app_basic_forall`). The step-index appears only in the `_n` lemmas,
  never in the main statements.
- User callbacks are pure in this spike (`returns` = `app ... emp (POSTv v.
  &R v)`). The recommended full design keeps them pure by making actions
  data.

## Conventions (shared machine)

- Never kill processes you didn't start yourself. No `pkill`/`killall` by
  pattern (an earlier `pkill -f Holmake` by another worker killed the shared
  base build). Kill only by a PID you recorded when you started the process.
- Wrap every Holmake / `hol` run in `timeout`; pass a short `timeout` (~30s)
  to hol-lsp `diagnostics` and call again to keep waiting.
- `Holmake -j2` at most (16 GB machine shared with other workers).
- Never run Holmake inside `~/Programming/cakeml` (the frozen base).

## Next steps (for the project, see 02-cf-feasibility.md §4)

1. Actions/responses version of `STEP` against `async-spike`'s `asyncCore`
   model.
2. The divergent event loop with `cfDiv` (`repeat_POSTd`, `xcf_div`).
3. Package "approximations then limit" as one reusable lemma/tactic.
4. (If effectful callbacks are ever needed) generalize `returns` with a heap
   invariant and `app_basic_forall` with it (needs a precise invariant).

## Dead ends / gotchas

- A committed nested `holproject.toml` whose `[projects.cakeml].path` is
  overridden by `holproject.local.toml` fails in a sparse worktree: HOL
  validates the committed path first (`no holproject.toml at ...`).
- A full (non-sparse) worktree registers `CAKEMLDIR` as itself, which
  collides with the base.
- `W` is HOL's W combinator; don't use it as a variable name.
- `CoInductive`: a free variable with the same name in every rule's
  conclusion becomes a fixed parameter. Quantify such variables explicitly.
- hol-lsp `goalState` times out (walker >1500 ms) after `xmatch` in these
  proofs. Use `diagnostics` to check, or a Holmake dumped heap.

## Final report (2026-10-15 02:05)

- **PR:** https://github.com/briancmlee/cakeml/pull/2 (spike/cf-feasibility → async-io).
- **Option A (residuals, no refs) works.** I proved CF specs for `return`, `poll`, `wait`
  and `bind` against the HOL history model via the coinductive predicate
  `STEP`, plus `bind_Done_spec`: finished binds leave no wrapper. There are no cheats,
  and Holmake succeeds. I did not try Option B.
- **Key definitions:** `STEP` (Done: finished with a represented result;
  Pending kv: not finished, and for every represented snapshot, `kv wv`
  returns a value implementing `after w m`). Also `returns` (CF `app` with emp pre
  and a pure post), `STEPn` (n-poll approximation), and `app_basic_forall`
  (determinism gives an infinite conjunction of pure posts).
- **What failed:** nothing in Option A. Friction: the `W` combinator name
  clash, CoInductive making a free `m` schematic, HO matching for
  `returns_forall`, and hol-lsp walker timeouts after `xmatch`.
- **Shared base:** the recipe works. Nothing in the base was modified; the only
  writes were 65 new make-deps cache files on the first run. Fixed overhead is about 6.5 s per run.
- **Time:** Step 0 waited ~60 min for the base build (00:40–01:40), during which I
  designed the setup and drafted the scripts. Step 1 took ~15 min. Step 2 took ~15 min of proving plus
  ~10 min of docs and PR.
- **Tools:** hol-lsp MCP tools were available (diagnostics, goalState, eval).
  `diagnostics` was the main loop, at ~10–60 s per iteration. `goalState` timed out on
  post-`xmatch` goals.
- **Recommendation:** use the residual style with CF for the library. Next, in order:
  actions/responses `STEP`, the `cfDiv` event loop, and a reusable
  approximation-limit lemma.

## Follow-up on stacked branch spike/cf-loop (PR against spike/cf-feasibility)

Task from the coordinator, worked overnight: (a) package "approximations, then the limit"
as a reusable lemma; (b) a toy never-ending event loop with cfDiv. No new
design decisions are made here; any choices go under "Assumptions made" in
`03-cf-loop.md`.

- (a) DONE. `asyncCfDetScript.sml`:
  - `app_forall` (curried version of `app_basic_forall`, for any non-empty
    argument list; it uses determinism to keep the intermediate closure and
    heap, plus `app_exact_pre`);
  - helpers `evaluate_to_heap_Val_det`, `POSTv_SEP_EXISTS_cond`, `SPLIT3_merge`.

  `asyncCfProgScript.sml`: `app_STEP_of_approx`. To prove a STEP spec,
  prove its approximations for every n. `wait_spec` and `bind_spec` are now
  2-line corollaries of `wait_spec_n`/`bind_spec_n`, so the closure reasoning
  is no longer duplicated. Statements are unchanged.
- (b) DONE. `asyncCfSnapScript.sml` (pure HOL: a minimal FFI model of a
  stream of one-byte snapshots, `after_list`, a lazy-list lemma) and
  `asyncCfLoopScript.sml` (`get_snapshot`/`step`/`run` in CakeML,
  `get_snapshot_spec`, `step_spec` (MAIN: one iteration = loop invariant),
  `run_spec` (MAIN: `POSTd io. io = LGENLIST (λi. snap_event (s i)) NONE`,
  i.e. it diverges with one get_snapshot event per snapshot)). Proved with
  `xcf_div_rule IMP_app_POSTd_one_FFI_part_FLATTEN`. The honest gap: `POSTd`
  only constrains the trace, so residual correctness shows up as the loop
  invariant, not in `run_spec` itself. Write-up: `03-cf-loop.md` (with
  "Assumptions made").
- Holmake -j2 green for all of `async/cf-spike`; no cheats.
- The 02:30–03:15 HOL maintenance window paused the work; HOL and the base were rebuilt and all
  theories here rebuilt cleanly.

## Tool feedback (for the upstream tracker)

- **hol-lsp lacks the current theory's CakeML env lookups inside
  `xcf_div` goals.** In `asyncCfLoop.run_spec`, `xapp` on `step` fails in
  hol-lsp with `Exception raised at optionSyntax.dest_some`, but the same
  tactic works under Holmake. Holmake prints "Adding nsLookup representation
  thms for [asyncCfLoop_env_1, asyncCfLoop_env_0]" at that point, so hol-lsp
  seems to miss that dynamic registration for the theory's own env
  constants. Workaround: replay the proof in Holmake's dumped heap
  (`hol --holstate=<thy>.<thm>.dumpedheap < replay.sml`, with
  `proofManagerLib.g`/`e`/`p`).
- **Editing above `Quote add_cakeml` breaks the LSP session**: re-running it
  gives `HOL_ERR "Out-of-date conclusion to theorem"` (from
  `Definition.new_definition`). Restarting the server fixes it, so pure HOL
  material now lives in a separate theory.
- **After rebuilding an ancestor theory with Holmake, the LSP keeps the old
  one** (same "Out-of-date" class of errors) until `restart`.
- **Memory**: one hol-lsp server died with "Run out of store - interrupting
  threads" while several of my servers (one per open script) were alive.
  Killing the idle servers fixed it. One server per file adds up quickly when
  each loads basisProg.
- **goalState after `xmatch`** (before the HOL rebuild): "walker timed out
  (>1500ms)". After the rebuild, goalState reports which tactic failed to
  apply ("Error: Tactic `...` failed to apply"), which was very useful.
- **Type-variable clashes when instantiating lemmas**: `qspecl_then` on a
  lemma whose type variable has the same name as an unrelated one in the goal
  silently unified them (`p : num ffi_proj`). Fix: annotate types in
  statements. Not a tool bug, but costly to diagnose.
- **Holmake fixed overhead** stays at ~6.5 s per run in the sparse worktree.

## Final report, follow-up (2026-10-15, ~04:15)

- **PR:** https://github.com/briancmlee/cakeml/pull/5 (spike/cf-loop → spike/cf-feasibility).
- **(a)** `app_forall` + `app_STEP_of_approx`. `wait_spec`/`bind_spec` are now
  corollaries of their `_n` lemmas, with statements unchanged.
- **(b)** `run_spec`: the loop diverges with trace `LGENLIST (λi. snap_event (s i)) NONE`.
  `step_spec` carries the STEP invariant. The gap: `POSTd` only constrains the trace.
- No cheats; Holmake -j2 green; nothing in the base or basis_ffi was touched.
- **Next** (not started, per the rules): the actions/responses `STEP`, after which the
  loop's trace can carry the model's meaning.
