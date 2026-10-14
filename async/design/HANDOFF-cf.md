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
