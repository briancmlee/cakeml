# Handoff: CF feasibility spike (spike/cf-feasibility)

Kept current at every commit. A fresh agent should be able to continue from
this file plus the coordinator's original brief.

## Where things are

- Worktree: `~/Programming/cakeml-worktrees/cf-spike`, branch
  `spike/cf-feasibility` (from `async-io` f73189499). It is a **sparse**
  worktree: only `async/` (and `.gitignore`) is checked out. See
  `async/design/shared-base-build.md` for why.
- Spike sources: `async/cf-spike/`
  - `asyncCfModelScript.sml`: the HOL history model (`mret`, `mwait`,
    `mbind`, `after`, `finished`).
  - `asyncCfDetScript.sml`: a general CF lemma (`app_basic_forall`).
  - `asyncCfProgScript.sml`: the CakeML code, the representation predicate
    `STEP`, and the CF specs.
  - `smokeScript.sml`: smoke test for the shared-base recipe.
- The base `~/Programming/cakeml` is frozen: never Holmake there.

## State

- Step 0 (wait for base build): in progress.
- Step 1 (shared base recipe): designed (sparse worktree + nested
  `holproject.toml` + local override), not yet tested.
- Step 2 (CF experiment): drafted, with cheats in wait/bind (not committed
  with cheats).

## Conventions (shared machine)

- Never kill processes you didn't start yourself. No `pkill`/`killall` by
  pattern (an earlier `pkill -f Holmake` by another worker killed the shared
  base build). Kill only by a PID you recorded when you started the process.
- Wrap every Holmake / `hol` run in `timeout`; pass a short `timeout` (~30s)
  to hol-lsp `diagnostics` and call again to keep waiting.
- `Holmake -j2` at most (16 GB machine shared with other workers).
- Never run Holmake inside `~/Programming/cakeml` (the frozen base).

## Decisions

- Option A (residuals, no refs) first.
- Representation predicate `STEP` is coinductive; recursive code (wait, bind)
  is proved via finite approximations `STEPn` + a determinism lemma
  (`app_basic_forall`) to pass to the limit. This avoids step-indexing in
  the *statement* of the specs.

## Next steps

(see bottom of file once the spike completes)

## Dead ends

(none yet)
