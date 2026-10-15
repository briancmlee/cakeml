# Handoff: M4 step 1, the concurrent echo server in CakeML (spike/m4-server)

Kept current at every commit.

## Where things are

- Worktree `~/Programming/cakeml-worktrees/m4-server`, branch
  `spike/m4-server`, from `spike/cf-reactive` (ea445fa7e), with
  `origin/spike/async-echo-server` merged in (no conflicts).
  PR base: `spike/cf-reactive`.
- New work: `async/m4-server/` (INCLUDES model, cf-spike, cf-actions;
  basis heap).
  - `asyncM4ApproxScript.sml`: depth-indexed approximation `STEPAd`/`COMPd`
    (shape fixed at depth 0), limit lemma `app_COMP_of_approxd`, and
    depth-n specs: `poll_spec_d`, `skip_spec_d`, `bind_spec_d`
    (nonexpansive), `bind_guarded_spec_0/_d` (guarded: gains one level),
    `both_spec_d`.
  - `asyncM4ServerProgScript.sml`: model types as CakeML datatypes
    (`register_type`), `has_readable`, `EVENTS`, the CakeML code
    (`readable`, `map`, `handler`, `server`), `readable_spec`, `map_spec_d`.
  - `asyncM4ServerSpecScript.sml`: `handler_spec_d`, `handler_spec`,
    `server_spec_d`, `server_spec` (MAIN).

## Status

- DONE (tasks 1, 2): `asyncM4ServerSpecScript.sml` proves `handler_spec`
  and `server_spec` (MAIN; COMP against the model's `handler fd` /
  `server lfd`), via `handler_spec_d` / `server_spec_d` (induction on the
  depth). Holmake -j2 green in `async/m4-server`, no cheats.
- Next: task 3 (program-level statement; adapter to M3's `sact`/`sresp`
  vocabulary; `srun_ok` discharge at the model level, requested by the
  coordinator), 15-m4-server.md, PR.

## Assumptions made (so far)

1. The CakeML server uses the model's own vocabulary (`event`, `action`,
   `response` of asyncServer) as CakeML datatypes; the ready set is a
   CakeML list of events. M3 (spike/m3-assembly) uses a different socket
   vocabulary (`sact`/`sresp`, word64 fds, ready set of fds); the bridge is
   an adapter (task 3), not a change to the model.
2. Recursion is proved with a new depth-indexed approximation (STEPAd)
   rather than cf-actions' STEPAn, because STEPAn 0 = T is too weak for
   code that inspects residuals (bind's case split, skip, both).

## How to build

    cd async/m4-server && timeout 1800 arch -arm64 /bin/zsh -lc '~/HOL/bin/Holmake -j2'

(builds ../model, ../cf-spike, ../cf-actions as needed; ~3 min clean.)

## Tool feedback

- Theorems/definitions added by `Quote add_cakeml:` (e.g. `map_v_def`) are
  not bound as ML values in the same script; use `fetch "-" "map_v_def"`
  (cf-actions' Both script does the same). Easy to trip over.
- hol-lsp `goalState` cannot step inside tactics defined as ML `val`s
  (e.g. `both_pending_tac`); to debug I inlined the tactic text
  temporarily. A "step into ML tactic" is probably infeasible; noting it.
- hol-lsp: after `Holmake` rebuilt a dependency, `retryCompile` reported
  "theory asyncCore is not in ancestry" (stale state); `restart` fixed it.
- There is no tool to close a file's hol-lsp server; working on three
  files leaves three servers (CONVENTIONS asks for at most two).
