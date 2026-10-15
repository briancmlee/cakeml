# Handoff: reactive world and choose (spike/cf-reactive)

Kept current at every commit. Read with the coordinator's brief and
`HANDOFF-actions.md` (the base of this branch).

## Where things are

- Worktree `~/Programming/cakeml-worktrees/cf-actions` (the same sparse
  worktree as spike/cf-actions), branch `spike/cf-reactive`, created from
  `spike/cf-actions` (0b976e841). PR base: `spike/cf-actions`.
- New work: `async/cf-reactive/` (Holmakefile INCLUDES `../model`,
  `../cf-spike`, `../cf-actions`; HOLHEAP = basis heap).
  - `asyncCfReactWorldScript.sml`: pure HOL. The generic world `rworld`
    (`step : 's -> word8 list -> word8 list # word8 list # 's`, `nready`,
    `enc`), `world_ok`, the FFI function `round_update` (one call `round`),
    `RW`, `wrounds`/`whist`/`wround_event`, `wtrace_actions_rounds` (MAIN).
  - `asyncCfReactLoopScript.sml`: CakeML `fill`, `read_bytes`, `step`, `run`;
    `fill_spec`, `read_bytes_spec`, `step_spec` (MAIN), `run_spec` (MAIN).
- Docs: this file; `async/design/10-cf-reactive.md` (to be written at the end).

## Status

- DONE (task 1, reactive world): Holmake green, no cheats.
- TODO: task 2, `choose`; then 10-cf-reactive.md; PR.

## Assumptions made (so far)

1. One FFI call per round (`round`): the buffer holds the round's
   actions followed by `nready` padding bytes, and comes back holding
   the responses then the readiness bytes. So the world sees the whole
   round's batch, which matches "(state, actions) → (snapshot, state)".
2. Actions, responses and readiness are bytes. Readiness is a list of
   `nready` bytes, read as the set `set rdy`. `now` is 0.
3. The world state is stored in the FFI state through an injective
   encoding `enc` (part of the world); the FFI function decodes with `@`.
4. `nready` is carried in the loop state (the pair `(nr, c)`), since the
   CakeML code is fixed and the world is a parameter.

## Tool feedback

- `W` (W combinator) again: a renaming regex also hit `W8ARRAY`.
- `xif` leaves `∃b. BOOL b bv ∧ ...` even when `BOOL T bv` is an
  assumption; `qexists_tac ‘T’ >> simp[]` was needed.
