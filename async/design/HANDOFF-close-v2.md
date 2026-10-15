# Handoff: close / fd reuse, v2 (close-v2)

Kept current at every push. Write-up: `25-echospec2.md`.

## Where things are

- Worktree `~/Programming/cakeml-worktrees/close-v2` (sparse, `/async/`).
- Branch `spike/echospec2` (spec first, for review), from
  `spike/m4-liveness` (PR #30, `echo_prog_spec`).
  - `async/socket-v2/`: `socketV2FFI` (world v2: clients by connection order,
    lowest-free fd at accept, `«sock_close»`), `socketV2Fair` (`sched_wf2`).
  - `async/spec/EchoSpec2Script.sml` (trusted statement),
    `EchoSpec2BiteScript.sml` (bite, reuse bug, non-vacuity).
  - `async/spec/Holmakefile`: INCLUDES now also `../socket-v2` (additive).
- Next branches (stacked): v2 world CF layer; handle-layer loop; simulation
  and `echo_spec2 3w <prog>`.

## How to build

    timeout 900 arch -arm64 /bin/zsh -lc "cd async/spec && ~/HOL/bin/Holmake -j2"

## Status

- DONE: EchoSpec2 statement, bite and non-vacuity (no cheats).
- NEXT: the proof (25 §4).

## Assumptions made (spec decisions, flagged for review in 25 §2)

1. Schedules name clients by connection order, not fds.
2. The kernel allocates the lowest free fd (POSIX); `reserved` fds are
   arbitrary in `server_world2`.
3. Liveness per client: client j ↔ episode j (one listener, FIFO accept).
4. Fairness bound: reserved + listeners + clients < 2^64.

## Gotchas

- `EVAL` of `lowest_free` (a `LEAST`) does not terminate on concrete lists:
  use `computeLib.RESTR_EVAL_TAC [“lowest_free”]` plus a computed
  `lowest_free [...] = ...` lemma (via `lowest_free_eq`).
- `ep_events`' numerals defaulted to `int`; annotate `(j:num) (k:num)`.

## Tool feedback

- None new.
