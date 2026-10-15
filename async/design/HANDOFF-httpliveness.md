# Handoff: HTTP liveness (spike/http-liveness)

Kept current at every commit.

## Where things are

- Worktree `~/Programming/cakeml-worktrees/http-liveness`, branch
  `spike/http-liveness`, from `origin/spike/http-impl`; merged
  `origin/spike/async-closed-loop` (closed-loop world model, asyncLiveness).
  PR base: `spike/http-impl`.
- `async/http-liveness/`:
  - `asyncSWProgress`: the generic `server_with hf` from the handler's side
    (`sw_handler_view`: each accepted fd is served by its own handler on a
    view of the history; `sw_accept_progress`).
  - `asyncSWClosedLoop`: closed-loop facts for `server_with hf`
    (`sw_consistent`, `sw_fresh`, `sw_round_conn`, `sw_eof`, ...).
  - `asyncHttpMachine`: the HTTP handler as a three-state machine
    (HA/HB/HD), `hmachine_trans`, the accounting invariant `hmachine_inv`.
  - `asyncHttpDrain`: machine-level liveness `hmachine_live` (MAIN).

## How to build

    timeout 3000 arch -arm64 /bin/zsh -lc "cd async/http-liveness && ~/HOL/bin/Holmake -j2"

## Status

- DONE: machine-level liveness `hmachine_live` (the machine answers every
  complete request in D within 2K + 2 rounds, under four environment
  hypotheses: readability, read-everything, EOF).
- NEXT: `asyncHttpLiveness` (closed loop): instantiate
  `hf = λfd. http_handler files (fd, "")`, use `sw_handler_view` to move the
  machine's facts to the world, discharge the four hypotheses from the
  world facts, and state: on an accepted connection with received data D
  at round n, by round n + 2·|parse_all D| + O(1), the responses to D
  are a prefix of what was written.

## Assumptions made

1. The machine-level theorem takes the environment facts as hypotheses;
   the closed-loop file discharges them from the world model.

## Tool feedback

- hol-lsp: a looping `gvs`/`simp` keeps the server busy ("checking for
  Nm") with no hint which tactic loops; `goalState` at successive lines
  (walker times out at the looping step) located it. Causes found here:
  two assumptions `LENGTH rq = LENGTH (parse_all b)` and
  `parse_all b = rq ++ ...` together, and a pair of symmetric equations.
- `simp[GSYM APPEND_ASSOC]` loops (simp normalises with APPEND_ASSOC).
- hol-lsp `eval` has no theory context (Ancestors not loaded).
- After Holmake rebuilds, hol-lsp sometimes needs `restart` (twice) to
  load dependencies.
- `qspecl_then` quantifier order surprises; `I`, `T`, `K` are constants;
  `outcome`/`response`/`action` type names clash between HttpSpec and
  semantics.
