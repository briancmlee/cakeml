# Handoff: M4 liveness assembly (spike/m4-liveness)

Kept current at every commit. Write-up: `19-m4-liveness.md`.

## Where things are

- Worktree `~/Programming/cakeml-worktrees/m4-liveness` (sparse: `/async/`),
  branch `spike/m4-liveness`, from `spike/async-closed-loop`. Merged in:
  `origin/spike/final-spec`, `origin/spike/m3-assembly`,
  `origin/spike/m4-server`, `origin/spike/m4-safety`. PR base:
  `spike/async-closed-loop`.
- `async/m4-common/asyncM4Loop` (mine): the dynamic-interest loop `run_i`
  and `run_i_spec`. Promised to the blocking-loop worker: no renames of
  `interest`, `add_accepted`, `step_i`/`run_i` or their specs without telling them first.
- `async/m4-liveness/`: asyncM4Sched, asyncM4Account, asyncM4LiveProg,
  asyncM4LiveWorld, asyncM4ReadSoon, asyncM4Drain, asyncM4Queue,
  asyncM4AcceptSoon, asyncM4EchoLive (`echo_live_rounds`).
- `async/m4-echospec-live/asyncM4EchoSpec`: **`echo_prog_spec : echo_spec 3w
  echo_prog`** (MAIN; safety from m4-safety/machine-code, liveness from here).

## How to build

    for d in m4-liveness m4-echospec-live; do
      timeout 3000 arch -arm64 /bin/zsh -lc "cd async/$d && ~/HOL/bin/Holmake -j2"
    done

(First build: model, ffi-spike, m3-assembly, m4-server, m4-common, spec,
m4-safety, runnable, machine-code, m4-echospec get built via INCLUDES.)

## Status

- DONE: `echo_live_rounds` and `echo_prog_spec`. Holmake green, no cheats.

## Assumptions made

See 19 §6.

## Next (queued by the coordinator)

EchoSpec2 (close + fd reuse, per-episode), spec first, as its own PR.
