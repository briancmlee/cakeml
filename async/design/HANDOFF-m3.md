# Handoff: M3 assembly (spike/m3-assembly)

Kept current at every commit. Read with the coordinator's brief and
`HANDOFF-reactive.md`.

## Where things are

- Worktree `~/Programming/cakeml-worktrees/cf-actions`, branch
  `spike/m3-assembly`, from `spike/cf-reactive` (ea445fa7e), with
  `origin/spike/cfdiv-multipart` merged in (380c95bb6; it contains
  spike/socket-model; one trivial conflict in async/.gitignore, both
  sides kept). PR base: `spike/cf-reactive`.
- New work: `async/m3-assembly/` (INCLUDES model, cf-spike, cf-actions,
  cf-reactive, ffi-spike; basis heap).
  - `asyncM3WorldScript.sml` (pure): socket actions `sact` and responses
    `sresp`; `sock_do`/`sock_acts` (performing actions with the socket
    model's operations), `act_event`/`spoll_event`, the history the
    socket world generates (`srounds`, `shist`, `sround_events`),
    `srun_ok` (no misuse), `strace_actions_rounds` (MAIN).
  - `asyncM3ProgScript.sml`: the library code declared again (module
    `Async`) after the Socket module, in one program; `step_stamps_agree`
    (same constructor stamps, so STEPA/COMP are reused); the library specs
    replayed (`Async_*_spec`).
  - `asyncM3LoopScript.sml`: CakeML `sact`/`sresp` datatypes, `do_act`
    (Socket calls), `perform`, `step`, `run`; event-exposing Socket specs;
    `step_spec`, `run_spec` (MAIN).

## Status

- DONE (task 1, app level): Holmake green, no cheats.
- DONE (tasks 2+3): `asyncM3ExampleModelScript.sml` (`accept3`,
  `srun_ok_accept3`) and `asyncM3ExampleScript.sml` (`main_spec`,
  `m3_semantics` (MAIN: the whole program diverges with the round-by-round
  socket trace), `m3_trace_actions` (MAIN)). Holmake green, no cheats.
- DONE: 13-m3-assembly.md.

## Assumptions made (so far)

1. Route: the loop calls the Socket functions directly, one per emitted
   action, then Socket.poll once per round, all in the socket worker's
   single FFI part (SOCKETS_EV), with cfDiv's one-part rule. This is
   simpler and more faithful than wrapping the socket model in my generic
   `round` call, which would need a new FFI interface.
2. The interest fds polled each round are a fixed list (loop state).
3. `now` is 0.
4. Misuse (e.g. reading from an fd that is not a connection) makes the
   real FFI call fail, so the loop theorem assumes `srun_ok` (no misuse
   in the run). It is a hypothesis about the program and the world,
   discharged per example.
5. The library code is declared a second time in the socket program
   (module Async), because the two translation chains are separate.
   Its specs are replayed with the same proofs.
6. The example computation is `accept3` (wait until listener 3 is ready,
   then accept), chosen so that `srun_ok` is provable from "3 is a
   listener" alone. The echo handler needs reasoning about responses
   over the run (see 13-m3-assembly.md).

## Tool feedback

- hol-lsp diagnostics/goalState worked well on these mid-size proofs; the
  FAIL_TAC-with-goal trick (HANDOFF-reactive.md) also helps inside `by`
  if `by` is replaced by `sg ... >-` (BasicProvers.by drops the message).
