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
- Branch `spike/close-v2-world` (from `spike/echospec2`): the v2 world in CakeML.
  - `async/socket-v2/socketV2Part`: the 5-name FFI part, state encoding,
    part lemmas.
  - `async/socket-v2-cf/`: `socketV2Prog` (module `SocketClose.close`,
    appended to the v1 echo program's translation state
    `asyncM4SockServer`), `socketV2Proof` (`SOCKETS2_EV` and the CF specs of
    Socket.poll/accept/read/write and SocketClose.close against the v2
    part, with events), `socketV2Div` (sockets-only v2 world =
    EchoSpec2's `socket2_ffi`, `limited_parts`, `parts_ok`, initial heap).
  - `async/runnable/socket_ffi.c`: `ffisock_close` (plain close(2)) and its
    mapping row (unused by v1).
- Branch `spike/close-v2-handles` (from `spike/close-v2-world`): the
  handle-layer loop, `async/close-v2-loop/`:
  - `asyncHLModel`: the model (`hstate` table handle ↦ fd, `hdl`/`hdln`
    handles skipping the listener's number, `hdo` with auto-close on EOF,
    `hacts`, `hpoll` (`hpoll_fds`, `hready`), `hrounds`, `hround_events`,
    `hrun_ok`);
  - `asyncHLProg`: the CakeML code (`hdo`, `hperform`, `step_h`, `run_h`;
    table helpers translated);
  - `asyncHLLoop`: `hdo_spec`, `hperform_spec`, `step_h_spec`, `run_h_spec`;
  - `asyncHLMain`: `main = run_h (3, [3], ([], 0), server 3)`, `echo2_prog`,
    `echo2_semantics_prog` (EchoSpec2's world, under `echo2_run_ok`).
- Next branch: the simulation, discharging `echo2_run_ok`, and
  `echo_spec2 3w echo2_prog`.

## How to build

    timeout 900 arch -arm64 /bin/zsh -lc "cd async/spec && ~/HOL/bin/Holmake -j2"
    timeout 3000 arch -arm64 /bin/zsh -lc "cd async/socket-v2-cf && ~/HOL/bin/Holmake -j2"
    timeout 3000 arch -arm64 /bin/zsh -lc "cd async/close-v2-loop && ~/HOL/bin/Holmake -j2"

## Status

- DONE: EchoSpec2 statement, bite and non-vacuity (no cheats).
- DONE: the v2 world's CF layer (25 §4 step 1), no cheats.
- DONE: the handle layer (25 §4 step 2): `run_h_spec`, `echo2_semantics_prog`.
- NEXT: the simulation (25 §4 step 3).

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
- Writing HOL through Python string edits: use raw strings (r'''...'''),
  or `\\` (cfLib's THEN) silently becomes `\`.

- CF: when xapp_spec with a Socket spec mixes up the pre/post state
  variables, prove the instance first (‘app p f [..] P Q’ by (irule spec ..))
  and xapp_spec that (version 1's pattern).
- The translator turns MEM into IN (untranslatable): use a recursive `nmem`.
- Theorem names like `tlookup_def` can be ambiguous with base theories:
  qualify (`asyncHLProgTheory.tlookup_def`).

## Tool feedback

- None new.
