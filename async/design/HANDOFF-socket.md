# HANDOFF: socket world model (for M4)

Branch `spike/socket-model`, stacked on `spike/ffi-integration` (PR #4), in
the worktree `~/Programming/cakeml-worktrees/ffi-spike`.  Code:
`async/ffi-spike/ffiSpikeSocket*`, `ffiSpikeDivMain`.  Write-up (when done):
`async/design/07-socket-model.md`.

## Goal
A socket world model as a new FFI part, by the same modular route as the
clock (no edits to basis_ffi or the base): model, FFI functions, encodings,
heap predicate `SOCKETS`, fairness assumptions with non-vacuity, a CakeML
`Socket` module with CF specs, a composed world with whole-program
theorem(s), a tiny example, and the write-up.

## State (update at every commit)
Times from the commit log.
- 10:12 branch created; worktree already up to date with the rebuilt base
  (Holmake no-op).
- 10:37 `810f8ef2a`: model, Socket module, `SOCKETS` + 4 CF specs,
  `call_main_thm_div` (forked helper). Pushed early for async-spike.
- 10:40 `4629bcc01`: `ffiSpikeSocketFair` (sched_wf, liveness, non-vacuity,
  invariance).
- 10:50 `6073423a3`: composed world, terminating + diverging whole-program
  theorems.
- 10:56 `3d2938eb1`: one-shot echo example, end to end.
- 11:05 `cef723b8b`: never-ending poll loop in a sockets-only world.
- ~11:10 write-up `07-socket-model.md`; PR opened (see Report).
  Nothing in progress.

## Files
| file | content |
|---|---|
| `ffiSpikeSocketFFIScript.sml` | model, byte-level FFI functions, encodings, `sockets_ffi_part` |
| `ffiSpikeSocketProgScript.sml` | CakeML module `Socket` (poll, accept, read, write) |
| `ffiSpikeSocketProofScript.sml` | `SOCKETS`, CF specs `Socket_{poll,accept,read,write}_spec` |
| `ffiSpikeSocketFairScript.sml` | `sched_wf`, liveness lemmas, non-vacuity, invariance |
| `ffiSpikeDivMainScript.sml` | `call_main_thm_div` (POSTd analogue of cfMain's call_main_thm2) |
| `ffiSpikeSocketWorldScript.sml` | composed world cl+fs+clock+sockets, both whole-program theorems |
| `ffiSpikeSocketWorldLib.sml` | `prove_sem_thm` for the socket world |
| `ffiSpikeSocketExampleScript.sml` | one-shot echo, MAIN `echo_example_semantics` |
| `ffiSpikeSocketDivScript.sml` | sockets-only world, never-ending loop, MAIN `serve_semantics` |

## Build
```sh
cd ~/Programming/cakeml-worktrees/ffi-spike/async/ffi-spike
timeout 3600 arch -arm64 /bin/zsh -lc '~/HOL/bin/Holmake -j1'
```

## Assumptions made
Final list: the end of `07-socket-model.md` (11 items). Summary:
1. Time = the schedule, advanced only by `sock_poll` (one step per poll);
   accept/read/write do not advance it.
2. fds are `word64` (always fit the 8-byte encoding); CakeML side uses
   `int` with `NUM (w2n fd)`.
3. Misuse (an fd of the wrong kind) makes the FFI call fail
   (FFI_failed); polling an unknown fd just reports "not ready".
4. Ill-formed arrivals are dropped by the model; `sched_wf` excludes them.
5. No fd ownership/accepted flag: a pending connection's data can be read
   before it is accepted (harmless; programs learn fds from accept).
6. Single fairness-type assumption `sched_wf`; liveness is by lemmas
   (delivery at the next poll).
7. Buffer layouts (status bytes etc.) as documented in ffiSpikeSocketFFI.

## Tool feedback
- hol-lsp `diagnostics` reports spurious errors for translator scripts
  (`prove_lookup_cons_eq failed`, `Out-of-date conclusion to theorem`) on
  `ffiSpikeSocketProgScript.sml`; Holmake builds the same file fine.
- `goalState` at a failing tactic usually shows the state *before* it;
  at the end of a failing `>-` branch it shows the residual goal
  ("branch did not prove its goal"), which was the most useful view.
- A user variable named `flags` (a constant elsewhere) gave
  "markerSyntax.Abbr: Ill-formed quotation" in `qabbrev_tac`; renaming fixed it.
- `eval` does not keep `open`s between calls; every call needs
  `open HolKernel boolLib bossLib`.
- After editing a `Quote add_cakeml` block, the file's server reported
  "Out-of-date conclusion to theorem" for every later add_cakeml and
  "xcf: theorem does not define main_v"; `restart` fixed it.
- `serve_spec` (xcf_div_rule) failed in hol-lsp with
  `optionSyntax.dest_some` but built fine with Holmake; after a server
  restart hol-lsp proved it too (stale server state again).
- `xmatch` left an unreduced `if` when the first case of an option match
  was the nullary `None`; putting `Some` first fixed it (seen in both
  hol-lsp and Holmake, so a real CF-tactic quirk, not a tool issue).
- Positive: goalState at the end of a failing `>-` branch, and the
  "checking for 3m (finished proofs here took ≤1s)" hint for a looping
  metis, were the two most useful features.
- Holmake: ~5 s fixed overhead per run; full socket build ~30–60 s.

## Report (final)
- PR: https://github.com/briancmlee/cakeml/pull/11 (base `spike/ffi-integration`).
- MAIN theorems: `Socket_{poll,accept,read,write}_spec`, `ticks_ready`,
  `sched_wf_preserved`, `hello_world_sched_wf`,
  `socket_whole_prog_spec_semantics`, `socket_whole_prog_div_spec_semantics`,
  `call_main_thm_div`, `echo_example_semantics`, `serve_semantics`.
- Gap: no instance of the composed world's diverging theorem (cfDiv needs
  a single-part world); see 07-socket-model.md §6.
