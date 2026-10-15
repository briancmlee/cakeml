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
- 10:12 branch created; worktree already up to date with the rebuilt base
  (Holmake no-op).
- ~11:05 committed `810f8ef2a`: model (`ffiSpikeSocketFFI`), module
  (`ffiSpikeSocketProg`), `SOCKETS` + 4 CF specs (`ffiSpikeSocketProof`),
  and `call_main_thm_div` (`ffiSpikeDivMain`, proved by a forked helper).
  Full Holmake green.
- ~11:30 `ffiSpikeSocketFair` (assumption `sched_wf`, liveness lemmas,
  non-vacuity, invariance under all operations) proved in hol-lsp.
- Next: composed world (`ffiSpikeSocketWorld`), example, divergence.

## Files
| file | content |
|---|---|
| `ffiSpikeSocketFFIScript.sml` | model, byte-level FFI functions, encodings, `sockets_ffi_part` |
| `ffiSpikeSocketProgScript.sml` | CakeML module `Socket` (poll, accept, read, write) |
| `ffiSpikeSocketProofScript.sml` | `SOCKETS`, CF specs `Socket_{poll,accept,read,write}_spec` |
| `ffiSpikeSocketFairScript.sml` | `sched_wf`, liveness lemmas, non-vacuity, invariance |
| `ffiSpikeDivMainScript.sml` | `call_main_thm_div` (POSTd analogue of cfMain's call_main_thm2) |

## Build
```sh
cd ~/Programming/cakeml-worktrees/ffi-spike/async/ffi-spike
timeout 3600 arch -arm64 /bin/zsh -lc '~/HOL/bin/Holmake -j1'
```

## Assumptions made
(collected here as they are made; the final list goes into 07-socket-model.md)
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
