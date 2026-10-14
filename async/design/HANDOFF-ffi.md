# HANDOFF: FFI-integration spike (clock part, modular world)

Branch `spike/ffi-integration` (sparse worktree
`~/Programming/cakeml-worktrees/ffi-spike`, built against the shared base
`~/Programming/cakeml`, see `shared-base-build.md` on the cf-spike branch).
Code: `async/ffi-spike/`. Write-up: `async/design/04-ffi-integration.md`.

## Goal
Add a new external-world component (a clock) to CakeML's FFI model without
editing `basis/basis_ffiScript.sml`: own FFI part, CF spec, own composed
world, own whole-program theorem, end-to-end example.

## State (update at every commit)
- 03:20 steps 1-2 done and green: clock model (`ffiSpikeClockFFI`), module
  `Clock.now` (`ffiSpikeClockProg`), `CLOCK` and the CF spec
  `Clock_now_spec` (`ffiSpikeClockProof`).
- 03:28 step 3-4 done and green: `ffiSpikeClockWorld` (composed oracle,
  projections, parts_ok, basis view of a run, initial heap, final file
  system, MAIN `clock_whole_prog_spec_semantics`).  Example (step 5) and the
  Lib are drafts (uncommitted until cheat-free).

## Files
| file | content |
|---|---|
| `ffiSpikeClockFFIScript.sml` | clock model: `ffi_now`, schedule assumptions, `clock_ffi_part` |
| `ffiSpikeClockProgScript.sml` | CakeML module `Clock.now : unit -> int` |
| `ffiSpikeClockProofScript.sml` | `CLOCK` heap predicate, CF spec `Clock_now_spec` |
| `ffiSpikeClockWorldScript.sml` | composed oracle/state/projections, parts_ok, whole-program theorem |
| `ffiSpikeClockWorldLib.sml` | `prove_sem_thm` for our world (adapted from basis_ffiLib) |
| `ffiSpikeClockExampleScript.sml` | two-reading example, end-to-end theorem |

## Build
```sh
cd ~/Programming/cakeml-worktrees/ffi-spike/async/ffi-spike
timeout 3600 arch -arm64 /bin/zsh -lc '~/HOL/bin/Holmake -j1'
```

## Assumptions made
(see 04-ffi-integration.md)

## Tool feedback
