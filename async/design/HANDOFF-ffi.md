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
  system, MAIN `clock_whole_prog_spec_semantics`).
- 03:34 step 5 done and green: `ffiSpikeClockExample` (MAIN
  `clock_example_semantics`, end to end) and `ffiSpikeClockWorldLib`.
  Full `Holmake -j1` green (74 s from clean), no cheats.
- 03:55 write-up `04-ffi-integration.md` done; pushed, PR opened (see
  Report below).  The spike is complete; nothing is in progress.

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
See the list at the end of `04-ffi-integration.md` (10 items: schedule
model, < 2^64 readings, 8-byte big-endian encoding, NUM result, no_ext,
only the terminating whole-program shape, file-system-only result, stdout
via add_stdout, basis-heap as HOLHEAP, `ffiSpike` prefix).

## Tool feedback
The hol-lsp MCP tools were available and used for all proof work.
- `goalState` returned `null` ("position is not inside a Proof ... QED
  block (or its statement does not parse)") for every position in a theorem
  whose statement contains an antiquotation `^(fetch_v "main" st)`, although
  `diagnostics` checked it.  Workaround: write `main_v` instead.
- `diagnostics` sometimes reports a failing tactic at the theorem's name
  (e.g. `34:9-18`) rather than at the tactic, e.g. for an `xapp` failure
  inside `\\`-chains; `goalState` at a later line then still worked.
- `eval` runs without `open HolKernel boolLib bossLib` (`|>` and
  `SIMP_RULE` undefined until opened), and settings like
  `Globals.show_types := true` persist and change every later `goalState`
  output of that server (expected per the docs, but easy to trip over).
- After rebuilding a dependency, a file's server reports `BLOCKED ...
  cannot load XTheory` until `restart`; the message is clear.
- Holmake: ~4.5 s fixed overhead per run (scanning 322 base directories +
  the `asl-equiv` preexec) even for a 2-second theory.  Compiling a plain
  `...Lib.sml` prints nothing on success, which made me check `.hol/objs`
  by hand.  Holmake output also shows `Context.snapshot: ambient context
  read while a proof was running` warnings (harmless here, unclear meaning).
- Check-waiting: Holmake 10 runs, 134 s total; ~35 `diagnostics` calls,
  roughly 10–60 s each (not individually timed), together at most ~10 of the
  19 minutes of proof work.

## Report (final)
- PR: https://github.com/briancmlee/cakeml/pull/4 (base `async-io`).
- **Proved end to end (source semantics):** `clock_example_semantics`.
  Under `wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ clock_ok (t1:::t2:::rest)`,
  the whole program (basis + Clock + main + call) terminates successfully,
  its replayed file-system events give `add_stdout fs ("<t1>\n<t2>\n")`, and
  t1 ≤ t2.  It goes through the generic `clock_whole_prog_spec_semantics`
  (MAIN) and `Clock_now_spec` (MAIN).  Compiler correctness for the new
  oracle was not instantiated (same as basis's examples at this level).
- **Copied/adapted from basis_ffi:**
  - definitions `whole_prog_spec_def` → `clock_whole_prog_spec_def`, plus
    oracle, ffi and projection definitions that *wrap/extend* the basis
    ones;
  - the statement shape of `whole_prog_spec_IMP`;
  - ~10 tactic lines;
  - `basis_ffiLib.prove_sem_thm` (~55 lines);
  - `IMP_STDIO_general` (local upstream) re-proved compositionally.

  Reused unchanged: `basis_ffi_oracle`, `basis_proj1/2`, `oracle_parts*`,
  `extract_fs*`, `RTC_call_FFI_rel_IMP_basis_events`, `STDIO_precond`,
  `COMMANDLINE_precond`, `append_hprop`, `SPLIT_exists`, `is_refs_basis`,
  `call_main_thm2` and all library specs.  No upstream change.
- **Time per step:** base wait 34 min (overlapped with 14 min
  reading/drafting); model 2 min; CF spec 3 min; world + whole-program
  theorem 7 min; example 6 min; write-up + PR ~25 min.  Check-waiting:
  Holmake 134 s over 10 runs, plus ≤ ~10 min of hol-lsp diagnostics.
  Clean build 74 s.
- **Socket estimate:** integration ~400–500 lines via this pattern; the
  total is 2–4 kLOC (model, Socket CF library, and a new whole-program
  theorem for diverging programs), 1–3 weeks supervised.
- **MCP tools:** yes, hol-lsp MCP was available and used throughout.
- **Assumptions:** the 10 items in `04-ffi-integration.md`.
