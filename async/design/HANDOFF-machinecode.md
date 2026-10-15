# Handoff: towards the machine-code theorem (spike/machine-code)

Kept current at every commit.

## Where things are

- Branch `spike/machine-code`, from `spike/runnable` (35fc22e2d), with
  `origin/spike/m4-safety` merged in (a902db27d; clean). PR base:
  `spike/runnable`.
- `async/runnable/asyncEchoMainScript.sml`: `echo_decs`, `echo_prog` (the
  m3 shape), `echo_prog_eq`. The export is unchanged; `check_printer.sh`
  still agrees.
- `async/machine-code/asyncEchoSemanticsScript.sml`: `main_spec`,
  `echo_semantics`, `echo_prog_syntax_ok`, `echo_semantics_prog`.
- `async/machine-code/compile/` (NOT BUILT): `echoServerCompileScript.sml`,
  `echoServerProofScript.sml`.
- Write-up: `22-machine-code.md`.

## Status

- DONE: the program's divergence semantics with the socket FFI part, plus
  echo_safe, in `semantics_prog` form. Holmake -j1 green, no cheats.
- BLOCKED (memory): building the compiler backend proofs and cv_translator,
  and with them the in-logic compilation and the machine-code theorem.
  Requirements, costs and steps are in 22 §3.

## Assumptions made

See 22 §4.

## Tool feedback

- The LSP cannot `fetch "-" "main_v_def"` (there is no current theory
  while it checks). Use the ancestor's binding `main_v_def` directly.
- The machine's swap was already past the agreed threshold when the task
  started, so the stop condition fired before any heavy step.

## Final report (2026-10-15)

- Proved: `main_spec`, `echo_semantics`, `echo_semantics_prog`. In the
  sockets-only world with listener 3w, `echo_prog` diverges with trace
  `echo_trace s0`, which satisfies `echo_safe`.
- Not run: `eval_cake_compile_arm8` and the `compile_correct` composition.
  The scripts are written, and no missing CakeML lemma was found.
  Estimated 6–12 h at -j1 with a 4–10 GB peak; needs a machine with free
  memory.
