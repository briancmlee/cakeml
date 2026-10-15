# Handoff: M4 safety assembly (spike/m4-safety)

Kept current at every commit. Write-up: `17-m4-safety.md`.

## Where things are

- Worktree `~/Programming/cakeml-worktrees/m4-safety`, branch
  `spike/m4-safety`, from `spike/m4-server`. Merged in:
  `origin/spike/m3-assembly`, `origin/spike/final-spec`, and
  `spike/m4-liveness@ff5f483c0` (the dynamic-interest loop). PR base:
  `spike/m4-server`.
- `async/m4-common/` (shared with the liveness worker; see 17 §4.5 for
  ownership): asyncM4GRounds, asyncM4RelabelDist, asyncM4SockModel,
  asyncM4SockInv, asyncM4GTrans, asyncM4EchoRunOk, asyncM4EchoSafe (mine);
  asyncM4Loop (liveness worker's).
- `async/m4-safety/`: asyncM4SockApprox (replayed depth specs, both/map),
  asyncM4SockServer (`sserver_spec`).
- `async/m4-echospec/asyncM4EchoSpecSafe`: `echo_prog_safe` (MAIN, EchoSpec's
  form), from cf-actions' `echo_semantics_prog` (spike/machine-code, merged)
  on spike/runnable's `echo_prog`.

## How to build

    for d in m4-common m4-safety m4-echospec; do
      timeout 3000 arch -arm64 /bin/zsh -lc "cd async/$d && ~/HOL/bin/Holmake -j2"
    done

(First build: m3-assembly, spec and m4-server get built via INCLUDES.)

## Status

- DONE: echo_safe for the verified echo program (`echo_prog_safe`); srun_ok
  discharged (`echo_grun_ok`). Holmake green, no cheats. PR to spike/m4-server.
- Liveness (`echo_live`): the liveness worker's (spike/m4-liveness); see 17 §3.

## Assumptions made

See 17 §4.

## Tool feedback

- hol-lsp `diagnostics` reported "xfun: goal is not a cf_fun" for the
  replayed bind specs in asyncM4SockApprox, while Holmake accepted the file
  and goalState showed xfun succeeding. It looks related to the
  CONVENTIONS note on hol-lsp vs Holmake for CF goals.
- hol-lsp: after a proof looped (metis), `diagnostics` kept reporting the
  old check as "still checking" across edits; `restart` was needed.
- hol-lsp: once, a fresh server reported "theory asyncCore is not in
  ancestry" for dependencies that Holmake considered up to date; a second
  `restart` fixed it.
- `qspecl_then` with a theorem whose free type variables differ from the
  goal's gives "No parse succeeds". Fully quantifying the lemma, or
  phrasing it so that `drule`/`simp` instantiate it, works.
- Variable names `I` and `T` are constants (identity combinator, truth)
  and give confusing type errors.
