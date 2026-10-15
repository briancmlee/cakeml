# Handoff: the HTTP server in CakeML (spike/http-impl)

Kept current at every commit.

## Where things are

- Worktree `~/Programming/cakeml-worktrees/cf-actions`, branch
  `spike/http-impl`, from `spike/http-model`, with `origin/spike/m4-server`
  merged in (fa459b678; clean). PR base: `spike/http-model`.
- New work: `async/http-impl/` (INCLUDES ../model ../cf-spike ../cf-actions
  ../m4-server ../http-model ../spec ../ffi-spike; basis heap).
  - `asyncHttpImplProgScript.sml`: `respond` + `respond_thm`; translations
    of `parse_request` and helpers; CakeML `server_with`, `http_handler`,
    `http_server`.
  - `asyncHttpImplSpecScript.sml`: `HANDLER`, `server_with_spec(_d)`,
    `server_with_handler_spec` (echo instance), `http_handler_spec(_d)`,
    `http_server_spec`.
- Write-up: `20-http-impl.md`.

## Status

- DONE: task 1 (translation), task 2 (code + MAIN specs, generic skeleton),
  task 3 (what is left for `http_safe`: 20 §4). Holmake green, no cheats.

## Assumptions made

See 20 §5 (model vocabulary; `respond` proved equal to the spec's printed
response; new generic `server_with`, m4-server's `server` untouched;
`HANDLER` includes wf; the file map is an association list of strings).

## Tool feedback

- The hol-lsp `eval` tool runs outside the theory's context (`fetch`,
  `print_thm` unbound), so inspecting certificate theorems had to go
  through `goalState` on a proof instead.
- A Holmake run that hit a failing `metis_tac` sat for over 10 minutes
  without output. Checking first with LSP `diagnostics` (which reports
  failures per proof) is much faster than Holmake for iteration.
- `xapp` does not use a spec for a function-valued *variable* (the handler
  parameter `h`) from a quantified assumption. State the instance with
  `by` and use `xapp_spec`.

## Final report (2026-10-15)

- Proved (no cheats, Holmake green): `respond_thm`; `server_with_spec`
  (any handler with a spec), `server_with_handler_spec` (echo instance),
  `http_handler_spec`, `http_server_spec`.
- Not started (by instruction): the program-level `http_safe` assembly.
  Steps and estimates are in 20 §4 (socket-vocabulary relabelling, a
  re-translation in M3's chain, `run_i`, the bridge via asyncM4GTrans,
  then liveness).
