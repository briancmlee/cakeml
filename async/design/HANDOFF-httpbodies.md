# Handoff: HTTP request bodies (spike/http-bodies)

Kept current at every commit.

## Where things are

- Worktree `~/Programming/cakeml-worktrees/http-bodies` (sparse, created
  with the infra script). Branch `spike/http-bodies`, stacked on
  `origin/spike/http-liveness` (75a768762), which has `http_prog_h_spec`.
  PR base: `spike/http-liveness`.
- `async/spec/HttpSpecBodiesScript.sml` (the spec, DRAFT for user review)
  and `HttpSpecBodiesBiteScript.sml` (24 proofs).
- `async/design/28-http-bodies.md`: spec and feasibility.
- `async/http-bodies/` (in progress), the `_b` pipeline:
  - parser: `asyncHttpParseB`, `asyncHttpParseBExt`;
  - model: `asyncHttpServerB`, `asyncHttpSafeB`, `asyncHttpSockModelB`;
  - CakeML: `asyncHttpSockProgB`, `asyncHttpSockSpecB`, `asyncHttpMainB`;
  - whole program: `asyncHttpSemanticsB`, `asyncHeadlineB`;
  - liveness: `asyncHttpMachineB`, `asyncHttpDrainB`, `asyncHttpLiveB`,
    `asyncHttpSpecB`.

  Everything except the parser theories was generated from the H versions
  with an identifier mapping, then fixed up by hand.

## Status

- DONE: spec plus bites (proved), feasibility note.
- IN PROGRESS: the parser and the `_b` pipeline (waiting for the
  dependency build in this fresh worktree, at `-j1`).

## Assumptions made

See 28 §3.

## Tool feedback

- A fresh sparse worktree builds the whole async stack (~81 theories) at
  `-j1` before anything downstream can be checked.
