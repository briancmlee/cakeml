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

- DONE: spec plus bites (proved), feasibility, parser, safety
  (`http_prog_b_safe`), liveness and the whole spec
  (`http_prog_b_spec : ⊢ http_spec_b 3w demo_files http_prog_b`, DISK_THM
  only), the linear-time parsing fix (2d54fd809), and the runnable demo with
  plain curl. No cheats; Holmake -j1 green.

## Assumptions made

See 28 §3.

## Tool feedback

- A fresh sparse worktree builds the whole async stack (~81 theories) at
  `-j1` before anything downstream can be checked.
- The hol-lsp session goes stale ("No merge for grammars", "not in
  ancestry") after ancestors are rebuilt underneath it. Restart it, or
  check with Holmake.
- The translator has no `toLower` and no `FOLDL`; num subtraction gives a
  precondition unless guarded.
- Running time is invisible to the proofs. A double recursive call made
  the parsers exponential, and only the runnable demo revealed it. Worth
  checking `FST (f x) … SND (f x)` patterns in any translated code.
