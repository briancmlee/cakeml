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
- DONE (option R1): merged origin/spike/http-h-linear (#54, which includes
  #48). The bodies parser now has its own header-line parser,
  `parse_bheaders` (the pre-#48 `parse_headers`, matching `valid_bheader`),
  with the linear `parse_bheaders2` for the translation. It reuses
  ProgH's `split_at2`/`toLower` and strict's `split_path2`.
  `http_prog_b_spec` is unchanged as a statement. The demo was rerun.

- DONE (SPEC CHANGE, user-approved): header names are RFC 9110 tokens
  (28 §7). `http_prog_b_spec` re-proved; demo rerun.

## Assumptions made

See 28 §6.

## Tool feedback

- A fresh sparse worktree builds the whole async stack (~81 theories) at
  `-j1` before anything downstream can be checked.
- The hol-lsp session goes stale ("No merge for grammars", "not in
  ancestry") after ancestors are rebuilt underneath it. Restart it, or
  check with Holmake.
- Merging a branch that translates the same constants (`split_at2`,
  `toLower`) as this one makes the descendant's translation clash. Reusing
  the ancestor's translation is the only fix, so put shared helpers low
  in the stack.
- The translator has no `toLower` and no `FOLDL`; num subtraction gives a
  precondition unless guarded.
- Running time is invisible to the proofs. A double recursive call made
  the parsers exponential, and only the runnable demo revealed it. Worth
  checking `FST (f x) … SND (f x)` patterns in any translated code.

- 2026-10-16: H-CHARS (04be60754, RFC character sets for paths and field values) approved by the user.
