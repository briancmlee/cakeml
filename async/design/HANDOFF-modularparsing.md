# Handoff: modular parsing (spike/modular-parsing)

Kept current at every commit.

## Where things are

- Worktree `~/Programming/cakeml-worktrees/http-bodies` (shared with
  spike/http-bodies; switch back with `git checkout spike/http-bodies`).
  Branch `spike/modular-parsing`, from `spike/http-bodies`; merged
  spike/http-bodies at dbff85681 (R1). PR base: `spike/http-bodies`.
- Design: `async/design/32-modular-parsing.md` (approved; §4 is progress).
- `async/http-proto/`: generic theories (Phase 1: `asyncProto`).
- `async/http-proto-inst/`: instance glue (`asyncProtoStrict`, `asyncProtoH`,
  `asyncProtoB`).

## Status

- DONE Phase 1: interface, derived lemmas, `proto_ok` and the spec
  equality for strict, `_h`, `_b`. P3 corrected to the never-a-prefix form.
- NEXT Phase 2: generic server and safety (Server, Safe, SockModel) and the
  `…_via_proto` re-derivations. Keep the server Level-2 friendly
  (`server_with2`, #53) for async-spike's option C.
- LATER 3b: the cause-of-actions lemma (§2.9), matching async-spike's
  echo statement.

## Assumptions made

See 32 §3.

## Tool feedback

- hol-lsp reports "theory ffiSpikeSocketFFI is not in ancestry" for a new
  theory whose ancestor was just built by Holmake. Holmake builds it
  fine. Restarting the server is the fix, but other files' checks are lost.
- `gvs` on `IS_PREFIX_APPEND` also rewrites the goal's `≼` into an `∃`;
  use `metis_tac[…, IS_PREFIX_APPEND]` afterwards.
- A `gvs[]` after two `parse (print r ++ x) = …` facts plus
  `print r1 ++ x = print r2 ++ y` looped; rewriting with the equality once
  (`qpat_x_assum … (fn th => fs[th])`) avoids it.
