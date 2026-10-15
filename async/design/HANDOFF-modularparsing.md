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
- DONE Phase 2 (branch `spike/proto-server`, stacked on
  spike/modular-parsing): asyncProtoServer, asyncProtoSafe,
  asyncProtoSockModel, plus `asyncProtoVia{Strict,H,B}`, which re-derive
  `http_comp_safe{,_h,_b}` through the generic pipeline.
- NEXT Phase 3: `proto_handler_live`, discharging design/34's
  `handler_live` (§2.9). Waiting on m4-server for the exact statement and
  branch.
- Not mine any more: cause-of-actions (async-spike's `hok_cause`).

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
