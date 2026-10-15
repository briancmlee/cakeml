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
- DONE Phase 3a (branch `spike/proto-live`, stacked on
  spike/proto-server): asyncProtoMachine, asyncProtoDrain,
  asyncProtoEnvLive (`proto_env_live`: handler_live with henv spelled out).
- NEXT Phase 3b: when m4-server pushes `spike/sw-live` (theory
  asyncSWLive: hread, henv, handler_live, sw_live), merge it and prove
  `proto_handler_live` by unfolding to `proto_env_live`. Then
  asyncProtoLive = sw_live instance, giving `proto_live` for the trace.
  Agreed bound: B D = (LENGTH D + 2) * (LENGTH (proto_all P D) + 3).
- THEN Phase 4: generic CakeML handler and CF spec (§2.4).
- Not mine any more: cause-of-actions (async-spike's `hok_cause`).

## Gotchas (phase 3)

- Ported proofs with a new hypothesis: state `proto_ok P ⇒ (orig)`,
  start with `DISCH_TAC`, and use lemmas as `ok th` (hypothesis
  undischarged), so drule/irule shapes are unchanged. Use
  `UNDISCH (SPEC_ALL th)` where a proof does `Q.INST` (ok's GEN_ALL
  hides the names).
- Renaming `h*` to `p*` must also rename `h*_def`: the stale names resolved
  silently to the echo machine's definitions in asyncProgress.
- `drule … Sj_SUC` with `qspecl_then` over the free variables is
  fragile; `drule_then (fn th => REWRITE_TAC[th]) Sj_SUC` is not.

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
