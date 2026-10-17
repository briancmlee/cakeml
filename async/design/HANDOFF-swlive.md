# Handoff: library liveness (spike/sw-live, design/34)

Kept current at every commit.

## Where things are
- Worktree `~/Programming/cakeml-worktrees/library-liveness`, branch `spike/sw-live`,
  stacked on `spike/library-liveness` (design/34, PR #59), from `spike/http-bodies`.
- `async/library-liveness/asyncServerWithLiveScript.sml` (theory
  asyncServerWithLive; renamed from asyncSWLive: `sw_live` clashes with
  async-spike's asyncSWLiveServer, PR #56): hread, henv, handler_live,
  interest_covers, uses_ok_sw, grun_ok_sw, sw_rounds_bytes, sw_view,
  sw_view_henv, sw_accepted_live, server_with_live.

## Plan
1. server_with_live (asyncServerWithLive).
2. asyncHttpLiveBLib: handler_live for http_handler_b from hmachine_live_p (bridge),
   then http_live_b_rounds_via_lib.
3. with_store_answers (KV).

## How to build
    ~/.cache/orchestrator/holslot timeout 3000 arch -arm64 /bin/zsh -lc \
      'cd async/library-liveness && ~/HOL/bin/Holmake -j1'

## Status
- DONE: server_with_live (and sw_accepted_live, parametric in the interest
  function). Holmake green, no cheats.
- DONE (branch spike/live-via-lib): asyncHttpLiveBLib: handler_live_http_b
  (the bridge from hmachine_live_p, ~40 lines) and http_live_b_rounds_via_lib
  (http_live_b_rounds' statement, from server_with_live).
- DONE (branch spike/with-store-answers, PR #69, base spike/http-kv-impl):
  with_store_answers (async/with-store-live).
- DONE (branch spike/echo-via-lib): asyncServerWithLiveFlat (handler_live_flat,
  server_with_live_flat, helpers hread_mono / new_action_unanswered /
  nreads_step_wf) and asyncEchoLiveLib (echo_reads, handler_live_flat_echo,
  echo_live_via_lib: echo_live_rounds' statement from the library).

- DONE (branch spike/server-v, stacked on spike/echo-via-lib): the skeleton over
  a vocabulary (KV liveness, principled version):
  - asyncServerV: vocab record, vocab_ok, idV, server_v (fix),
    server_with_eq_v (server_with = server_v idV), sproj, on_fd_v.
  - asyncServerVProgress: sv_isolates, sv_handler_view, sv_accept_progress
    (asyncSWProgress for any V); sw_handler_view_from_v /
    sw_accept_progress_from_v re-derive the old statements.
  - asyncServerVLive: (1) any socket machine M: accepts_progress,
    m_conn_accepted, henv_t, m_view_henv; (2) handler_live_v; (3) wrap_ok V W
    inner (wrap_ok_id); (4) sv_uses_ok, uses_ok_wrap, accepts_progress_wrap,
    view_wrap; (5) server_v_live, and server_with_live_from_v (the old
    statement, for idV and the identity wrapper).
  DONE (branch spike/kv-wrap, PR #73): async/kv-live/asyncServerVKv: sockV,
  wrap_ok_with_store, with_store_v_live (asyncWithStore definitions only).
  NEXT (was: sockV +) server_with_k = server_v sockV + wrap_ok sockV (with_store δ s0)
  (inner_hist δ s0), on the KV base (spike/http-kv-impl, once its
  asyncWithStoreStep is fixed by stacked-pr-continuation); then kv_live_rounds.

## Assumptions made
1. sw_accepted_live is parametric in the interest function (interest_covers);
   server_with_live is stated for the dynamic-interest loop (EI lfdn), because
   accept progress (sw_conn_accepted) is proved for that loop only.
2. server_with_live needs FLAT (out "") = "" (nothing is owed for no data).
4. The KV handler's "5th fact" (each query is answered in the next round) is
   prompt (hf fd) g, already a hypothesis of handler_live_v; henv_v is
   henv_t on λq. sproj V (trans (hf fd) q).
5. wrap_ok asks the wrapper for: wf, actions = sacts V of m's actions on
   inner m h, trans = sproj V of m's transcript on inner m h, prompt
   transfer, and inner keeping lengths, ready sets and prefixes.  "relabel
   commutes with W" (plan item iv) was not needed: the loop runs W m itself.
3. handler_live compares the owed output as a list of writes; echo's writes
   are not a function of D (they follow how reads were split), so a FLAT
   variant (handler_live_flat) was added, implied by handler_live.

## Tool feedback
See ~/.cache/http-liveness-worker/STATE.md (Gotchas) and HANDOFF-httpliveness.md.
