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

## Assumptions made
1. sw_accepted_live is parametric in the interest function (interest_covers);
   server_with_live is stated for the dynamic-interest loop (EI lfdn), because
   accept progress (sw_conn_accepted) is proved for that loop only.
2. server_with_live needs FLAT (out "") = "" (nothing is owed for no data).
3. handler_live compares the owed output as a list of writes; echo's writes
   are not a function of D (they follow how reads were split), so a FLAT
   variant (handler_live_flat) was added, implied by handler_live.

## Tool feedback
See ~/.cache/http-liveness-worker/STATE.md (Gotchas) and HANDOFF-httpliveness.md.
