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
- NEXT: with_store_answers (KV); then, if cheap, echo_live_via_lib.

## Assumptions made
1. sw_accepted_live is parametric in the interest function (interest_covers);
   server_with_live is stated for the dynamic-interest loop (EI lfdn), because
   accept progress (sw_conn_accepted) is proved for that loop only.
2. server_with_live needs FLAT (out "") = "" (nothing is owed for no data).

## Tool feedback
See ~/.cache/http-liveness-worker/STATE.md (Gotchas) and HANDOFF-httpliveness.md.
