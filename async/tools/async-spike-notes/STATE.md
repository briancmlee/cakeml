After compaction: read this file and your HANDOFF before doing anything else.
(HANDOFF = "Next" below + FINAL-SERIES-PROPOSAL.md §9. History: STATE-HISTORY-2026-10-16{,b}.md here.
 Copies of these notes are on branch tools/final-series under async/tools/async-spike-notes/ — use them if ~/.cache was not moved.)

# async-spike STATE (2026-10-16, wind-down before the move to Sisyphus)

## Contacts (SendMessage by NAME; ListAgents if a name fails)
coordinator "CakeML async orchestrator"; m4-server (owns final L0 stack, KV fold); cf-actions (stateful quiescence fold into final/10);
stacked-pr-continuation (KV worker); close-v2; honest-ffi.

## Rules
- Holmake ONLY via ~/.cache/orchestrator/holslot … Holmake -j1; ASK the coordinator before any holslot build (memory); use
  async/tools/final-series/watch_build.sh (timeout + footprint watchdog, only this tree's processes).
- NO hol-lsp --lsp-check-proofs on whole files (a looping simp grew one to 13 GB). Check single proofs or short holslot builds.
- Sparse worktrees (infra/async/design/new-experiment-worktree.sh with ABSOLUTE paths; then git branch --unset-upstream).
- No cheats; no force-push/rewrite; explicit staging; draft PRs on briancmlee/cakeml; never close old PRs.
- Trailer: Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com> + Claude-Session: https://claude.ai/code/session_01H3taUnqjUMSjFfuYgFmnm2.
- ✅ only with BUILD evidence (Holmake -n up to date + no cheat tag in .dat, or the author's green statement).

## Done (all pushed)
- review-v2 series 01–14 + next-steps (#84–#92, #100, #109, #112, #113, #115, #116). README socket_ffi.c paragraph narrowed (user-approved) on review-v2/14 5c6d31fba.
- final/00-headlines (Layer H) @ 32c50d9bd, PR #129: HEADLINES.md (final names; §7 peers simple-class only; §8 per-headline kernel transfer table — corrected per ~/.cache/transfer-review/REPORT.md), design/NAMES.md + names.tsv.
- Tools: branch tools/final-series @ 760f76169 (async/tools/final-series: rename.py, names.tsv [MASTER], mknames.py, genhm.py, watch_build.sh).
- lifetime_core_link PROVED (user-approved iff; LEAF): spike/lifetime-core 276d017ca.
- Final L1 (lifetimes), stacked on final/11 @ 8efb292d6, all PUSHED:
  - final/L1-01-trusted-surface bb08556fb — built green — draft PR #142
  - final/L1-02-link 6e47b28c4 — built green — draft PR #143
  - final/L1-03-echo-episodes a2eb6499c — build WAS RUNNING at wind-down (lifetimes/world-cf, loop, echo, headline); NO PR yet.
  Worktree ~/Programming/cakeml-worktrees/final-l1 (L0 objects rsync'd from m4-server's final-l0 at 8efb292d6).

## Next (exact)
1. L1-03: rebuild on the new machine (ask coordinator): in a sparse worktree of final/L1-03-echo-episodes with L0 built
   (or rsync m4-server's built final-l0 at the same final/11 commit, preserving mtimes), run from async/:
   tools/final-series/watch_build.sh LOG lifetimes/world lifetimes/spec lifetimes/link lifetimes/world-cf lifetimes/loop lifetimes/echo headline
   Then check: no "cheat" in scripts, no cheat tag in .dat, echoEpisodesHeadline has echo_episodes_prog_spec. Open draft PR
   "[final L1 03/03] the echo server with close and fd reuse" (base final/L1-02-link; body: commit a2eb6499c's message).
2. FIRST on Sisyphus, together with step 1's rebuild: final L0 is COMPLETE (KV + stateful quiescence merged; final/10 18a50b3af,
   final/11 5a407ebb6). Merge final/11-it-runs @ 5a407ebb6 into final/L1-01, then L1-01→L1-02→L1-03 (merges only, no rewrites);
   rebuild all of L1 on top (L0 objects from m4-server's built tree at 5a407ebb6, or build L0 once); update PR #142/#143 bodies' base commit; open L1-03's PR.
3. (merged into 2) cf-actions' stateful quiescence is already in final/10 18a50b3af.
4. Later: L2 (peers) waits for close-v2; L3 after honest-FFI R1–R4 — write first (HEADLINES §8): l1pf_simple, l0_echo2_spec, quiet_on_kernel + hup_spin_bite.
5. Scratch, safe to delete: worktree final-rename-test (branch scratch/rename-test, local only, uncommitted test rename — not needed).
