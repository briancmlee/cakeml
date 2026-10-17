After compaction: read this file and your HANDOFF before doing anything else.

# STATE: KV worker (HTTP key-value server, CakeML async) — 2026-10-16, clean point before the machine move

Coordinator: "CakeML async orchestrator" (on the old machine uds:/tmp/cc-socks/60951.sock; after the move use
ListAgents). Peers: honest-ffi, m4-server, close-v2, moonshot, async-spike.
HANDOFF (older, KV-only): async/design/HANDOFF-httpkv.md on spike/http-kv-impl. This file wins.

## Everything is committed and pushed (verified: local = origin for all branches below)
- spike/http-kv-impl b6244f2d9: KV headline ⊢ kv_spec 3w kv_prog (kv-live/asyncKvProgSpec) + runnable demo. PR #111.
- spike/kv-order-generic 08b322415: unification (asyncKvOrderGen.kv_safeG_rounds; kv_comp_safe + kv2_safe instances).
  PR #138 (base spike/kv-v2), green.
- spike/kv-proto-l0 ebcb36a7e: KV CakeML on the proto pipeline (programs/kv, final names). Merged by m4-server into
  final/09-protocols as 82120c7ec (forwarded to 10, 11). PR #140 closed.
- spike/kv-proto 7eb3d0fb5: the old pre-fold draft (superseded by kv-proto-l0; kept only because asked to push).
- spike/servers-honest-l1 4645f7765: CURRENT task, WIP (below).

## CURRENT task: servers onto the honest FFI's prefetching L1 (CakeML level)
Branch spike/servers-honest-l1 (from origin/spike/honest-connect 04e72d9d3). Sparse /async/. New dir async/honest-l0-cf.
- USER APPROVED (2026-10-16) the statement echo_l0_safe (sent via coordinator): new trusted raw-trace defs
  l0_accepted, l0_ep_events, l0_read, l0_sent, l0_server_world, echo_safe_l0; theorem
  ∀w0. l0_server_world w0 ⇒ ∃io. (semantics_prog (init_state (l0_ffi w0)) init_env echo_l0_prog (Diverge io) ∧
  echo_safe_l0 io) ∨ (io = [failed sys_listen] ∧ Terminate). Choices (a)–(e) approved. CONDITION: BITES BEFORE the P3
  proof: swapped clients, dropped byte, duplicated byte, leak across fd reuse, non-vacuity on an ideal real trace.
  Record the approval in the PR/note.
- Plan: P1 honest-l0-cf (honestL0Part [WIP], honestL0Prog wrappers sys_listen/poll/accept/recv/send/shutdown/close,
  honestL0Proof CF specs vs l0_ffi_fn); P2 honest-l1-cf (PF L1 = honestL1PFModel pdo/pacts/pf_tail/pround in CakeML,
  extending asyncM4SockServer's chain; divergence spec vs prounds using honestL1PFInv prun_total, pl2_ok); P3 echo:
  main = sys_listen constant port, run_pf with v2 echo server on the RETURNED lfd; semantics_prog; R1-safe
  (l1pf_refines_hl, psk_server_world) RESTRICTED to rounds ≤ N (ask honest-ffi to add it); transfer raw sent ≼ abstract
  written ≼ abstract read ≼ raw received; then echo_l0_safe. P4 HTTP, KV (send their statements first).
- P1 status, honestL0Part (history-replay encoding: part parameterised by w0; state encoded by its hist if l0_reach w0 w
  [l0_rely ∧ replay w0 w.hist = SOME w], else Num 0; ffi_next replays and calls l0_ffi_fn; no choice fn encoded):
  built: l0_reach_init, l0_reach_step, enc_hist_11, dec_hist_enc, names_apply/lookup/update, l0_next_return/diverge.
  l0_parts_ok: last checked build failed only at the final step (the state var is named w, not x); fixed in 4645f7765
  by `qpat_assum ‘l0_reach w0 _’ (strip_assume_tac o REWRITE_RULE [l0_reach_def])` — NOT yet build-checked.
- EXACT NEXT STEPS on the new machine:
  1. In the worktree (recreate if needed: git worktree add --no-checkout -b … ; sparse /async/ /.gitignore; copy
     async/holproject.toml from another worktree — it is gitignored and needed for CAKEMLDIR), build:
     cd async/honest-l0-cf && Holmake -j1 --noqof honestL0PartTheory.uo  → confirm l0_parts_ok saved (no ORACLE).
  2. honestL0Prog: CakeML module (as socket-v2-cf/socketV2Prog) with the 7 wrappers; confs/alens from
     honestL1Model (sys_accept/sys_recv/sys_send/sys_close/sys_poll, poll_conf) and honestL0World l0_call; 13-byte
     header decode (honestL0 dec_res / l0_res_of).
  3. honestL0Proof: an IO predicate L0_EV w0 w evs = one (FFI_part (l0_enc w0 w) (l0_next w0) l0_names evs)
     (+ l0_reach), and per-wrapper CF specs (as socketV2Proof); the semantics link uses l0_parts_ok.
  4. Then P2.
- The coordinator noted the encoding must be minimal + adequacy proved: l0_parts_ok IS that (it is parts_ok), and the
  encoding is not in the trusted surface (the statement is over l0_ffi w0). Mention l0_parts_ok in the PR note.

## Rules
- Holmake only via ~/.cache/orchestrator/holslot arch -arm64 /bin/zsh -lc 'timeout N ~/HOL/bin/Holmake -j1 X';
  REPL also via holslot. -j1, ≤1 hol-lsp (check footprint with top -o mem). Reaped for memory: report, don't restart.
- No cheats in pushed work (FAIL_TAC "WIP"). Merges only; no rebase/force-push. Kill only own PIDs.
  Never Holmake in base ~/Programming/cakeml. Temp files in $CLAUDE_JOB_DIR/tmp.
- Commit trailer Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>; PR footer 🤖 Generated with [Claude Code](https://claude.com/claude-code).
- PR per green milestone; message coordinator at milestones or when blocked. Statements to the user BEFORE proofs.
- Keep stable (others depend): kv_server, kv_server_uses_ok, kv_comp_safe (+ lemmas), kv_server_spec,
  kserver_with_k_spec, with_store_spec, kv_delta_al_DELTA (close-v2, moonshot).

## Tools (~/.cache/kv-worker/tools)
rp.py, step2.py (top-level stepping script from a dumped heap; NB `e` applies to the FIRST goal only, so combinator
chains across Induct/Cases must be replayed as one e(...)), dbg.py (replay to step N + extra text), concl.py.

## Gotchas
- HOL prints the CURRENT goal LAST. simp eagerly uses var=term assumptions: orient facts term=var.
- simp discharges an mp_tac'd antecedent from the assumptions and DROPS the fact: use MATCH_MP / ACCEPT_TAC instead.
- qspecl_then on a polymorphic lemma can clash type vars with the goal's: rename apart (fresh_tys in asyncWithStoreSpec),
  excluding 'ffi. Q.ISPEC parses without goal context: annotate types.
- `t1 >- t2` applies t2 to the FIRST goal of all t1 produces (after Induct: TRY (... >> NO_TAC) instead).
- CakeML evaluates constructor arguments right to left. `let v = Con` needs xlet before the final xcon.
- dimword(:64) gets evaluated in goals but not always in assumptions: use fs[] to normalise both.
- IS_PREFIX_TRANS subgoal order is unpredictable; zsh `$b:a` is a path modifier (quote "${b}:path").
- Worktrees need async/holproject.toml (gitignored).
