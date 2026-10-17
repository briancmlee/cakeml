# Handoff: honest FFI (honest-ffi)

Write-up and decisions for review: `36-honest-ffi.md`. Status: **AUDIT + DESIGN done; STOPPED for user review** (D1–D8 in §9). Nothing implemented beyond statement drafts.

- Worktree `~/Programming/cakeml-worktrees/honest-ffi` (sparse `/async/`), branch `spike/honest-ffi` from `spike/endpoint-world` (722f909b1).
- Drafts in `async/honest-ffi/`:
  - `honestL0`: error codes, the 13-byte result header (`dec_enc_res`), revents (`byte_revents_revents_byte`), L0 result types;
  - `honestL1`: the L1 functional core (outbox, gone, round discipline, exhausted, poll set) in today's vocabulary. Proved: `write_simple`, `read_simple`, `accept_simple`, `poll_simple`, `stall_local`, `gone_is_eof`, `exhausted_quiet`.
  - 11 theorems; no cheats.
- No endpoint-world file was touched. close-v2 was told (and agreed) that §4.1 fixes the refused/error encoding; ping close-v2 once the user settles §4.1.

## How to build

    ~/.cache/orchestrator/holslot timeout 3000 arch -arm64 /bin/zsh -lc \
      "cd async/honest-ffi && ~/HOL/bin/Holmake -j1"

(seconds; ancestors only words/list/alist/mlstring/Marshalling)

## Next (after user decisions)

These are §8's phases: 1 the C (point (c) of §3.5 recommended), then 2 the tester (first confirm the platform claims of §4), 3 the L0 world, then 4–6 L1 + refinement.

## Tool feedback

- hol-lsp: a file whose ancestor theory isn't built yet is BLOCKED until you Holmake the ancestor and call retryCompile. That worked as documented.

## Implementation (from 2026-10-16; user decisions in design/36 §9)

Stacked branches (one worktree):
- `spike/honest-ffi`: design/36 + drafts. PR #94.
- `spike/honest-l0`: phase 1, the C `async/runnable/l0/socket_ffi_l0.c` (trusted, 130 code lines), plus harness and probes. PR #96.
- `spike/honest-l0-world`: phase 3 (+2b):
  - `async/honest-l0/`: `honestL0World` (trusted, standards-anchored with cited sections), `honestL0Rely` (trusted), `honestL0WorldProps` (16 theorems: buffer lengths, the rely kept along a run);
  - conformance tests `runnable/l0/tester/{l0check,probes,random_test,mutants,explain}.py`. `make conformance` in `runnable/l0`.

Results (macOS 26, arm64): probes 10/10 conform; random 100×200 (12146 calls) 0 findings / 0 warnings; mutants 8/8 caught. Three model gaps were found by the random test and fixed (design/36 §4.3). Linux is not run yet (no machine): a to-do, framed as a conformance check.

Gotchas:
- `closed` is a HOL constant (topology): don't use it as a variable name.
- l0check's state set grows with EMFILE branches; the cap is 4096 and it warns when reached.
- The child's pipes are fds 60/61; they are reserved fds (they count as used for fd numbering).

Next: phase 4, the L1 functional core (extend honestL1 to the L0 world, v2 only per D5), coordinated with close-v2's handle layer.

## Phase 4 (L1 core), branch spike/honest-l1 (on spike/honest-l0-world)

- `async/honest-l1/`: honestL1Model (L1 over L0, v2 only; follows asyncHLModel's handle layer, imported later), honestL1Props (8 theorems), honestL1Simple (simple0 + R3: write/read/accept_simple; 13 theorems). Holmake green; no cheats.
- close-v2: asyncHL* stays unchanged. The v2 targets are the generic proto server (asyncProtoServer.proto_server) on the handle loop, plus HTTP http_prog_pb2 → http_spec_b2 (design/43 on spike/http-v2-prog).
- Gotchas:
  - `GSYM APPEND_ASSOC` in simp loops;
  - a left-associated append can print exactly like a right-associated one (metis_tac[APPEND_ASSOC] closed it);
  - state hypotheses about fds as numerals (2147483648) for simp's if-conditions;
  - simp ignores ∀-hypotheses: use asm_simp_tac or state the instance.
- Next: fd-ownership invariant (lrun_ok), then R1/R2 vs asyncHLModel.

## Phase 4b (no failing L0 call), branch spike/honest-l1-inv (on spike/honest-l1)

- honestL1Inv (34 theorems): small_fds invariant; sys_*_ok; l1do_ok; l1round_ok; lrounds_ok; lrun_ok_thm (given l2_ok, which mirrors hrun_ok).
- Model change: polls are chunked (poll_chunks, ≤ 4096 entries per sys_poll): the C's MAX_FDS made a > 4096-fd poll a misuse.
- Gotchas:
  - `chunks` clashes with rich_list's `chunks` (the statement silently used the wrong constant): renamed to poll_chunks;
  - macOS sed has no \b;
  - `LENGTH acts + st.nxt` vs `st.nxt + LENGTH acts` blocks drule_all: restate the hypothesis.

## Phase 6 (R2: L1 refines asyncHLModel in simple worlds), branch spike/honest-refine (on spike/honest-l1-inv)

- This branch also merges origin/spike/v2-events @87cdc6733 (close-v2's light theory socketV2Events, which holds spoll2_event and close_event).
- `async/honest-l1/`:
  - honestL1Refine: l1v2_rel, core_rel, rdy_ok, drops support.
  - honestL1Steps: act_step and its per-action lemmas.
  - honestL1Round: acts_step, tail_step, round_step, hl_ok, polp_at, hround_SUC, and **l1_refines_hl** (R2).
  - Full Holmake is green; no cheats. Design/36 §6 has "R2, as built".
- Model change: poll_chunks always polls at least once per round (an empty interest still ticks the clock, as the handle layer's poll does).
- Findings:
  - the trace relation is `drops` (L1 deletes would-block events), not equality;
  - the discipline is tracked per polled (handle, fd) pair;
  - core_rel needed four extra invariants.
- Gotchas:
  - `GSYM MAP_APPEND` in simp loops, like GSYM APPEND_ASSOC. To find a looping tactic, run a holslot Holmake under `timeout 240` with printing progress markers (`fun MK s g = (print ...; ALL_TAC g)`), not the LSP.
  - Keep at most one hol-lsp and restart it between big checks: it sits outside the holslot limit.
  - `metis_tac[Abbrev_def]` on a big assumption set hangs. Substitute instead (SUBST1_TAC o SYM).
- Next:
  - R1: general worlds, with regrouping;
  - then sys_connect and its L1 wrapper (a moonshot dependency).

## Phase 7 (R1: the prefetching L1), branch spike/honest-r1 (on spike/honest-refine)

- Finding: R1 is false for the lazy L1 (design/36 §6, C1–C5). User decision D10: the prefetching L1 becomes THE L1, built additively.
- `async/honest-l1/`:
  - honestL1PFModel: the prefetching L1.
  - honestL1PFRefine: 104 theorems, including **l1pf_refines_hl** (R1-safe in any L0 world) and **psk_server_world** (the world built from L1's run satisfies server_world2). No cheats.
  - design/36 §6 has "R1-safe, as built".
- User decisions: D11 [F1] in the weak fairness form; D12 [F2]. Both are recorded in §4.2 and §9, and are used only by R1-live.
- Next:
  - R1-live (fetch completeness under [F1]/[F2]);
  - switch the servers over (L1 CakeML code for the PF model, its CF spec);
  - sys_connect.
- Gotchas:
  - In the LSP, the first start after a restart often fails with "theory honestL0 is sealed" (dependency loads fail). Restarting again fixes it.
  - The goal walker times out (10 s) on big proof states. Replacing `gvs[AllCaseEqs()]` with explicit Cases_on/PairCases_on keeps states small.
  - `simp` uses a kept assumption to rewrite an `mp_tac`'d copy of itself to T (`qpat_assum … mp_tac >> simp[Once def]` does nothing). Unfold a copy with ONCE_REWRITE_RULE instead.
  - `ASM_REWRITE_TAC` with a ∀-hypothesis also rewrites its own instance to T.
  - `rw` / `strip_tac` split goal conjunctions before `irule IH`, and then `irule` of the whole IH fails.
  - `metis_tac` looped (minutes, GBs) several times on big assumption sets. Prefer drule/qspecl_then.
  - `hst` and `o` are constants: do not use them as variable names.


## Machine move (2026-10-16): exact next steps

Branch tip spike/honest-connect. Decisions since the last section: D11′ ([F1] on observed outcomes; poll: any failure counts as retried), S4 with no-Write (approved text), l0wf/noconn w0 hypotheses OK. close-v2's PR #141 (Settle as an arrival) is approved; base E1 on spike/ep-settle @3c916c510.

   1. honest-l1/honestL1PFRoundScript.sml: live part proved (winv, winv_do, pend_do, ev_do, sys_winv, l1_close_f, fds_lt_call, l1_close_winv, l1_polls_winv...). WIP comment block at end holds: pdo_winv, pacts_winv, l1_flush_winv, l1_reap_winv, pf_fetch_winv (loop on 'TRY (metis_tac[])' — replace with targeted drule of sys_winv / IH), pround_winv, pend_recv_retried, pdo_f, pacts_f, l1_polls_f, l1_flush_f, l1_reap_f, pf_fetch_f, pround_f. Un-comment one at a time (replace '(-*' '*-)' back), prove, keep cheats out of commits.
   2. Run-level: winv along prun (needs l0wf w0 ∧ noconn w0 ∧ errb w0 hyps, + rely/fds_lt from l1pf_refines_hl); fkeep from pown/pl2_ok; revs prefix-monotone (prounds evs ++ revs).
   3. fetch_progress in honestL1PFLive (statement in comment; add hyps l0wf/noconn/errb w0 and fds_lt w0, MEM lfd used); proof: by contradiction, use pround_f each round + F1(poll,f) + F1(recv,f) + S1/S3/S4.
   4. Stream invariant, live-data (D16), live-conn ([F3]). Then E1 EP→endpointHL refinement on 3c916c510.
