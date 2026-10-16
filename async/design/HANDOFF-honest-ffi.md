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
