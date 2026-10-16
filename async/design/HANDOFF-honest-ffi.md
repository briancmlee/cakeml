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
