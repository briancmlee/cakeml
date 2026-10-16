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
