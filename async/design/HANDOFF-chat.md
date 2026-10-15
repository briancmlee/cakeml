# HANDOFF: verified chat server (moonshot worker)

Kept current at every push. Worker state: ~/.cache/moonshot/STATE.md; log ~/.cache/moonshot/TRAJECTORY.md.

## Where things are
- Worktree `~/Programming/cakeml-worktrees/chat` (sparse), base `spike/http-kv-impl` (7d91ee53c).
- M1 (spec): `async/spec/ChatSpecScript.sml` (trusted), `async/spec/ChatSpecBiteScript.sml` (bites, all proved).
- Design note: `async/design/40-chat.md` (decisions D1–D8 with rationale).
- M2 (model): `async/chat/` asyncWithTap, asyncChatSW, asyncChatModel, asyncChatSafe (branch spike/chat-model, PR #72).
- M3 (CakeML + whole program): `async/chat/` asyncWithTapStep, asyncChatSockModel, asyncChatProg (code),
  asyncChatSpec (CF), asyncChatTrace (trace bridge to ChatSpec), asyncChatMain (main + sexp export),
  asyncChatSemantics (whole-program), asyncChatHeadline (chat_prog_safe). Branch spike/chat-cakeml.

## Build
`cd async/spec && ~/.cache/orchestrator/holslot timeout 3000 arch -arm64 /bin/zsh -lc '~/HOL/bin/Holmake -j1 ChatSpecBiteTheory.uo'`
`cd async/chat && ~/.cache/orchestrator/holslot timeout 3000 arch -arm64 /bin/zsh -lc '~/HOL/bin/Holmake -j1 asyncChatHeadlineTheory.uo'`

## Status
- M1: ChatSpec + bites: GREEN (Holmake), no cheats. PR #66.
- M2: asyncWithTap (generic tap handler), asyncChatSW (copy of KV server_with_k, uses_accepted fixed), asyncChatModel, asyncChatSafe: GREEN. MAIN: chat_server_safe.
- M3: CF specs GREEN (asyncChatSpec 20/20); trace bridge asyncChatTrace 38/38 (lsp); Main/Semantics/Headline building.
- Next: M3 PR; M4 liveness via m4-server's server_v/wrap_ok (spike/server-v); M5 nc demo.

## Tool feedback
- holslot queue: the M1 build waited ~15 min for a slot (7–8 waiters); hol-lsp can't check a theory until its ancestors are Holmade in the same worktree.
- `simp` does not use assumptions (use `gvs`/`fs`, or `metis_tac`); SPLITP lemmas need `rich_listTheory.SPLITP` qualified in this context.
- CF: nested constructor patterns in CakeML (`Kvr (Lines s)`) block xmatch's case split: flatten to one constructor per match. Polymorphic basis functions (List.length) leave existentials at a free type variable: translate a monomorphic wrapper.
- `dimword(:64)` vs its numeral after simp is the main source of irule/qpat misses in bridge proofs; metis_tac[] with ~25 assumptions loops.
