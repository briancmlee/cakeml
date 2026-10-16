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
- M3: PR #75 GREEN (chat_prog_safe). M5: PR #76 (demo + design/41 write-up).
- M4 DONE (spike/chat-live, 76b822420): chat_prog_spec : chat_spec 3w chat_prog (asyncChatLiveHeadline), Holmake GREEN, no cheats.
  Clause 2: asyncChatLiveRead/Reads/ReadRun (chat_live_reads). Files from before: asyncChatLiveV (library instance), asyncServerVPushLive (generic push
  liveness, for the library), asyncChatLiveAccept (clause 1: chat_live_accepts), asyncChatLiveDeliver/Cover/Glue/
  CoverRun/DeliverRun (clause 3: chat_live_deliver).

## Tool feedback
- An Overload name that is not in scope (CWr/CIn from a non-ancestor theory) silently parses as a free variable; library side conditions then fail for no visible reason.
- holslot queue: the M1 build waited ~15 min for a slot (7–8 waiters); hol-lsp can't check a theory until its ancestors are Holmade in the same worktree.
- `simp` DOES use assumptions (asm_simp): in long proofs it rewrites with context equations — orient them towards abbreviations; SPLITP lemmas need `rich_listTheory.SPLITP` qualified in this context.
- CF: nested constructor patterns in CakeML (`Kvr (Lines s)`) block xmatch's case split: flatten to one constructor per match. Polymorphic basis functions (List.length) leave existentials at a free type variable: translate a monomorphic wrapper.
- `dimword(:64)` vs its numeral after simp is the main source of irule/qpat misses in bridge proofs; metis_tac[] with ~25 assumptions loops.

## Translator prototype (PR #114, spike/async-translate)
- `async/translate/`: asyncTranslate (lemmas), asyncTranslateLib (generator + proof tactic + define_async), asyncTranslateEcho (demo). Design: design/44-async-translator.md.
- Build: `cd async/translate && ~/.cache/orchestrator/holslot timeout 3000 arch -arm64 /bin/zsh -lc '~/HOL/bin/Holmake -j1 asyncTranslateEchoTheory.uo'` (~3 min).
- Phase 2 (PR #130, spike/async-translate-proto, worktree ~/Programming/cakeml-worktrees/translate-proto on close-v2's chain): socket library wrappers, generated proto handler, http_prog_gpb_spec. Build: `cd async/translate && holslot … Holmake -j1 asyncTranslateHttpBTheory.uo`.
