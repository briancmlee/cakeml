# HANDOFF: verified chat server (moonshot worker)

Kept current at every push. Worker state: ~/.cache/moonshot/STATE.md; log ~/.cache/moonshot/TRAJECTORY.md.

## Where things are
- Worktree `~/Programming/cakeml-worktrees/chat` (sparse), base `spike/http-kv-impl` (7d91ee53c).
- M1 (spec): `async/spec/ChatSpecScript.sml` (trusted), `async/spec/ChatSpecBiteScript.sml` (bites, all proved).
- Design note: `async/design/40-chat.md` (decisions D1–D8 with rationale).
- M2+ (model, WIP): `async/chat/` (not yet committed on spike/chat-spec).

## Build
`cd async/spec && ~/.cache/orchestrator/holslot timeout 3000 arch -arm64 /bin/zsh -lc '~/HOL/bin/Holmake -j1 ChatSpecBiteTheory.uo'`

## Status
- M1: ChatSpec + bites: GREEN (Holmake), no cheats.

## Tool feedback
- holslot queue: the M1 build waited ~1.5 h for a slot (7–8 waiters); hol-lsp can't check a theory until its ancestors are Holmade in the same worktree.
- `simp` does not use assumptions (use `gvs`/`fs`, or `metis_tac`); SPLITP lemmas need `rich_listTheory.SPLITP` qualified in this context.
