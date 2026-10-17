# Handoff: HTTP key-value server (spike/http-kv-impl)

Kept current at every commit.

## Where things are
- Worktree `~/Programming/cakeml-worktrees/http-kv` (sparse). Branch
  `spike/http-kv-impl` = `spike/http-kv` (PR #52, the spec) + merges of
  `origin/spike/http-bodies` (latest: dbff85681, own header parser, #48/#54).
- Spec: `async/spec/HttpKvSpecScript.sml` (approved), bites `HttpKvSpecBite`.
- Notes: `async/design/30-http-kv.md` (§5: the with_store decision).
- Code: `async/http-kv/` (Holmakefile includes ../http-bodies etc.).

## Design (approved by the user)
Shared store as a pure effect handler: `with_store δ s0 m`. Its argument emits
`Sock a | Kv q`; it answers Kv itself, emits only socket actions. No REF.
The linearization point is the model round in which with_store answers. Real time
is from the first byte read.

## Theories (status)
| theory | content | status |
|---|---|---|
| asyncWithStore | with_store, inner_hist, wf/agree/new_actions/trans_with_store, kv_answers | PROVED (44/44 in hol-lsp; built by Holmake) |
| asyncKvOrder | earlier/is_order lemmas, started/answered, precedes_answered_started | PROVED (built) |
| asyncServerWithK | server_with with Sock/Kv tags; isolates_k, uses_accepted_k | isolates fixed in REPL (acceptedk_CONS); uses_accepted FAILS (next) |
| asyncWithStoreStep | inner_hist_CONS, with_store_suspended, relabel_with_store, prompt_with_store | inner_hist_CONS WIP (FAIL_TAC at the end) |
| asyncKvLabel | label, label_FILTER/requests, replies_label, commits_at_real_time | label_requests/replies_label fixed in REPL; rest unchecked |
| asyncKvHandler | kv_handler, kv_handler_serves | unchecked |
| asyncKvModel | kv_server, kv_server_uses_ok, kv_server_serves | unchecked |
| asyncKvTraceLemmas, asyncKvSafe | order construction, kv_comp_safe (MAIN, trace-level safety) | unchecked |
| asyncKvSockModel, asyncKvProg, asyncKvSpec | socket vocabulary; CakeML with_store/server/handler; CF specs | unchecked; kv_delta_al_DELTA is FAIL_TAC TODO |
| asyncKvMain, asyncKvSemantics, asyncKvHeadline | kv_prog, kv_semantics_prog, kv_prog_safe | unchecked |

No cheats anywhere; unfinished proofs are `FAIL_TAC "WIP"` / TODO.

## Next steps
1. inner_hist_CONS: finish the new_actions equality (goal after DROP_DROP_T:
   `new_actions (log_of m) (w'::(l++[x])) = DROP (L - |a0| + |a0|) (m (w'::(l++[x]))).actions`:
   use the LENGTH a0 ≤ ... fact, SUB_ADD, new_actions_SNOC on the left), then the
   store_answers equality (old version of the proof had it: log_new_actions + run_store_APPEND_FST).
2. server_with_k_uses_accepted: replay in REPL (heap dump name below).
3. Build -k up to asyncKvHeadline; fix; then liveness (port bodies MachineB/DrainB/LiveB + prompt_with_store).

## Gotchas
- HOL orders a datatype's type parameters alphabetically: `kres = SockR 'r | KvR 'b` is
  `('b,'r) kres`. Write `('b, response) kres`.
- Never REWRITE_TAC with `GSYM (EVAL “[] ++ [x]”)` or `GSYM APPEND` (loops). Use
  `ONCE_REWRITE_TAC[GSYM (CONJUNCT2 APPEND)]` or an explicit `‘w::(h++[x]) = (w::h)++[x]’`.
- Don't keep two-way equations as assumptions (simp loops): e.g. `(m' p).actions = DROP ..`
  together with `(m (w'::p)).actions = a0 ++ (m' p).actions`.
- `simp` rewrites with assumptions: use `qunabbrev_tac` + `irule` to keep a goal's shape.
- acceptedk on `p :: l`: use `Once acceptedk_CONS` (a simp rule would loop).
- REPL debugging: `holslot arch -arm64 zsh -lc "timeout 240 hol --holstate=<thy>.<thm>.dumpedheap < script"`;
  extra theories can be `load`ed in the REPL. Holmake timeouts: keep them short (a looping
  proof cost a 2.5 h slot).

## Tool feedback
- Two machine-wide holslot slots; a full -k build here waits 10–40 min for a slot.
