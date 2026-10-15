# Handoff: actions and responses in the CF layer (spike/cf-actions)

Kept current at every commit. A fresh agent should be able to continue from
this file plus the coordinator's original brief.

## Where things are

- Worktree: `~/Programming/cakeml-worktrees/cf-actions`, branch
  `spike/cf-actions`. It is sparse (only `async/`) and was created with
  `async/design/new-experiment-worktree.sh` from `origin/spike/cf-loop`, then
  `origin/spike/async-level2` (the HOL model) was merged in (clean merge).
- New work: `async/cf-actions/` (its Holmakefile INCLUDES `../model` and
  `../cf-spike`):
  - `asyncCfActModelScript.sml`: pure HOL. One lemma per implementation
    step: what `suspended (...) [w]` is for finished/wait/emit/bind, plus
    the helpers `prepend` and `skipping` for bind's finished case.
  - `asyncCfActProgScript.sml`: the CakeML code (`step` datatype, `return`,
    `poll`, `wait`, `never`, `emit`, `skip`, `bind`), the predicates
    `SNAPSHOT`, `POLL_RESULT`, `STEPA` (coinductive), `COMP`, the
    approximations `STEPAn` and the limit lemma `app_COMP_of_approx`.
  - `asyncCfActSpecScript.sml`: the CF specs (in progress).
- Docs: this file; `async/design/05-cf-actions.md` (to be written).

## Representation (decided, see the comment at the top of asyncCfActProg)

```
datatype ('act,'w,'a) step = Done 'a | Pending ('w -> 'act list * ('act,'w,'a) step)
```
A computation value is a pair `(acts, s)`: the actions of its current
round and its residual. `COMP p ACT RES WORLD m (acts, s)` holds when
`acts = (m []).actions` and `STEPA ... m s`, where `STEPA`'s Pending case
says that `k w` returns a pair implementing `suspended m [w]` (the model's
own "m with w delivered"). So each poll emits exactly the model's
`new_actions` (lemma `suspended_one_actions_NIL`; for iterated polls
`suspended_suspended_one` + the model's `suspended_first_poll`, both need `wf m`).
Snapshots are CakeML triples `(ready, now, results)` (`SNAPSHOT READY R`).

## Status

- DONE: all model lemmas, including `suspended_bind` (needs `wf m`).
- DONE: `STEPA`, `COMP`, `STEPAn`, `app_COMP_of_approx`, `STEPA_prepend`.
- DONE: `return_spec`.
- TODO next: `poll_spec`, `wait_spec(_n)`, `never_spec`, `emit_spec`,
  `skip_spec`, `bind_spec(_n)`; then the event loop (step 4) and 05-cf-actions.md.

## Plan for the event loop (step 4)

One self-contained FFI part with names `act` and `ready` over one `Stream`
of bytes (an oblivious world): `act` sends the action byte in a 1-byte
buffer and gets the response byte back; `ready` returns one byte, the
snapshot's ready set `{b}`; `now` is 0. Loop:
`step (acts, s) = poll (acts, s) (ready_byte, 0, perform acts)`,
`run c = run (step c)`. The trace is `LFLATTEN` of per-round events, and a
pure corollary says that the actions in the first n+1 rounds are
`(m h_n).actions` for the world-induced history `h_n`.

## Assumptions made (so far)

1. Poll results are `(actions, residual)` pairs, and `Done` carries no
   actions (the pair does). This is the form closest to the model's `outcome`.
2. Specs that need the model's log to grow (bind, the loop) assume `wf m`,
   which every library computation satisfies.
3. `skip k s` always wraps the residual (even when k = 0). This is simpler
   to verify, at the cost of one closure per finished bind.

## Conventions

As in HANDOFF-cf.md: never Holmake in the base; `-j2` at most; kill only
by recorded PID; no cheats in commits.

## Tool feedback

- After building ancestor theories with Holmake, `retryCompile` in hol-lsp
  failed with `target theory "asyncCore" is sealed; cross-theory mints are
  refused`. `restart` fixed it.
- `S` (as a variable name) is the S combinator: type errors far from the cause
  (cf. `W` in HANDOFF-cf.md).
