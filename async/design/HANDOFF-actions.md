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
  - `asyncCfActSpecScript.sml`: the CF specs.
  - `asyncCfActWorldScript.sml`: pure HOL: the FFI model, the snapshot
    sequence the world provides, and the trace/model link.
  - `asyncCfActLoopScript.sml`: the CakeML event loop and its cfDiv spec.
  - `asyncCfActBothModelScript.sml`, `asyncCfActBothScript.sml`: `both`.
- Docs: this file; `async/design/05-cf-actions.md` (the write-up).

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
- DONE (`asyncCfActSpecScript.sml`): `return_spec`, `poll_spec`,
  `wait_spec` (via `wait_spec_n`), `never_spec`, `emit_spec`, `skip_spec`,
  `bind_Done_spec_n`, `bind_spec` (via `bind_spec_n`). Step 2 is complete.
- DONE (step 4, `asyncCfActWorldScript.sml` + `asyncCfActLoopScript.sml`):
  FFI model (`act`/`ready` over one byte stream), `rounds`/`hist`/
  `round_events`, `trace_actions_rounds` (MAIN: the trace's actions are
  the model's log after the world's snapshots), `do_act_spec`,
  `perform_spec`, `get_ready_spec`, `step_spec`, `run_spec` (MAIN: the loop
  diverges with trace `LFLATTEN (LGENLIST (λi. fromList (round_events m ws i)) NONE)`).
- DONE (step 3, part): `both`. `asyncCfActBothModelScript.sml`
  (`suspended_both`, from the model's `both_split`; `both_finished_finished`)
  and `asyncCfActBothScript.sml` (CakeML `both`, `both_spec_n`, `both_spec`).
- NOT DONE: `choose` (estimated and deferred, see 05-cf-actions.md).
- DONE: `05-cf-actions.md` (the write-up, with estimates and assumptions).
- Next for the project: `choose` (estimate in 05 §4), then the M2
  scheduler, Level 2, a non-oblivious world.

## Plan for the event loop (step 4)

One self-contained FFI part with names `act` and `ready` over one `Stream`
of bytes (an oblivious world): `act` sends the action byte in a 1-byte
buffer and gets the response byte back; `ready` returns one byte, the
snapshot's ready set `{b}`; `now` is 0. Loop:
`step (acts, s) = poll (acts, s) (ready_byte, 0, perform acts)`,
`run c = run (step c)`. The trace is `LFLATTEN` of per-round events, and a
pure corollary says that the actions in the first n+1 rounds are
`(m h_n).actions` for the world-induced history `h_n`.

## Assumptions made

The full list (10 items) is in `05-cf-actions.md` §5. In short:
`(actions, residual)` pairs; the general (not settled-only) representation
with `skip`; `skip` always wraps; `wf` as an explicit hypothesis; snapshots
as triples; a byte-stream world (oblivious, `now = 0`, ready set `{b}`);
the loop polls `Done` forever; `both` exactly as the model; the loop
before `both`; seven small theories.

## Conventions

As in HANDOFF-cf.md: never Holmake in the base; `-j2` at most; kill only
by recorded PID; no cheats in commits.

## Tool feedback

- `xcf_div` + `xapp` worked in hol-lsp this time (unlike in HANDOFF-cf.md),
  maybe because the step function's spec was used via `xapp_spec` on an
  assumption, or because of the basis heap.
- Debugging tactics stored in SML `val`s is painful: an error inside
  `FIRST [t1, t2]` or a tactic function is reported at the theorem's first
  line, and goalState can't look inside. I inlined the tactic temporarily to
  step through it. A "goal state at the failing step of a named tactic" view
  would help.
- `K` is the K combinator (an `Abbr ‘K’` failed with "Ill-formed quotation").
- BSD `sed -E` has no `\b`; a rename of `IO` (which clashes with the
  basis's `IO`) silently missed the definition label. Not a HOL issue.

- After building ancestor theories with Holmake, `retryCompile` in hol-lsp
  failed with `target theory "asyncCore" is sealed; cross-theory mints are
  refused`. `restart` fixed it.
- `imp_res_tac` with a polymorphic lemma leaves a type variable fixed in the
  new assumption, unrelated to the goal's (e.g. the action type of `emit`),
  so `simp` silently doesn't use it. Fix: `‘...’ by metis_tac[lemma]`.
- The Holmakefile now uses `HOLHEAP = $(CAKEMLDIR)/basis/basis-heap` (the
  coordinator's tip, from CONVENTIONS.md); hol-lsp restarts are much faster.
- `S` (as a variable name) is the S combinator: type errors far from the cause
  (cf. `W` in HANDOFF-cf.md).

## Final report (2026-10-15)

- **PR:** https://github.com/briancmlee/cakeml/pull/10 (spike/cf-actions → spike/cf-loop;
  it also merges spike/async-level2, so the diff includes the model).
- **Representation:** a computation value is the pair `(acts, residual)`, with
  `datatype step = Done 'a | Pending ('w -> 'act list * step)`.
  Snapshots are triples `(ready, now, results)`. `STEPA`/`COMP` relate
  values to the model's own `suspended m [w]` and `finished A x`, so each
  poll emits exactly the model's `new_actions`.
- **Proved** (no cheats, Holmake green): model step lemmas (incl.
  `suspended_bind`, `suspended_both`); CF specs `return_spec`, `poll_spec`,
  `wait_spec`, `never_spec`, `emit_spec`, `skip_spec`, `bind_spec`, `both_spec`.
- **Event loop:** fully connected for a restricted world. `run_spec` (cfDiv:
  diverges, trace = LFLATTEN of `round_events m ws i`) plus
  `trace_actions_rounds` (the trace's actions in rounds 0..n =
  `(m (hist m ws n)).actions`). The world: bytes, an oblivious response stream,
  `now = 0`, ready set `{b}`.
- **Not done:** `choose` (estimated at 300–450 lines). Estimates for the
  M2 scheduler (~400–600) and Level 2 (~600) are in 05 §4.
- **Tools:** hol-lsp MCP tools were available and used throughout
  (diagnostics, goalState, eval, restart, retryCompile). `xcf_div` + `xapp`
  worked in hol-lsp this time.
- **Assumptions:** see 05-cf-actions.md §5 (10 items).
