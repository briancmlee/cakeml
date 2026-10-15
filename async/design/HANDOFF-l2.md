# HANDOFF: Level 2 blocking (spike/l2-blocking)

Branch `spike/l2-blocking`, stacked on `spike/cfdiv-multipart` (PR #13), in
`~/Programming/cakeml-worktrees/ffi-spike`. `spike/cf-reactive` and
`spike/async-m2` are merged in (read-only use of async/model, cf-spike,
cf-actions). New code: `async/l2-blocking/` (INCLUDES ../model ../cf-spike
../cf-actions ../ffi-spike). Write-up to come: `async/design/14-l2-blocking.md`.

## State
- DONE, all pushed (green, no cheats): Level 2 CF (`asyncL2BlkModel/Prog/Spec`),
  blocking world (`asyncL2BlkWorld`: brounds, blocking_same_actions),
  FFI (`asyncL2BlkFfi`: select, trace_actions_brounds), loop
  (`asyncL2BlkLoop`: bselect_spec, bstep_spec, brun_spec,
  blocking_trace_same_actions), socket select (`ffiSpikeSocketSelect`).
- Write-up `14-l2-blocking.md`; PR opened (see Report).
- NEXT (queued by coordinator): blocking version of async-spike's
  dynamic-interest loop (spike/m4-liveness), transfer echo_safe/echo_live;
  replace blk_live by a two-outcome theorem if possible (§3a).

## Tool feedback
- hol-lsp reports spurious failures ("fail", dest_some) on CF/translator
  files here; Holmake is the authority (print goals with a `show` tactic).
- Name clashes: `set` resolved to an oset type in this context (use
  LIST_TO_SET); EVENTS also clashed.
- `qabbrev_tac ‘j = …’` silently misbehaved because `j` was already a free
  variable (from an existential hypothesis); and an abbreviation `k = 0`
  made simp fold every literal 0 into `k` and loop.
- `io2_update`'s byte type was polymorphic in a `by` statement (`[0w]`
  without annotation), so the assumption never matched the goal.
- Debugging CF proofs: hol-lsp was unreliable on translator/CF files; I
  used Holmake plus a `show` tactic printing goals, and replayed steps in
  the dumped heap (`hol --holstate=…dumpedheap`) with `proofManagerLib`.

## Report
- PR: https://github.com/briancmlee/cakeml/pull/21 (base spike/cfdiv-multipart).
