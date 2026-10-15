# HANDOFF: Level 2 blocking (spike/l2-blocking)

Branch `spike/l2-blocking`, stacked on `spike/cfdiv-multipart` (PR #13), in
`~/Programming/cakeml-worktrees/ffi-spike`. `spike/cf-reactive` and
`spike/async-m2` are merged in (read-only use of async/model, cf-spike,
cf-actions). New code: `async/l2-blocking/` (INCLUDES ../model ../cf-spike
../cf-actions ../ffi-spike). Write-up to come: `async/design/14-l2-blocking.md`.

## State
- DONE, pushed `818b8c918` (green, no cheats):
  - `asyncL2BlkModel`: prepend2, skipping2, finished2, never2; one-poll
    lemmas suspended2_wait_on_NONE/SOME, suspended2_emit2_*, suspended2_never2,
    suspended2_prepend2/skipping2, bind2_finished, suspended2_bind2.
  - `asyncL2BlkProg`: datatype step2 (Done2 | Pending2 of events list * k),
    return2/poll2/interest/wait_on/never2/emit2/skip2/bind2; STEPA2, COMP2,
    EVLIST, approximations, app_COMP2_of_approx, STEPA2_prepend2.
  - `asyncL2BlkSpec`: CF specs for all eight functions.
- IN PROGRESS (uncommitted): `async/ffi-spike/ffiSpikeSocketSelectScript.sml`
  — sock_select model; sock_select_polls and sock_select_live need fixing
  (hol-lsp: THEN1 at line 57, `by` at line 76).
- NEXT: the blocking loop. Plan: new world in l2-blocking with FFI names
  act/ready/select over cf-actions' byte stream (select skips ready bytes
  not in the interest list; never found = FFIdiverge); brounds c ws n =
  (kept, full, pos); theorem kept = blocked skip_loop [] full and
  full = cf-actions' hist (erase c) ws M (via same_for_step), so by
  blocked_sound the blocking loop emits exactly the polling loop's actions;
  then CF bstep_spec/brun_spec (cfDiv one-part FLATTEN) under a named
  assumption select_live (select always finds a declared byte).
  Then 14-l2-blocking.md, PR (base spike/cfdiv-multipart).

## Tool feedback
- hol-lsp reports spurious failures ("fail", dest_some) on CF/translator
  files here; Holmake is the authority (print goals with a `show` tactic).
- Name clashes: `set` resolved to an oset type in this context (use
  LIST_TO_SET); EVENTS also clashed.
