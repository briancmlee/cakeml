# Handoff: M4 step 1, the concurrent echo server in CakeML (spike/m4-server)

Kept current at every commit.

## Where things are

- Worktree `~/Programming/cakeml-worktrees/m4-server`, branch
  `spike/m4-server`, from `spike/cf-reactive` (ea445fa7e), with
  `origin/spike/async-echo-server` merged in (no conflicts).
  PR base: `spike/cf-reactive`.
- New work: `async/m4-server/` (INCLUDES model, cf-spike, cf-actions;
  basis heap).
  - `asyncM4ApproxScript.sml`: depth-indexed approximation `STEPAd`/`COMPd`
    (shape fixed at depth 0), limit lemma `app_COMP_of_approxd`, and
    depth-n specs: `poll_spec_d`, `skip_spec_d`, `bind_spec_d`
    (nonexpansive), `bind_guarded_spec_0/_d` (guarded: gains one level),
    `both_spec_d`.
  - `asyncM4ServerProgScript.sml`: model types as CakeML datatypes
    (`register_type`), `has_readable`, `EVENTS`, the CakeML code
    (`readable`, `map`, `handler`, `server`), `readable_spec`, `map_spec_d`.
  - TODO `asyncM4ServerSpecScript.sml`: `handler_spec`, `server_spec`
    (MAIN), by induction on the depth with `bind_guarded_spec_d` at the
    outer bind and `app_COMP_of_approxd`.

## Status

- WIP (2026-10-15, paused for usage limit): asyncM4Approx being debugged
  with hol-lsp; first group of proofs just rewritten (STEPAd_SUC_IMP,
  STEPA_IMP_STEPAd, STEPAd_IMP_STEPAn, app_COMP_of_approxd), the rest
  (prepend, poll, skip, bind*, both) still failing. Not built green, not
  pushed.
- Next: fix asyncM4Approx, then ServerProg, then ServerSpec; then task 3
  (relabel adapter to M3's `sact`/`sresp` vocabulary; `srun_ok` discharge,
  per the coordinator's request) and 15-m4-server.md.

## Assumptions made (so far)

1. The CakeML server uses the model's own vocabulary (`event`, `action`,
   `response` of asyncServer) as CakeML datatypes; the ready set is a
   CakeML list of events. M3 (spike/m3-assembly) uses a different socket
   vocabulary (`sact`/`sresp`, word64 fds, ready set of fds); the bridge is
   an adapter (task 3), not a change to the model.
2. Recursion is proved with a new depth-indexed approximation (STEPAd)
   rather than cf-actions' STEPAn, because STEPAn 0 = T is too weak for
   code that inspects residuals (bind's case split, skip, both).

## Tool feedback

- (none yet)
