# HANDOFF: the blocking echo program (spike/m4-blocking)

The write-up is `async/design/17-m4-blocking.md`.

## State

- Branch `spike/m4-blocking`, pushed, stacked on `spike/l2-blocking`
  (PR #21). It merges `origin/spike/m4-liveness` (ff5f483c0) and
  `origin/spike/m4-safety` (a902db27d) read-only.
- `async/m4-blocking/` holds 5 theories:
  - World: bgrounds, the invariant, the two outcomes;
  - Trace: unwaited traces, echo_safe/echo_live transfer;
  - Echo: idle_quiet discharged for the server;
  - Loop: CF code and specs, SSEL part;
  - Main: the program, the sockets+select oracle, semantics.
- `Holmake -j2` in `async/m4-blocking` is green. There are no cheats
  (`grep cheat` is empty).
- Headline: `asyncM4BlkMain.echo_blocking_spec`. Its only hypotheses are
  the initial world; there is no blk_live and no idle_quiet.
- EchoSpec is untouched. Whether to amend it is the user's call (17 §7).

## Next steps (if continued)

1. Combine with the polling liveness (`echo_live` for `poll_io`) once
   async-spike lands it. The blocking liveness is then unconditional.
2. Optionally remove `blk_live` from `async/l2-blocking`, using the same
   two-outcome structure. Do this on a new stacked branch, because PR #21
   is under review.
3. If EchoSpec is amended (option b), restate `echo_blocking_spec`
   against the amended `socket_ffi`. `ssel_ffi` is the intended shape.

## Tool feedback

- `Q.INST` cannot instantiate a variable whose type contains type
  variables fixed in the theorem ("No consistent parse"). Use
  `irule`/`MATCH_MP`, or a `suffices_by` that matches the conclusion.
- In CF, a POSTf spec for an FFI call that diverges must keep the call's
  buffer. `xsimpl` cannot drop a `W8ARRAY` into garbage on the POSTf
  side, so the posts carry `SEP_EXISTS av. W8ARRAY av []`.
- `xlet_auto` fails with "rewr_head_conv" or "Not a cf_let" when the goal
  is a POSTf. Use an explicit `xlet`.
- `xapp_spec` against an app whose argument is a `v` bound by an earlier
  `xlet` fails with "Could not apply specification". Substitute first
  (`rveq`, or `qpat_x_assum ‘v = _’ SUBST_ALL_TAC`).
- `drule_all` with a lemma about `bgrounds … n` picked the
  `bgrounds … (SUC i)` assumption, silently. Pin it with
  `irule … >> metis_tac[]`.
- Python heredocs with `'\\ '` produce a single backslash. Use raw
  strings, or copy the proof text from files.
- REPL replay in dumped heaps (`hol --holstate=…`), with
  `proofManagerLib.g/e`, was again the fastest way to debug.
  `DB.fetch "<thy>"` works for the current theory's definitions there;
  `fetch "-"` does not.
- In theories that see EchoSpec/HttpSpec, `bytes` is a constant. Do not
  use it as a variable name.
