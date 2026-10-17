# 47. The echo on the kernel: liveness (PF trace)

Goal (coordinator, 2026-10-17): the liveness half of the echo's
`echo2_guar_l0` (L3-00's kernelStatements) for the prefetching-L1 echo:

    F1_io io ∧ F2 w0 ∧ accepts_below io ⇒ echo_live_l0 K w0 io ∧ conn_live_l0 w0 io

with `io` the PF echo's trace. That is honestEchoL0Main's
`echo_l0_run k w1`, the flattened `pround_evs` of the run
`(n2w k, echo_hw, interest [n2w k], srelabel (server k))`. The main form
keeps D16/D18's observed excuses (`ep_hard_err`, `accepts_fail_io`). The
strong corollary (HD16_io, H1_io, H3_io) comes after, if it is cheap.

Consumer: cf-actions' quiescence transfer, spike/l3-quiet
`honestL1BLive.echo_live_transfer`. It takes `echo_live_l0` on the PF trace
of a REINDEXED world (`reindex (btr …) w0`), so the theorem here is stated
for every L0 world `w0` under hypotheses that reindexing keeps.

Safety (`echo_l0_safe`) is the KV worker's (design/46), so nothing here
re-proves its invariants.

## Pieces

**A. The trace bridge (PF run ↔ io).** All model-level:
- `LPREFIX (fromList evs) io` ⇔ evs is a prefix of the run's events
  (`revs n`, through `pround_evs`). This needs `prounds_t = prounds` while
  `hdl_room` holds (the KV worker adds `prounds_t_prounds`), and `hdl_room`
  from `accepts_below`.
- `world_at w0 evs` is the run's world at the matching point (the L0 replay
  of the run's own calls; spike/l3-quiet `rplays` is the model).
- The readings of the trace:
  - `F1_io io ⇒ F1`;
  - `accepts_fail_io io ⇔ accepts_fail`;
  - `l0_accepted` and `l0_sent` against `rlog` / `pcm`;
  - `ep_open` / `ep_closed` against the fd's handle lifetime;
  - `ep_hard_err` against FReset in `rlog`.

**B. The echo's obligations.** S1, S2 and S3 for `srelabel (server k)`:
- S1: it is interested in its handles and the listener.
- S2: with an accept pending it accepts.
- S3: it consumes its input.

S4 is honest-ffi's: today S4, and S4w (derived, via `flush_progress`, from
moonshot step 8) once it is ready. Until then S4 stays an explicit
hypothesis.

**C. conn_live_l0.** From `live_conn_psk` (D18's three disjuncts) and A, B.
It needs no output-side progress, so it comes first.

**D. echo_live_l0.**
- Input: `live_data` / `live_data_psk_d16`. What reached the kernel's inbox
  reaches client j's data in `psk`, unless the episode ended; the hard-error
  end is `ep_hard_err`.
- The server: the v2 echo's liveness (`echo2_live`, echo-episodes) on `psk`.
  This needs `psk`'s `lifetime_fair` and its initial shape.
- Output: what the server wrote reaches the kernel. `honestL1PFOut` gives
  `sent ++ outbox = outgoing`, and the outbox must drain. That is
  `flush_progress` (honest-ffi, step 8, not proved yet), under F1, F2,
  `drains`, and D19's `hup_drains` after a hang-up.
- Close: on peer EOF the v2 echo closes (`echo2_closes`), and L1's close
  reaches the trace (`ep_closed`).

D's output half waits for honest-ffi's `flush_progress`. Everything else
is buildable now.

## Order

A (bridge) → B (S1–S3) → C (conn_live) → D input and server halves → D
output (after flush_progress) → corollary.
