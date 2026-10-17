# L3-09: quiet_on_kernel for the blocking L1 (honest-l1b, honest-l1b-cf)

Branch `spike/l3-quiet`. Worker: cf-actions. Everything listed here is built
with holslot `Holmake -j1` and has no cheats.

- `honest-l1b/`: the blocking L1 model, its refinement of the PF L1, and the transfers.
- `honest-l1b-cf/`: the blocking L1 in CakeML, the echo program, and the instance.

## The chain

| Step | Theorem | File |
|---|---|---|
| Model: S1 + S3 + S4′ | `l1b_quiet` | honest-l1b/honestL1BQuietScript.sml |
| (S1) never fails | `brounds_ok` | honest-l1b/honestL1BNoFailScript.sml |
| Refinement blocking ⇒ PF | `l1b_refines_pf`, `b2p` | honest-l1b/honestL1BSimScript.sml, honestL1BCorrScript.sml |
| (S3) guarantee transfer | `echo2_guar_transfer_full` | honest-l1b/honestL1BTimeoutScript.sml |
| (S4) PF run settles, given SQ | `l1pf_stable` (`SQ_def`) | honest-l1b/honestL1BStableScript.sml |
| (S4′) blocking run sleeps | `l1b_sleeps` | honest-l1b/honestL1BSleepScript.sml |
| CakeML step / loop | `step_pfb_spec`, `step_pfb_sleep_spec`, `run_pfb_div_spec`, `run_pfb_sleep_spec` | honest-l1b-cf/honestL1BSpecScript.sml |
| CakeML trace = model trace | `div_btrace`, `sleep_btrace`, `bt_guard_ok`, `pf_trace_exists` | honest-l1b-cf/honestL1BTraceScript.sml |
| Program semantics (fail / Diverge / FFI_diverged) | `echo_l0b_semantics_prog` | honest-l1b-cf/honestEchoL0BSemScript.sml |
| Across the leading listen | `echo2_guar_shift`, `sys_listen_echo_shift` | honest-l1b/honestL1BShiftScript.sml |
| **Instance** | `echo_l0b_quiet` (L3-00's `quiet_on_kernel_claim`, with D29), `echo_l0b_quiet_a` (the same, kept as an alias) | honest-l1b-cf/honestEchoL0BQuietScript.sml |

## Premises of `echo_l0b_quiet`: `echo_pf_facts KK k w1`

These are stated in the PF world `epfw k w1 = reindex (btr …) w1`, for
listener k.

| Conjunct | Owner | Status |
|---|---|---|
| `run_ok`, `winv`, `linv`, `qfresh`, `MEM lfd (l0_used …)`, pcm bound | async-spike / honest-ffi (PF standing facts; design/47 for reindexing) | open |
| `S1`, `S2` | async-spike (`S1_interest`, `echo_S2`) | available for `interest`; needs re-pointing to `epfw` |
| `SQ` | cf-actions | partial, see below |
| `flush_ok` (D32's excuse, PF ⇒ blocking) | cf-actions; needs the PF invariant "L1 owns every open fd it opened" (honest-ffi, queued) | open, see below |
| `∀io_p. ptrace … io_p ⇒ echo2_guar_l0 KK (epfw k w1) io_p` | async-spike (liveness), KV worker (safety) | open |

These are already discharged, so they are no longer premises:
- `bquiet`: `echo_bquiet` (honest-l1b-cf/honestEchoL0BStutterScript.sml);
- `l0wf` and `lone` after the listen: `listen_l0wf`, `listen_lone` (honestEchoL0BQuietScript.sml).

### SQ status

| Part | Theorem | File |
|---|---|---|
| Drain (independent of (C)) | `pf_drain`, `pf_drain_read`, `echo_drain` | honest-l1b/honestL1BQuietDrainScript.sml, honestL1BEofCloseScript.sml, honest-l1b-cf/honestEchoL0BDrainScript.sml |
| Echo silent when nothing is ready | `server_settles` | honest-l1b-cf/honestEchoQuiesceScript.sml |
| End-of-file read-soon (M4) | `read_soon_eof_s` | m4-liveness/asyncM4ReadSoonEofScript.sml (lifted to PF by async-spike: honest-echo-live/honestEchoL0EofRead `echo_read_soon_eof`) |
| Drained ⇒ nothing ready | `live_held` (honest-ffi @c837d1a91), then re-point the chain to `live` | in progress (D26) |

## Copies and placement at the fold

| Item | Kind | At the fold |
|---|---|---|
| honest-l1b/honestL1BStmtsScript.sml | verbatim copy of L3-00 @ad23dafc5 | replace with L3-00's file |
| m4-liveness/asyncM4ReadSoonEofScript.sml | mine; async-spike carries a verbatim copy | keep one copy (mine) and drop theirs |
| honestL1BShift | shared with async-spike's program-level assembly | keep in honest-l1b, or move next to L3-00 |
| honestEchoL0BStutter (`stut_at`, combinator lemmas), honestEchoQuiesce (`settles`, combinator lemmas) | generic model lemmas plus echo instances | generic parts → model/ or m4-common/; echo parts stay |
| honestL1BQuietDrain, honestL1BEofClose | PF-model facts | could move to honest-l1 |

## Rulings applied

| Ruling | Where |
|---|---|
| D27: close call, not a successful close | `close_call_transfer` (honestL1BLive), `echo_live_shift` (honestL1BShift) |
| D29 = #3 = decision 9: handle cut-off excuse | in L3-00's claim; `echo_l0b_quiet` proves it |
| D32 (narrows D28): `flushed_open` excuse | `flushed_open_shift`; transfer is the premise `flush_ok` (honestL1BLive) |
| D26 = (C) = decision 13: live interest lists | m4-common/asyncM4LiveInterest (d3b6d0dd5); `echo_bquiet_live` (c27f90155); S1_live / live_held: honest-ffi @c837d1a91 |

### flush_ok plan

1. A broken channel with an empty inbox stays so under every L0 step.
2. PF prefix aligned with a blocking round, or mid-idle with the blocking poll waking later: reachability, by 1.
3. Mid-idle, blocking poll never wakes: impossible while the episode is open. Its fd is owned by L1 (needs used ⇒ owned), its handle is live (S1), and in an idle round wants_input holds, so it is polled for IN; a break sets rin.
