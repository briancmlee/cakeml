# 49 — D25 cut-off, option (b): stop accepting, keep serving

Status: ESTIMATE for the user. No code.
Author: honest-ffi, 2026-10-17. Base: spike/l3-quiet @c27f90155.

## Today (D25)

- The model `prounds` has no cut-off. `pdo`'s Accept (honest-l1/honestL1PFModelScript.sml:107-120)
  fails (`NONE`, misuse) when `l1hdln (w2n lfd) nxt` is no longer below `dimword (:64)`.
- The PF proofs assume this never happens. `pl2_ok` (honestL1PFInvScript.sml:187, inside
  `run_ok`) asserts, for every round, `nxt + naccepts acts < dimword (:64)`.
- The CakeML loop has the cut-off as a whole-round guard. `step_pf`
  (honest-l1-cf/honestL1PFProgScript.sml:549-556) is "if not hdl_room then st else …", so at
  the cut-off `run_pf` spins without I/O, and existing connections stop being served.
  - The specs model this with `prounds_t` (honestL1PFSpecScript.sml:475) and
    `step_pf_stop_spec` (:455). `prounds_t_prounds` (:568) shows that `prounds_t` equals
    `prounds` while every round had room.
  - honest-l1b-cf has the same guard (honestL1BProgScript.sml:71).
- At L0 the cut-off is the `accepts_below io` hypothesis (`< 2^64 − 1` accepts on every
  prefix). It appears in `echo_conn_live_trace`, `l0_echo2_claim` / `_strong_claim`, and
  `echo2_guar_l0`, and as the `¬accepts_below` excuse of the quiet claim.
  `echo_guard_stop` (honestEchoL0NoGuard:379) is the only theorem about the cut-off firing.

## Option (b): the model change

1. **pdo's Accept without room** returns `Accepted NONE` with the state unchanged and
   **no sys_accept**, instead of `NONE`. To the server this is just "no connection yet",
   which every server already handles.
2. **L1 stops polling lfd without room.** The poll set drops lfd, so pending connections
   don't wake the loop on every round. Otherwise the loop busy-polls and the quiet property
   fails.
   - Also L1 must stop prefetching. A connection already prefetched into `acq` at
     nxt = 2^64 − 1 (the NoGuard header's case) is either closed (the client sees EOF) or
     held for ever. Recommend: never prefetch past the last handle, so `acq` is empty at
     the cut-off.
3. `pl2_ok` drops its room conjunct (it keeps `pact_ok`). `pround_ok` drops its room
   hypothesis. **A round never fails for lack of room.**
4. The CakeML loop: `step_pf` loses its guard. `prounds_t` becomes `prounds`, so
   `step_pf_stop_spec`, `prun_SUC`'s case split and `prounds_t_prounds` go away. The L1
   CakeML code for Accept gets the room test, with its CF branch.

## What it does to the results

- **Safety.** The `< 2^64 − 1` accept bound in `echo_safe_l0`, `honestHttpKvL0Spec` and the
  L3-00 statements becomes a theorem (no accepts happen past the cut-off), so it can leave
  the statements. `echo_l0_safe_ng` (bound already dropped) becomes the main form.
- **R1 liveness (`live_conn`, ConnRun:502 and its corollaries).** `run_ok` no longer
  promises room for ever, so `live_conn` (a pending connection is eventually resolved ∨
  `accepts_fail`) needs an excuse.
  - The excuse is "the handles ran out": the observed L1 state, or at L0 `¬accepts_below`.
  - Connection-level liveness (data, flush, EOF, the D16/D23 clauses) **no longer needs any
    room assumption**. This is the point of (b): existing connections keep being served.
  - The client bound `∀n. SND (pcm …) + 1 < dimword (:64)` is unrelated and stays.
- **Echo liveness** (`echo_conn_live_trace`, honest-echo-live) splits in two.
  - The per-connection clauses lose `accepts_below`.
  - Only "a pending connection is eventually accepted" keeps it, now as an excuse.
  - `pcm_bound_accepts_below` (ConnTrace:346) is still needed for the client bound.
  - Obl:121's case split on the Accept room becomes the new branch.
- **Quiet** (honest-l1b-cf/honestEchoL0BQuiet).
  - With point 2, the loop stays quiet past the cut-off: nothing on the poll set is ready
    unless an existing connection is.
  - So the `¬accepts_below io` excuse in `quiet_on_kernel_claim_a` (:31-39)
    **disappears**, and the README amendment #3 is withdrawn.
  - Without point 2 it would have to stay, and in a worse form: past the cut-off the loop
    would busy-poll.
- **KV CF loop.** No KV branch touches `hdl_room`/`prounds_t`. The KV worker's PF port
  (spike/servers-honest-l1: the honest-l1-cf Prog/Spec plus the echo Main/Run/Safe files)
  carries the same guard and simplifies the same way. `honestHttpKvL0Spec` loses its accept
  bound (:46, :81) and its "loop stops" comment.

## Estimate per owner

| Owner | Work | Est. |
|---|---|---|
| honest-ffi | pdo Accept branch, poll set and prefetch rule (PFModel); `pl2_ok`/`pround_ok` without room; re-prove the room-hypothesis lemmas (PFInv :61/:87, PFConn :1087, ConnRun `round_facts`) with the new branch, which is simpler since no hypothesis is left; the `live_conn` excuse | 2 d |
| KV worker | honest-l1-cf `step_pf`/`run_pf` and specs (removes `prounds_t`); echo Inv/Run/LiveOwn room hypotheses (≈12 sites, mostly deletions); retire NoGuard; HttpKvL0 and echo statements without the bound | 2–2.5 d |
| cf-actions | honest-l1b-cf blocking copy (guard, `brounds_t`, specs); the quiet claim without the excuse; L3-00 statements (`accepts_below` only where a pending accept is owed) | 1.5 d |
| echo-live worker | split `echo_conn_live_trace`; Obl:121 | 1 d |
| design/36 | D25 → D25′ text; fix the stale line design/46:21 | 0.1 d |

Total ≈ 6.5–7 days. Nothing here is hard; most of it removes hypotheses. The risk is in
point 2: the poll-set change touches `pf_ready`/interest, which D26 (live interest) is
changing right now, so it should be done after D26 lands, by the same hands.
