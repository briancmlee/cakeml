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

Base: spike/l3-quiet @7b91911f6, which has D20 + D21 + the moonshot pol
model, cf-actions' honest-l1b, and its statement copy `honestL1BStmts`
(synced to #153 3593187d9). The trace is cf-actions' plain-prounds one
(`ptrace`/`ppre`), for an arbitrary start world:
`LPREFIX (fromList evs) io ⇔ ∃N h ws evs' logs. prounds lfd pol ifds m (w, pinit) N = SOME (h, ws, evs', logs) ∧ evs ≼ evs'`.
The CakeML loop's trace (`prounds_t`, guarded by `hdl_room`) is the
whole-program step and is not proved here. Flagged to the coordinator:
`accepts_below` does not imply `hdl_room`, because the loop reserves room
for every action of a round.

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

## Status (2026-10-17)

Proved (spike/echo-live-pol, honest-echo-live/): S1 (generic), S2, S3w for
the echo; the trace bridge (pftrace, F1_io ⇒ F1, accepts_fail ⇒
accepts_fail_io); conn_live_l0 (generic pf_conn_live; the echo's
echo_conn_live_trace under the statement's premises, the client bound from
accepts_below).

### D progress (2026-10-17, later)

Proved (Holmake, no cheats), honest-echo-live/:
- (i) output accounting: `l0_sent_open` (Sent), `faithful_csent`,
  `faithful_accept_csent`, `episode_csent` (KSent): while episode j is open
  on f and no close was called on f, f's channel holds `l0_sent j` as sent.
- (3) input hypothesis: `echo_writes_stop` (Stop), and with honest-ffi's
  `S4w_of_stop`, `echo_S4w`: the PF echo meets S4w on every fd.
- (4) the server: `hst_written`, `echo_out_live` (SrvOut): what client j of
  psk sends is eventually in its outgoing stream.

Open: (2) kernel input accounting (peer_sent = fetched ++ inbox);
locating a trace prefix in the run; the excuse mapping; the close step
(prove "a close call on f while open"; derive ep_closed only under no
close failure, per the coordinator, pending the user's ruling on the
interrupted-close finding); assembly.

### D progress (2026-10-17, evening): the round-level chain is done

Proved (Holmake, no cheats), honest-echo-live/:
- `released_frozen` (Frozen): once L1 releases f, client j's outgoing is
  final (the echo writes only through table handles; handles are fresh).
- `out_chain_any` (OutAny): for every N ≥ n, client j's outgoing at N
  reaches csent c, or ep_hard_err j0 ∨ ep_timed_out j0.
- `fetched_out` (DataOut): L1's fetches on f since its connect → server →
  kernel.
- `conn_data_out` (DataIn): from a round with f in L1's table (no EOF):
  peer_sent c ≼ csent c later ∨ flushed ∨ ep_hard_err j0 ∨ ep_timed_out j0.
  `fkeep_noconn`: no re-connect in a round where L1 keeps f.
- `echo_read_soon_eof` (EofRead): an fd held at EOF is read within three
  rounds (cf-actions' M4 read_soon_eof_s, lifted; `eof_gone` invariant).
- `drains_round` (Drains): L3's drains w0 io c ⇒ the round-level drains.

### D trace assembly plan (2026-10-17, evening)

For evs ≼ io with ep_open j evs, f = EL j (l0_accepted evs), w =
world_at evs, c = f's channel at w:
1. Locate evs = revs r ++ pre (`locate`); D := peer_sent c at w ≼
   peer_sent c at round SUC r (arrivals only append).
2. f's connect round a (`last_conn`, from pcm: entries come only from
   FConn).
3. Cases on round SUC r:
   - episode j ended in the rest of round r: a hard error (excuse) or an
     L1 close (EOF seen ⇒ the EOF case below at an earlier round);
   - f in tbl, no EOF: `conn_data_out`;
   - f at EOF (in tbl or closing): EOF case: at the fetch round k of FEof,
     run_peer_sent at k + 1 with an empty inbox (recv returned 0; LData is
     dropped after peer_eof), so peer_sent is final and = L1's fetches
     since a; then `fetched_out`;
   - f in acq: the echo accepts it (M4 queue_progress lifted), then the
     cases above at that round.
4. csent c at n' ≼ l0_sent j evs' (`episode_csent` while open; after the
   close both are frozen).
5. flushed (rworld k) f ⇒ flushed_ch w0 io c (ruling #4's X).

### D assembly plan (2026-10-17, after flush_live2 / run_gone_cause)

Target: for a prefix evs with ep_open j0 evs, f = EL j0 (l0_accepted evs),
c = f's channel at world_at evs, drains c (and the pending forms of #2/#4):
peer_sent c ≼ l0_sent j0 evs' eventually, unless ep_hard_err j0 ∨
ep_timed_out K j0 ∨ flushed_ch c.

Episode identity is the crux: every excuse must be j0's, not a later
episode on the same fd number.  Tool: f's index in the episode fold's open
map (KV's own_ok / call_open); a pure trace lemma `idx_stable`: if f maps to
j at evs and at evs ++ mid, then no ep_ends f in mid (indices are fresh);
with ep_state_open this pins j = j0.

1. Locate: evs ≼ revs (SUC r), evs = revs r ++ pre; f maps to j0 there.
2. Output (O): from round boundary N on (f held), flush_live2 gives
   outgoing ≼ csent, or gone (run_gone_cause → hard_send ∨ rdrop at k),
   or hard_send / rdrop at k; run_ep_hard_err / rdrop_excuse give the
   trace excuse for f's episode at round k; idx_stable makes it j0's
   (f held from N to k: KV's round_no_end).
3. Input (I): run_peer_sent (+ acq_quiet, cdata_before_conn,
   client_rounds) gives peer_sent ≼ cdata j (pars 0 N), or flushed
   (→ flushed_ch); live_data covers the inbox.
4. Server (S): echo_out_live: cdata j (pars 0 N) ≼ outgoing at N'.
5. Accounting (A): episode_csent: csent c = l0_sent j0 while open and no
   close call on f; after a close call, both frozen (run_closed_quiet).
6. Close step: peer_eof ⇒ a close call on f while open (prove);
   ep_closed j0 under no close failure (corollary), per the coordinator.

## D: echo_live_l0, decomposed

Fix a prefix evs of the trace with episode j open on channel c (fd f), and
drains c.  Excuses: ep_hard_err j, ep_timed_out K j (D23).

1. Locate: evs lies in round N; the episode's world at the end of round N
   has peer_sent ⊒ the one at evs (arrivals only append).
2. Kernel input accounting (new): for a held fd f on channel c,
   peer_sent c = (what L1 fetched on f, = client j's data in psk) ++ inbox c,
   unless c broke and flushed its inbox (then a hard recv error is
   observed: ep_hard_err).
3. Input reaches psk: live_data (honest-ffi): inbox c at N ≼ client j's
   data in psk, unless the episode ends (FEof / FReset; FReset is
   ep_hard_err).
4. The server: the M4 echo's liveness through hrun_sim (as S2/S3w did):
   everything in client j's data is eventually in its outgoing in psk.
5. Output: flush_live (honest-ffi): outgoing(j at n) ≼ csent c at n', or
   broken / gone / hard_send (→ ep_hard_err) / rdrop (FReset → ep_hard_err,
   or the D23 window → ep_timed_out, from the window's event facts).
6. Kernel output accounting (new): csent c at a round boundary = l0_sent j
   of the run's events (sends on f in episode j).
7. EOF: peer_eof ⇒ EOF fetched (live_data's FEof) ⇒ the echo reads it and
   closes its handle ⇒ L1's close of f reaches the trace (ep_closed j),
   after the flush (closing) or at once.
8. Strong form: HD16_io and stall_drains replace the excuses (honest-ffi's
   D16 corollary and their model-level "peer drains within pf_sendwait"
   corollary, bridged from the trace).
