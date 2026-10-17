# 48 — Live interest lists (option (C)): design note

Status: PROPOSAL, pending the user's ruling on (C). No code yet.
Author: cf-actions (L3-09), 2026-10-17.

## Why

The servers' loop polls L1 with an interest list `ifds h = interest fds0 h`
(m4-common/asyncM4Loop): the initial fds plus every handle ever handed out.
It never shrinks. honest-l1's `pf_ready` reports every handle in that list
that is not in L1's table as ready:

    pf_ready lfd ps hs = FILTER (λh. case ALOOKUP ps.b.tbl h of
                                     | SOME f => inb_of ps f ≠ [] ∨ MEM f ps.eof
                                     | NONE => if h = lfd then ps.acq ≠ [] else T) hs

When the server reads EOF on a handle, L1 removes the handle from its table
(pdo's auto-close, `ADELKEY h`), but the handle stays in `interest`. From
then on `pf_ready ≠ []` in every round. So:

- The blocking L1 (L3-09) is never idle, and it never sleeps once a single
  connection has closed. `SQ` (premise of `echo_l0b_quiet`,
  honest-l1b-cf/honestEchoL0BQuiet) is false on every such world.
- A real server's interest set grows with every connection ever accepted,
  which is a memory leak.

(C) drops a handle from the interest list once the server has read EOF on
it.

## 1. The new `ifds`: live handles

Results don't name their handle; they are positional to the round's
actions. So the new interest list reads the server's actions with their
results. It is still a function of the history for a fixed server `m`:

```
(* A round's actions, paired with their results *)
drop_eof fds acts rs =
  FILTER (λh. ¬MEM (Read h, Got (SOME [])) (MAP (λ(a, r). (rd a, r)) (ZIP (acts, rs)))) fds
  (* rd (Read h k) = Read h; other actions never match *)

live_round fds acts rs = drop_eof (add_accepted fds rs) acts rs

(* The live interest list after h: per round, the new connections are
   added and the handles whose Read returned end-of-file are dropped *)
live fds0 m h =
  FOLDL (λfds (i, s). live_round fds (new_actions (log_of m) (TAKE i h)) s.results)
        fds0 (ZIP (COUNT_LIST (LENGTH h), h))
```

At the socket level the EOF result is `Got (SOME [])` (asyncM4ReadSoon's
`sfr_Eof`). An L1 Read on an unknown handle also returns `Got (SOME [])`;
dropping that handle is harmless, because it is dead already.

The listener is never read, so it is never dropped. `MEM lfd fds0`
therefore gives `MEM lfd (live fds0 m h)`.

Invariant this is designed for (PF run): a handle in
`live fds0 m (rhist n)` other than lfd is in L1's table. Handles leave the
table only through the EOF read, so this is a run lemma. Consequence: once
the live fds are drained, `pf_ready lfd ps (live …) = []`, so `SQ` follows
from pf_drain plus server_settles.

## 2. S1 and S1_interest, restated

`S1` (honest-l1/honestL1PFLive) is unchanged in form:

```
S1 lfd pol ifds m w0 ⇔
  (∀n h f. ALOOKUP (rstate … n).b.tbl h = SOME f ⇒ MEM h (ifds (rhist … n))) ∧
  ∀n. MEM lfd (ifds (rhist … n))
```

`S1_interest` (honest-echo-live/honestL1PFObl:84) becomes `S1_live`:

```
Theorem S1_live:
  run_ok lfd pol (live fds0 m) m w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol (live fds0 m) m w0 n) + 1 < dimword (:64)) ∧
  MEM lfd fds0 ⇒
  S1 lfd pol (live fds0 m) m w0
```

New obligation in its proof: a handle in L1's table is not EOF-read. That
is the converse direction of async-spike's `eof_read_gone`
(honestEchoL0EofRead: an EOF-read handle is out of the table), so it is
already available for the echo. The generic proof needs it as a run
invariant of the PF model: a handle stays in the table until pdo's EOF
auto-close, and that close is the round in which `Got (SOME [])` is
returned for it.

The other direction is new, and is what SQ needs:

```
Theorem live_held:
  run_ok … (live fds0 m) m w0 ∧ MEM h (live fds0 m (rhist … n)) ∧ h ≠ lfd ⇒
  ∃f. ALOOKUP (rstate … n).b.tbl h = SOME f
```

## 3. The CakeML loop: the drop step (KV worker, honest-l1-cf)

`step_pf` (honestL1PFProg:555) ends with

```
(lfd, hw, add_accepted fds rs, ps2, Async.poll c (map_num rdy, 0, rs))
```

It becomes

```
(lfd, hw, live_round fds acts rs, ps2, Async.poll c (map_num rdy, 0, rs))
```

`acts` and `rs` are both in scope, and `live_round` is pure and
translatable (FILTER / MEM / ZIP). Spec changes:

- step_pf_spec's post: `LIST_TYPE NUM (MAP w2n (live_round fds acts snap.results)) fdsv'`.
- run_pf_spec: `interest fds0` becomes `live fds0 m`.
- The loop invariant is `interest_SNOC` → `live_SNOC`: live over h ++ [s] is live_round of live over h, with that round's actions and s.results.
- The same edit applies to my `step_pfb` (honest-l1b-cf/honestL1BProg:78).

## 4. Lemmas to redo

Everything stated with `ifds = interest [n2w k]` (`EI`), or using its
monotonicity, needs restating for `live`. From the grep of `interest` / `EI`:

async-spike (honest-echo-live):
- honestL1PFObl: S1_interest → S1_live (above), run_hyp uses.
- honestEchoL0Obl: echo_sim (the PF history is the M4 one, `ghist EI`), echo_S2, echo_read_soon, echo_S3w.
- honestEchoL0EofRead: echo_read_soon_eof.
- honestEchoL0Stop / SrvOut / DataIn / DataOut / OutAll / OutAny / Frozen / Live: all through EI. Mostly parameter re-pointing, plus wherever `interest_accepted` or monotonicity is used.

M4 layer (m4-common, m4-liveness; current owner unknown, likely async-spike via the echo_sim route):
- asyncM4LiveProg.interest_accepted: every accepted connection is in the interest list. For `live` this becomes "every accepted connection not yet EOF-read". read_soon_s and accept_soon_s use it in exactly that form, since their connections are unread. My read_soon_eof_s already carries the "EOF not yet read" hypothesis.
- asyncM4ReadSoon.read_soon_s, asyncM4AcceptSoon, asyncM4Drain, asyncM4EchoLive, asyncM4EchoRunOk, asyncM4GRounds / GTrans (ifds-parametric: re-instantiate).
- close-v2-sim (asyncHLSimRun / Trace / EchoSpec2): the handle-layer runs are parametric in ifds. Re-instantiate, and check whether any lemma uses growth.

KV worker (honest-echo, honest-l1-cf):
- honestEchoL0Main / Sem / Safe / NoGuard: `echo_l0_run` and `run_pf_spec` with `interest [n2w k]`. Re-point to live. Safety doesn't depend on which handles are polled, so this should be mechanical.

honest-l1:
- honestL1PFConn / PFRound / PFLive / Model: ifds is a parameter. Only lemmas that fix `interest` need care (S1_interest's helpers).

cf-actions (mine):
- honest-l1b Sim/Refine (bquiet: ifds (h ++ [esnap] ++ k) = ifds (h ++ k)). For live, esnap has no results and the idle round has no actions, so it is unchanged; re-prove.
- echo_bquiet (honestEchoL0BStutter): the interest conjunct, re-proved for live.
- step_pfb / run_pfb specs, honestL1BTrace, honestEchoL0BMain / Sem / Quiet: re-point to live.
- New: live_held, then SQ for the echo = pf_drain_read + live_held + server_settles. This removes SQ from echo_pf_facts.

## 5. Order of work, once (C) is approved

1. Shared definition `live` / `live_round` / `live_SNOC` in m4-common/asyncM4Loop (one copy, next to interest), plus the CakeML `live_round`.
2. In parallel: the KV worker re-points CF and safety; async-spike re-points the M4 and echo liveness; I re-point the blocking chain and prove live_held + SQ.
3. Merge order: (1) first, then the rest independently. Nothing depends on the cross-worker order once (1) is in.

## Estimate

About 2–3 worker-days in total. The largest share is async-spike's
re-pointing (≈1 day). The KV CF change is ≈½ day; honest-l1 S1_live is
≈½ day; mine is ≈½ day plus SQ.
