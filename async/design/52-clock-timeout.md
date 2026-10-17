# 52 — A time-based write timeout (R1, option C): `sys_clock` and D23 in time

Status: APPROVED by the user (via the coordinator, 2026-10-17) as design/36 §9 D35; scheduled after echo liveness and the quiet echo, with D25 serve-on. No code yet.
Author: m4-server, 2026-10-17. Base: spike/moonshot-live (R1, README §5).

## (0) The problem (R1)

D23 drops an fd's outbox after `pf_sendwait` = 8 consecutive L1 *rounds* with a non-empty outbox
and no send progress (`stall_step`, honestL1PFModel).

L1 polls without blocking whenever any outbox is non-empty. The blocking L1 sleeps only in
`pf_idle`, which needs every outbox empty. So 8 rounds can be microseconds long. A normal
backpressure episode can last longer than that: KV stops reading while its outbox is full, so the
proxy's sends on Bᵢ stall. That episode then kills the connection.

The main theorems stay true, because the timeout is an observed excuse (`ep_timed_out`,
`timed_out_sys`). But they promise nothing in exactly the regime where backpressure matters. The
strong form's "no timeout" then becomes a hypothesis about the relative speed of our own processes.

Option (C) is what real servers do: a write timeout in *time*, measured with a monotonic clock.

## (1) The trusted addition: `sys_clock`

**C.** As thin as `ffisys_fdok`: one syscall and its encoding.
```
void ffisys_clock(unsigned char *c, long clen, unsigned char *a, long alen) {
  struct timespec t;
  if (clen != 0 || alen != 8) die("sys_clock: lengths");
  if (clock_gettime(CLOCK_MONOTONIC, &t) != 0) die("sys_clock: clock_gettime");
  put_be(a, 8, (uint64_t)t.tv_sec * 1000000000u + (uint64_t)t.tv_nsec);
}
```
- The result is an 8-byte big-endian count of nanoseconds. Like `sys_fdok`, it has no result header.
- POSIX.1-2017 `clock_gettime`: CLOCK_MONOTONIC "represents the amount of time since an unspecified
  point in the past"; it "cannot be set", and its values do not decrease.
- The only POSIX error for a supported clock is EINVAL, for an unsupported clock id. CLOCK_MONOTONIC
  is required by POSIX.1-2008 and later. So a failure is a broken platform: `die`, which the model
  answers with FFI_failed, as for misuse.
- Overflow: 2^64 ns is about 584 years of uptime. The rely bounds it (below), as D24 bounds counts.

**Model.** This needs no new world state. The world chooses the reading from the history, and the
rely makes it monotone:
- `lchoices` gains `now : lcall list -> num`.
- `l0_call «sys_clock» conf bytes w = if conf = [] ∧ LENGTH bytes = 8 then SOME (FFIreturn (n2w8 (w.ch.now w.hist)) w) else NONE`.
  The world is unchanged.
- `l0_rely` gains two conjuncts:
  - `∀h x. w.ch.now h ≤ w.ch.now (h ++ [x])`, i.e. monotone along the history. Only readings are
    observed, so this is exactly "each reading ≥ the previous one";
  - `∀h. w.ch.now h < 256 ** 8`.
- Any value ≥ the previous reading is allowed: equal readings, arbitrary jumps forward, no
  relation to the step counter `clock`. That is POSIX's whole promise.

**l0sys.** Nothing to add.
- `sys_step`'s Call case calls `l0_call`, so each process gets its own monotone readings from its
  own `ch`.
- There is no shared kernel clock. Safety needs none. The per-process liveness facts below are
  stated per process, so they need none either.
- The real CLOCK_MONOTONIC is system-wide. Treating it as per-process is a sound
  over-approximation: independent monotone sequences include the shared one.
- B1's post-hoc world uses the same `ch`, so it answers the run's readings unchanged.

## (2) D23 revised: per-fd last progress in time

L1 reads the clock once per round, after the round's sends. It records the reading `t` in the
round's log.
- `stalls : (word64 # num) list` now holds, per held fd, the **time of its last send progress**,
  or of the round in which its outbox became non-empty. It used to hold a round count.
- `stall_step` gets `t`:
  - progress, or an empty outbox, sets the fd's entry to `t`;
  - an `FReset f` still drops at once (D19 (a));
  - a held fd with a non-empty outbox and `t − last ≥ pf_sendtime` is dropped.

  `pf_sendtime` is a named constant, like `pf_backoff`; no proof uses its value. 30 s is the usual
  server default.
- The dropping path is unchanged (`drop_out`, `gone`, the reap/auto-close). So R1-safe, R1-live
  and the D16 corollary are unchanged, as they were for D23: nothing on the input side reads `gone`.

**The observed excuse.** `ep_timed_out K j io`, "≥ K output polls of the fd and no send progress",
becomes a time form:
```
ep_timed_out_t T j io ⇔
  ∃evs span t0 t1.
    LPREFIX (fromList (evs ++ span)) io ∧ ep_open j evs ∧
    clock_read t0 (LAST_CLOCK evs) ∧ clock_read t1 span ∧ T ≤ t1 − t0 ∧
    EVERY (λe. poll_ev e ⇒ out_poll (EL j (l0_accepted evs)) e) span ∧
    ¬EXISTS (send_took (EL j (l0_accepted evs))) span ∧
    ¬EXISTS (ep_ends (EL j (l0_accepted evs))) span
```
- That is: between two observed clock readings T apart, the fd was polled only for output, took no
  bytes, and stayed open.
- It is observable, like D16's hard error, and stated on the raw trace.
- `timed_out_sys` (moonshot-live) changes the same way.
- The strong form's hypothesis `stall_drains` ("the peer reads within K out-polls") becomes "within
  time T of a stall". That is a statement about the environment (the peer's reading speed), not
  about our own processes' relative speed. This resolves R1.

## (3) One fairness fact: the clock passes any bound

A dropped fd is the excuse, and liveness then needs the drop to happen: a stall must not last
forever unexcused. So the clock must eventually pass `last + T`. POSIX does not promise this; a
stopped clock is monotone. It is a new observed fairness hypothesis in D11′'s weak, trace-level
form (`F1_io`'s style):

```
F5_io io ⇔
  (∀i. ∃i' ev. i ≤ i' ∧ LNTH i' io = SOME ev ∧ clock_ev ev) ⇒
  ∀T. ∃i ev. LNTH i io = SOME ev ∧ clock_ev ev ∧ T ≤ clock_val ev
```
- In words: if the program reads the clock infinitely often, its readings are unbounded.
- Like [F1], it is stated on observed results, not on world choices. It is used for liveness only.
  Safety needs nothing.
- The system form is the same per process (`F5_sys`).

## (4) Reuse of the old clock theories

`ffiSpikeClock{FFI,Proof,Prog,World}` (and `world/clock` on the final/review branches) model the
FFI `«now»` as a stream of readings (`num llist`), with `clock_mono`/`clock_fits` as assumptions,
composed with the *basis* oracle (`clock_world_oracle`).

None of that fits L0: one oracle, choices from the history, the rely for monotonicity. So the
theories themselves are **not reusable**. Two things carry over:
- the 8-byte `n2w8` encoding with its `< 256 ** 8` bound, and `ffi_now_not_diverge`'s point that a
  clock call never diverges;
- the CF spec shape (`Clock_now_spec`), as the template for `L0.clock`/`L0_clock_spec`, which is
  the same shape as `L0_fdok_spec`.

archive/2024's `getNow` used `gettimeofday`, which is not monotonic. It is not a model.

## (5) Should L1 also block in stalled rounds?

**Today.** L0's poll has only timeout 0 and infinity. The blocking L1 sleeps only when idle (empty
outboxes, no pending stalls), and otherwise busy-polls.

**With (C), busy-polling no longer matters for correctness.** The timeout is measured in time, so
fast rounds don't shorten it. What remains is CPU use: a stalled connection makes L1 spin until it
drains or times out.

**Blocking with a deadline** would need a new trusted poll mode, a finite timeout, and a model
change:
- the blocking poll's wait must be able to end because time passed, which ties poll's ticks to
  clock readings: `l0_wait` with a deadline, and the world's `now` advancing during a wait;
- l0sys's `poll_may_return` must allow the deadline as a reason to return.

That is a second trusted change, larger than (1).

**Recommendation.** Do (1)–(3) now. Keep busy-polling in stalled rounds: it's correct and costs only
CPU. Make "poll with a timeout tied to the next deadline" a separate later decision, if the CPU cost
matters in practice. Note that blocking with POLLOUT interest but *no* timeout would be wrong: a
peer that never reads would park L1 forever, and the timeout could not fire.

## (6) Per-owner estimate (≈ 6–8 days in total)

| Owner | Work | Est. |
|---|---|---|
| honest-ffi (model) | `sys_clock` case, `now` choice, two rely conjuncts, the Props/Inv cases (world unchanged) | 0.5 d |
| honest-ffi (C) | `ffisys_clock`, header-comment row | 0.1 d |
| honest-ffi (L1 PF) | `stall_step` on times, one clock read per round in `pf_tail`/`bround`, the stall invariants, `rdrop_timeout` in time | 1.5–2 d |
| KV worker (CF) | `L0.clock` and `L0_clock_spec`; the L1 loop's CF follows the model's extra call | 0.5 d |
| cf-actions (quiet / bquiet) | the quiet definitions skip clock events (one per round); `ep_timed_out_transfer` in time | 0.5 d |
| async-spike (echo liveness) | `ep_timed_out` → `ep_timed_out_t` through honest-echo-live's excuse chain (Chain, DataOut, OutAll/Any, Excuse) and the L3 statements; `F5_io` | 1.5–2 d |
| moonshot-live | `timed_out_sys` in time, `F5_sys`, R1 closed | 0.5 d |
| l0sys / bridges (m4-server) | none for l0sys; B1's world already carries `ch` | 0.1 d |
| design/36 (new D), README | text | 0.1 d |

**What it replaces:**
- D23's round counter (`stalls` as counts, `pf_sendwait` = 8 as the drop criterion);
- the round form of the observed excuse (`ep_timed_out K`, `timed_out_sys K`);
- the strong form's "the peer reads within K out-polls" hypothesis;
- R1's dependence on how fast our own processes run.

It keeps D23's dropping path, the `gone` bookkeeping, and every safety statement.
