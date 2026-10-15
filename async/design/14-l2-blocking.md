# 14: Level 2 blocking: an event loop that sleeps in `select`

Branch `spike/l2-blocking`, stacked on `spike/cfdiv-multipart` (PR #13).
It merges `spike/cf-reactive` and `spike/async-m2` and uses them read-only:
`async/model`, `async/cf-spike`, `async/cf-actions`.
- New code: `async/l2-blocking/` (6 theories).
- Also `async/ffi-spike/ffiSpikeSocketSelectScript.sml`.

Full `Holmake` is green and there are no cheats. Handoff:
`async/design/HANDOFF-l2.md`.

## Result in one paragraph

The real event loop now blocks instead of busy-polling. A computation's
CakeML value exposes the events it declares (Level 2 interest). When the
computation is waiting and has nothing to perform, the loop calls a
blocking `select` on those events. Otherwise it performs the round's
actions and polls, as before.

What is proved, end to end:
- **The loop (CF):** it diverges, with an exact I/O trace (`brun_spec`).
- **The rounds it skipped are irrelevant:** the computation's history
  under the blocking loop is exactly the model's `blocked` subsequence of
  the polling loop's history over the same input
  (`blocking_same_actions`).
- **Same behaviour as polling:** the actions in its trace are exactly
  those of cf-actions' polling loop (`blocking_trace_same_actions`).

This is the CF-level counterpart of M2's `no_busy_waiting`, and it goes
through the same model lemmas (`same_for_step`, i.e. `blocked_sound`'s
invariant). The socket model also gets a blocking `select`, proved to be
"polling with the empty polls skipped" and live under `sched_wf`.

## 1. Level 2 interest in the CF layer (`asyncL2BlkModel`, `asyncL2BlkProg`, `asyncL2BlkSpec`)

The representation is cf-actions', plus one field:

```sml
datatype ('act, 'e, 'w, 'a) step2 =
    Done2 'a
  | Pending2 ('e list) ('w -> 'act list * ('act, 'e, 'w, 'a) step2)
```

`Pending2 es k` declares the events `es`. `STEPA2` relates a residual to
the model's Level 2 computation `comp2` (`run` plus `interest`). It is
`STEPA` with one more conjunct in the pending case:

```
CoInductive STEPA2:
  (∀c A x xv. c.run = finished A x ∧ RES x xv ⇒ STEPA2 … c (Done2V xv)) ∧
  (∀c iv kv. (c.run []).result = NONE ∧ EVLIST EV (c.interest []) iv ∧
     (∀w wv. WORLD w wv ⇒ returns p kv [wv]
        (POLL_RESULT2 ACT (STEPA2 …) (suspended2 c [w]))) ⇒
     STEPA2 … c (Pending2V iv kv))
EVLIST EV E v ⇔ FINITE E ∧ LIST_TYPE EV (SET_TO_LIST E) v
```

`suspended2 c [w]` is the model's own "c one poll later". Its interest
is c's on the longer history, so the declared events are right at every
round, not just the first.

**Model lemmas** (one per implementation step):
- `suspended2_wait_on_NONE/SOME`, `suspended2_emit2_NIL/CONS`,
  `suspended2_never2`;
- `bind2_finished`: `c.run = finished A x ⇒ bind2 c f = prepend2 A
  (skipping2 (LENGTH A) (f x))`;
- `suspended2_bind2`: `wf c.run ∧ (c.run []).result = NONE ⇒
  suspended2 (bind2 c f) [w] = bind2 (suspended2 c [w]) f`, as an
  equation of records, so the interest is the model's `bind_interest`
  exactly.

**CF specs (MAIN)**, generic in `p`:
- `return2_spec`, `poll2_spec`, `wait_on_spec`, `never2_spec`,
  `emit2_spec`, `skip2_spec`, `bind2_spec`, all against the model's
  `return2`, `suspended2`, `wait_on`, `emit2`, `bind2`.
- `interest_spec`: `COMP2 … c cv ⇒ app p interest_v [cv] emp (POSTv v.
  &EVLIST EV (waiting_on c []) v)`. The CakeML call returns exactly what
  the model says c is waiting on.

`wait_on e q` takes a CakeML `q` that implements `λw. if e ∈ w.ready then
p w else NONE`, so the ready set's representation stays abstract.

## 2. The blocking world and why blocking is sound (`asyncL2BlkWorld`)

The world is cf-actions' byte stream `ws`. Responses and ready bytes are
read in order, and a polling round's ready set is `{b}`. `brounds c ws n
= (kept, full, pos)` follows n rounds of the blocking loop:

- `kept`: the snapshots c is actually polled with;
- `full`: the snapshots of every round the world went through, i.e.
  the polling loop's history;
- `pos`: the stream position.

When `blocks c kept` holds (no action to perform, not finished), the
round skips `skips (c.interest kept) ws pos` bytes, i.e. up to the first
declared byte.

```
loop_skip c h s ⇔ new_actions (log_of c.run) h = [] ∧ (c.run h).result = NONE ∧
                  DISJOINT (c.interest h) s.ready ∧ s.results = []     (⇒ irrelevant)
(* ASSUMPTION *) blk_live c ws: whenever the loop blocks, a declared byte eventually comes

(* MAIN *) blocking_same_actions:
  wf c.run ∧ quiet c ∧ blk_live c ws ∧ brounds c ws n = (kept, full, pos) ⇒
  full = hist c.run ws (LENGTH full) ∧          (* the polling loop's history *)
  kept = blocked (loop_skip c) [] full ∧        (* the model's blocked subsequence *)
  c.run kept = c.run full                       (* same actions, same result *)
```

The proof (`brounds_inv`) is an induction carrying `same_for c full
kept`. That is exactly the invariant of the model's `blocked_sound`,
preserved by its `same_for_step`: skipped snapshots satisfy `loop_skip`,
hence `irrelevant`. `quiet c` is the model's Level 2 well-formedness
(`wf2`); every Level 2 primitive and combinator is quiet (asyncLevel2).

## 3. The FFI and the loop (`asyncL2BlkFfi`, `asyncL2BlkLoop`)

The FFI part has names `act`, `ready` and `select`. `select` takes the
declared bytes as its config. It returns the first declared byte of the
stream and consumes everything before it; if none ever comes, it is
`FFIdiverge`. The loop:

```sml
fun bstep c = case c of (acts, s) =>
  let val rs = bperform acts
      val b = case s of Done2 x => bget_ready ()
              | Pending2 es k => (case acts of [] => bselect es | _ => bget_ready ())
  in poll2 c (b, 0, rs) end
fun brun c = brun (bstep c)
```

Main statements:

```
(* MAIN *) bselect_spec:
  limited_parts io2_names p ∧ EVLIST WORD E esv ∧ (∃j. ws j ∈ E) ⇒
  app p bselect_v [esv] (IOS2 ws evs)
    (POSTv v. &WORD (ws (skips E ws 0)) v *
              IOS2 (sdrop (SUC (skips E ws 0)) ws)
                (evs ++ [select_event (SET_TO_LIST E) (ws (skips E ws 0))]))

(* MAIN *) bstep_spec:      one iteration = bstep_world c ws (block or poll)

(* MAIN *) brun_spec:
  limited_parts io2_names p ∧ wf c.run ∧ blk_live c ws ∧
  COMP2 p WORD A WORD (SNAPSHOT BREADY1 WORD) c cv ⇒
  app p brun_v [cv] (IOS2 ws [])
    (POSTd io. io = LFLATTEN (LGENLIST (λi. fromList (bround_events c ws i)) NONE))

(* MAIN *) trace_actions_brounds:
  wf c.run ⇒ trace_actions (FLAT (GENLIST (bround_events c ws) (SUC n))) =
             (c.run (FST (brounds c ws n))).actions

(* MAIN *) blocking_trace_same_actions:
  wf c.run ∧ quiet c ∧ blk_live c ws ∧ brounds c ws n = (kept, full, pos) ⇒
  trace_actions (FLAT (GENLIST (bround_events c ws) (SUC n))) =
  trace_actions (FLAT (GENLIST (round_events c.run ws) (SUC (LENGTH full))))
```

Read together:
- The blocking loop never terminates.
- Its trace is one `select` event per idle stretch and the usual
  act/ready events otherwise.
- The actions it performs are exactly those that cf-actions' polling
  loop (`run_spec`, `round_events`) performs over the same stream.

The loop proof uses `xcf_div_rule IMP_app_POSTd_one_FFI_part_FLATTEN`, as
cf-actions does. Its invariant is "the value implements `suspended2 c
kept_i`", and `bstep_world_brounds` lines one CF iteration up with one
round of `brounds`.

## 3a. The assumption `blk_live`, in plain terms

**What it says.** Whenever the loop goes to sleep (the computation is
waiting and has nothing to perform), something the computation is
waiting for eventually happens. In this world: a byte the computation
declared eventually appears later in the stream. It is a statement about
the environment's future relative to what the program waits for. It is
not about the program alone, and not about the world alone.

**Why it is needed.** `select` returns only when a declared event comes.
If none ever comes, the call never returns. CakeML's semantics records
that as an FFI that *diverged*, which the program reports as a final
event, not as the program running forever. A `POSTd` ("runs forever, with
this infinite trace") spec, like `brun_spec`, is then simply false. The
polling loop has no such issue: with nothing to do it keeps polling
forever, emitting only ready events. So the assumption is what makes the
blocking loop's outcome the same *kind* of outcome as the polling loop's.

**Does it follow from `sched_wf`?** No.
- `sched_wf` (the socket world's assumption) only says arrivals are well
  formed. It allows a schedule in which nothing ever arrives, e.g. the
  quiet schedule from its non-vacuity lemma.
- `blk_live` is a genuine liveness assumption: "the peer eventually does
  something we wait for". What `sched_wf` does give, as
  `sock_select_live`, is the conditional form: if an arrival for one of
  the fds is scheduled, select returns.
- So in the socket world, `blk_live` would read: whenever the server
  blocks, some arrival for a declared fd is scheduled later. For an echo
  server that always waits on its listener, that is "connections (or
  data) keep coming forever". This is a strong assumption about clients,
  and not one to put in the final theorem.

**What breaks without it, and how to drop it.** Only the *form* of the
whole-loop theorem breaks. The two loops still do the same thing up to
the point where the blocking loop sleeps forever. From then on, the
polling loop emits no more actions either: the computation is quiet and
nothing it waits for ever comes, so by `same_for` its log doesn't grow.

The honest replacement for `blk_live` is therefore a two-outcome
theorem. Either:
- the world keeps delivering, the loop diverges, and its actions equal
  the polling loop's (as now); or
- `select` blocks forever, the program ends with an FFI divergence after
  a finite trace, and that trace's actions are all the actions the
  polling loop would ever perform.

The second case needs CF's `POSTf` (FFI-divergence postcondition) for
the loop body and a variant of cfDiv's loop rule that allows an
FFI-divergence exit. That keeps `blk_live` out of the trusted surface
entirely. Estimate: 1–2 days (a POSTf loop rule, ~200–300 lines in
cfDiv's style, plus the "no more actions" model lemma, which follows
from `quiet`).

## 4. A blocking select in the socket model (`ffiSpikeSocketSelect`)

```
sock_select fds s = SOME (FILTER (is_ready s') fds, s') with s' = ticks (SUC n) s,
                    n least such that some fd of fds is ready; NONE (blocks forever) if none
(* MAIN *) sock_select_polls: sock_select fds s = SOME (r, s') ⇒
  ∃n. (∀m. m < n ⇒ FST (sock_poll fds (ticks m s)) = []) ∧ sock_poll fds (ticks n s) = (r, s') ∧ r ≠ []
(* MAIN *) sock_select_live: sched_wf s ∧ MEM a (next_step (ticks k s)) ∧
  arrival_nonempty a ∧ MEM (arrival_fd a) fds ⇒ ∃r s'. sock_select fds s = SOME (r, s')
```

That is, select is polling with the empty polls skipped, which are exactly
the rounds a blocking scheduler may skip. Under the socket world's single
assumption it returns.

## 5. Gaps

1. **`both2`/`choose2` in CF are not done.** Their interest is a union, so
   they would need a canonical-union CakeML function (sorted merge) to
   keep `EVLIST`'s canonical `SET_TO_LIST` form. The alternative is
   relaxing the select event's config (see assumption 3). Estimate:
   `both2` ~250 lines (model one-poll split as `suspended_both` plus the
   interest union), `choose2` ~350.
2. **The socket world's select is not wired into an FFI part.** It is a
   model function with lemmas. Adding it means a fifth FFI name and a
   `Socket.select` spec, with `FFIdiverge` for "never". That is
   mechanical, ~150 lines, but it changes the socket part (PR #11's file),
   so I left it additive.
3. **The loop world is cf-actions' oblivious byte stream**, not the socket
   world. Combining them (actions = socket operations, interest = fds)
   is M3 assembly (another worker's `spike/m3-assembly`).
4. **No deadlines or timers.** `select` waits for events only. A timer is
   another event in the model (M2 §4.4); a world reporting timers is M3
   material.
5. **The result of the computation isn't observed.** The loop runs
   forever, as cf-actions' does, and a finished computation is polled,
   not blocked. Blocking on `Done` would need `select` on an empty set,
   i.e. sleeping forever. That is fine semantically but doesn't fit
   `POSTd`.

## 6. Estimates

- `both2` and `choose2` in CF: 1–2 days.
- Wiring `select` into the socket part and a sockets-plus-actions world
  for the blocking loop: 2–4 days.
- The loop proof itself carries over unchanged in shape.
- This spike: about 3½ hours of wall clock (13:00–14:20 by the commit
  log, plus the earlier Level 2 CF part before the pause), 6 theories,
  about 1.2 kLOC.

## Assumptions made

1. **Interest lists are canonical**: `EVLIST` requires the CakeML list to
   be `SET_TO_LIST` of the declared set. This makes each round's `select`
   event a function of the model. Only `[]` and `[e]` are built so far.
2. **The loop blocks exactly when the computation is pending and its
   round has no actions.** A finished computation is polled, as in
   cf-actions.
3. **`select`'s config records the declared bytes**, so the trace shows
   what was waited on.
4. **One named assumption, `blk_live`** (§3a): whenever the loop blocks,
   a declared byte eventually comes. It does not follow from `sched_wf`.
   It can be removed with a two-outcome theorem (§3a), which I recommend
   before it reaches the final echo theorem.
5. **`quiet c`** (the model's Level 2 well-formedness) is assumed for
   the comparison with polling. It holds for all Level 2 combinators.
6. **`wait_on e q`** takes a CakeML `q` that already checks `e ∈ ready`,
   so the ready set's representation stays abstract.
7. Read-only use of other branches, via merges (`spike/cf-reactive`,
   `spike/async-m2`). Nothing in their directories was edited.
