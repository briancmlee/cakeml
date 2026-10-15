# 10: The event loop in a reactive world, and `choose`

Status: **both tasks done.** There are no cheats, and `Holmake -j2` in
`async/cf-reactive/` is green. Branch `spike/cf-reactive`, stacked on
`spike/cf-actions` (see `05-cf-actions.md` for the representation
`(acts, residual)`, the predicate `STEPA`/`COMP`, and the first event loop
with an oblivious byte stream).

Files (`async/cf-reactive/`, 240–256 lines each):

| file | contents |
|---|---|
| `asyncCfReactWorldScript.sml` | the generic world, its FFI function, the snapshot sequence it generates, the trace lemma |
| `asyncCfReactLoopScript.sml` | the CakeML loop (`fill`, `read_bytes`, `step`, `run`) and its specs |
| `asyncCfChooseModelScript.sml` | one-poll lemmas for the model's `choose` |
| `asyncCfChooseScript.sml` | the CakeML `choose` and `choose_spec` |

## 1. A reactive world

In 05 the world was an oblivious byte stream: responses could not depend
on the actions. Here a world is **any state plus a step function**:

```
Datatype:
  rworld = <| step : 's -> word8 list -> word8 list # word8 list # 's ;
              nready : num ;
              enc : 's -> ffi |>
End
```

`wd.step s acts = (rs, rdy, s')`: in state `s`, given all the actions the
program emitted this round (oldest first), the world answers with:
- one response per action (`rs`, positionally);
- `nready` readiness bytes (`rdy`, read as the ready set `set rdy`);
- its next state `s'`.

The state type `'s` is arbitrary, so it can hold a schedule of future
arrivals, buffers, connection tables, and so on. `enc` stores the state
in CakeML's FFI state type (`ffi`). The world must be well-behaved:

```
world_ok wd ⇔
  (∀s acts. LENGTH (FST (wd.step s acts)) = LENGTH acts ∧
            LENGTH (FST (SND (wd.step s acts))) = wd.nready) ∧
  (∀s1 s2. wd.enc s1 = wd.enc s2 ⇒ s1 = s2)
```

**The FFI side is a single FFI part with a single call, `round`**, as
cfDiv's loop rule requires (`limited_parts [«round»] p`). Its buffer
goes out as the actions followed by `nready` zero bytes, and comes back
as the responses followed by the readiness bytes (the same length, as
`call_FFI` demands). The FFI function decodes the state with `@` (it is
unique since `enc` is injective), applies `step`, and re-encodes. The
heap assertion is `RW wd s evs = one (FFI_part (wd.enc s) (round_update wd)
[«round»] evs)`.

**The history the world generates** is defined by iterating `step` with
the model's actions:

```
wrounds wd m s0 0 = ([], s0)
wrounds wd m s0 (SUC n) =
  let (h, s) = wrounds wd m s0 n;
      r = wd.step s (new_actions (log_of m) h)
  in (h ++ [wsnap (FST r) (FST (SND r))], SND (SND r))

wsnap rs rdy = <| ready := set rdy; now := 0; results := rs |>
whist wd m s0 n = FST (wrounds wd m s0 n)
wround_event wd m s0 n = the `round` I/O event of round n
                         (actions + padding out, responses + readiness in)
```

### The loop

```sml
fun step (nr, c) =                          (* c = (acts, s) *)
  let val k = List.length acts
      val buf = Word8Array.array (k + nr) (Word8.fromInt 0)
      val _ = fill buf 0 acts
      val _ = #(round) "" buf
      val rs = read_bytes buf 0 k
      val rdy = read_bytes buf k nr
  in (nr, poll c (rdy, 0, rs)) end;
fun run st = run (step st);
```

`nr` (the world's `nready`) is carried in the loop state, because the
CakeML code is fixed while the world is a parameter.

### What is proved (verbatim)

```
(* MAIN: the trace and the model agree, in any well-behaved reactive world.
   The actions handed to the world in the first n+1 rounds of the loop's
   trace are exactly the model's action log on the history the world
   generates (by iterating its step function with the model's actions). *)
Theorem wtrace_actions_rounds:
  world_ok wd ∧ wf m ⇒
  wtrace_actions wd (GENLIST (wround_event wd m s0) (SUC n)) =
  (m (whist wd m s0 n)).actions

(* MAIN: one loop iteration in a reactive world. ... *)
Theorem step_spec:
  world_ok wd ∧ limited_parts [«round»] p ∧ NUM wd.nready nrv ∧
  COMP p WORD A (SNAPSHOT READYL WORD) m cv ⇒
  app (p:'ffi ffi_proj) step_v [Conv NONE [nrv; cv]] (RW wd s [])
    (POSTv v.
       &(∃cv'. v = Conv NONE [nrv; cv'] ∧
               COMP p WORD A (SNAPSHOT READYL WORD)
                 (suspended m [wsnap (FST (wd.step s (m []).actions))
                                     (FST (SND (wd.step s (m []).actions)))])
                 cv') *
       RW wd (SND (SND (wd.step s (m []).actions)))
          [round_event wd (m []).actions (FST (wd.step s (m []).actions))
                          (FST (SND (wd.step s (m []).actions)))])

(* MAIN: in any well-behaved reactive world wd started in state s0, the
   event loop never terminates, and its I/O trace is one round event per
   round, for the history the world generates ... *)
Theorem run_spec:
  world_ok wd ∧ limited_parts [«round»] p ∧ wf m ∧ NUM wd.nready nrv ∧
  COMP p WORD A (SNAPSHOT READYL WORD) m cv ⇒
  app (p:'ffi ffi_proj) run_v [Conv NONE [nrv; cv]] (RW wd s0 [])
    (POSTd io. io = LGENLIST (wround_event wd m s0) NONE)
```

`wtrace_actions` keeps the outgoing action bytes of each `round` event
(without the padding). `READYL rdy v ⇔ ∃bs. rdy = set bs ∧ LIST_TYPE WORD
bs v`. Helpers: `fill_spec` and `read_bytes_spec` (byte-buffer loops),
`round_update_enc` (the FFI function on an encoded state), and the
lazy-list lemmas.

Read together: **in any well-behaved reactive world, the loop diverges,
its trace is one `round` event per round, and the actions in it are
exactly the model computation's action log on the history the world
generates in response to those very actions.** The proof has the same
shape as in 05 (cfDiv's `IMP_app_POSTd_one_FFI_part_FLATTEN`, with loop
invariant `COMP … (suspended m (whist wd m s0 i))`, world state
`SND (wrounds wd m s0 i)`). The oblivious stream of 05 is the special
case where `step` ignores the actions.

### What instantiating it with sockets would need

The socket model (`async/ffi-spike/ffiSpikeSocketFFIScript.sml` on
`spike/socket-model`, by another worker; I did not edit it) has a state
`sockets` (listeners, connections, a schedule `sched` of arrivals), the
operations `sock_poll`/`sock_accept`/`sock_read`/`sock_write`, and an
encoding `sockets_encode : sockets -> ffi`. To plug it in:

1. **Actions and responses as bytes.** Here an action and its response
   are one byte each. Socket actions (accept on fd l, read n bytes from
   c, write bs to c) and their responses (an fd, data or EOF, an
   acknowledgement) need a byte encoding of variable length. Two options:
   - (a) Generalise `rworld` from `word8` to byte strings, with a framing
     in the `round` buffer (e.g. length-prefixed records) and a decoding
     relation in place of `WORD`. This changes `fill`/`read_bytes` into a
     serialiser/parser and `wtrace_actions` into a decoder. It is the same
     proof shape, maybe 200–300 more lines.
   - (b) Keep bytes and make actions indices into a table in the world
     state. That is simpler, but less faithful.
2. **A round-level step from the per-call operations.** Define
   `sock_step s acts` as: perform the decoded actions in order with
   `sock_accept`/`sock_read`/`sock_write` (collecting the responses), then
   `sock_poll` on the interest fds (which advances the schedule) for the
   readiness. Readiness is a set of fds, so `nready` would be replaced by a
   framed list. `world_ok` needs "one response per action" (true by
   construction) and injectivity of `sockets_encode` (the socket worker has
   `encode_*_11` lemmas, from which this should follow).
3. **Misuse.** The socket operations return `NONE` (FFI failure) on
   misuse (an fd of the wrong kind). The round step must be total, so
   either map misuse to an error response (an extra response byte) or add
   a precondition that the program's actions are well-typed. The first is
   simpler, and it keeps `world_ok` unconditional.
4. **One FFI part.** The socket model is its own FFI part with four
   names. For this loop it would be wrapped in one `round` call (the world
   performs the batch), which matches "a sockets-only server world". A
   whole-program theorem then needs the socket worker's
   `call_main_thm_div` with this single part.
5. **The schedule.** `sock_poll` advancing the schedule once per round
   matches this model's "one snapshot per round". The fairness assumption
   `sched_wf` would be a hypothesis on `s0` only, since `run_spec` holds
   for every world state.

So instantiation is mostly plumbing (encodings) plus the choice in (1).
The theorem's statement and its proof would not change.

## 2. `choose`

`choose` races two computations and returns the winner's result together
with the loser, **still running** (Async-style; see 01 §4). The loser is
an ordinary computation value, i.e. a pair `(acts, residual)`. So
choose's result relation simply holds `COMP` for it:

```
CHOOSE_RES p ACT A B WORLD =
  SUM_TYPE (PAIR_TYPE A (COMP p ACT B WORLD))
           (PAIR_TYPE (COMP p ACT A WORLD) B)
```

The CakeML code (`asyncCfChooseScript.sml`) has four cases:

| case | returns |
|---|---|
| left side `Done x` | `(acts1, Done (Inl (x, c2)))`: m2 is not polled, so its actions are not emitted (the loser value still carries them) |
| right `Done y`, left emitted nothing | `(acts2, Done (Inr (c1, y)))` |
| right `Done y`, left emitted actions | `(acts1 @ acts2, Pending k)`, where `k w = ([], Done (Inr (poll c1 w1, y)))`: wait one round for the left's responses and deliver them to the loser (01 §4, the one-round delay) |
| neither done | `(acts1 @ acts2, Pending k)`, where `k w` polls each side with its share of `w` and continues with `choose` |

The model side needed a **one-poll split of `choose`** (the model had a
split for `both` but not for `choose`):

```
Theorem suspended_choose:
  wf m1 ∧ wf m2 ∧ (m1 []).result = NONE ∧ (m2 []).result = NONE ⇒
  suspended (choose m1 m2) [w] =
    choose (suspended m1 [take_snap (LENGTH (m1 []).actions) w])
           (suspended m2 [skip_snap (LENGTH (m1 []).actions) w])
```

It is derived from the model's `views_split` and `par_log_split`, through
one-snapshot versions of the views, logs, `either_done` and
`first_prefix` (`views_cons`, `par_log_cons`, `log_before_cons`,
`either_done_cons`, `first_prefix_either_cons`) and
`suspended_suspended` (iterated `suspended`). The three "someone has
finished" cases are `choose_finished_left`, `choose_finished_right_quiet`
and `choose_finished_right_waits`. The view bookkeeping I had flagged as
the risk turned out to be routine with these lemmas.

```
(* MAIN: choose c1 c2 implements the model's choose m1 m2 (Async-style:
   the result is the winner's result with the loser still running, as a
   computation value implementing the model's loser; ties go left; if the
   right side wins while the left has requests in flight, choose waits one
   round so that the loser gets their responses).  Needs both sides
   well-formed. *)
Theorem choose_spec:
  wf m1 ∧ wf m2 ∧
  COMP p ACT A (SNAPSHOT READY (R : 'r -> v -> bool)) m1 c1 ∧
  COMP p ACT B (SNAPSHOT READY R) m2 c2 ⇒
  app (p:'ffi ffi_proj) choose_v [c1; c2] emp
    (POSTv v. &COMP p (ACT : 'act -> v -> bool)
                (CHOOSE_RES p ACT A B (SNAPSHOT READY R))
                (SNAPSHOT READY R) (choose m1 m2) v)
```

Cost: about 500 lines (model ~250, CF ~250). The estimate in 05 was
300–450. The overrun is in the tactic plumbing for the case split, not in
the model.

With this, the whole Level 1 library of the model (`return`, `wait`,
`emit`, `bind`, `both`, `choose`, plus `never` and `poll`) has CF specs
against the model's own definitions.

## 3. What remains (estimates)

- **Sockets instantiation**: see §1. Plumbing plus encodings, maybe 300–500
  lines, mostly in encodings and the round step.
- **Recursion** (`fix`, loops like the echo server) in CakeML: CakeML's own
  recursion gives the code. The spec needs `STEPA` for a model `fix`. The
  approximation lemma handles the coinduction, and the model's
  `fix_unfold` gives the one-step equation. I expect this to be about the
  size of `wait_spec` per loop, once a generic "guarded recursion" CF lemma
  exists (~150 lines).
- **Scheduler with many tasks (M2)** and **Level 2**: unchanged from 05 §4.
- **A non-zero `now`**: add a time component to the world's answer. This
  is trivial in this framework (one more field in `wsnap`).

## 4. Assumptions made

1. **One FFI call per round** (`round`): the world sees the whole round's
   batch of actions at once. This is the round-level "(state, actions) →
   (snapshot, state)" of the brief. A per-call world (one FFI call per
   action) is the special case where `step` folds a per-action function.
2. **Bytes everywhere**: actions, responses and readiness are bytes.
   Readiness is `nready` bytes read as a set. `now` is 0 (as in 05).
3. **The world state is stored through an injective `enc`**, part of the
   world record. The FFI function decodes with `@`.
4. **`nready` is carried in the loop state** `(nr, c)`, since the code is
   fixed and the world a parameter.
5. **Buffer layout**: actions then `nready` zero bytes out; responses then
   readiness in.
6. **`choose` computes `acts1 @ acts2` before the case split**, even in the
   left-wins case where it is unused. This kept the four cases uniform in
   the proof, at the cost of one unneeded append when the left side has
   already finished.
7. **`choose`'s loser is returned as the CakeML pair it was given (or
   polled into)**. In particular, when the left side wins at once, the
   loser still carries its own first-round actions, which are emitted when
   the caller next runs it. This is exactly the model's `suspended m2 []
   = m2`.
8. **The work is additive**: the new directory `async/cf-reactive/` and
   `async/design/10-cf-reactive.md`, `HANDOFF-reactive.md`. Nothing else
   was changed, and the socket worker's branch was not touched.
