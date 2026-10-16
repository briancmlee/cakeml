# 05: Actions and responses in the CF layer, and the event loop's trace

Status: **steps 1, 2 and 4 done, step 3 half done** (`both` proved,
`choose` estimated and deferred). There are no cheats, and `Holmake -j2`
in `async/cf-actions/` is green. Branch `spike/cf-actions`, stacked on
`spike/cf-loop`, with `spike/async-level2` (the HOL model) merged in.

This note is for a reader who knows OCaml and some HOL but wasn't in the
earlier discussions. Background:

- `01-semantics.md` covers the HOL model: computations as functions from
  snapshot histories to outcomes (actions plus result), positional routing,
  `suspended`, `both`, `choose`.
- `02-cf-feasibility.md` and `03-cf-loop.md` cover the results-only CF layer:
  residuals, `STEP`, the approximation-then-limit lemma, and the cfDiv loop.

The gap that 03 left open: the event loop's `POSTd` postcondition only
talks about the I/O trace, and the trace had nothing to do with the
computation. This note closes that gap for a restricted world. The library
now emits actions and receives responses exactly as the model says, and
the loop performs those actions through an FFI. So its trace *is* the
model's action log over the snapshots the world provides.

## 1. The representation

```sml
datatype ('act, 'w, 'a) step =
    Done 'a
  | Pending ('w -> 'act list * ('act, 'w, 'a) step)
```

A computation value is a **pair `(acts, s)`**: the actions it emits in its
current round, and its residual `s`. Polling a `Pending k` with the next
snapshot `w` calls `k w`, which returns the next round's `(acts', s')`.
The model's outcome is `<| actions; result |>`, and the pair mirrors it
round by round: `acts` is the round's slice of `actions`, and `s` says
whether `result` is `SOME x` (`Done x`) or `NONE` (`Pending k`).

A snapshot is the CakeML triple `(ready, now, results)`, matching the
model's record. `results` holds the responses to the previous round's
actions, in emission order (positional routing, as in the model).

The library (`asyncCfActProgScript.sml`) is plain CakeML with no refs:

```sml
fun return x = ([], Done x);
fun poll c w = case c of (acts, s) => case s of Done x => ([], s) | Pending k => k w;
fun wait p = ([], Pending (fn w => case p w of Some a => ([], Done a) | None => wait p));
fun never u = wait (fn w => None);
fun emit a = ([a], Pending (fn w => case w of (rdy, t, res) =>
               case res of [] => never () | r :: rs => ([], Done r)));
fun skip k s = case s of Done x => s
  | Pending g => Pending (fn w => case w of (rdy, t, res) => g (rdy, t, List.drop res k));
fun bind c f = case c of (acts, s) => case s of
    Done x => (case f x of (acts2, s2) => (acts @ acts2, skip (List.length acts) s2))
  | Pending k => (acts, Pending (fn w => bind (k w) f));
```

`skip` is the implementation of the model's `skip_results`. When `m`
finishes in the round in which `bind m f` starts `f x`, the next
snapshot's first `LENGTH acts` responses belong to `m`, so `f x`'s first
poll must not see them. `both` (`asyncCfActBothScript.sml`) concatenates
the two sides' actions and gives the left side the first `LENGTH acts1`
responses (`List.take`) and the right side the rest (`List.drop`).

**Alternatives considered** (briefly):

- `Done` and `Pending` each carry the round's actions
  (`Done of 'act list * 'a | Pending of 'act list * (...)`). This is
  isomorphic to the pair. The pair matches "poll returns `(actions,
  residual)`" (01 §11) directly, and keeps `Done`/`Pending` exactly as in
  the results-only spike.
- A free-monad constructor `Emit of 'act * step`, which emits one action and
  continues in the same round. Collecting a round's actions then needs a
  traversal, and the refinement statement no longer lines up with the
  model's `new_actions` in one step.
- `Done` without actions, so that only settled computations can be
  represented. Then `bind` needs no `skip`, but the representation covers
  less than the model. The general version cost one small function (`skip`)
  and one lemma (`skip_spec`), so I kept the general one.

## 2. The predicate

```
(* STEPA p ACT RES WORLD m s: the residual s implements the model computation m *)
CoInductive STEPA:
  (∀m A x xv. m = finished A x ∧ RES x xv ⇒
     STEPA p ACT RES WORLD m (DoneV xv)) ∧
  (∀m kv. (m []).result = NONE ∧
     (∀w wv. WORLD w wv ⇒
        returns p kv [wv]
          (POLL_RESULT ACT (STEPA p ACT RES WORLD) (suspended m [w]))) ⇒
     STEPA p ACT RES WORLD m (PendingV kv))
End

(* v = (acts, s) with acts = m's first-round actions and RESID m s *)
POLL_RESULT ACT RESID m v ⇔
  ∃av sv. v = Conv NONE [av; sv] ∧ LIST_TYPE ACT (m []).actions av ∧ RESID m sv

(* the CakeML pair v implements m *)
COMP p ACT RES WORLD m v ⇔ POLL_RESULT ACT (STEPA p ACT RES WORLD) m v
```

- `ACT`, `RES` and `WORLD` relate actions, results and snapshots to CakeML
  values. `SNAPSHOT READY R` is the relation for the triple, with `R` for
  the responses. The ready set's representation is left to `READY`.
- `finished A x` and `suspended m [w]` are **the model's own definitions**
  (`asyncChooseScript.sml`). `suspended m [w]` is "m with snapshot `w`
  delivered, its poll with `w` still to come". So the residual after a
  poll with `w` implements exactly that, and its first-round actions are
  m's actions in round 1 (`suspended_one_actions_NIL`):

  ```
  (suspended m [w] []).actions = new_actions (log_of m) [w]
  ```

  After any number of polls (`suspended_suspended_one`, plus the model's
  `suspended_first_poll`, both needing `wf m`), **each poll emits exactly
  the model's `new_actions` for that round**.
- `returns p f args R` means that calling `f` terminates with a value
  satisfying `R`, from the empty heap, keeping no heap (pure callbacks, as
  in 02).
- `STEPA` is coinductive because a computation may stay pending forever.
  As in 03, proofs go through finite approximations `STEPAn` and one
  packaged limit lemma:

  ```
  Theorem app_COMP_of_approx:
    args ≠ [] ∧
    (∀n. app p f args H (POSTv v. &POLL_RESULT ACT (STEPAn p ACT RES WORLD n) m v)) ⇒
    app (p:'ffi ffi_proj) f args H (POSTv v. &COMP p ACT RES WORLD m v)
  ```

  It reuses `app_forall` from `async/cf-spike/asyncCfDetScript.sml` unchanged.

## 3. What is proved

All statements are against the real model in `async/model` (the
Holmakefile INCLUDES it), not a copy.

### Model-side lemmas (`asyncCfActModelScript.sml`, `asyncCfActBothModelScript.sml`)

There is one lemma per implementation step, saying what
`suspended (...) [w]` is:

| lemma | statement (abridged) |
|---|---|
| `suspended_finished_one` | `suspended (finished A x) [w] = finished [] x` |
| `suspended_wait_SOME/NONE` | `p w = SOME a ⇒ … = finished [] a`; `p w = NONE ⇒ … = wait p` |
| `suspended_emit_CONS/NIL` | `w.results = r :: rs ⇒ … = finished [] r`; `w.results = [] ⇒ … = never` |
| `bind_finished` | `bind (finished A x) f = prepend A (skipping (LENGTH A) (f x))` |
| `suspended_bind` | `wf m ∧ (m []).result = NONE ⇒ suspended (bind m f) [w] = bind (suspended m [w]) f` |
| `suspended_both` | `wf m1 ∧ wf m2 ⇒ suspended (both m1 m2) [w] = both (suspended m1 [take_snap k w]) (suspended m2 [skip_snap k w])`, with `k = LENGTH (m1 []).actions` |
| `both_finished_finished` | `both (finished A x) (finished B y) = finished (A ++ B) (x, y)` |
| `suspended_suspended_one` | `wf m ⇒ suspended (suspended m r) [w] = suspended m (r ++ [w])` |

`prepend A g` (g with `A` emitted first) and `skipping k g` (g with the first
`k` results of its first snapshot removed) are the only new notions. Both
are only needed for bind's finished case. `suspended_both` is a direct
corollary of the model's `both_split`.

### CF specs (`asyncCfActSpecScript.sml`, `asyncCfActBothScript.sml`), verbatim

```
(* MAIN: return x builds a finished computation that has emitted nothing. *)
Theorem return_spec:
  RES x xv ⇒
  app (p:'ffi ffi_proj) return_v [xv] emp
    (POSTv v. &COMP p ACT RES WORLD (return x) v)

(* MAIN: polling with snapshot w returns the next round's actions and a
   residual: together they implement the model computation with w delivered. *)
Theorem poll_spec:
  COMP p ACT RES WORLD m cv ∧ WORLD w wv ⇒
  app (p:'ffi ffi_proj) poll_v [cv; wv] emp
    (POSTv v. &COMP p ACT RES WORLD (suspended m [w]) v)

(* MAIN: wait f emits nothing and finishes at the first snapshot w with
   f w = SOME a, with result a. *)
Theorem wait_spec:
  (∀w wv. WORLD w wv ⇒ returns p fv [wv] (OPTION_TYPE RES (f w))) ⇒
  app (p:'ffi ffi_proj) wait_v [fv] emp
    (POSTv v. &COMP p ACT RES WORLD (wait f) v)

(* MAIN: emit a emits a in its first round and finishes at the next
   snapshot, with the first response in it.  With no response it never
   finishes, as in the model. *)
Theorem emit_spec:
  ACT a av ⇒
  app (p:'ffi ffi_proj) emit_v [av] emp
    (POSTv v. &COMP p ACT R (SNAPSHOT READY R) (emit a) v)

(* MAIN: bind m g implements the model's bind m g ... The actions of each
   round, including the round in which m finishes and g x starts, are
   exactly the model's. *)
Theorem bind_spec:
  wf m ∧ COMP p ACT A (SNAPSHOT READY R) m mv ∧
  (∀x xv. A x xv ⇒
     returns p gv [xv]
       (COMP p ACT B (SNAPSHOT READY (R : 'r -> v -> bool)) (g x))) ⇒
  app (p:'ffi ffi_proj) bind_v [mv; gv] emp
    (POSTv v. &COMP (p:'ffi ffi_proj) (ACT : 'act -> v -> bool) B
                (SNAPSHOT READY R) (bind m g) v)

(* MAIN: both c1 c2 implements the model's both m1 m2 ... *)
Theorem both_spec:
  wf m1 ∧ wf m2 ∧
  COMP p ACT A (SNAPSHOT READY (R : 'r -> v -> bool)) m1 c1 ∧
  COMP p ACT B (SNAPSHOT READY R) m2 c2 ⇒
  app (p:'ffi ffi_proj) both_v [c1; c2] emp
    (POSTv v. &COMP p (ACT : 'act -> v -> bool) (PAIR_TYPE A B)
                (SNAPSHOT READY R) (both m1 m2) v)
```

Helpers: `never_spec`, `skip_spec`, `bind_Done_spec_n`, `wait_spec_n`,
`bind_spec_n` and `both_spec_n` (the approximations), and `STEPA_prepend`.

`wf` (the model's well-formedness: the log only grows, and finished stays
finished) is needed exactly where the model's log is split across
rounds: `bind` (`suspended_bind`), `both` (`both_split`) and the loop.
Every library computation is `wf` (the model proves `wf_return`,
`wf_wait`, `wf_emit`, `wf_bind`, `wf_both`, ...).

### The event loop (`asyncCfActWorldScript.sml`, `asyncCfActLoopScript.sml`)

```sml
fun do_act a = let val buf = Word8Array.array 1 a
                   val _ = #(act) "" buf in Word8Array.sub buf 0 end;
fun perform acts = case acts of [] => []
                   | a :: rest => let val r = do_act a in r :: perform rest end;
fun get_ready u = (* #(ready) into a 1-byte buffer, return the byte *);
fun step c = case c of (acts, s) =>
               let val rs = perform acts
                   val b = get_ready ()
               in poll c (b, 0, rs) end;
fun run c = run (step c);
```

**The world** (a self-contained FFI model, not basis_ffi) is an infinite
byte stream `ws`. `act` sends the action byte in a one-byte buffer, and the
world overwrites it with the next byte of the stream (the response).
`ready` returns the next byte `b`, and the snapshot's ready set is `{b}`.

**The snapshot sequence the world provides**, as a HOL function of `m` and
`ws`:

```
rounds m ws 0 = ([], 0)
rounds m ws (SUC n) =
  let (h, pos) = rounds m ws n;
      k = LENGTH (new_actions (log_of m) h)
  in (h ++ [world_snap (sdrop pos ws) k], pos + k + 1)

world_snap ws k = <| ready := {ws k}; now := 0; results := GENLIST ws k |>
round_events m ws n =       (* with (h, pos) = rounds m ws n *)
  MAP2 act_event acts (GENLIST (sdrop pos ws) (LENGTH acts)) ++
  [ready_event (sdrop pos ws (LENGTH acts))]
  where acts = new_actions (log_of m) h
```

Round n performs the model's new actions of round n, each paired with the
world's response, then reads the ready byte. The next snapshot is built
from exactly those bytes.

```
(* MAIN: one loop iteration.  If cv implements m, the iteration performs
   m's first-round actions against the stream ws (one event each, with the
   world's responses), reads the ready byte, and returns a value
   implementing m with the resulting snapshot delivered. *)
Theorem step_spec:
  limited_parts io_names p ∧
  COMP p WORD A (SNAPSHOT READY1 WORD) m cv ⇒
  app (p:'ffi ffi_proj) step_v [cv] (IOS ws [])
    (POSTv v. &COMP p WORD A (SNAPSHOT READY1 WORD)
                 (suspended m [world_snap ws (LENGTH (m []).actions)]) v *
              IOS (sdrop (LENGTH (m []).actions + 1) ws)
                 (round_events_of (m []).actions ws))

(* MAIN: the event loop never terminates, and its I/O trace is the
   concatenation, over all rounds i, of round_events m ws i ... *)
Theorem run_spec:
  limited_parts io_names p ∧ wf m ∧
  COMP p WORD A (SNAPSHOT READY1 WORD) m cv ⇒
  app (p:'ffi ffi_proj) run_v [cv] (IOS ws [])
    (POSTd io. io = LFLATTEN (LGENLIST (λi. fromList (round_events m ws i)) NONE))

(* MAIN: the trace and the model agree.  The actions performed in the
   first n+1 rounds of the loop's trace are exactly the model's action log
   after the n snapshots the world has provided. *)
Theorem trace_actions_rounds:
  wf m ⇒
  trace_actions (FLAT (GENLIST (round_events m ws) (SUC n))) =
  (m (hist m ws n)).actions
```

Here `trace_actions` keeps the action bytes of the `act` events in a
finite trace, and `hist m ws n = FST (rounds m ws n)`.

Read together, `run_spec` and `trace_actions_rounds` say: **the loop
diverges, and the actions in its trace are, round by round, exactly the
model computation's action log over the snapshot sequence that the world
(the byte stream) provides. Each snapshot carries exactly the responses
recorded in the trace.** The loop invariant is `COMP … (suspended m (hist
m ws i))`. The proof is `xcf_div_rule IMP_app_POSTd_one_FFI_part_FLATTEN`,
with `step_spec` for each iteration, as in 03.

## 4. What wasn't done, and why

1. **`choose`: estimated and deferred**, not attempted. The pieces it needs:
   - A model lemma for `suspended (choose m1 m2) [w]` in each case: nobody
     finished (it behaves like `both`), left wins, right wins with no
     requests in flight, and right wins with requests in flight (the
     one-round delay). The model has `choose_running`, `choose_at`,
     `choose_left_wins`, `choose_right_wins(_later)` and `both_split`, but no
     one-poll split for choose. Writing one is maybe 100–150 lines.
   - A CakeML `choose` with a third state for the delay round ("right won,
     waiting one poll for the left side's responses").
   - A result relation that contains computations: the loser is returned as
     a CakeML pair, so `RES` for `choose` is
     `SUM_TYPE (PAIR_TYPE A (COMP p ACT B W)) (PAIR_TYPE (COMP p ACT A W) B)`
     on the model's `suspended m2 r` / `suspended m1 l`. `COMP` is already a
     fixed point, so this is not circular. But the loser's model value is
     `suspended m2 (right_view m1 m2 p)` for the whole prefix `p`. Matching it
     with the residual held after one-poll steps needs a lemma relating
     iterated `suspended` to the views (in the spirit of `views_split`).

   Estimate: **300–450 lines** (model 150–200, CF 150–250), one to two
   working sessions. The risk is in the view bookkeeping, not in CF: the
   `both` proof shows that the CF side of a two-sided combinator is
   routine once the model has a one-poll split lemma.
2. **A scheduler with many tasks** (01 §11's M2): a pool of `(acts, s)`
   pairs, each polled with its own share of the responses. In this
   representation, the pool is `both` folded over the tasks (positional
   routing composes). A dynamic pool (spawning) needs a model notion of a
   task list first (M2's pure step function). Estimate: M2's pure
   scheduler, then a CF `step` over a list of pairs. That is about the size
   of `both` per operation (poll-all, add, remove), plus a list version of
   `suspended_both`: maybe 400–600 lines including the model side. The event
   loop proof would not change shape: `step_spec`'s invariant just becomes
   "the pool implements the M2 state".
3. **Level 2 (declared interest)**: the loop would block in `select` on the
   union of the interest sets instead of polling every round. On the CF
   side, `Pending` would carry the interest set (as `comp2` does in the
   model), and `STEPA` would relate it to the model's `interest`. The loop's
   world would then skip quiet rounds. The model's `quiet` and
   `no_progress_without_ready_event` justify that the skipped polls change
   nothing. Estimate: a `STEPA2` mirroring `STEPA` with one extra field
   (about 1.2× the current Prog+Spec, ~600 lines), plus a loop whose FFI
   models blocking. The trace statement then has to say which rounds are
   skipped.
4. **The event-loop world is restricted** (see "Assumptions made"): bytes;
   an oblivious response stream; `now = 0`; a one-byte ready set. A richer
   world changes the FFI model and `world_snap`, not the proof's shape.
   The one structural gap: the world here can't make a response depend on
   the action. Doing that needs an FFI state that is a function of the
   action history (e.g. an oracle in the FFI state). `trace_actions_rounds`
   is stated over `rounds`, so it would carry over unchanged.
5. **The result of the computation isn't observed** by the loop. It polls
   forever, even after `Done` (it then performs no actions and keeps
   reading ready bytes), as in 03. A loop that exits on `Done` would be
   ordinary terminating CF plus the same invariant.
6. **Callbacks are pure** (`returns` keeps no heap), as in 02. Effectful
   callbacks would need a heap invariant in `returns` and in
   `app_forall`.

## 5. Assumptions made

I made these choices without asking. Each is the simplest or most
conservative option, and each can be changed without touching the rest:

1. **Representation**: a poll returns `(actions, residual)`; `Done`
   carries no actions (the pair does). Closest to the model's `outcome`.
2. **The general representation, not settled-only**: `bind` handles a
   first part that emits in its finishing round, via `skip` (the model's
   `skip_results`).
3. **`skip k s` always wraps the residual**, even when `k = 0`. This is
   simpler to verify, at the cost of one closure per finished `bind`.
4. **Specs that split the model's log across rounds assume `wf`** of the
   computations involved (`bind`'s first part, both sides of `both`, the
   loop's computation), rather than building `wf` into `STEPA`.
5. **Snapshots are CakeML triples `(ready, now, results)`**, with the ready
   set's representation left abstract (`READY`), `now` a `num`, and the
   responses a list.
6. **The event-loop world**: actions and responses are bytes; one FFI call
   `act` per action (action byte in, response byte out, in one buffer);
   one call `ready` per round, whose byte `b` is the ready set `{b}`;
   `now` is always 0; both calls consume one infinite byte stream in order
   (an oblivious world, `Stream` FFI state, as in 03).
7. **The loop polls `Done` forever** (as in 03), and the trace includes
   the `ready` events.
8. **`both`'s CakeML code** returns `Done (x, y)` only when both sides are
   `Done` in the same round, otherwise `Pending`. This matches the
   model's `both` exactly. No early exit.
9. **The order of work**: I did the event loop (step 4) before `both`
   (step 3), because the loop connection was the stated top risk. Then
   `both`. `choose` was left as an estimate.
10. **File layout**: seven small theories (87–288 lines each) in
    `async/cf-actions/`, depending on `async/model` and `async/cf-spike`
    (for `app_forall` only). Nothing outside `async/cf-actions/` and
    `async/design/` was touched, and neither was the base or basis_ffi.
    The Holmakefile uses the base's `basis/basis-heap` (CONVENTIONS.md).
