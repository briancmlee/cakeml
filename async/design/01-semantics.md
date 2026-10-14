# Asynchronous I/O for CakeML: the semantics (M1 design spike)

This note describes a small, fully proved HOL4 model of monadic asynchronous
programming in the style of OCaml's Async/Lwt (`return`, `bind`, `map`,
`both`, `choose`), and the decisions behind it. It is written for a reader
who knows OCaml and some HOL but was not part of the design discussion.

The model is in `async/model/` (HOL only, no CakeML dependency). Everything
quoted below is from those scripts and is proved, with no `cheat`.
Conjectures are listed separately in §12.

Contents:

1. [The idea in one page](#1-the-idea-in-one-page)
2. [Level 1: plain polling](#2-level-1-plain-polling)
3. [Actions, responses and routing](#3-actions-responses-and-routing)
4. [choose: nothing is lost](#4-choose-nothing-is-lost)
5. [Well-formedness and the equality notion](#5-well-formedness-and-the-equality-notion)
6. [The recursion rule, and the echo loop](#6-the-recursion-rule-and-the-echo-loop)
7. [Level 2: declared interest](#7-level-2-declared-interest)
8. [Decisions and rejected alternatives](#8-decisions-and-rejected-alternatives)
9. [The optional ownership discipline](#9-the-optional-ownership-discipline)
10. [The world model and environment assumptions (M3/M4)](#10-the-world-model-and-environment-assumptions-m3m4)
11. [Implementation and refinement plan](#11-implementation-and-refinement-plan)
12. [What is proved, and what is conjectured](#12-what-is-proved-and-what-is-conjectured)
13. [Proposed MAIN theorems](#13-proposed-main-theorems)
14. [What current CakeML offers (open problem 3)](#14-what-current-cakeml-offers-open-problem-3)
15. [Risks](#15-risks)
16. [Decisions needed from the user](#16-decisions-needed-from-the-user)

---

## 1. The idea in one page

A program is polled once per **round**. Before each round except the first,
the outside world provides a **snapshot**: which events are ready (an fd is
readable, a timer expired, ...), the time, and the **responses** to the
actions the program emitted in the previous round. The meaning of a
computation is a function of the **history** of snapshots it has been polled
with:

```
snapshot = <| ready : 'e set ; now : num ; results : 'r list |>
outcome  = <| actions : 'act list ; result : 'x |>

computation : ('e,'r) snapshot list -> ('act, 'a option) outcome
```

- The history is chronological, oldest first. The empty history is the
  first poll, round 0. Polling with a history `h` is round `LENGTH h`.
- `(m h).actions` is everything `m` has emitted so far. It only grows, and
  it is the program's only way to affect the world.
- `(m h).result = SOME x` means `m` has finished with `x`; once finished it
  stays finished.

The whole system runs as an alternating loop: poll, emit actions, the world
performs them, next snapshot. Snapshot n+1 depends only on the actions
emitted up to round n, so nothing is circular.

The two primitives are `wait p` (finish at the first snapshot `s` with
`p s = SOME x`) and `emit a` (emit `a` now, and finish with its response).
Everything else (`return`, `bind`, `map`, `both`, `choose`, loops) is built
on top. There are two levels:

- **Level 1** is plain polling, as above.
- **Level 2** adds, while a computation is unfinished, the set of events it
  is waiting for. An `erase` function forgets that set, and erasure commutes
  with every combinator, so all Level 1 laws transfer. Level 2 additionally
  proves "no progress without a declared ready event", which is what lets a
  scheduler block in `select` instead of busy-polling.

## 2. Level 1: plain polling

**Primitives** (`asyncLevel1Script.sml`):

```
Definition wait_def:
  wait p h = <| actions := []; result := first_some p h |>
End

Definition emit_def:
  emit a h =
    <| actions := [a];
       result := case h of [] => NONE | s :: _ => oHD s.results |>
End
```

- `return x h = <| actions := []; result := SOME x |>`.
- `never = wait (λs. NONE)`.
- `wait` and `emit` both **need a snapshot** to finish:
  `(wait p []).result = NONE` and `(emit a []).result = NONE`. This is what
  makes loops well-founded (§6).

**bind.** When `m` first finishes, in round n, the continuation starts *in the
same round n*. So `return`, `map` and further pure steps cost nothing, and an
`emit` in the continuation is emitted immediately. The continuation only
*sees* the snapshots after round n:

```
Definition bind_def:
  bind m f h =
    case first_prefix (λp. (m p).result ≠ NONE) h of
      NONE => <| actions := (m h).actions; result := NONE |>
    | SOME n =>
        let hm = TAKE n h;
            k = LENGTH (new_actions (log_of m) hm);
            next = f (THE (m hm).result) (skip_results k (DROP n h))
        in
          <| actions := (m hm).actions ++ next.actions;
             result := next.result |>
End
```

- `first_prefix P h` is the length of the shortest prefix of `h` satisfying
  `P`.
- `skip_results k` drops the first `k` responses of the first snapshot,
  namely the responses to `m`'s actions in its last round (§3).

The two characterising theorems:

```
bind_running:    (∀n. n ≤ LENGTH h ⇒ (m (TAKE n h)).result = NONE) ⇒
                 bind m f h = <| actions := (m h).actions; result := NONE |>
bind_continues:  first_done m h1 x ⇒
                 ∀f h2. bind m f (h1 ++ h2) =
                   let next = f x (skip_results (LENGTH (new_actions (log_of m) h1)) h2)
                   in <| actions := (m h1).actions ++ next.actions; result := next.result |>
```

**both** runs two computations side by side. Both sides see the same ready
sets and times. In each round the left side's actions come first, and each
side only receives the responses to its own actions:

```
Definition both_def:
  both m1 m2 h =
    <| actions := par_log m1 m2 h;
       result :=
         case ((m1 (left_view m1 m2 h)).result,
               (m2 (right_view m1 m2 h)).result) of
           (SOME x, SOME y) => SOME (x, y)
         | _ => NONE |>
End
```

`left_view`/`right_view` (via `par_views` in `asyncCoreScript.sml`) give
each side the snapshots with its share of the results. `par_log`
interleaves the two sides' new actions round by round.

**map**: `map f m h = <| actions := (m h).actions; result := OPTION_MAP f (m h).result |>`.

**choose** is the subject of §4.

## 3. Actions, responses and routing

**Every interaction with the world is an emitted action.** Actions go into
the output log, which only grows. Their responses, including read results,
arrive in later snapshots. A read is `emit (Read fd)`; `readLine` and the
like are library functions on top.

**Positional routing (the key decision).** Every action emitted in round n
gets exactly one response. Responses arrive in snapshot n+1's `results`, at
the action's position within round n's batch. Tags are positions, so no
identifiers are needed. Each combinator routes responses down the program
tree:

- `both`/`choose`: the left side gets the first `k1` results of each
  snapshot, where `k1` is the number of actions it emitted in the previous
  round. The right side gets the rest.

  ```
  par_views acts1 acts2 h = ... (h1 ++ [s with results := TAKE k1 s.results],
                                 h2 ++ [s with results := DROP k1 s.results])
  ```
- `bind`: the continuation gets the results that are not responses to `m`'s
  actions.

This is the pure counterpart of the implementation, which delivers each
response straight to the requester's ref cell. In the implementation the
order doesn't matter at all; in the model the order is how a response finds
its requester.

Worked examples, all proved by `EVAL` in `asyncEchoScript.sml`.
`snap rdy res` is a snapshot with those ready events and results.

```
bind (emit "a") (λx. bind (emit "b") (λy. return (x, y)))
     [snap {} [1]; snap {} [2]]
  = <| actions := ["a"; "b"]; result := SOME (1, 2) |>

both (emit "a") (emit "b") [snap {} [1; 2]]
  = <| actions := ["a"; "b"]; result := SOME (1, 2) |>

(* in round 1 only the left side emits (c), so it gets all of snapshot 2 *)
both (bind (emit "a") (λx. emit "c")) (emit "b") [snap {} [1; 2]; snap {} [3]]
  = <| actions := ["a"; "b"; "c"]; result := SOME (3, 2) |>
```

**emit waits for its response.** `emit a` finishes at the next snapshot,
with its response. So `wait` and `emit` are enough, and a fire-and-forget
write still costs one round (it finishes when the acknowledgement
`Written` arrives).

**Does bind lose responses?** `bind m f` does not pass `f x` the responses
to the actions that `m` emitted *in the round in which it finished*.
Dropping them would be a silent loss (for example, a read emitted in that
round). We address this with an invariant rather than by changing `bind`:

```
Definition settled_def:
  settled m ⇔ ∀h. (m h).result ≠ NONE ⇒ new_actions (log_of m) h = []
End
```

A settled computation emits nothing in the round in which it finishes, so
there is nothing for `bind` to drop:

```
(* MAIN *) bind_settled_continues:
  settled m ∧ first_done m h1 x ⇒
  bind m f (h1 ++ h2) =
    <| actions := (m h1).actions ++ (f x h2).actions; result := (f x h2).result |>
```

Every primitive is settled, and every combinator preserves settledness:
`settled_return/wait/emit/never`, `settled_map`, `settled_bind`,
`settled_both`, `settled_choose`, `settled_fix`, and `settled_echo` for the
echo loop. So **for programs built from the library, bind never drops a
response.**

- The only way to emit in a finishing round used to be the losing side of
  an old-style `choose`. The new `choose` (§4) never does that.
- We kept the `skip_results` in `bind` instead of removing it, because with
  it the monad laws hold as exact equalities without assuming
  settledness.

## 4. choose: nothing is lost

**Decision (from the user).** `choose` is Async-style. It returns the
winner's result together with the loser *still running*, as a computation
the caller can continue or drop. There is no implicit cancellation, and ties
go to the left:

```
choose m1 m2 : (('a × 'b computation) + ('a computation × 'b)) computation
```

The loser must not lose the responses to its requests in flight. A pure
value created in round n cannot contain the responses that arrive in round
n+1. So the loser is returned **suspended**: every response to its earlier
actions has been delivered, and its next poll is still to come. Whoever holds
the loser makes that poll, whenever they like.

```
(* the rest of m after it has been polled with p *)
resume m p h = <| actions := DROP (LENGTH (m p).actions) (m (p ++ h)).actions;
                  result := (m (p ++ h)).result |>

(* m polled with every proper prefix of r; its poll with r is still to come *)
suspended m r = if r = [] then m else (λh. resume m (FRONT r) (LAST r :: h))
```

Let n be the first round in which a side has finished:

- **m1 wins** (including ties): m2 is *not* polled in round n. The loser is
  `suspended m2 r`, i.e. m2 with snapshot n delivered but not yet acted on.
- **m2 wins**: m1 has already been polled in round n.
  - If that poll emitted nothing, the loser is m1 as it is.
  - Otherwise choose **waits one more round** for the responses, then
    returns m1 with them delivered.

The theorems `choose_left_wins`, `choose_right_wins` and
`choose_right_wins_later` state exactly this. Invariant: **a returned loser
never has requests in flight**, so nothing is lost even if the caller polls
it much later.

The headline theorem is an exact equality:

```
Definition rejoin_def:
  rejoin r = case r of INL (x, rest2) => both (return x) rest2
                     | INR (rest1, y) => both rest1 (return y)
End

(* MAIN: nothing is lost *)
Theorem choose_rejoin:
  wf m1 ∧ wf m2 ⇒ bind (choose m1 m2) rejoin = both m1 m2
```

Running `choose` and then continuing with the winner's result alongside the
loser gives exactly the same actions, in the same order, and the same
results as running both sides with `both`.

- The continuation has the shape of `both` rather than
  `map (λy. (x, y)) rest2`. `both` passes each side only its own share of
  the responses, while a bare `map` would also see any extra responses an
  ill-behaved world sends.
- With a world that sends exactly one response per action, the two are
  equal.

Also proved: `wf (choose m1 m2)` holds *unconditionally*, and
`settled_choose`. The `resume` lemmas the user asked for are proved too:

```
wf_resume:        wf m ⇒ wf (resume m p)
resume_resume:    wf m ⇒ resume (resume m p) q = resume m (p ++ q)
resume_finished:  wf m ∧ (m p).result = SOME x ⇒ resume m p = return x
```

The key lemma behind `choose_rejoin` is that `both` can be split at any
point:

```
(* MAIN *) both_split:
  wf m1 ∧ wf m2 ⇒
  both m1 m2 (p ++ q) =
    let rest = both (suspended m1 (left_view m1 m2 p))
                    (suspended m2 (right_view m1 m2 p)) q
    in <| actions := log_before m1 m2 p ++ rest.actions; result := rest.result |>
```

EVAL examples:

```
(* ties go left, and the loser keeps the response to its request *)
bind (choose (wait (λs. if 3 ∈ s.ready then SOME 3 else NONE)) (emit "b")) rejoin
     [snap {3} [7]]
  = <| actions := ["b"]; result := SOME (3, 7) |>

(* return 5 wins at once, but emit "a" has a request in flight *)
choose (emit "a") (return 5) [] = <| actions := ["a"]; result := NONE |>
bind (choose (emit "a") (return 5)) rejoin [snap {} [42]]
  = <| actions := ["a"]; result := SOME (42, 5) |>
```

Consequences to be aware of:

1. **The one-round delay.** When the right side wins while the left side
   has requests in flight, choose finishes one round late. This is
   unavoidable in a pure model. The implementation would naturally finish
   at once, because its cells buffer responses; it should mirror the delay
   so that the refinement is simple (the delay costs one poll, not one
   blocking wait, since the responses are already due).
2. **A suspended loser sees a stale snapshot** (old ready set and time) at
   its first poll. Readiness is only a hint (§9) and timers only fire late,
   never early, so this is harmless.
3. **Recursion through choose's arguments** is not covered by the recursion
   rule (§6). choose's result contains a computation, which is not a
   "shorter-history" quantity. Recursion *in choose's continuation* is fine.
   A loser-dropping variant
   `pick m1 m2 = map (λr. case r of INL (x,_) => INL x | INR (_,y) => INR y) (choose m1 m2)`
   would be non-expansive (not yet proved; see §12).

## 5. Well-formedness and the equality notion

```
Definition wf_def:
  wf m ⇔ ∀h s. (m h).actions ≼ (m (h ++ [s])).actions ∧
               ((m h).result ≠ NONE ⇒ m (h ++ [s]) = m h)
End
```

So the log only grows, and once finished nothing changes:

- `wf_actions_grow: wf m ∧ h1 ≼ h2 ⇒ (m h1).actions ≼ (m h2).actions`;
- `wf_finished_stays: wf m ∧ (m h1).result = SOME x ∧ h1 ≼ h2 ⇒ m h2 = m h1`.

Every primitive and combinator preserves `wf`, and `choose` is well-formed
whatever its arguments.

**The equality notion is plain equality of functions.** No equivalence
relation was needed:

- `bind_left_identity: bind (return x) f = f x`;
- `bind_right_identity: wf m ⇒ bind m return = m`;
- `bind_assoc: wf m ⇒ bind (bind m f) g = bind m (λx. bind (f x) g)`;
- `map_id`, `map_map`, `bind_map` and `map_bind` hold without
  assumptions, and `map_as_bind` needs `wf m`.

The `wf` assumptions are needed because an ill-formed `m` can change its
mind after finishing; `bind` reads `m`'s result only at the first finishing
point.

## 6. The recursion rule, and the echo loop

A loop such as

```
echo fd = bind (readable fd) (λ_.
          bind (emit (Read fd)) (λres.
          case res of Data d => bind (emit (Write fd d)) (λ_. echo fd)
                    | Eof => return ()
                    | _ => echo fd))
```

needs a justification in HOL. Computations are functions of histories, so
`r = body r` is well-defined when `body` only needs `r` on *strictly shorter*
histories. Then `r` on histories of length n is determined by `r` on
lengths below n. This is the usual "contractive map" argument from guarded
recursion. `asyncCoreScript.sml`:

```
Definition guarded_def:
  guarded G ⇔ ∀n r1 r2. (∀p. agree_below n (r1 p) (r2 p)) ⇒
                        agree_below (n + 1) (G r1) (G r2)
End
Definition contractive_def:
  contractive body ⇔ ∀p. guarded (λr. body r p)
End
Definition fix_def:
  fix body p h = FUNPOW body (SUC (LENGTH h)) ARB p h
End

(* MAIN *) fix_unfold: contractive body ⇒ fix body = body (fix body)
(* MAIN *) fix_unique: contractive body ∧ body r = r ⇒ r = fix body
```

- `agree_below n m1 m2` says that `m1` and `m2` agree on histories shorter
  than `n`.
- Loops are parameterised (`'p -> computation`), so a loop can carry state
  such as a buffer or a counter.
- `ARB` is never reached when `body` is contractive. `EVAL` of `fix` works,
  and is fast in the examples.

**The rule** (`asyncLoopScript.sml`): every combinator is non-expansive
(`bind_agree`, `map_agree`, `both_agree`), and a recursive call is allowed
anywhere after something that needs a snapshot to finish:

```
(* MAIN: the recursion rule *)
Theorem guarded_bind:
  (m []).result = NONE ∧ (∀x. nonexpansive (λr. G x r)) ⇒
  guarded (λr. bind m (λx. G x r))
```

In words: **each iteration of a loop must use up at least one snapshot.**
`wait` and `emit` both do (`wait_needs_snapshot`, `emit_needs_snapshot`).
This is why `bind` runs its continuation in the same round but shows it only
later snapshots: a waiting continuation starts no earlier than the next
snapshot, so a loop cannot spin within one round.

Well-formedness and settledness are preserved by `fix` (`wf_fix`,
`settled_fix`), so a contractive body that preserves them gives a
well-formed, settled loop.

**The echo loop is in the model** (`asyncEchoScript.sml`): `echo = fix
echo_body`, with `echo_body_contractive`, `echo_unfold` (the recursive
equation above), `wf_echo` and `settled_echo`. EVAL checks:

```
echo 0 [snap {Readable 0} []; snap {} [Data "hi"]; snap {} [Written]]
  = <| actions := [Read 0; Write 0 "hi"]; result := NONE |>
echo 0 [...; snap {Readable 0} []; snap {} [Eof]]
  = <| actions := [Read 0; Write 0 "hi"; Read 0]; result := SOME () |>
echo 0 [snap {Readable 0} []; snap {} [WouldBlock]; snap {Readable 0} []; snap {} [Data "x"]]
  = <| actions := [Read 0; Read 0; Write 0 "x"]; result := NONE |>
```

**Relation to the CF non-termination logic.** In CakeML, the event loop and
any never-ending task are real non-terminating code, reasoned about with
`POSTd` (§14). The HOL model still has to say what such a loop *means*: a
function of the history, given by `fix`. The CF proof then shows that the
I/O trace of the diverging CakeML program is the limit of the model's
action logs, i.e. that for every prefix of the history the trace so far
matches `(echo fd h).actions`. `fix_unique` is what makes "the model of
the loop" well-defined: the CF side may prove that the code satisfies the
recursive equation, and uniqueness identifies it with `fix`.

## 7. Level 2: declared interest

**Representation** (`asyncLevel2Script.sml`). A Level 2 computation is a
Level 1 computation together with the events it is waiting for:

```
Datatype:
  comp2 = <| run : ('e,'r) snapshot list -> ('act,'a option) outcome ;
             interest : ('e,'r) snapshot list -> 'e set |>
End
status c h = case (c.run h).result of SOME x => Done x
                                   | NONE => Waiting (c.interest h)
erase c = c.run
```

This is the user's `Done 'a | Waiting (event set)` (see `status`), stored as
two functions, so that `erase` is just the `run` field. Every Level 2
combinator is *defined* so that its `run` is the Level 1 combinator, so the
erasure theorems hold by construction:

- `erase_return2`, `erase_emit2`, `erase_map2`,
  `erase_bind2: erase (bind2 c f) = bind (erase c) (λx. erase (f x))` and
  `erase_both2`;
- `erase_wait_on: erase (wait_on e p) = wait (λs. if e ∈ s.ready then p s else NONE)`;
- for choose, erasing the losers too:
  `erase_choose2: map (map_loser erase erase) (erase (choose2 c1 c2)) = choose (erase c1) (erase c2)`.

The Level 1 laws transfer up to erasure (`bind2_left_identity`,
`bind2_right_identity`, `bind2_assoc`). Left identity even holds exactly,
interest included.

The primitive `wait_on e p` declares interest `{e}` and looks only at
snapshots where `e` is ready. `emit2` declares no events: it waits only for
its response. `bind2` waits for what the running part waits for. `both2` and
`choose2` wait for the union over the unfinished sides.

**What Level 2 adds: quiet.** A quiet computation that is unfinished and has
no request in flight makes no progress, now or later, on a snapshot that has
no responses and none of its declared events ready. Such a snapshot can be
*deleted* from the history without changing anything:

```
Definition quiet_def:
  quiet c ⇔
    ∀h s h'.
      (c.run h).result = NONE ∧ new_actions (log_of c.run) h = [] ∧
      s.results = [] ∧ DISJOINT (c.interest h) s.ready ⇒
      c.run (h ++ [s] ++ h') = c.run (h ++ h') ∧
      c.interest (h ++ [s] ++ h') = c.interest (h ++ h')
End

(* MAIN *) no_progress_without_ready_event:
  wf2 c ∧ status c h = Waiting E ∧ new_actions (log_of c.run) h = [] ∧
  DISJOINT E s.ready ∧ s.results = [] ⇒
  c.run (h ++ [s]) = c.run h ∧ status c (h ++ [s]) = Waiting E
```

**Why deletion, rather than "one more poll changes nothing".** The one-step
property is too weak to justify a blocking scheduler. A computation could
remember an irrelevant snapshot (say, its timestamp) without changing its
outcome, and behave differently later. A scheduler that blocks in `select`
never shows the computation those snapshots at all. Deletion is exactly the
statement that this is invisible.

Proved: `quiet_return2`, `quiet_wait_on`, `quiet_emit2`, `quiet_map2`,
`quiet_bind2`, `quiet_both2` and `quiet_choose2`, so every Level 2
combinator preserves quietness.
The general lemma underneath is `first_prefix_delete`: deleting a snapshot
that never changes whether a property holds delays the first point where
it holds by one.

**The escape hatch.** Arbitrary conditions remain expressible by waiting on
an event that is ready in every snapshot, e.g. `Always` in a world that
always reports it:

```
wait_on_always: EVERY (λs. e ∈ s.ready) h ⇒ erase (wait_on e p) h = wait p h
```

Such a computation is quiet only vacuously (it never blocks), which is the
honest price of busy-polling.

**Recursion at Level 2** (`asyncLoop2Script.sml`). We pack a Level 2
computation into one function of the history,
`pack c = λh. (c.run h, c.interest h)`, which lets us reuse the Level 1
guarded-recursion machinery (`fix`, `fix_unfold`, `fix_unique`,
`fix_preserves`) unchanged:

```
fix2 body2 p = unpack (fix (lift_body body2) p)

(* MAIN *) fix2_unfold:   contractive2 body2 ⇒ fix2 body2 = body2 (fix2 body2)
(* MAIN *) guarded2_bind2:
  (c.run []).result = NONE ∧ (∀x. nonexpansive2 (λR. G x R)) ⇒
  guarded2 (λR. bind2 c (λx. G x R))
(* MAIN *) erase_fix2:
  contractive body1 ∧ contractive2 body2 ∧
  (∀R p. erase (body2 R p) = body1 (λq. erase (R q)) p) ⇒
  ∀p. erase (fix2 body2 p) = fix body1 p
(* MAIN *) wf2_fix2:
  contractive2 body2 ∧ (∀R. (∀p. wf2 (R p)) ⇒ ∀p. wf2 (body2 R p)) ⇒
  ∀p. wf2 (fix2 body2 p)
```

The recursion rule is the same as at Level 1. `wf2 c = wf c.run ∧ quiet c`
is preserved by the fixpoint because it is a "closed" property: it only
ever looks at finitely many histories at a time.

**The echo loop at Level 2** (`asyncEcho2Script.sml`). `echo2` is the echo
loop written with `wait_on (Readable fd)`, `emit2`, `bind2` and `return2`.
Proved: `echo2_unfold`, `erase_echo2: erase (echo2 fd) = echo fd`, and
`wf2_echo2: wf2 (echo2 fd)`. So a scheduler may block until `fd` is
readable. EVAL checks confirm what it waits for:

- `Waiting {Readable 0}` at first;
- `Waiting ∅` while its read is in flight (it waits only for the
  response);
- `Waiting {Readable 0}` again after echoing.

## 8. Decisions and rejected alternatives

| Decision | Chosen | Rejected, and why |
|---|---|---|
| Meaning of a computation | function of the history of snapshots (user's 2024 design) | `step = Done 'a \| Pending ('w -> step)`: `wait` needs infinite-depth values, which HOL's inductive datatypes can't hold, and HOL4 has no general codatatype package. Interaction trees: need coinduction for the same reason. |
| Primitives | `wait p` + `emit a` | separate `create p f` (2024); merged into `wait`. |
| Response tagging | positional (§3) | user-chosen tags: freshness becomes a load-bearing discipline. Address/path parameters: break exact left identity and grow without bound in loops. Keying by (round, action): collides when two tasks issue the same read in one round. Global log indices: sub-computations can't know their offset. |
| `bind`'s snapshot convention | continue in the same round, see only later snapshots | continue in the next round (2024): pure steps would cost a round each. |
| Responses at m's last round | skipped by `bind`, but `settled` proves there are none for library programs | not skipping: the laws would need `settled` assumptions. |
| `choose` | Async-style, loser returned suspended (user's decision) | Lwt.pick-style cancellation (the first version): loses in-flight responses (e.g. a read). |
| Equality | plain equality; `wf` hypotheses where needed | an equivalence on well-formed computations: not needed. |
| Recursion | guarded recursion via `fix`/`contractive` | requiring loops to be CakeML-only: the model would have nothing to say about `echo`. |
| Level 2 representation | `run` + `interest` record; erase = run | separate Level 2 definitions with status results: erase commutation would be a page of proof per combinator for no extra insight. |
| Level 2 property | deletion of irrelevant snapshots | one-step "polling again changes nothing" (too weak, §7). |

The right side of `both`/`choose` receives `DROP k1` of the results rather
than `TAKE k2 (DROP k1)`. This keeps laws like `choose_rejoin` exact even
when the world sends extra responses.

## 9. The optional ownership discipline

Reads are honest: a read may return data, `WouldBlock` (readiness was only a
hint, e.g. another task consumed the data) or `Eof`. The model has no fd
ownership. `echo` simply waits again on `WouldBlock` (see the EVAL example in
§6).

Ownership is an *optional* discipline, with its own theorem, never a
foundation. Planned statement for M3:

> If at most one task reads a given fd, then a `Read fd` emitted in the
> round where that task observed `Readable fd` never gets `WouldBlock`.

This needs a world assumption ("a readable fd stays readable until it is
read"). Because of `bind`'s same-round convention, the read is emitted in
the round where readiness was observed, so no other round intervenes. The
assumption that each fd is waited on by at most one task is a property of
the program, checkable syntactically for programs like the echo server.

## 10. The world model and environment assumptions (M3/M4)

Sketch, following `fsFFI`'s use of an oracle schedule:

- **fds** are abstract byte streams: incoming data arriving over time,
  possibly ending in EOF, and an output log.
- **Listening fds** yield new fds.
- **A clock.**
- The unpredictable future (when data or connections arrive) is an
  *arbitrary schedule* in the world state, a lazy list as in fsFFI's
  `numchars`. Theorems quantify over all schedules.
- A **snapshot** is computed from the world state and the previous round's
  actions:
  - `ready`: the fds with buffered data or EOF pending, listeners with
    pending connections, expired timers, and `Always`;
  - `now`;
  - `results`: one response per action of the previous round, in order.

Named assumptions, each with a non-vacuity lemma:

| Name | Statement | Non-vacuity |
|---|---|---|
| `one_response_per_action` | snapshot n+1 has exactly one result per action of round n, in order | true of the concrete world by construction |
| `clock_monotone` | `now` never decreases | any increasing schedule |
| `clock_progress` | `now` eventually exceeds every bound (timers fire) | e.g. `now = round number` |
| `data_live` | like fsFFI's `live_numchars`: always eventually, a read of an fd with pending data returns some of it | the schedule "deliver everything immediately" |
| `readiness_honest` (for §9 only) | a readable fd stays readable until read | the same schedule |

Non-vacuity will be shown by a concrete world (deliver all data at once,
`now` = round number), with a lemma that it satisfies all the assumptions.
The M3 whole-program theorem will say: for every schedule satisfying the
named assumptions, the I/O trace of the CakeML program is the model's action
log on the corresponding history.

## 11. Implementation and refinement plan

**Architecture**: a functional core (the library) plus a CF-verified
imperative shell (the FFI primitives and the event loop).

- **Library.** Most likely hand-written CakeML with refs (caches, as in
  2024). A computation value is a record of closures, with
  `poll : snapshot -> (action list * 'a option)` and mutable state for
  `bind` (running m, or running f x) and `both`/`choose`. Each `emit`
  allocates a cell that the shell fills with the response.
- **Refinement relation**, one direction only:
  `FUTURE m h v`: "the CakeML value `v` represents the model computation `m`
  after history `h`". CF specs per function:
  - `poll`: from `FUTURE m h v`, polling with the next snapshot `s` (and
    with the cells of the previous round's emits filled) returns the new
    actions and result of `m (h ++ [s])`, and re-establishes
    `FUTURE m (h ++ [s]) v`;
  - constructors: `return`, `wait`, `emit` produce `FUTURE (…) [] v`;
  - `bind`, `map`, `both`, `choose`, and `fix` for loops.
  - Positional routing in the model corresponds to cell delivery in the
    implementation. The refinement relation maps each pending cell to its
    position in the routed results.
- **Event loop**: never-ending, verified with the ITP 2019 `POSTd`
  machinery (§14), with `repeat_POSTd_one_FFI_part_FLATTEN` as the likely
  workhorse. With Level 2, it blocks in `select` on the union of the
  interest sets; `quiet` plus the M2 scheduler theorem justify this.

**Expected hard parts:**

1. `bind` is higher-order and stateful. The spec of the stored continuation
   `f` mentions `FUTURE`, which mentions the heap. CakeML has no existing
   pattern for closures stored in refs whose specs mention those refs (see
   §14 and §15).
2. A whole-program `POSTd` theorem (divergence plus I/O trace) does not
   exist yet.
3. Adding a world component to `basis_ffi` touches many places (§14).

**M2 sketch** (scheduler; pure step function, before any CakeML):

- `step : pool → snapshot → pool × action list`, where a pool is a list of
  tasks, each a computation and the history it has seen.
- *Tasks not lost*: every task is either finished or still in the pool.
- *Results match M1*: each task's actions and result after n rounds are its
  model outcome on its own view.
- *Progress*: under the fairness assumptions, every task is polled each
  round (or, at Level 2, whenever one of its events is ready or a response
  is due).
- *Level 2 blocking*: a scheduler that skips rounds in which no task has an
  interesting event or a response due produces the same per-task outcomes
  as the busy-polling one. This follows from `quiet` (deletion), applied
  task by task.

## 12. What is proved, and what is conjectured

All files build with `Holmake` in `async/model`, with no `cheat`.

| File | Contents |
|---|---|
| `asyncCoreScript.sml` | snapshots, outcomes, `first_prefix`, `new_actions`, routing (`skip_results`, `par_views`, `par_actions`), guarded recursion (`fix_unfold`, `fix_unique`, `fix_preserves`), congruence and deletion lemmas |
| `asyncLevel1Script.sml` | primitives, `bind`, `map`, `both`, `wf`, monad and functor laws, `wf`/`settled` preservation, `both` characterisations |
| `asyncChooseScript.sml` | `resume`, `suspended`, Async-style `choose`, `both_split`, `choose_rejoin`, `wf_choose`, `settled_choose` |
| `asyncLoopScript.sml` | agreement lemmas, `guarded_bind`, `settled_fix` |
| `asyncEchoScript.sml` | the echo loop and 10 EVAL sanity theorems |
| `asyncLevel2Script.sml` | `comp2`, erasure, transferred laws, `quiet`, quiet preservation for every combinator including `choose2` |
| `asyncLoop2Script.sml` | Level 2 recursion: `fix2`, `guarded2_bind2`, `erase_fix2`, `wf2_fix2` |
| `asyncEcho2Script.sml` | the Level 2 echo loop: `erase echo2 = echo`, `wf2 echo2`, EVAL checks of its interest |

**Conjectures** (not in the scripts):

1. `pick` (choose that drops the loser) is non-expansive, so recursion
   through `pick`'s arguments is allowed. Evidence: the result contains no
   computation, and `choose`'s decision and log only depend on the sides'
   shorter histories (as for `both_agree`).

   Note that dropping a loser can lose data that was already read (§4).
   This conjecture is about well-definedness, not about safety.

`quiet_choose2` and Level 2 recursion, conjectures in the first version of
this note, are now proved (`quiet_choose2`, `asyncLoop2`, `asyncEcho2`).

## 13. Proposed MAIN theorems

**Convention**: a user-owned, milestone-level statement is marked with
`(* MAIN: <one-line meaning> *)` immediately above the `Theorem`. Use
`grep -n "MAIN:" async/model/*.sml` to list them. Everything else is a helper
lemma.

The list below is generated from the scripts and is verbatim:

M1, Level 1 (asyncCore, asyncLevel1, asyncChoose, asyncLoop, asyncEcho):
`fix_unfold`, `fix_unique`, `wf_actions_grow`, `wf_finished_stays`,
`bind_running`, `bind_continues`, `bind_left_identity`,
`bind_right_identity`, `bind_assoc`, `map_id`, `map_map`, `bind_map`,
`map_bind`, `map_as_bind`, `wf_map`, `wf_bind`, `wf_both`, `both_result`,
`both_new_actions`, `both_views_world`, `wf_fix`, `bind_settled_continues`,
`settled_bind`, `settled_both`, `wf_resume`, `resume_resume`,
`resume_finished`, `both_split`, `choose_left_wins`, `choose_right_wins`,
`choose_right_wins_later`, `choose_rejoin`, `wf_choose`, `settled_choose`,
`guarded_bind`, `settled_fix`, `echo_unfold`, `wf_echo`, `settled_echo`.

M1, Level 2 (asyncLevel2): `erase_return2`, `erase_wait_on`, `erase_emit2`,
`erase_map2`, `erase_bind2`, `erase_both2`, `erase_choose2`,
`bind2_left_identity`, `bind2_right_identity`, `bind2_assoc`,
`no_progress_without_ready_event`, `quiet_wait_on` (primitives),
`quiet_map2`, `quiet_bind2`, `quiet_both2`, `quiet_choose2`.

M1, Level 2 recursion (asyncLoop2, asyncEcho2): `fix2_unfold`,
`erase_fix2`, `guarded2_bind2`, `wf2_fix2`, `echo2_unfold`, `erase_echo2`,
`wf2_echo2`.

The full statements are in the PR description and in the scripts.

## 14. What current CakeML offers (open problem 3)

Paths are relative to the CakeML repository root (upstream master f73189499).

**Non-termination CF (ITP 2019)**

- `characteristic/cfHeapsBaseScript.sml`:
  - `res = Val | Exn | FFIDiv … | Div (io_event llist)`;
  - `POST Qv Qe Qf Qd`, with `POSTv/POSTe/POSTf/POSTd` and the combined
    forms `POSTve`, `POSTvd`, `POSTed`.
- `characteristic/cfAppScript.sml` `evaluate_to_heap_def`: in the `Div io`
  case every clock times out, and `io` is the `lprefix_lub` of the
  io_events.
- `characteristic/cfDivScript.sml`:
  - `repeat_clos`/`repeat_v`, `repeat_POSTd`,
    `repeat_POSTd_one_FFI_part`, and the most usable,
    `repeat_POSTd_one_FFI_part_FLATTEN` (conclusion
    `Q (LFLATTEN (LGENLIST (fromList o events) NONE))`);
  - `IMP_app_POSTd`, `IMP_app_POSTd_one_FFI_part_FLATTEN` and
    `tailrec_POSTd` for recursive closures.
- Tactics: `characteristic/cfDivLib.sml` (`xcf_div`, `xcf_div_rule`,
  `xcf_div_FFI_full`).
- Examples:
  - `examples/divScript.sml`: `yes_spec_lemma`, `catLoop_spec`, and
    `myRepeat_spec`, a higher-order repeat whose step spec is carried in
    `&(...)`;
  - `examples/filterProgScript.sml`: `forward_matching_lines_div_spec`, and
    `semantics_diverge_filter`, which builds
    `semantics_prog … (Diverge events)` by hand.
- **There is no generic POSTd → Diverge whole-program theorem.**
  `cfMainScript` has only `call_main_thm2` (POSTv) and an FFIDiv variant,
  and `basis_ffi` has no POSTd `whole_prog_spec`. M3 must add one.

**fsFFI** (`basis/fsFFIScript.sml`, `basis/fsFFIPropsScript.sml`,
`basis/TextIOProofScript.sml`)

- `IO_fs` has `inode_tbl`, `files`, `infds`, `numchars : num llist` and
  `maxFD`.
- `numchars` is the oracle's nondeterminism: a read returns
  `MIN n (… SUC strm)`, and a write may write 0 bytes.
- Fairness:
  `live_numchars ns ⇔ ¬LFINITE ns ∧ always (eventually (λll. ∃k. LHD ll = SOME k ∧ k ≠ 0)) ns`,
  which `liveFS`/`wfFS` build on.
- `STDIO fs = (SEP_EXISTS ll. IOFS (fs with numchars := ll)) * …` hides the
  schedule existentially.
- **Recipe to reuse for sockets and time:**
  1. a state record with an llist schedule;
  2. a `live_*` always-eventually predicate;
  3. encode/decode via `cfFFIType`;
  4. a `*_ffi_part`;
  5. an `IOx` heap predicate that hides the schedule.

**basis_ffi** (`basis/basis_ffiScript.sml`)

- `basis_ffi_oracle ext` falls through to `ext`.
- `basis_proj1`/`basis_proj2` list `cl_ffi_part`, `fs_ffi_part` and
  `runtime_ffi_part`.
- **Adding a component touches:**
  - the state tuple, the oracle, `is_basis_ffi_name`, the projections, and
    the length/part definitions;
  - `oracle_parts` and `parts_ok_basis_st`;
  - a `*_precond` lemma and an `FFI_part_hprop` lemma;
  - every `whole_prog_spec*` and the `IMP_STDIO*` lemmas;
  - `basis_ffiLib` and `basis_ffi.c`.
- The 2024 project (branch `archive/2024-project`) did exactly this for
  time:
  - `basis/tsFFIScript.sml` with
    `IO_ts = <| latest_time; microseconds_elapsed : num -> int option |>`,
    `ts_ffi_part` and `ffi_now`;
  - `TimeProgScript.sml`/`TimeProofScript.sml` (`TIME ts`, `now_spec`);
  - `cfFFIType` gained `Option`;
  - the basis state became `(cls, fs, ts)`, and every `whole_prog_spec*`
    gained `* TIME ts`;
  - the C side gained `ffinow`, `ffiselect`, `ffiopen_listenfd`,
    `ffiaccept` and others.

  There is no monotonicity or fairness predicate for time there yet.

**CF for higher-order and stateful code**

- `basis/ListProofScript.sml` `app_spec` takes the closure's spec as a
  premise, with an indexed effect invariant `eff`. The Array `app` specs
  are similar.
- The translator's `-->` (`ml_translatorScript.sml`) is pure only.
- `basis/TextIOProofScript.sml` `sub_spec_def` is the existing pattern for
  "a returned closure satisfies an app spec", carried as a pure fact
  `&(sub_spec f …)`. `divScript.myRepeat_spec` is similar.
- **There is no existing pattern for closures stored in refs whose specs
  mention those refs.** That is exactly what a stateful `bind` needs (§15).

**The 2024 work** (`archive/2024-project`):

- `unverified/async/PromisedCake.cml`: a callback/promise event loop with
  a global job list and `select`;
- `unverified/async/pure_async/lib/promise.ml`: the pure poll model
  (`'a t = World.t -> 'a option`, cached `bind`/`create`), which this
  design generalises;
- `examples/promiseScript.sml`: an incomplete monadic-translator attempt.

## 15. Risks

1. **Closures in refs (CF).** A stateful `bind` stores the continuation's
   state in a ref, and the stored closure's spec mentions `FUTURE`, which
   mentions the heap. Possible ways out:
   - a stratified invariant (the program tree is finite at any moment;
     loops create new nodes per iteration);
   - step-indexing;
   - a library design where the continuation is not stored but recomputed,
     at a performance cost.

   This could limit *how* we prove things, but should not limit *what* we
   prove.
2. **The whole-program divergence theorem** has to be built (`POSTd` to
   `semantics_prog … Diverge`); `filterProgScript` shows it is possible by
   hand.
3. **basis_ffi changes** ripple through many proofs; the 2024 time
   component shows the scale.
4. **Positional routing in the shell.** The model routes responses by
   position; the implementation by cells. The refinement relation must
   connect the two, a new kind of bookkeeping (but local to `poll`).
5. **choose's one-round delay** must be mirrored by the implementation, or
   the refinement must allow finishing early.
6. **Level 2 coverage**: every combinator and recursion are covered, but
   the M2 theorem that a blocking scheduler is sound (built on `quiet`) is
   still to be done.
7. **Fairness assumptions** for sockets (connections eventually accepted,
   data eventually delivered) have no precedent beyond `live_numchars`.

## 16. Decisions needed from the user

1. **Positional response routing** (§3) instead of tags or ids. It keeps the
   laws exact and needs no freshness discipline, but the world must answer
   in order (an M3 assumption).
2. **emit waits for its response**, so fire-and-forget costs a round. The
   alternative is a separate `send` that finishes at once, with its
   response discarded; that would break settledness unless `send`'s
   responses are dropped by design.
3. **bind continues in the same round** (§2), with the
   last-round-responses convention justified by `settled` (§3). OK?
4. **choose** (§4): the one-round delay, the stale snapshot for the loser,
   and no recursion through choose's arguments (use `pick`). Acceptable?
5. **Laws need `wf`** for right identity, associativity and `choose_rejoin`;
   the Level 2 laws hold up to erasure. Acceptable as the equality notion?
6. **Level 2 representation and quiet as deletion** (§7). Is "deleting
   irrelevant snapshots changes nothing" the property you want the
   blocking-scheduler theorem to rest on?
7. **The MAIN theorem list** (§13): which statements do you want to own,
   reword, or demote to helpers?
8. **Next step**: move on to the M2 scheduler?
