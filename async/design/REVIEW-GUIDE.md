# Review guide for the async model (PRs #1 and #3)

The scripts mark 79 theorems `(* MAIN: … *)`. That is too many to own. This
guide proposes:

1. a trimmed **headline list** of 14 entries for you to own: the statements
   that define what the model promises;
2. the remaining MAIN items to **demote** to helpers, one line each;
3. every **decision** waiting for you, in one place;
4. a **reading order**.

Nothing has been changed yet: the MAIN markings stay as they are until you
approve a list. All statements below are copied verbatim from the scripts
in `async/model/` (PR #1 plus PR #3).

Vocabulary used below:

- **history**: the list of world snapshots a computation has been polled
  with, oldest first;
- **round**: one poll;
- **wf**: the action log only grows, and once finished nothing changes;
- **settled**: a computation emits nothing in the round in which it
  finishes, so no response can be lost;
- **quiet** (Level 2): a snapshot with none of the declared events ready
  can be deleted from the history without changing anything.

---

## 1. Proposed headline theorems

### H1. Monad laws (`asyncLevel1`)

```
bind_left_identity:  bind (return x) f = f x
bind_right_identity: wf m ⇒ bind m return = m
bind_assoc:          wf m ⇒ bind (bind m f) g = bind m (λx. bind (f x) g)
```

**Meaning.** `return` and `bind` form a monad, with *equality* of
computations: the same action log and the same result on every history.

**Why this statement.**
- Weaker forms (equal results only, or equality up to some equivalence)
  would let a law change the order of emitted actions or drop one, which
  is exactly what an I/O library must not do.
- The `wf` hypotheses are needed, and harmless: an ill-formed `m` can
  change its result after finishing, and `bind` reads it only at the first
  finishing point. Every library computation is `wf`.

### H2. What bind means (`asyncLevel1`)

```
bind_continues:
  first_done m h1 x ⇒
  ∀f h2.
  bind m f (h1 ++ h2) =
    let next = f x (skip_results (LENGTH (new_actions (log_of m) h1)) h2) in
      <| actions := (m h1).actions ++ next.actions; result := next.result |>
```

**Meaning.** Suppose `m` first finishes with `x` after the snapshots `h1`.
Then `bind m f` continues as `f x`, started in that same round:
- `f x` sees only the later snapshots `h2`;
- the responses to `m`'s own actions of that last round are not passed
  to it.

**Why this statement.**
- It pins down the two conventions you need to approve:
  - the same-round start (§16, item 3);
  - the skipped responses.
- The laws alone would allow other conventions, e.g. starting `f x` one
  round later. This theorem says exactly which one we chose.

### H3. Bind drops nothing for settled computations (`asyncLevel1`)

```
bind_settled_continues:
  settled m ∧ first_done m h1 x ⇒
  bind m f (h1 ++ h2) =
    <| actions := (m h1).actions ++ (f x h2).actions;
       result := (f x h2).result |>
```

**Meaning.** If `m` is settled, `bind` hands `f x` *every* later snapshot
unchanged; no response is skipped.

**Why this statement.** It turns H2's "skipped responses" from a possible
loss into a non-issue. Every library computation is settled (H7). Without
it, a reviewer must trust that the skip never matters.

### H4. What both means (`asyncLevel1`)

```
both_result:
  (both m1 m2 h).result = SOME (x, y) ⇔
    (m1 (left_view m1 m2 h)).result = SOME x ∧
    (m2 (right_view m1 m2 h)).result = SOME y
```

**Meaning.** `both` finishes exactly when both sides have finished, each on
the snapshots routed to it, with the pair of their results.

**Why this statement.**
- It is an "iff": `both` neither finishes early nor waits longer than its
  sides.
- The views (`left_view`/`right_view`) are where response routing lives. A
  weaker statement ("if both finish, the result is the pair") would allow a
  `both` that never finishes.

### H5. choose loses nothing (`asyncChoose`)

```
choose_rejoin:
  wf m1 ∧ wf m2 ⇒ bind (choose m1 m2) rejoin = both m1 m2
```

with `rejoin (INL (x, rest2)) = both (return x) rest2` and
`rejoin (INR (rest1, y)) = both rest1 (return y)`.

**Meaning.** Run `choose`, then continue with the winner's result alongside
the returned loser. The outcome is *exactly* running both sides with
`both`: the same actions in the same order, and the same results. So the
loser `choose` returns is the rest of the losing computation, with nothing
lost and nothing duplicated.

**Why this statement.**
- An exact equality with `both` is the strongest form of "nothing is
  lost".
- A weaker one ("the loser eventually produces its result") would allow
  lost or repeated actions, such as a read issued twice.
- Caveat (§3 below): this covers callers that *continue* the loser. A caller
  that drops the loser can lose data.

### H6. What choose returns (`asyncChoose`)

```
choose_losers:
  wf m1 ∧ wf m2 ∧ can_return (choose m1 m2) z ⇒
  (∀x l. z = INL (x, l) ⇒ wf l ∧ (settled m2 ⇒ settled l)) ∧
  (∀l y. z = INR (l, y) ⇒ wf l ∧ (settled m1 ⇒ settled l))
```

**Meaning.** Every loser that `choose` can return is well-formed, and
settled if its side was. So programs that continue a loser stay within the
reach of the closure theorems (H7, H10).

**Why this statement.** Without it, the closure lemmas don't apply to the
programs `choose` exists for (the review of #1, concern 1).

### H7. Well-formedness and settledness are preserved (`asyncLevel1`, `asyncChoose`)

```
wf_bind_on:      wf m ∧ (∀x. can_return m x ⇒ wf (f x)) ⇒ wf (bind m f)
settled_bind_on: wf m ∧ settled m ∧ (∀x. can_return m x ⇒ settled (f x)) ⇒ settled (bind m f)
wf_choose:       wf (choose m1 m2)
```

**Meaning.** `bind` preserves `wf` and `settled`, needing the
continuation's property only for results `m` can actually produce.
`choose` is always well-formed. (`both`, `map`, the primitives and
`settled_choose` are in the helper list; same shape.)

**Why this statement.**
- The `can_return` hypothesis, not `∀x`, is what makes the lemmas usable
  when `x` contains a `choose` loser. The `∀x` versions are corollaries.
- These are the "no lost responses" guarantee, combinator by combinator.

### H8. Loops are well-defined (`asyncCore`)

```
fix_unfold: contractive body ⇒ fix body = body (fix body)
fix_unique: contractive body ∧ body r = r ⇒ r = fix body
```

**Meaning.** A recursive definition whose body is contractive (each
unfolding uses up a snapshot) has exactly one solution, `fix body`, and
that solution satisfies the recursive equation.

**Why this statement.**
- Unfolding alone would allow `fix` to be an arbitrary fixpoint.
- Uniqueness is what lets the CF proof (M3) show that the CakeML loop
  satisfies the equation and conclude that it *is* the model loop.

### H9. The recursion rule (`asyncLoop`)

```
guarded_bind_split:
  (∀x. nonexpansive (λr. G x r)) ∧
  (∀x. (m []).result = SOME x ⇒ guarded (λr. G x r)) ⇒
  guarded (λr. bind m (λx. G x r))
```

**Meaning.** A recursive call may appear in the continuation of `m`:
- Continuations reachable before any snapshot must themselves be guarded,
  e.g. they wait or emit before recursing.
- All others only need to be non-expansive.

If `m` needs a snapshot to finish, the second hypothesis is vacuous, and
this is the basic rule "recurse after a wait or an emit" (`guarded_bind`).

**Why this statement.**
- The basic rule can't handle loops that carry a pending computation,
  which may already have finished. The split form covers them; see the
  idle-deadline loop in `asyncIdle`.
- Being one theorem, it replaces the basic rule rather than adding a
  second one.

### H10. Loops preserve settledness (`asyncLoop`)

```
settled_fix_on:
  contractive body ∧
  (∀r. (∀p. ok p ⇒ settled (r p)) ⇒ ∀p. ok p ⇒ settled (body r p)) ⇒
  ∀p. ok p ⇒ settled (fix body p)
```

**Meaning.** If the body preserves settledness, for parameters satisfying
an invariant `ok` (for example "the pending read is well-formed and
settled"), so does the loop. (`wf_fix_on` is the same for `wf`.)

**Why this statement.** Without the invariant `ok`, the hypothesis would
have to hold for *every* parameter. That fails for loops that carry a loser
(the review of #1, concern 1).

### H11. Level 2 refines Level 1 (`asyncLevel2`, `asyncLoop2`)

```
erase_bind2:   erase (bind2 c f) = bind (erase c) (λx. erase (f x))
erase_choose2: map (map_loser erase erase) (erase (choose2 c1 c2)) =
               choose (erase c1) (erase c2)
erase_fix2:
  contractive body1 ∧ contractive2 body2 ∧
  (∀R p. erase (body2 R p) = body1 (λq. erase (R q)) p) ⇒
  ∀p. erase (fix2 body2 p) = fix body1 p
```

**Meaning.** Forgetting the declared interest turns every Level 2
combinator, including loops, into the corresponding Level 1 one. So
everything proved at Level 1 holds of Level 2 programs.

**Why this statement.**
- `bind` and `choose` are the interesting combinators; the others follow
  the same pattern and hold by construction.
- `erase_fix2` is the one with content: a Level 2 loop *is* the Level 1
  loop.

### H12. No busy-waiting: every combinator and loop is quiet (`asyncLevel2`, `asyncLoop2`)

```
quiet c ⇔
  ∀h s h'.
    (c.run h).result = NONE ∧ new_actions (log_of c.run) h = [] ∧
    s.results = [] ∧ DISJOINT (c.interest h) s.ready ⇒
    c.run (h ++ [s] ++ h') = c.run (h ++ h') ∧
    c.interest (h ++ [s] ++ h') = c.interest (h ++ h')

quiet_bind2_on: wf c.run ∧ quiet c ∧ (∀x. can_return c.run x ⇒ quiet (f x)) ⇒ quiet (bind2 c f)
quiet_both2:    wf c1.run ∧ wf c2.run ∧ quiet c1 ∧ quiet c2 ⇒ quiet (both2 c1 c2)
quiet_choose2:  wf c1.run ∧ wf c2.run ∧ quiet c1 ∧ quiet c2 ⇒ quiet (choose2 c1 c2)
quiet_fix2:
  contractive2 body2 ∧ (∀R. (∀p. wf2 (R p)) ⇒ ∀p. wf2 (body2 R p)) ⇒
  ∀p. quiet (fix2 body2 p)
```

**Meaning.** Take a computation that is waiting, has no request in flight,
and is shown a snapshot in which none of its declared events is ready.
That snapshot can be *deleted* from its history without changing anything,
now or later. This holds for every combinator and every guarded loop. It is
what lets a scheduler block in `select` instead of polling (the M2
theorem).

**Why this statement.**
- The one-step version ("polling once more changes nothing") is too weak:
  a computation could remember an irrelevant snapshot and act on it later.
  Deletion rules that out.
- `no_progress_without_ready_event` is the one-step corollary; see the
  demote list.

### H13. The laws hold for what a scheduler sees (`asyncLevel2`)

```
status_bind2_right_identity: wf c.run ⇒ status (bind2 c return2) h = status c h
status_bind2_assoc:
  wf c.run ⇒
  status (bind2 (bind2 c f) g) h = status (bind2 c (λx. bind2 (f x) g)) h
```

(Left identity holds exactly, `bind2_left_identity_exact`.)

**Meaning.** Rewriting a Level 2 program by the monad laws doesn't change
its status: its result, or, while it waits, the events it waits for.

**Why this statement.** The erasure versions (`bind2_assoc` etc.) say
nothing about interest, which is what the scheduler blocks on. A rewrite
that changed the interest could make a blocking scheduler miss a wake-up.

### H14. The echo loop, end to end (`asyncEcho`, `asyncEcho2`)

```
settled_echo: settled (echo fd)
erase_echo2:  erase (echo2 fd) = echo fd
quiet_echo2:  quiet (echo2 fd)
```

**Meaning.** The echo loop never loses a response. Its Level 2 version is
the same loop, and is quiet: a scheduler may block until `fd` is readable.

**Why this statement.**
- This is the worked example showing that the theory reaches a real loop:
  defined by the recursion rule, settled, refined, quiet.
- The M4 echo server builds on it.

---

## 2. Proposed demotions (MAIN → helper)

| Theorem(s) | Why demote |
|---|---|
| `wf_actions_grow`, `wf_finished_stays` | direct consequences of `wf`'s definition; used everywhere, but not promises |
| `bind_running` | the "before m finishes" half of H2; follows from the definition |
| `map_id`, `map_map`, `bind_map`, `map_bind`, `map_as_bind` | standard functor laws; worth keeping as a secondary list, but they add no design content beyond H1 |
| `wf_map`, `wf_bind`, `wf_both`, `wf_fix` | subsumed by H7/H10 (`wf_bind` and `wf_fix` are corollaries of the `_on` forms) |
| `settled_bind`, `settled_both`, `settled_choose`, `settled_fix` | same family as H7/H10; `settled_bind` and `settled_fix` are corollaries |
| `both_new_actions`, `both_views_world` | describe `both`'s log and views; implementation detail behind H4 |
| `wf_resume`, `resume_resume`, `resume_finished` | you asked for these; they are correct and useful, but they describe `resume`, not the library's promises. Keep them MAIN if you want `resume` to be a user-facing operation |
| `both_split` | the key lemma behind H5; a proof device |
| `choose_left_wins`, `choose_right_wins`, `choose_right_wins_later` | the exact case-by-case behaviour of `choose`; H5 and H6 are the promises (keep these as documentation of the one-round delay) |
| `choose_results` | the stronger form behind H6 |
| `guarded_bind` | the special case of H9 |
| `wf_fix_on` | the `wf` twin of H10 (mentioned there) |
| `echo_unfold`, `wf_echo` | details of the example; `echo_unfold` is a useful sanity check of the definition |
| `idle_body_contractive`, `idle_unfold`, `wf_idle`, `settled_idle` | a second example (a loop that carries a loser); keep it as the test case for H9/H10 |
| `erase_return2`, `erase_wait_on`, `erase_emit2`, `erase_map2`, `erase_both2` | hold by construction (one-line proofs); H11 keeps the interesting ones |
| `bind2_left_identity`, `bind2_right_identity`, `bind2_assoc` | immediate from erasure + H1; H13 is the stronger form |
| `no_progress_without_ready_event` | the one-step corollary of `quiet`; the content is H12 |
| `quiet_wait_on`, `quiet_map2`, `quiet_bind2` | the primitives and the `∀x` corollary; same family as H12 |
| `fix2_unfold`, `guarded2_bind2`, `wf2_fix2`, `wf2_fix2_on` | Level 2 copies of H8/H9/H10 (via the packed representation); `quiet_fix2` is in H12 |
| `echo2_unfold`, `wf2_echo2` | details of the example; H14 keeps `erase_echo2` and `quiet_echo2` |

## 3. Decisions waiting for you

From design note §16:

1. **Positional response routing** instead of tags or ids. It keeps the
   laws exact and needs no freshness discipline; the world must answer in
   order (an M3 assumption).
2. **emit waits for its response**, so a fire-and-forget write costs one
   round.
3. **bind continues in the same round** (H2), with the
   last-round-responses convention justified by `settled` (H3).
4. **choose**:
   - a one-round delay when the right side wins while the left has
     requests in flight;
   - the loser sees a stale snapshot at its first poll;
   - no recursion *through* choose's arguments (loops that carry a loser
     are fine, H9).
5. **Laws need `wf`** (H1, H5). The Level 2 laws hold up to erasure, and
   for status (H13).
6. **Level 2 representation and quiet as deletion** (H12): is this the
   property you want the M2 blocking-scheduler theorem to rest on?
7. **The MAIN list**: approve, edit or replace the headline list above.
   I'll then change the markings in one commit.

From the review of #1:

8. **`pick` (choose that drops the loser) can lose data that was already
   read.** If the timer wins in the round in which a read was emitted, the
   read's data is inside the dropped loser (design note §4, with the
   example). Options:
   - (a) don't provide `pick`;
   - (b) provide it with a safety condition (drop only a loser that has
     emitted nothing since its last poll);
   - (c) make it refuse to finish while the loser has requests in flight.
9. **Should M4 state "no consumed input is discarded" explicitly?** M4's
   trace theorem would not rule out the `pick` loss on its own.

Until you decide, the model keeps `choose` as is, and `pick` is not
defined in the scripts.

## 4. Suggested reading order

1. `README.md` (two minutes).
2. Design note `01-semantics.md` §1 (the idea) and §2 (Level 1 definitions).
3. **H1–H4** in `asyncLevel1Script.sml`: laws, bind, both. Check the
   statements against the definitions `bind_def` and `both_def`.
4. Design note §3 (routing) and the EVAL examples at the end of
   `asyncEchoScript.sml`: they show routing on concrete histories.
5. Design note §4 and **H5–H6** in `asyncChooseScript.sml`, with the EVAL
   examples `example_choose_*`.
6. Design note §5–§6 and **H7–H10**, `asyncLoopScript.sml`, then the echo
   loop (`asyncEchoScript.sml`) and the idle loop (`asyncIdleScript.sml`)
   as worked examples.
7. Design note §7 and **H11–H13** in `asyncLevel2Script.sml` and
   `asyncLoop2Script.sml`.
8. **H14** in `asyncEcho2Script.sml`.
9. Design note §10–§16: world model, refinement plan, risks, decisions.

Every proof script builds with `Holmake` in `async/model`, with no
`cheat`. Proofs can be skipped on a first reading: the statements and the
comments above them are meant to stand alone.
