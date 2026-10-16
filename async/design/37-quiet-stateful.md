# 37. Quiescence for stateful servers (with_store, with_tap)

*cf-actions, 2026-10-16. Extends design/33 §4 (the `Now` amendment) to a
plan with statements. Status: in progress. §4: R1 decided (coordinator,
2026-10-16); cf-actions owns the loop variant.*

## 1. Goal

KV (and later chat) should get a quiescence theorem of the same form as
`http_q_quiet` (`⊢ http_quiet_b 3w demo_files http_q_prog`, spike/option-c-int
65799d592): in QuietSpec's world, once only finitely many things arrive,
the program ends up blocked forever in `select`.

These servers are built as
`with_store δ s0 (server_v V (λfd. proto_handler_v V P ansq fin (fd, "")) lfd)`
(KV), or with `with_tap σ δ s0` (chat). So the work is:

1. a Level 2 `with_store2` (and `with_tap2`) with its `erase`, `wf`, quiet
   and finiteness facts (§3);
2. how the select loop learns "answers are pending, do not sleep" (§4);
3. a generic stability lemma, `proto_stable`'s analogue for
   `with_store2 ∘ server_v2` under `proto_ok P` (§5);
4. the instances (KV, then chat), as `http_q_quiet` was assembled.

No spec changes: QuietSpec is approved. The work is additive.

## 2. The problem (recap of 33 §4)

`with_store δ s0 m` answers `m`'s `Kv` queries itself. The answers to a
round's queries arrive in the **next** snapshot, merged into that round's
results (`inner_hist`).

- In a round where `m` emits only `Kv` queries, `with_store` emits
  nothing. The select loop then sees no actions and selects on the
  declared interest. If that is only `m`'s socket events, it can block
  with answers owed.
- In the model, plain `quiet` fails for the same reason. Take a snapshot
  with no results and nothing declared ready, taken while answers are
  pending. It changes what `m` sees: it carries the store's answers. So
  it cannot be deleted.

## 3. The model: `with_store2`

```
with_store2 now δ s0 m2 =
  <| run := with_store δ s0 m2.run;
     interest := λh. (if kv_pending δ s0 m2.run h then {now} else ∅) ∪
                     m2.interest (inner_hist δ s0 m2.run h) |>

kv_pending δ s0 m h ⇔
  queries (new_actions (log_of m) (inner_hist δ s0 m h)) ≠ []
```

`now` is a parameter: an event of `m2`'s event type that the loop
reports ready in every snapshot. In the model vocabulary it is
`asyncServer$Always`, which already exists.

**Facts.**
- `erase_with_store2`: `erase (with_store2 now δ s0 m2) = with_store δ s0 (erase m2)`.
  This holds by definition.
- `wf (with_store2 …).run` follows from `wf_with_store`.
- `finite2_with_store2`: `finite2 m2 ⇒ finite2 (with_store2 now δ s0 m2)`.

**Quiet, relative to the loop's snapshots.** Plain `quiet` is false (§2).
It holds for snapshots that report `now`:

```
quiet_on R c ⇔ ∀h s h'. R s ∧ (c.run h).result = NONE ∧
                        new_actions (log_of c.run) h = [] ∧ s.results = [] ∧
                        DISJOINT (c.interest h) s.ready ⇒
                        c.run (h ++ [s] ++ h') = c.run (h ++ h') ∧
                        c.interest (h ++ [s] ++ h') = c.interest (h ++ h')

quiet_with_store2: quiet m2 ⇒ quiet_on (λs. now ∈ s.ready) (with_store2 now δ s0 m2)
```

Proof idea: if `now ∈ s.ready` and nothing declared is ready, then
`now ∉ interest`. So no `Kv` is pending, and `s` reaches `m2` with no
results (the merge adds nothing). By `quiet m2`, deleting it changes
nothing for `m2`. The store's later answers depend only on `m2`'s
queries, which do not change. The key lemma is
`inner_hist (h ++ [s] ++ h') = inner_hist (h ++ h')` with `s` spliced in.
That is about 150–250 lines.

`quiet ⇒ quiet_on R` holds trivially, so the existing servers are
instances of the relative form.

`with_tap2 now σ δ s0 m2` is the same construction over `tap_hist`. The
tap updates only on answered `Sock` responses, and a deleted snapshot has
none. So the proof carries over.

## 4. The socket level and the loop (decided: R1)

The socket-level program is `srelabel2 (…)`. Its interest is a set of
`word64` fds (`sie` keeps only `Readable n`), and `step_q` selects on
`qsel c h` when the round's actions are `[]`. `now` must survive the
relabelling, and the loop must poll instead of selecting when `now` is
declared.

| option | socket-level interest | loop change | cost |
|---|---|---|---|
| **R1 (recommended)** | `word64 option set`: `SOME fd`, and `NONE` for `now`. `sie'` maps `Always ↦ NONE`; the snapshot map adds `NONE` to every ready set. | `step_q'`: select only if `acts = []` ∧ `NONE ∉ waiting_on`; `qsel` keeps the `SOME`s. | a variant of `srelabel2`/`qsel`/`step_q`/`lbgrounds` and their proofs; HTTP and echo keep the current loop as is (an instance with no `NONE`) |
| R2 | unchanged; `comp2` gets a separate "busy" field | the loop reads it | changes `comp2`'s type, so everything at Level 2: rejected |
| R3 | a reserved fd value | the loop special-cases it | needs a world invariant that no real fd equals it: fragile |

In CakeML (R1), the Level 2 value's event list carries an `int option`
(or a boolean "busy" alongside the list). `with_store2`'s code sets it
while queries are pending, and `step_q'` tests it before
`q_wait_ready`.

**Decision: R1, as an additive variant.** The variant comprises
`srelabel2'`, `qsel'`, `step_q'`, `lbgrounds'` and `qsel_sleeps'`.
Today's loop and its theorems for echo and HTTP stay untouched. A goal
(not a prerequisite): prove that the variant restricted to computations
that never declare `NONE` coincides with today's loop, so that one loop
could eventually serve all servers.

### 4.1 R1 as modelled (asyncOCBusy, asyncStoreQuiet)

The model keeps the loop's snapshots as they are (the world reports fds
only) and states R1 as a **busy test**: a round with no actions selects
only if the program does not wait for `Always`; otherwise it polls at
once, as a round with actions does (`lbgroundsB`). This is the same loop
as "interest `word64 option set`, `NONE` = `Always`, select only if
`NONE ∉ waiting_on`": the `NONE` entry is the busy flag. For a program
that never waits for `Always`, `lbgroundsB` is today's `lbgrounds`.

- Skipping a snapshot needs `quiet_nb` (quiet while not busy), not
  `quiet`. `with_store2 Always` has it (`quiet_nb_with_store2`), because
  not busy means no query is pending (`with_store2_busy`, with `rd2`: the
  skeleton waits only for `Readable` events).
- `qsel_sleepsB`: under `store_stable`'s three facts, the loop blocks
  forever in select. `store_sleeps` is the instance for the store server
  with query handlers.
- In CakeML, `step_q'` tests for `Always` in the program's event list
  before `q_wait_ready`; the select set stays the `Readable` fds.

## 5. Stability for `with_store2 ∘ server_v2` under `proto_ok`

`proto_stable`'s analogue, for any `proto_ok P`, any `V` with
`vocab_ok`/`vocab_qok`, any store:

```
store_stable:
  proto_ok P ∧ vocab_ok V ∧ vocab_qok V ∧ s0.listeners = [(n2w lfdn, [])] ∧
  s0.conns = [] ∧ lfdn < dimword (:64) ∧ arrivals_finite s0 ⇒
  ∃n1. ∀n. n1 ≤ n ⇒ no actions in round n ∧ no Kv pending after round n ∧
       nothing the Level 2 program waits for is ready
```

The proof is as for `proto_stable` (asyncProtoMeasure / asyncProtoReact),
with one change: the measure gains a term for pending queries. That term
is trivial, because a pending query is answered in the next round
whatever the world does, and new queries come only from handling
complete requests (at most one per request: `proto_handler_v` emits the
query, then, once answered, the write; the `QA → QW` states of
asyncProtoMachineV). The per-action cause
(`sw_new_actions`) and the reaction lemma (`sw2_reacts`) are generic
over `server_with`. They need versions for `server_v` (the vocabulary
skeleton), plus the `with_store` layer. The writes term is unchanged:
safety still bounds the writes by the complete requests.

## 6. Plan and estimate

| step | content | estimate |
|---|---|---|
| A | `with_store2`, `kv_pending`, `quiet_on`, `quiet_with_store2`, `finite2`, `erase` (model, representation-free) | 300–400 lines |
| B | `server_v` versions of `sw_new_actions` / `sw2_reacts`; the store layer's cause and reaction | 300–400 |
| C | `store_stable` (measure with the pending-query term) | 400–600 |
| D | the loop variant (R1) and its `qsel_sleeps'`; CakeML `with_store2` | depends on §4; with async-spike |
| E | KV instance: `⊢ kv_quiet …` | 150–250 |
| F | `with_tap2` and the chat instance | 200–300 |

I start with A, B and C (model only, additive, in a sparse worktree on
spike/option-c-int's layout, with `asyncWithStore` brought in from
spike/kv-live as is). I'll open a PR per milestone, and none of it
depends on the §4 decision.

## 7. Temporary copies (to be replaced by a merge)

`pk/quiet-store` holds two files copied as is, to avoid a branch
dependency. Each is a **temporary copy, to be replaced by a merge**, so
that the final series has one copy of each:

- `asyncWithStoreScript.sml`: temporary copy of spike/kv-live's
  `asyncWithStore`;
- `asyncServerVKvScript.sml`: temporary copy of spike/kv-live's
  `asyncServerVKv` @5a72181db.
