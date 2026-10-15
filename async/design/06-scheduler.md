# M2: the scheduler

This note describes milestone M2: a pure HOL model of the scheduler that runs
a pool of tasks, and its theorems. It builds on the M1 semantics
(`01-semantics.md`). The scripts are `async/model/asyncSchedScript.sml`
(Level 1) and `async/model/asyncSched2Script.sml` (Level 2). Everything
below is proved, with no `cheat`.

## 1. The model

A **task** is a computation together with its own **view**: the snapshots
it has been shown, each carrying only the responses to that task's own
actions.

```
task = <| comp : ('e,'r) snapshot list -> ('act,'a option) outcome ;
          view : ('e,'r) snapshot list |>

in_flight t = new_actions (log_of t.comp) t.view    (* requests awaiting a response *)
```

A **scheduler state** is a list of tasks: the pool, in a fixed order. One
**round** delivers a snapshot to every task, then polls every task:

```
step [] s = []
step (t :: ts) s =
  let k = LENGTH (in_flight t) in
    (t with view := t.view ++ [s with results := TAKE k s.results]) ::
    step ts (s with results := DROP k s.results)

round_actions ts = FLAT (MAP in_flight ts)
```

- The snapshot's responses are split among the tasks in pool order. Each
  task gets as many as it has requests in flight, which is the same
  positional routing as in M1 (§3 of the semantics note).
- The round's actions are the tasks' new actions, in pool order.
- `sched ms h` folds rounds over the history `h`, starting from
  `start ms`, where every task has seen nothing.
- `run ms h` is the resulting pool, and `sched_log ms h` is everything
  emitted so far.

EVAL check (`example_sched_routing`): two tasks each emit a request in
round 0, and the next snapshot's responses `[1; 2]` go to them in pool
order.

## 2. Theorems (Level 1)

**Composition.** The scheduler running the tasks `ms` *is* the M1
computation `all ms`, the tasks combined with `both`:

```
all [] = return []
all (m :: ms) = map (λ(x, xs). x :: xs) (both m (all ms))

(* MAIN *) sched_log_all:
  EVERY wf ms ⇒ ∀h. sched_log ms h = (all ms h).actions
(* MAIN *) all_result:
  ∀ms h xs. (all ms h).result = SOME xs ⇔
            LIST_REL (λt x. (t.comp t.view).result = SOME x) (run ms h) xs
```

- Everything the scheduler emits is exactly the action log of `all ms`.
- `all ms` finishes with the list `xs` exactly when every task has
  finished, on its own view, with the corresponding element of `xs`.
- So every M1 theorem applies to the whole system: well-formedness,
  settledness ("no lost responses"), and the laws.

The key lemma is `run_cons`. Scheduling `m :: ms` gives `m` its left view
in `both m (all ms)`, and schedules `ms` on the right view. The
scheduler's routing is `both`'s routing.

**Tasks are never lost** (`run_tasks`, MAIN):
`MAP (λt. t.comp) (run ms h) = ms`. The pool keeps every task, in order.
A finished task stays in the pool, frozen by well-formedness.

**Fairness and progress** (`run_views_world`, MAIN):

```
∀ms h. EVERY (λt. MAP (λs. (s.ready, s.now)) t.view = MAP (λs. (s.ready, s.now)) h)
             (run ms h)
```

Every task is polled in every round and sees every snapshot's ready set
and time. With a polling scheduler this is the whole fairness story: no
task can be starved. A ready task makes progress in the sense that it sees
the ready event in the round in which the world reports it. Whether it
then finishes depends only on its own M1 meaning.

## 3. No busy-waiting (Level 2): the headline result

A **blocking scheduler** skips a round (blocks, e.g. in `select`) when
every task is idle:

```
idle_task c t s ⇔
  in_flight t = [] ∧
  ((t.comp t.view).result = NONE ⇒ DISJOINT (c.interest t.view) s.ready)

sched_idle cs h s ⇔
  s.results = [] ∧ LIST_REL (λc t. idle_task c t s) cs (run (MAP erase cs) h)
```

Here `cs` are the Level 2 tasks and `h` the snapshots the scheduler has
acted on so far. `blocked skip [] H` is the subsequence of `H` that a
scheduler skipping by `skip` acts on.

```
(* MAIN *) no_busy_waiting:
  EVERY wf2 cs ⇒
  ∀H. let K = blocked (sched_idle cs) [] H in
      sched_log (MAP erase cs) K = sched_log (MAP erase cs) H ∧
      ∀xs. LIST_REL (λt x. (t.comp t.view).result = SOME x) (run (MAP erase cs) K) xs ⇔
           LIST_REL (λt x. (t.comp t.view).result = SOME x) (run (MAP erase cs) H) xs
```

Take tasks that are well-formed and quiet (every Level 2 program is, by
M1). A scheduler that blocks through every idle round emits exactly the
same actions, and its tasks finish with exactly the same results, as the
scheduler that polls every task in every round.

**Progress under blocking** (`ready_task_polled`, MAIN): the scheduler never
blocks through a snapshot in which some waiting task has a declared event
ready, or in which some task has a request in flight.

**How it is proved.**

1. The pool of Level 2 tasks is the Level 2 computation `all2 cs`. It is
   well-formed and quiet because every combinator is (`wf2_all2`, from
   `quiet_both2` and friends). Its run is `all (MAP erase cs)`
   (`erase_all2`).
2. `blocked_sound` (MAIN): for any well-formed, quiet `c` and any skip
   rule that only skips *irrelevant* snapshots (no request in flight, no
   responses, no declared event ready), acting on the kept snapshots gives
   the same outcome as acting on all of them. This is quietness's
   *deletion* property, applied one snapshot at a time. The invariant
   `same_for c full kept` ("the full and kept histories are
   indistinguishable for c, now and later") is preserved by each round
   (`same_for_step`).
3. `sched_idle_irrelevant`: if every task is idle, the snapshot is
   irrelevant to `all2 cs`. The pool's in-flight requests are the tasks'
   (composition). Its interest is the union of the waiting tasks'
   interests (`idle_waiting_on`).
4. Composition (§2) turns equal runs of `all (MAP erase cs)` into equal
   scheduler logs and task results.

This is why `quiet` was defined by deletion rather than by "one more poll
changes nothing" (§7 of the semantics note): step 2 deletes snapshots in
the middle of a history, and the one-step property can't justify that.

## 4. Decisions and assumptions (for the user)

1. **The pool is fixed; no dynamic spawning.** A `Spawn` action carrying a
   computation would need an action type that contains computations, i.e.
   a recursive datatype through a function space, which HOL's datatypes
   can't express.
   - Fork/join inside a task is available through `both`.
   - Spawning an unbounded number of tasks (e.g. one per accepted
     connection, for M4) needs a decision. Options:
     - (a) a task tree: tasks are `both`/`choose` combinations, and a
       "server" task forks per connection by recursion. This is
       expressible today with `fix` and `both`.
     - (b) a two-level model where the scheduler, not the action type,
       knows about computations: actions include `Spawn i` with an index
       into a fixed family of task constructors.
     - (c) a coinductive or indexed encoding.

     (a) is the cheapest and may be enough for M4.
2. **Pool order is the action order within a round**, and responses are
   routed by position, as in M1.
3. **Finished tasks stay in the pool** (they are frozen). Removing them is
   an optimisation that changes nothing observable. It isn't modelled.
4. **The blocking scheduler's wake-up condition** is exactly "some task has
   a request in flight, some waiting task has a declared event ready, or
   responses arrived". Timers are events like any other (e.g. `Timer t` in
   the ready set), so a blocking `select` needs the world to report them.
   That is an M3 world-model assumption.

## 5. What M2 does not cover yet

- **Fairness assumptions on the world** (data eventually arrives, timers
  eventually fire) are M3 material. M2's progress statements are about the
  scheduler: it polls everyone, or never blocks past a ready event.
- **Liveness of whole programs** (e.g. "every line sent to the echo server
  is eventually echoed") needs those world assumptions plus M1 facts about
  the tasks. That is planned for M3/M4.
- **The CakeML event loop** that implements `step` (with `select` for
  blocking) is M3. It will be proved against `sched`/`blocked` with the CF
  non-termination logic (§11 and §14 of the semantics note).

## 6. Proposed MAIN theorems (M2)

| Theorem | File | Meaning |
|---|---|---|
| `run_tasks` | asyncSched | tasks are never lost |
| `run_views_world` | asyncSched | every task sees every snapshot (fairness) |
| `sched_log_all` | asyncSched | the scheduler's log is the log of `all ms` |
| `all_result` | asyncSched | the tasks' results are `all ms`'s result |
| `blocked_sound` | asyncSched2 | skipping irrelevant snapshots is sound, for any quiet computation |
| `no_busy_waiting` | asyncSched2 | the blocking scheduler = the polling scheduler (headline) |
| `ready_task_polled` | asyncSched2 | the scheduler never blocks past a ready event or a pending response |

Suggested headline for M2: `no_busy_waiting`, with `sched_log_all` and
`all_result` as the composition theorem.
