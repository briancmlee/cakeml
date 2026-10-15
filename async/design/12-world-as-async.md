# The world as an async program (experiment)

Status: **experimental**, timeboxed. Prototypes in `async/world-async/`
(pure HOL, includes `../model`; all proved, no `cheat`):
`worldAsyncNetScript.sml` (one connection, §2–§3),
`worldAsyncMultiScript.sml` (the full server, any number of clients, §8),
`worldAsyncCtransScript.sml` (shared transcript lemmas).

**Verdict, short.** The literal idea, a world that is an async computation
with the interface flipped, has no clean formulation (§1), so I shelved
that version. A nearby one works well: **clients are ordinary async
programs, and the world is those clients plus a small network kernel (a
state machine)**. Composition is well defined, takes a page of HOL, and
gives a closed-system theorem for *every* client program at almost no cost
(§3). Liveness, i.e. fairness derived from client structure, is plausible
but unproved (§5). Worth one more step (§7).

**Update (§8): the step from §7 is done.** The full server `server lfd`, run
against any number of clients written as one async program (e.g. `both
client1 client2`), with a multi-connection kernel: on every connection,
what the client receives is a prefix of what it sent, in order. `fresh` is
now a proved kernel fact, so the closed-system theorem has **no
assumptions**. Liveness is still open; §8.4 says exactly what blocks it.

## 1. The literal mirror doesn't work

The program maps snapshots (readiness, time, positional responses) to
actions. The world would map actions to snapshots. To write a world *with
the library*, it would be a `computation` whose "snapshot" carries the
program's latest batch of actions and whose "actions" are the program's
responses. Three mismatches:

1. **Responses aren't actions.** In the library an emitted action waits for
   its own response, positionally. The world never gets a response to "here
   is your Data". Every program action must be answered in the same round
   and in order, which is a totality constraint the world's code would have
   to meet, not something `emit` gives you.
2. **Routing is by position, not by address.** `both w1 w2` gives the left
   side the first k results, where k is the number of actions the *left
   side* emitted. Program actions arrive unsolicited and are addressed by
   fd. So `both client1 client2` as a world does not route `Read 5` to
   client 5. You'd need a different `both` that routes by address, i.e. a
   different library.
3. **Readiness is state, not an event.** "fd 5 is readable" is a property of
   buffered data. A world-as-program would have to re-emit it every round.

So a world written as a flipped async program needs a second, dual
combinator library, and it would be a worse way to write what is really a
state machine. **Shelved.**

## 2. What works: clients as programs, the kernel as glue

Put the program on *both* ends and the OS in the middle, as in reality:

```
server m  ──actions──▶            ◀──actions──  client c
          ◀─snapshot──  kernel k  ──snapshot─▶
```

- The **client** is an ordinary async computation in its own vocabulary:
  `Send d | Recv`, responses `Sent | Got d | Empty`, event `CReadable`. It
  is written with `bind`/`emit`/`wait`/`fix`/`both`.
- The **kernel** is a state machine: `net = <| up; down |>`, two message
  queues. It answers the server's batch (`Read fd` pops `up`, `Write fd d`
  pushes onto `down`), then the client's (`Send d` pushes onto `up`, `Recv`
  pops `down`), one response per action, in order. Readiness is computed
  from the new state (`Readable fd` iff `up ≠ []`, `CReadable` iff
  `down ≠ []`), so it is honest by construction.

```
world_step fd c (k, hc) as =
  let (k1, rs) = sacts fd k as;                          (* server batch *)
      (k2, rc) = cacts k1 (new_actions (log_of c) hc);   (* client batch *)
      n = SUC (LENGTH hc)
  in (ssnap fd k2 n rs, (k2, hc ++ [csnap k2 n rc]))

run fd m c 0       = ([], (net0, []))
run fd m c (SUC n) = let (hs, w) = run fd m c n;
                         (s, w') = world_step fd c w (new_actions (log_of m) hs)
                     in (hs ++ [s], w')
```

**`connect` is well defined, by plain primitive recursion.** Each side's
round-n actions depend only on its first n snapshots, and that's guaranteed
by the type (`computation` = function of the history so far). So both sides
emit, the kernel steps, and both get their next snapshot. The result is
**a pair of histories built round by round** (plus the kernel state), not a
single trace. Each side has the usual one-round delay. The only arbitrary
choice is the order within a round: the server's batch first, then the
client's.

**For the server, `(kernel, client history)` is a world given as a state
plus a step function.** `world_step` has exactly the shape that the
closed-loop spike (`spike/async-closed-loop`) and the CF result
(`spike/cf-reactive`) take. The client being an async program is invisible
to them: it's polled inside the step. So a world built from client programs
plugs into the cf-reactive theorem directly, as long as that theorem's world
type is this kind of state + step function (I haven't checked its exact
signature).

## 3. What is proved

Completed transcript (rounds whose responses have arrived):
`ctrans m h = FLAT (GENLIST (round_trans m h) (LENGTH h))`, with
`ctrans_SNOC` and `trans m h = ctrans m h ++ zipr (new_actions (log_of m) h) []`.
`sent`/`got` are the client's counterparts of `written`/`read`.

```
(* MAIN: for ANY server m and ANY client c, the network neither creates nor
   drops a string *)
net_conservation:
  run fd m c n = (hs, (k, hc)) ⇒
  read fd (ctrans m hs) ++ k.up = sent (ctrans c hc) ∧
  got (ctrans c hc) ++ k.down = written fd (ctrans m hs)

(* MAIN: echo handler, ANY client: everything the client sent is received,
   queued downwards, being written back this round, or queued upwards *)
echo_conservation:
  run fd (handler fd) c n = (hs, (k, hc)) ⇒
  sent (ctrans c hc) =
    got (ctrans c hc) ++ k.down ++
    written fd (zipr (new_actions (log_of (handler fd)) hs) []) ++ k.up

(* MAIN: whatever the client program, it only ever receives what it sent,
   in order *)
client_receives_what_it_sent:
  run fd (handler fd) c n = (hs, (k, hc)) ⇒ got (ctrans c hc) ≼ sent (ctrans c hc)
```

`echo_conservation` is the existing `handler_echoes` (written = read, on the
server's own transcript) composed with the kernel's conservation law. No
server proof was redone. The client is arbitrary, with no well-formedness
assumption on it and no `fresh`: the kernel has one connection.

Concrete runs (`EVAL`, in the script):

```
echo_client ls  = bind (send_all ls) (λu. recv_n (LENGTH ls))          (* send, then read *)
echo_client2 ls = map SND (both (send_all ls) (recv_n (LENGTH ls)))    (* concurrently *)

example_run_sequential: after 8 rounds against handler 7,
  echo_client ["hi"; "yo"] has result SOME ["hi"; "yo"], and the network is empty
example_run_concurrent: after 7 rounds,
  echo_client2 ["hi"; "yo"] has result SOME ["hi"; "yo"];
  the server emitted [Read 7; Write 7 "hi"; Read 7; Write 7 "yo"]
```

Measured, not in the script: `echo_client` finishes at round 3·|ls|+1 for
|ls| = 2 and 4. The handler is the bottleneck: one line per wait/read/write
cycle.

Cost: about 350 lines, around an hour of proof work, all proofs short.

## 4. Simplifications (honest list)

- **One connection, already open.** There is no `Accept`/`Connect`, and the
  server is `handler fd`, not `server lfd`.
- **Messages, not byte streams.** `Write fd "ab"` arrives as one `Got "ab"`.
  There's no chunking and no partial reads or writes.
- **A deterministic, eager kernel.** Data is visible the round after it's
  sent, and there are no spurious `WouldBlock`s. All nondeterminism comes
  from *quantifying over clients* (which can delay via timers, split lines,
  interleave sends and receives). An adversarial network would need an
  oracle in the kernel state, i.e. back to the schedule of
  `01-semantics.md` §10, but only for the kernel's own choices.

## 5. Can fairness be derived from client structure?

**Plausibly yes, but it isn't proved here.** In this setting `data_live`,
`one_response_per_action` and honest readiness aren't assumptions: they
are facts about the kernel (the second and third hold by construction). The
liveness statement would be:

> Conjecture (echo liveness). For all `ls`, there is `n` (≈ 3·|ls|+1) with
> `run fd (handler fd) (echo_client ls) n = (hs, (k, hc))` and
> `(echo_client ls hc).result = SOME ls`.

Combined with `echo_conservation`, that yields "the client receives exactly
what it sent" as an equality, from the structure of the client (it
eventually stops sending and keeps receiving) rather than from a fairness
predicate on an arbitrary schedule.

Why it's not quick: the existing transcript lemmas (`trans_bind_continues`)
reason about a given history. Here the history depends on the programs
themselves. You need *progress* lemmas for each side under `run`, e.g. "if
`up ≠ []` and the handler is waiting, within 2 rounds a line moves from `up`
to `down`", stated about the unfolding of `fix`/`bind` along a run. That's a
simulation argument, likely several hundred lines. I'd only do it if
liveness becomes a goal at the model level, and the closed-loop spike may
cover the same ground with a step-function world.

## 6. The four payoffs

| Payoff | Status |
|---|---|
| 1. Echo clients as async programs; M4 as "every client receives exactly what it sent" | **Partly.** One client: prefix (safety) proved for every client; equality needs liveness (§5). Many clients: needs a kernel with `Connect`/`Accept` (§7). |
| 2. Fairness derived from clients rather than assumed | **Plausible, not done** (§5). The assumptions turn into kernel facts; progress needs a simulation proof. |
| 3. Clients compiled as a real test harness | **Plausible.** The clients use the same library as the server, so once the CakeML library exists they compile unchanged against a real socket FFI. `echo_conservation` is then the spec of what the harness should see. Nothing is proved about the real OS. |
| 4. Write-up story: the abstraction is closed under what it describes | **Yes, in the modified form.** Both ends of the wire are async programs; the OS is a small state machine between them, and `run` composes them. The literal mirror (§1) is *not* a good story. |

## 7. Recommendation and next step

**Promising in the modified form; the literal mirror is shelved.** If
pursued, the next step (about half a day) is:

1. A multi-connection kernel: a pending-connection queue and per-connection
   `up`/`down`. Client actions `Connect | Send conn d | Recv conn`, so that
   `both client1 client2` is meaningful (client-side routing *is* positional
   and works, because each client names its connection). Server against
   `server lfd`.
2. Reuse `server_echoes`/`echo_server_safety` the way `handler_echoes` is
   reused here: every client receives a prefix of what it sent. `fresh`
   becomes a kernel fact (it hands out distinct connections) instead of an
   assumption.
3. Only then decide whether to invest in the liveness simulation (§5), in
   coordination with the closed-loop spike so the two don't duplicate work.

## 8. Many clients, the full server (`worldAsyncMulti`)

### 8.1 The kernel

```
knet = <| pending : num list; next : num;
          up : num -> string list; down : num -> string list |>
net0 lfd = <| pending := []; next := SUC lfd; up := K []; down := K [] |>

client actions:  Connect | Send g d | Recv g        responses: Connected g | Sent | Got d | Empty
server actions:  Accept l | Read g | Write g d      responses: Accepted g | NoConn | Data d | WouldBlock | Written
```

- `Connect` takes a fresh number `next` (above the listener), appends it to
  `pending` and returns it to the client at once. The client can start
  sending before it is accepted, as with a real socket's backlog.
- `Accept` pops `pending`. `Read g`/`Write g d` and `Send g d`/`Recv g`
  work on connection g's two queues, as before.
- Readiness: `Readable lfd` iff something is pending; `Readable g` iff
  `up g ≠ []`; the client's `CReadable g` iff `down g ≠ []`. This is
  computed over the connections handed out so far
  (`conns lfd k = [SUC lfd ..< k.next]`), so the sets are finite and EVAL
  can compute them.
- `world_step` and `run` are as in §2, with the client batch being the
  combined batch of `both client1 client2 …`. **Client-side `both` works
  unchanged:** the kernel answers the combined batch positionally, and
  `both` routes each response back to the client that asked. Each client
  names its connection, so no routing by address is needed on that side.
  The asymmetry in §1 disappears once the world is a kernel rather than a
  program.

### 8.2 What is proved

```
(* any server m, any client program c *)
multi_conservation:
  run lfd m c n = (hs, (k, hc)) ⇒
  (∀g. read g (ctrans m hs) ++ k.up g = sent g (ctrans c hc) ∧
       got g (ctrans c hc) ++ k.down g = written g (ctrans m hs)) ∧
  accepted (ctrans m hs) ++ k.pending = conns lfd k ∧ SUC lfd ≤ k.next

(* `fresh` is a kernel fact, not an assumption *)
fresh_kernel:
  run lfd m c n = (hs, (k, hc)) ⇒ fresh (trans m hs)

(* MAIN: the echo server, any clients: everything sent on g is accounted for *)
closed_echo:
  run lfd (server lfd) c n = (hs, (k, hc)) ⇒
  ∀g. sent g (ctrans c hc) =
        got g (ctrans c hc) ++ k.down g ++
        written g (zipr (new_actions (log_of (server lfd)) hs) []) ++ k.up g

(* MAIN: for any number of clients (one async program, e.g. a `both` of
   them), on every connection, received ≼ sent, in order *)
every_client_receives_what_it_sent:
  run lfd (server lfd) c n = (hs, (k, hc)) ⇒
  ∀g. got g (ctrans c hc) ≼ sent g (ctrans c hc)
```

The server side is entirely `echo_server_safety` from
`asyncServerSafety`, reused as is. Its one hypothesis, `fresh`, is
discharged by `fresh_kernel`: the server is handed exactly the connections
that were made, in order (`accepted ++ pending = conns`), and those are
distinct. The new proofs are the kernel's bookkeeping (`sacts_moves`,
`cacts_moves`) and an induction over rounds, about 300 lines in all.

**Per connection versus per client.** The theorem is stated per
connection. It becomes per client when each client only uses the
connection it got from `Connect`, which is true of `client` below. A client
that sends on someone else's connection number is not prevented (no
ownership), and the theorem still holds per connection, which is the
honest statement.

### 8.3 Clients and a concrete run

```
client ls = bind (emit Connect) (λr. case r of
              Connected g => bind (send_all g ls) (λu. recv_n (g, LENGTH ls))
            | _ => return [])
two = both (client ["hi"; "there"]) (client ["yo"])
```

`example_two_clients` (EVAL, about 12 s): after 10 rounds,
`(two hc).result = SOME (["hi"; "there"], ["yo"])`, and the server emitted

```
[Accept 0; Read 1; Accept 0; Write 1 "hi"; Read 2; Read 1; Write 2 "yo"; Write 1 "there"]
```

So client 1 got connection 1 and client 2 got connection 2, and the two
connections were served interleaved.

Cost of EVAL: the model recomputes each computation from its whole history
every round, so running n rounds costs roughly n² polls of a tree that
grows with the number of handlers. It takes 0.3 s for 4 rounds, 4 s for 8,
and 27 s for 12. That's fine for examples but not for a test harness. A
harness would run the compiled clients, not EVAL (§6, payoff 3).

A pitfall I hit: with readiness written as `set l ∪ {Readable lfd}`, EVAL
can't decide membership. `wait` then never resolves, and evaluating `fix`
blows up without an error. Readiness is now a single `set` of a list.

### 8.4 Liveness: what exactly blocks it

The conjecture:

> For all `ls1 ls2`, there is n such that
> `run lfd (server lfd) (both (client ls1) (client ls2)) n = (hs, (k, hc))`
> and `(both (client ls1) (client ls2) hc).result = SOME (ls1, ls2)`.
> More generally: for any client program that eventually stops sending and
> keeps receiving on its connections, `got g = sent g` eventually.

With `closed_echo`, it reduces to showing that the queues drain:
`k.up g`, `k.down g`, the in-flight writes and `pending` eventually become
empty, and the clients keep receiving. Three things block a cheap proof:

1. **No residual operator.** A computation is a function of its *whole*
   history. A progress argument needs "after history h, m behaves like
   m' on the rest", i.e. `m (h ++ h') = (m after h) h'` up to the actions
   already emitted. The model has this for `bind` once the first part has
   finished (`bind_continues`). It does not have it for `both`: the
   routing of h' depends on `par_views` of all of h, and for `fix` only via
   unfolding. A residual operator `after m h` with laws for `bind`/`both`/
   `map`/`fix` (and `wf` preservation) is the missing infrastructure. It's
   probably a few hundred lines in `asyncCore`/`asyncLevel1`, and generally
   useful (it is also what a step-function view of a program needs).
2. **An unbounded tree of handlers.** After k accepts, the server's
   residual is `both (handler g1) (both (handler g2) (… (server lfd)))`.
   Progress needs a phase per handler (waiting / reading / writing) and a
   measure that decreases: total strings in `up`/`down`, plus pending
   connections, plus each handler's phase. That's a simulation over a tree
   built by `fix`, not a single loop invariant.
3. **The clients' structure has to be expressed.** "Eventually stops
   sending and keeps receiving" is a property of a program, not of a
   schedule. With the residual operator it's an invariant of the client's
   residuals, e.g. a phase function like the server's. Without it, it can
   only be stated for specific clients (`client ls`).

None of these is a problem with the closed-system formulation. They're the
cost of reasoning forwards about history-function programs. The likely
cheaper route is the closed-loop spike's: liveness for a state + step
function. That needs the server as a step function (a residual operator
again, or a refinement), and then this kernel and the clients are the
world. Which way to go is worth deciding together with that spike.

### 8.5 Verdict (update)

**Promising, and now with a clean headline:** for any number of clients
written as async programs, in a closed system with no assumptions, every
connection receives exactly a prefix of what was sent on it, in order. The
world-as-programs view made `fresh` a theorem and turned the M4 safety
property into a statement about clients, at low cost, reusing the existing
server proof unchanged. Liveness (fairness from client structure) is still
open. It needs a residual operator for computations (§8.4), which is the
recommended next step if liveness at the model level is wanted. Otherwise
stop here; the safety result stands on its own.
