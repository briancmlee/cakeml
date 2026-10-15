# The world as an async program (experiment)

Status: **experimental**, timeboxed. Prototype in
`async/world-async/worldAsyncNetScript.sml` (pure HOL, includes
`../model`; all proved, no `cheat`).

**Verdict, short.** The literal idea, a world that is an async computation
with the interface flipped, has no clean formulation (§1), so I shelved
that version. A nearby one works well: **clients are ordinary async
programs, and the world is those clients plus a small network kernel (a
state machine)**. Composition is well defined, takes a page of HOL, and
gives a closed-system theorem for *every* client program at almost no cost
(§3). Liveness, i.e. fairness derived from client structure, is plausible
but unproved (§5). Worth one more step (§7).

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
