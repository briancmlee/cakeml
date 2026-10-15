# The echo server in the closed loop: safety and liveness

This note covers M4's closed loop in pure HOL. The echo server runs
against a model of the outside world (sockets), and we prove that:

- every client gets back only its own data, in order (**safety**);
- every byte that arrives on a connection is written back to it within a
  bounded number of rounds (**liveness**).

The scripts are:

- `asyncWorldScript.sml`: the world and the closed loop;
- `asyncClosedLoopScript.sml`: the world invariant, and safety;
- `asyncProgressScript.sml`: progress of the server, as a program;
- `asyncLivenessScript.sml`: liveness in the closed loop.

All proved, with no `cheat`.

## 1. The world

The world mirrors the socket model of `spike/socket-model`
(`async/ffi-spike/ffiSpikeSocketFFIScript.sml`), so that the two layers line
up for M4. That model depends on CakeML theories and this one doesn't, so
the world is mirrored here rather than imported.

```
arrival = Connect l c | Arrive c d | Hangup c        (the socket model: Connect | Data | Eof)
conn    = <| incoming; peer_closed; outgoing; received |>
world   = <| listeners : (fd # fd list) list;        (pending connections, oldest first)
             conns : (fd # conn) list;
             sched : arrival list llist |>           (the unpredictable future)
```

- `tick w` delivers the next step of the schedule. As in the socket model,
  an arrival that makes no sense is dropped (`deliver1`). Examples: a
  connection that reuses an fd, or data after the peer has closed.
- `perform a w` performs one action:
  - `Accept l` takes the oldest pending connection, or answers `NoConn`;
  - `Read c` returns all unread data (`Data`), else `Eof` if the peer has
    closed, else `WouldBlock`;
  - `Write c d` appends `d` to `outgoing` and answers `Written`.
- `ready_fds w`: the listeners with pending connections, and the
  connections with unread data or a closed peer.

**Differences from the socket model** (recorded for reconciliation):

| here | socket model | why |
|---|---|---|
| fds are `num`, data are `string` | `word64`, byte lists | no CakeML dependency; the server's vocabulary (`asyncServer`) uses `num` / `string` |
| `Connect` / `Arrive` / `Hangup` | `Connect` / `Data` / `Eof` | `Data` and `Eof` already name responses in `asyncServer` |
| a read returns all available data | `sock_read c n` returns at most `n` bytes | the server reads whole buffers; bounded reads are a refinement detail |
| ghost field `received` (everything that ever arrived) | none | the theorems are stated against it |
| the closed loop (§2) | `sock_poll` ticks, then reports readiness | same order: act, tick, report |

## 2. The closed loop

```
closed_loop m w0 0       = ([], w0, [])
closed_loop m w0 (n + 1) = let (h, w, perf) = closed_loop m w0 n;
                               acts = new_actions (log_of m) h;     (round n's actions)
                               (rs, w1) = perform_all acts w;       (performed in order)
                               w2 = tick w1                         (time passes)
                           in (h ++ [snapshot_of w2 (n + 1) rs], w2, perf ++ ZIP (acts, rs))
```

After n rounds we have three things:
- `h`: the history the program has seen;
- `w`: the world;
- `perf`: every action performed, with its response.

`snapshot_of` reports the ready fds as `Readable` events, with the round's
responses in order. This is positional routing (semantics note §3).

`trans_closed_loop` (MAIN): the program's transcript is `perf`, with
responses, followed by the current round's actions, which have no response
yet. So the safety theorems about transcripts (`08-echo-server.md`) apply
to the closed loop.

## 3. Safety in the closed loop

`consistent lfd w perf`: the world agrees with what the server has done.

- One listener. The connections already handed out, together with the
  pending ones, are distinct, known connections.
- On every known connection c:
  - `received = FLAT (read c perf) ++ incoming`;
  - `outgoing = FLAT (written c perf)`.
- Unknown connections have been neither read nor written.

| Theorem | Meaning |
|---|---|
| `closed_loop_consistent` (MAIN) | the invariant holds in every round |
| `closed_loop_accounting` (MAIN) | per connection: received = written back ++ being written back this round ++ unread |
| `closed_loop_safety` (MAIN) | per connection: `outgoing ≼ received` (nothing written that was not sent on that connection, nothing out of order) |

The world itself guarantees `fresh`, the one assumption of
`echo_server_safety`: it never hands out the same fd twice.

## 4. Progress of the server, as a program (`asyncProgress`)

These are facts about the program alone, on any history in which the world
answers **promptly**:

```
prompt m h ⇔ ∀i < LENGTH h. LENGTH (new_actions (log_of m) (TAKE i h)) ≤ LENGTH (responses_at h i)
```

That is, every action gets its response in the next snapshot. `prompt`
passes to the continuation of `bind` (`prompt_bind`) and to both sides of
`both` (`prompt_both`).

| Theorem | Meaning |
|---|---|
| `handler_progress` (MAIN) | if fd is readable in three snapshots in a row, the handler reads fd in those rounds, unless it has seen end-of-file |
| `server_accept_progress` (MAIN) | if the listener is readable in two snapshots in a row, the server accepts in those rounds |
| `server_handler_view` (MAIN) | inside the server, each accepted fd is served by its own handler, running on a view `g` of the server's history from the round `a` it was accepted. `g` has the same ready sets, it is prompt, the handler's transcript is the server's restricted to fd, and the server's reads of fd are the handler's, round by round |

Why three and two: one cycle of the handler is wait, read (one round for
the response), write (one round for the response). One cycle of the
server is wait, accept (one round for the response). A continuation only
sees snapshots after the one that finished the previous step (`bind`, §4
of the semantics note).

## 5. Liveness in the closed loop (`asyncLiveness`)

| Theorem | Meaning |
|---|---|
| `read_soon` | an accepted connection with unread data is read in one of rounds n .. n+3 |
| `closed_loop_echo_accepted` (MAIN) | on an accepted connection, everything that has arrived by round n has been written back by round n + 5 |
| `accept_soon` | with connections pending, the server accepts in one of rounds n .. n+2 |
| `queue_progress` (MAIN) | a pending connection with p connections ahead of it is handed out within 3 (p + 1) rounds |
| `closed_loop_liveness` (MAIN, headline) | on every connection, everything that has arrived by round n has been written back by any round N ≥ n + 3q + 5, where q is the number of pending connections at round n |

```
closed_loop_liveness:
  closed_loop (server lfd) (start_world lfd sch) n = (h, w, perf) ∧
  ALOOKUP w.conns c = SOME cn ∧ w.listeners = [(lfd, q)] ∧
  n + 3 * LENGTH q + 5 ≤ N ∧
  closed_loop (server lfd) (start_world lfd sch) N = (hN, wN, pN) ⇒
  ∃cnN. ALOOKUP wN.conns c = SOME cnN ∧ cn.received ≼ cnN.outgoing
```

**How `read_soon` is proved.** Suppose the server does not read c in rounds
n .. n+3.

1. Then c's data stays unread, so c is readable in snapshots n+1 .. n+3.
2. The handler of c has not seen end-of-file: by `closed_loop_eof`, that
   would mean c has nothing left to read.
3. So by `server_handler_view` and `handler_progress`, the handler reads c
   in one of rounds n+1 .. n+3.
4. Then so does the server, which contradicts the supposition.

`accept_soon` is the same argument with `server_accept_progress`.

**Then** a read of c takes all of c's data (`round_conn`), and everything
read by round m is written back by round m + 1 (`echo_next`, from
`echo_server_safety`). That gives n + 5. For pending connections, each
accept moves c up the queue (`round_queue`), and nothing gets ahead of it.

## 6. Assumptions, and fairness

**No fairness assumption is needed beyond the world model.** In the socket
model too, fairness is not an assumption on the program's environment but
a property of the world. An arrival is delivered when it is scheduled, and
a delay is just a later position in the schedule. The world properties the
proofs use are lemmas:

- the world answers every action in the next snapshot (`closed_loop_prompt`);
- a read returns all unread data, and end-of-file only once the peer has
  closed (`perform_conn`, `closed_loop_eof`);
- a write always completes (`perform_def`);
- unread data and pending connections are reported ready (`incoming_ready`,
  `listener_ready`);
- data only arrives and connections only join the back of the queue
  (`tick_conn`, `tick_listener`).

**From the clients' side.** Liveness is stated against `received`, which is
what actually arrived. The socket model's single named assumption,
`sched_wf`, says that no arrival of the schedule is dropped. Its per-arrival
condition is mirrored here as `arrival_ok`, and `arrive_received` shows that
data a client sends, if effective, is recorded in `received`. So under the
socket model's `sched_wf`, every byte a client sends is written back.

**Non-vacuity.** `example_closed_loop` (EVAL, about 3 s) runs the server
for 9 rounds on a schedule where two clients connect, interleave their data,
and one closes. Each client gets back exactly what it sent.

**Recorded assumptions and decisions** (for the user):

1. Reads return all available data (the socket model reads at most n
   bytes). With bounded reads the handler needs a loop that drains the
   buffer, and the bounds grow by the number of reads per buffer.
2. Writes always complete. Partial writes and backpressure are out of scope
   (as in `08-echo-server.md` §4).
3. The bounds count rounds of the polling closed loop. With a blocking
   scheduler (`server_no_busy_waiting`), the same actions are emitted on
   the non-idle rounds. A blocking closed loop, in which the world advances
   while the program blocks, is not formalised; see §7.
4. The world is single-listener (`start_world`), matching the server.

## 7. Gaps

- **Blocking scheduler.** The closed loop here runs the polling semantics.
  `server_no_busy_waiting` (M2) says a scheduler that blocks through idle
  rounds emits the same actions on the rounds it does not skip. Lifting
  liveness to a blocking closed loop needs a world that keeps ticking while
  the program blocks, and a proof that it only skips idle rounds. That is
  natural, but not done. Liveness bounds would then count non-idle rounds.
- **Schedule-level statement.** `arrive_received` connects one effective
  arrival to `received`. A theorem quantified over the whole schedule
  ("under `sched_wf`, every byte in the schedule for c is eventually in c's
  outgoing") needs the socket model's `ticks` machinery and is left for the
  reconciliation with that model.
- **CakeML level.** The closed loop here is the specification that the M3
  event loop and the FFI world model must refine.

## 8. Proposed MAIN theorems

| Theorem | File | Meaning |
|---|---|---|
| `trans_closed_loop` | asyncClosedLoop | the transcript in the closed loop |
| `closed_loop_consistent`, `closed_loop_accounting`, `closed_loop_safety` | asyncClosedLoop | safety in the closed loop |
| `handler_progress`, `server_accept_progress`, `server_handler_view` | asyncProgress | progress of the server, as a program |
| `closed_loop_echo_accepted`, `queue_progress` | asyncLiveness | liveness, per accepted / pending connection |
| `closed_loop_liveness` | asyncLiveness | **every byte that arrives is written back within n + 3q + 5 rounds** (headline) |
