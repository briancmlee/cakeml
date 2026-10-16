# 42 — Chat: bounded latency, prompt accepts, departed clients, bounded memory

Follow-up to the chat server (design/40, design/41), on the user's point:

> accepting a program that indefinitely buffers and never sends out seems quite sad

ChatSpec's delivery clause only says "eventually". The hub's log also grows forever on the heap, and the trace cannot show that.
This note covers two things:
- the candidate spec additions (all in new files, for review);
- what is proved about the chat program.

## 1. What the trace can measure

The trace has no clock. The only time it shows is the server's own polls: each round of the event loop ends with exactly one «sock_poll» event (`grounds_events_def`).
In the socket world each poll is one step of the schedule (`tick`). So **polls are the time unit** in everything below.

Two caveats:
- A server that never polls meets a poll-counted bound only by delivering eventually. A server that waits for readiness has to poll.
- Inserting extra polls changes the count. That is intended: the polls are the clock.

## 2. Candidate spec: `spec/ChatSpecTimely` (+ `ChatSpecTimelyBite`)

ChatSpec is unchanged. The candidate adds three clauses, one for each finding of the independent adequacy review:

| finding | clause | what it rules out (proved bite) |
|---|---|---|
| C-DELAY: no latency bound | `chat_prompt B io`: whatever d is owed at any point is written to d before B more polls | `broken_delays`: for every B, a trace that relays a line only after B+1 polls fails `chat_prompt B` (and still delivers eventually) |
| C-JOIN: owed starts at accept, so a late accept loses lines | `chat_accept_prompt A sk io`: a connection that arrived within the first n schedule steps is accepted by poll n + A·`nconnects n sk` | `broken_accepts_late`: leaving c1 pending for 2A+2 polls (2 arrivals) fails `chat_accept_prompt A` |
| C-EOF: a departed client is owed lines forever | `owed_open`: owed, counting only lines completed before the server read d's EOF; `chat_live_open` uses it | `departed_client`: a server that drops c2 after its EOF fails ChatSpec's `chat_live`, but c2 is owed nothing under `owed_open` |

Further facts proved in the bites file:
- **Relation to ChatSpec:**
  - `owed_open_prefix`: `owed_open ≼ owed`;
  - `chat_live_open_of_chat_live`: chat_live implies chat_live_open;
  - `chat_prompt_delivers`: chat_prompt implies the delivery clause.
- **Non-vacuity:** `chat_timely_satisfiable`. ChatSpecBite's ideal trace meets `chat_prompt 0`, `chat_accept_prompt 0` and `chat_live_open`.

The candidate statement is `chat_spec_timely B A R lfd prog`: chat_safe ∧ chat_live_open ∧ chat_prompt B ∧ chat_accept_prompt A ∧ chat_read_prompt R.

**Revision after the machine-checked review of ChatSpecTimely (T1, T2), for user review:**
- **T1 (reading was still "eventually").** New clause `chat_read_prompt R`: the complete lines a client sent within n schedule steps are read by poll `n + R·(1 + nconnects n + bytes sent)`.
  - The per-byte term is unavoidable: a read may return a single byte.
  - The per-connection term covers the client waiting to be accepted.
  - Bite: `broken_reads_late`.
- **T2 (the accept bound counted every past connection).** `chat_accept_prompt A` is now measured at the n-th poll (the prefix ending with it) against the *current backlog*: `nconnects n − naccepts evs0`.
  - Bite: `broken_accepts_backlog`. c1 is accepted at once, and leaving c2 pending for A+2 more polls fails. The old bound allowed it.
- **Non-vacuity with the world's polls** (the reviewer's stutter point): `chat_timely_satisfiable` now uses a trace with one poll per schedule step. It meets every clause with B = A = R = 0.
- **What is not fixed, and why.** The review's `join_late_A1` and `join_same_round_A0`: a client misses lines completed between its connection becoming pending and its accept.
  - The suggested fix, "owed from CONNECT", is not implementable in this world. Poll only says the listener is readable, so no server can know when a given connection arrived, or the log position at that time.
  - The faithful options are:
    - **(a), this revision:** owed from accept, plus an accept bound on the current backlog. The residual gap is A·backlog polls, plus at most one round.
    - **(b), follow-up:** a server that drains its accept queue before any read in each round, i.e. A = 0 with no same-round miss. With (b), "owed from the poll at which the connection became pending" becomes provable. It is a change to the server skeleton, with M3/M4 re-proofs.
- **D20:** the per-byte read bound (T1) and the backlog accept bound (T2) are the tightest bounds a one-accept-per-round, partial-read server can meet. Tighter constants are a server change, not a spec change.

Design decisions:
- **D14:** the time unit is polls, because they are the only time-like observable in the trace. Rounds are an implementation notion.
- **D15:** the accept bound is proportional to the backlog (`nconnects`), not a constant. Any server that accepts a bounded number of connections per poll needs this, and ours accepts one per ≤ 2 rounds. A constant K is impossible against bursty arrivals unless the server drains the whole queue every poll.
- **D16:** C-EOF ends the *owed* range at the EOF read. It does not stop the server from writing: chat_safe still allows writing up to `owed` (half-close semantics). "Owed from connect" for C-JOIN was rejected, because a server cannot know about a connection before it accepts it.

## 3. Proved for the chat program: `chat_prog_timely : chat_spec_timely 4 3 4 3w chat_prog`

How the bounds are proved:
- **Delivery within 3 rounds** (`chat_deliver_rounds`). What d is owed at round R is written by the end of round R+2, independent of the number of clients:
  - `writer_window`: in every 2 consecutive rounds the writer makes a new answered Fetch;
  - `chat_cover_at`: by round R+2, the hub has told d's writer everything owed at round R. This replaces the old global counting, which gave round 3R+4;
  - `server_v_live_at` (generic, B = 0): what the writer was told is written in the same round.

  On the trace this gives `chat_prompt 4` (`chat_prompt_trace`). A point inside round n has ≥ n polls, and the write is in the first n+4 rounds.
- **Accepts** (`chat_accept_rounds`). The connection is accepted by round n + 3·nconnects:
  - `m_queue_progress_at` (generic): a connection at queue position k is handed out within 3(k+1) rounds;
  - `lq_nconnects`: the listener's queue is no longer than the number of connections that arrived, because the world creates connections only on Connect arrivals (`conn_arrived`).
- **Reads** (`asyncChatTimely2`, `chat_read_trace`): by n + 4·(1 + nconnects + bytes). The client is accepted by n + 3·nconnects, and its reader then gets at least one byte every 4 rounds (`chat_reads`).
- **Accepts against the backlog** (`chat_accept_backlog`), from three facts:
  - `rounds_at_poll`: the prefix ending with the n-th poll is exactly the first n rounds;
  - `naccepts_rounds`: its accept events are the connections handed out;
  - `acc_lq_nconnects`: handed out plus waiting ≤ arrived.
- **Departed clients.** The program keeps serving them, so it meets the stronger ChatSpec `chat_live`, and hence `chat_live_open`.

Cost (lines):

| part | lines |
|---|---|
| writer window lemmas (asyncChatLiveCover) | ~130 |
| `chat_cover_at` (CoverRun, a copy of chat_cover with a new counting step; chat_cover is now a corollary) | ~40 changed |
| generic `server_v_live_at` | ~45 |
| generic `m_queue_progress_at` | ~65 |
| asyncChatTimely (polls, world lemmas, chat bounds) | 374 |
| headline | 44 |
| spec | 125 |
| bites | 273 |

None of it needed new invariants of the hub. The bound was always there; the old proof threw it away.

## 4. Bounded memory: the GC hub (`asyncChatGC*`)

**What the trace can and cannot say.** In this world writes always succeed, so nothing about memory is observable on the trace. A server that buffers forever and one that frees promptly produce identical traces. So memory is stated about the implementation: the hub's store, at the model level and as the CakeML value it is carried in.

**The hub.**
- Each connection has a **cursor**: the position its writer last fetched from. The writer asks for `Fetch i` only after writing everything before `i`, so the cursor is how much of the log that client has confirmed. Before its first Fetch, the cursor is the client's join position.
- After every step, `collect` drops the log below the least cursor. With no clients connected, it drops everything.
- The store keeps `base` (bytes dropped so far) and `glog` (the log from `base` on).

**Theorems.**
- `gc_space` (store level) and `gc_run_space` (at every point of the run):

      LENGTH glog = gend − cmin

  The hub holds exactly the bytes after the least client cursor, i.e. the largest amount any connected client has not yet confirmed. `gc_space_max` gives the per-client form: `gend − c ≤ LENGTH glog` for every cursor `c`.
- **No re-proof of safety or liveness.** `gc_trace_eq`: the GC server's trace *is* the chat server's trace, so every M3/M4/timely theorem transfers.

How `gc_trace_eq` is proved:
- `asyncWithTapSim` (generic): a guarded simulation between two taps.
- `gR`: the relation between the full hub and the GC hub (same buffers and joins, same log end, GC log = full log from `base`). It holds unconditionally. Only the answer to `Fetch i` needs a guard: `i ≥ base`.
- `chat_gc_guard`: the guard holds on every run that hands out distinct 64-bit connections. The ingredients:
  - `writer_args`: a writer's Fetch positions start at its join and never decrease;
  - `gc_curs`: a cursor is a join position or at most an earlier Fetch position of the same connection;
  - freshness: the join a writer was told is still current.
- `gc_server_eq`, `grounds_cong`, `gc_grounds_eq`: the two servers agree on the run's histories, so the runs are equal.

**In CakeML** (`asyncChatGCProg`, `GCSpec`, `GCMain`, `GCSemantics`, `GCValue`):
- The GC hub is translated. The tap, the query step and `gc_server` are new CakeML code; with_tap, the skeleton and the handler are reused. CF instances: `gc_tap_s_TAP`, `gdelta3_DELTA`, `gc_server_spec`.
- `gc_prog_timely : chat_spec_timely 4 3 4 3w chat_prog_gc`. The GC program's trace is `chat_trace s0` (`gc_trace_eq`), so every chat theorem applies.
- `gc_value_space`: the store value `v` the program carries (with `GSTORE st v`) holds its log as a CakeML list of exactly `gend st − cmin st` cells.
- `make demo-gc` builds the GC binary with the release compiler and passes the same 3-client demo.

A surprise: the translator turned the hub's `i − base` into a side condition `base ≤ i`, which is exactly the GC guard. The code was made total (`if base ≤ i then i − base else 0`, equal to the model's truncated subtraction). The guard is then needed only for *equality with the full hub*, and that is discharged once, at the model level.

**Combined with timeliness.** Every client fetches at least every 2 rounds (`writer_window`). So every cursor is at least the log length of a few rounds ago, and the hub holds at most the lines completed in the last few rounds. This is a corollary not yet stated formally; it is the natural next statement.

Design decisions:
- **D17:** GC by refinement, not by re-proof. The GC hub is proved observationally equal on runs, so the existing 5,000+ lines of safety/liveness proofs are reused unchanged.
- **D18:** the cursor is the writer's *fetch* position, not a separate acknowledgement. The protocol is unchanged, and the writer code is unchanged.
- **D19:** `collect` runs after every step, including taps, so a server with no connected clients keeps nothing.

## 5. Next steps: clients leaving, slow readers

These are where unbounded buffering really bites. Neither is in this work.

**Clients leaving (needs `close`, cf. close-v2's v2 world and handle layer).**
- In v1 a connection never goes away. Its cursor pins the log forever if its writer stops.
- With `close`, `owed_open` extends naturally: what a client is owed ends at its EOF/close.
- The hub needs a `Leave fd` event, tapped like `Accept`: remove fd's cursor and join, then `collect`.
- Proof obligations:
  - the guard argument is unchanged for live connections;
  - `gR` needs joins to match modulo departed fds;
  - the space theorem then says the log is bounded by the least cursor among *live* clients.
- The real risk is fd reuse after close. `freshc` (distinct accepts) becomes "distinct among live connections", and `chat_gc_guard`'s freshness step must use the latest join only. The `ALOOKUP` shadowing already does that.

**Slow readers / backpressure (needs the endpoint world, where writes can block or be partial).**
- Today `chat_prompt` holds because writes always complete in one round. With blocking writes, delivery latency depends on the reader, so the spec must change:
  - promptness relative to the client's readiness ("written within B polls of the socket becoming writable");
  - or a bounded-buffer policy: drop or disconnect clients more than M bytes behind.
- The GC hub is exactly what makes the second policy expressible. The space theorem's quantity, `gend − cmin`, is the slowest client's lag. A policy "disconnect any client whose lag exceeds M" makes `LENGTH glog ≤ M + (one round's input)` a theorem.
- Spec side: owed must end at the disconnect, as for leaving (C-EOF style), plus a fairness clause that only clients over the limit are dropped.
- Proof side: the writer's partial writes need a cursor that advances by the bytes actually written. A per-write-acknowledged cursor instead of fetch-based (D18) is the natural change.
- Bounded latency then becomes "within B polls of writability", and the window lemma carries over with the reader's readiness as a hypothesis.
