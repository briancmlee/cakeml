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

The candidate statement is `chat_spec_timely B A lfd prog`: chat_safe ∧ chat_live_open ∧ chat_prompt B ∧ chat_accept_prompt A.

Design decisions:
- **D14:** the time unit is polls, because they are the only time-like observable in the trace. Rounds are an implementation notion.
- **D15:** the accept bound is proportional to the backlog (`nconnects`), not a constant. Any server that accepts a bounded number of connections per poll needs this, and ours accepts one per ≤ 2 rounds. A constant K is impossible against bursty arrivals unless the server drains the whole queue every poll.
- **D16:** C-EOF ends the *owed* range at the EOF read. It does not stop the server from writing: chat_safe still allows writing up to `owed` (half-close semantics). "Owed from connect" for C-JOIN was rejected, because a server cannot know about a connection before it accepts it.

## 3. Proved for the chat program: `chat_prog_timely : chat_spec_timely 4 3 3w chat_prog`

How the bounds are proved:
- **Delivery within 3 rounds** (`chat_deliver_rounds`). What d is owed at round R is written by the end of round R+2, independent of the number of clients:
  - `writer_window`: in every 2 consecutive rounds the writer makes a new answered Fetch;
  - `chat_cover_at`: by round R+2, the hub has told d's writer everything owed at round R. This replaces the old global counting, which gave round 3R+4;
  - `server_v_live_at` (generic, B = 0): what the writer was told is written in the same round.

  On the trace this gives `chat_prompt 4` (`chat_prompt_trace`). A point inside round n has ≥ n polls, and the write is in the first n+4 rounds.
- **Accepts** (`chat_accept_rounds`). The connection is accepted by round n + 3·nconnects:
  - `m_queue_progress_at` (generic): a connection at queue position k is handed out within 3(k+1) rounds;
  - `lq_nconnects`: the listener's queue is no longer than the number of connections that arrived, because the world creates connections only on Connect arrivals (`conn_arrived`).
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

## 4. Bounded memory (GC hub)

See §5 (to be written with the GC milestone).
