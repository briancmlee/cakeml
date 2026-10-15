# 40. A verified chat (broadcast) server: spec, design, plan

Branch `spike/chat-spec` (M1), from `spike/http-kv-impl` (for `with_store`).
Worker: the "moonshot" session, working autonomously. Every design decision
below is the worker's own, with a one-line rationale; the user has not
reviewed them yet.

## 1. The statement (`async/spec/ChatSpecScript.sml`, trusted)

Clients connect to one listener and send lines (bytes ending in `\n`). The
server relays every line, verbatim, to every connected client, the sender
included.

- `relayed evs`: all lines the server has *completed reading* in the trace
  `evs`, in the order it completed them (an event completes the lines whose
  newline it read). This is the one global order.
- `owed d evs`: the lines completed after the event that accepted `d`.
- `chat_safe io`: at every point, `bytes_written_to d evs ≼ owed d evs` for
  every `d`.
- `chat_live sk io`: every connection in the schedule is eventually
  accepted; every complete line a client sends is eventually read; whatever
  a client is owed at some point is eventually written to it.
- `chat_spec lfd prog`: as `echo_spec`. In every fair one-listener world the
  program diverges, and its trace is `chat_safe` and `chat_live`.

## 2. Decisions

| # | decision | rationale |
|---|---|---|
| D1 | The global order is **fixed by the trace**: the order in which the server completed reading the lines. No existential order. | It's a short, deterministic statement that a reader can check. It implies one consistent order for all clients, causality and real time (a line read in full before another starts comes first for everybody), with no extra clauses. The only servers it excludes are those that reorder concurrent lines, which a chat server has no reason to do. |
| D2 | The sender is included: everyone gets every line. | It gives one uniform rule. Seeing its own line come back confirms to the sender where the line sits in the global order. Echo is the one-client special case. |
| D3 | A client is owed **exactly** the lines completed after its accept event: no backlog, and no gap. | The join point is observable in the trace, so neither a server-chosen join point nor an existential is needed. It forbids the "late joiner gets history" behaviour (a choice; bite `broken_sends_backlog`). |
| D4 | Lines are relayed verbatim (no sender prefix). | The spec stays byte-exact and short. The demo can still prefix names client-side. |
| D5 | Only complete lines are relayed. After EOF, the unterminated tail is never relayed. | A partial line is not a message. Relaying partial lines would make the order of interleaved fragments meaningless. |
| D6 | Liveness: accept, then read, then deliver, as three clauses. | Each clause is the natural "eventually" of one stage. Together they give "every line a client sends reaches every client accepted before the line was read". |
| D7 | Join is relative to the **accept event**, not the schedule's `Connect`. | The server cannot know about a connection before accepting it. Fairness (clause 1) bounds the delay. |
| D8 | Safety is stated per finite prefix, as in `echo_safe` and `http_safe`. | It's the standard form, and it gives a prefix-closed property. |

Rejected alternative: **an existential, linearizable order**, as in
`HttpKvSpec`: some order G per prefix, consistent per sender, with a
real-time clause "delivered to anyone before the other's first byte was
read". It is more general (it allows reordering of concurrent lines), but
the statement is much longer: liveness then needs "line x delivered to d"
relative to G. It also has to be checked against G in every bite. D1 is
strictly stronger, and the implementation below meets it.

## 3. Implementation plan (model level)

- The hub is `with_store` (KV's generic effect handler, `asyncWithStore`),
  instantiated with the **chat log** as its store:
  `Publish ls` appends lines, `Join` answers the current length, `Fetch i`
  answers `DROP i log`.
- `chat_server lfd = with_store chat_delta [] (server_with_k chat_handler lfd)`.
- `chat_handler fd = both (reader fd "") (writer fd)`:
  - **reader**: `readable fd; Read fd`. In the round the data arrives, it
    `Publish`es the newly complete lines (one action with the list), then
    loops.
  - **writer**: `Join`, then forever `Fetch i`. If there are new lines, it
    `Write`s them all and advances `i`.
- **Why the order comes out right** (the proof's spine):
  1. **Shift.** A reader publishes, in round i+1, exactly the lines its
     reads completed in round i. `both` keeps left-then-right order within
     a round for both reads and publishes. So the hub log after round i+1
     is exactly `relayed` of the trace up to round i.
  2. **Join.** The accept loop is the rightmost fiber, so `Accept` is the
     last action of its round. The new handler `Join`s in the next round,
     after all older handlers' publishes of that round. So the join index is
     exactly the number of lines completed before the accept event.
  3. **Writer.** What it writes is a prefix of `DROP join log` ≼ `owed`.
- Liveness: a reader reads within a bounded number of rounds of data being
  readable (as echo does). Publishing takes 1 round. A writer fetches every
  other round, so it delivers within a bounded number of rounds. Reuse
  `server_with_live` / `henv` for the reading part where possible.

## 4. Status

- M1: spec + bites (this note's §1–2): in progress.
