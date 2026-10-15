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

## 3. Implementation (model level)

**Pivot (D9).** The first plan had readers `Publish` lines to a `with_store` log. That needs a *round-shift* lemma: reads in round n are published in round n+1, in the same fiber order, through `both` and `server_with`'s dynamic spawn tree. This is KV's "timestamped bridge" (design/30 §4.3) in another form. The library's transcript lemmas are flat, not per round, so it would have been a large new proof.

**Decision D9: sequence at the I/O boundary.** A new generic effect handler, `with_tap σ δ s0 m` (asyncWithTap), generalizes `with_store`:
- it answers m's queries with δ, as `with_store` does;
- it also **observes** m's socket (action, response) pairs, in order, through the tap σ.

The store at any position of m's transcript is a fold over the transcript up to that position (`tap_answers`). `with_store` is the special case σ = K.

Rationale: the chat's global order is defined by I/O (the order of reads). A tap sees exactly that order, so the hub's log equals `relayed` by construction. Neither a shift lemma nor a fiber-order lemma is needed.

- The hub's store: `log` (complete lines, in order), `bufs` (each connection's partial line), `joins` (the log length at each accept). Keys are 64-bit words, as the socket world's fds are. Then the socket-level tap is the model tap read through `srelabel`, exactly (`chat_tap_s_sfa`, D10).
- `chat_server lfd = with_tap chat_tap chat_delta empty_store (cserver_with chat_handler lfd)`.
- `chat_handler fd = both (reader fd) (writer fd)`:
  - **reader**: `readable fd; Read fd`, forever, until EOF. The data goes to the tap, not to the reader.
  - **writer**: `Start` (where did I join?), then forever `Fetch i`. If there are new lines, `Write` them all and advance `i`. If the connection has not joined, the answer is `NotJoined` and the writer stops: safe by construction.
- **Safety proof** (asyncChatSafe), in three parts:
  1. `tap_inv`: the hub describes the transcript. Pure list induction.
  2. `writer_written`: with any growing log oracle, the writer writes a prefix of the log from its join position. Local to the handler.
  3. Gluing: `cserver_with_isolates` (copied from KV's `server_with_k`), `tap_answers`, and the monotone positions. No round reasoning anywhere.
- `cserver_with` is a renamed copy of KV's `server_with_k` (D11). KV's file is WIP: one proof fails, so it can't be a dependency yet. Reconcile later.

## 4. Status

- M1: spec + bites: DONE (PR #66).
- M2: model + model-level safety: DONE (`chat_server_safe`, asyncChatSafe; with_tap metatheory asyncWithTap).
- M3: CakeML + CF + whole-program safety: next (drafts in asyncWithTapStep, asyncChatSockModel, asyncChatProg, asyncChatSpec).
