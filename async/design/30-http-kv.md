# 30. An HTTP key-value server: spec and feasibility

Branch `spike/http-kv`, stacked on `spike/http-bodies` (#28's
HttpSpecBodies). This note is for the user to review before any proof
work.
- **Spec:** `async/spec/HttpKvSpecScript.sml` (135 lines; HttpSpecBodies
  is 142).
- **Bites:** `async/spec/HttpKvSpecBiteScript.sml`. Everything in it is
  proved, with no cheats.
- No other spec file changes.

Target: go past Zhang et al., ITP 2021 ("Verifying an HTTP Key-Value
Server with Interaction Trees and VST"). They verify each module of a C
key-value server. They say they don't refine to a request-level "linear
specification", and they prove no liveness. The statement here has both.

## 1. The statement (`kv_spec lfd prog`)

**Requests and framing:** HttpSpecBodies' `brequest`, unchanged
(Content-Length bodies, the same validity and printer). The answers are:
- `GET k`: 200 with the value stored under `k`, or 404 if there is none.
- `POST k`, body `v`: store `v` under `k`, answer 200 with an empty body.

The keys are the paths, and the store starts empty. `kv_step` and
`kv_run` give the sequential semantics on a single store.

**Shape:** as in HttpSpecBodies. In every fair world with one listener
(`server_world`), the program diverges with an I/O trace `io` that
satisfies `kv_safe io ∧ kv_live sk io`.

**Safety, `kv_safe`.** Take any point `evs` of the run. Let `rss c` be
the complete requests read from connection `c` so far (followed by a
partial one; this split is unique, see `parse_unique`). Then there is an
`order` such that:
1. `is_order rss order`: the order lists every complete request `(c, i)`
   (connection `c`'s `i`-th) exactly once, and each connection's requests
   appear in the order they were sent.
2. **Real time:** if `precedes rss order evs x y` for requests `x` and `y`
   on different connections, then `x` comes `earlier` than `y` in the
   order. `precedes` means that at some earlier point `evs1` of the
   trace, the server had already written the whole response to `x`, and
   had not yet read any byte of `y`.
3. On every connection `c`, what the server has written is a prefix of
   `replies rss order c`. Those are the responses to `c`'s requests when
   all requests run one at a time, in `order`, on one store.

**Liveness, `kv_live`:** HttpSpecBodies' `http_live_b`, per connection.
If client `c` has sent requests `rs`, the server eventually writes
`LENGTH rs` whole responses to `c`. Their content is fixed by safety.

## 2. Why linearizability, and these details

**Sequential consistency is too weak.** Without condition 2, safety is
sequential consistency (`kv_safe_sc` in the bite file). Take this trace:
1. A's `POST /x` is answered.
2. B then connects and sends `GET /x`.
3. B gets 404.

The trace is sequentially consistent: order B's GET first
(`stale_read_sc`). But no client would accept this from a single key-value
store. A told B "I've written x", and B didn't see it. Linearizability
forbids it (`broken_stale_read`), and it's what users of a key-value
server expect. Linearizability is stronger, so `kv_safe` implies
`kv_safe_sc` (theorem `kv_safe_sc`).

**Real time from the server's trace.** A request's interval runs from the
moment the server reads its first byte to the moment the server has
written its whole response. Each endpoint is approximated from the
server's side, as the trace sees it.
- "Response written" comes before the client receives it.
- "First byte read" comes after the client sent it.

So any real precedence between clients (A received its answer, then told
B, then B sent) shows up as a precedence in the trace. Condition 2
therefore gives linearizability as clients see it. Using the first byte
is the weakest choice that still does this.

An alternative is the point where the request is *fully* read. That
would order more pairs, and so be a stronger spec. It would rule out
servers that are linearizable but take a snapshot early. The coordinator
mentioned this variant as "(fully) read". I chose the first byte. Either
version is proved the same way for the server in §3, so this is the
user's call. Switching is a one-line change in `precedes_def`: the last
conjunct becomes `¬(brequests (TAKE (SUC j) (rss d)) ≼ bytes_read_from d
evs1)`.

**Detail choices:**
- **Same-connection pairs are excluded from condition 2**
  (`FST x ≠ FST y`). `is_order` already orders them. Including them
  would only matter for traces that safety rules out anyway (a response
  written before its request), and it would make the statement depend on
  that argument.
- **Pending requests.** Every *complete* request is in the order, even
  one not yet answered. That costs nothing: such a request never has to
  come before anything, so it can be placed last.
- **The order is chosen per point `evs`**, not once for the infinite
  trace. This is the usual "every finite prefix is linearizable" form of
  a safety property, as in HttpSpec's `http_safe`. Each order explains
  all of `evs`, including every earlier point of it, because condition 2
  quantifies over all `evs1 ≼ evs`.

## 3. The bites (`HttpKvSpecBite`, all proved)

| theorem | trace | violates |
|---|---|---|
| `broken_loses_write` | c1: `POST /x 1`, then `GET /x` gets 404 | `kv_safe` |
| `broken_store_per_connection` | c1: `POST /x`, then `GET /y` gets 404; c2: `POST /y`, then `GET /x` gets 404 | even `kv_safe_sc`: in every order, the last GET sees both POSTs |
| `broken_stale_read` | c1's `POST /x` answered; then c2's `GET /x` read, gets 404 | `kv_safe` |
| `stale_read_sc` | the same trace | satisfies `kv_safe_sc` (so only real time catches it) |
| `broken_never_answers_kv` | nothing written to a client that sent `GET /x` | `kv_live` |
| `both_trace_safe_and_live` | fair world with two clients; read c1's `POST /x 1`, read c2's `GET /x`, answer both, c2 gets `1` | satisfies `server_world`, `kv_safe` and `kv_live` |

Tools for checking traces by hand:
- `parse_unique`: what has been read splits in exactly one way.
- `orders_two`: with two connections, the orders are exactly the
  shuffles of the two connections' request lists, so a bite can check
  each order.

## 4. Feasibility: shared state in our model

**Today** (see notes 18, 20, 23, 25):
- A computation is a pure function of its history. The server is
  `server_with h lfd`, which spawns each handler with `both (h fd) (rest)`.
- Each handler's state (its buffer) lives only in its own recursion.
- Responses are a pure function, `print_response (handle files req)`,
  computed in the round in which the request first parses.
- Safety is per connection (`http_handler_serves`), carried to the
  server by `server_with_isolates`. Nothing is shared except the
  constant `files`.

The options for a shared store:

**(A) The store is part of the world, reached by an action.**
**Recommended.**
- Add an action `Kv req` whose response is the answer.
- The handler, on a complete request, emits `Kv req`. It then writes
  `print_response` of the answer it gets back.
- The CakeML event loop performs `Kv` actions in its existing `perform`
  step, in order, on one ref holding the store (a CakeML `ref` to an
  association list or map). This is verified CakeML, not a new FFI.
- No new combinator, and no change to the semantics. Handlers stay
  per-connection and pure. Only the action vocabulary grows, and the
  response type gains an answer case.
- **The linearization point is when the loop performs `Kv`.** That is
  one total order over all connections, by round and then by position
  in the round's action list.
- **Why real time holds:** suppose x's response was fully written before
  y's first byte was read. x's `Kv` was performed before x's write.
  y's `Kv` can only be performed after y is fully read, which is after
  its first byte. So x's `Kv` comes first.

**(B) A store computation that handlers send messages to.** This needs
communication between computations, which `both` doesn't have (the two
sides only share the ready set). It would be a **genuinely new
combinator**, with new metatheory (`par_views` splitting, `wf`, the CF
`both`). I don't recommend it.

**(C) Thread the store through the scheduler** (a state-passing `both`).
This is a **change to the model's semantics**: a computation would no
longer be a pure function of its own history. All Level 1 and Level 2
lemmas would need revisiting. I don't recommend it.

(A) is the most proof-friendly: everything per-connection carries over.

**The proof plan under (A):**
1. **Handler, per connection.** `http_handler_serves` becomes "written ≼
   the printed answers to the `Kv` actions so far, and the `Kv` requests
   are the parsed requests, in order". This is a mechanical adaptation:
   one more round per request (machine `HA → HK → HB`).
2. **Store, global, new.** In the closed loop, the sequence of all
   performed `Kv` actions, with their responses, is `kv_run` of that
   sequence. This is an invariant of the CakeML loop (the ref holds
   `kv_run`'s final store), proved once in CF with a `REF` in the loop's
   frame. Today all specs use `emp`, so this is the first heap state in
   the loop. It is routine CF work.
3. **Gluing, hardest.** Build the order from the global `Kv` sequence:
   - Its projection to connection `c` is `rss c` restricted to the
     handled requests, by (1) and `server_with_isolates`. The complete
     but unhandled requests go last.
   - The answers agree, by (2).
   - **Real time** needs a *timestamped* version of the trace bridge
     `gen_rounds_bytes` (http-safety, `asyncRunOkGen`): the I/O events
     of round t sit between those of rounds t-1 and t+1, so "x's `Kv`
     happened before evs1" can be read off the trace.

   That timestamped bridge is the lemma I expect to be hardest. The
   existing bridge only relates the trace's bytes per connection, not
   positions across connections.
4. **Liveness.** A `Kv` action never waits; it is answered in the round
   it is emitted. So `hmachine_live`'s bound becomes about 3K+2 rounds
   instead of 2K+2, and the rest of the liveness chain is unchanged.

**Estimate:**

| step | time |
|---|---|
| (1) handler + per-connection safety | 1–2 days |
| (2) loop + REF + store invariant | 2 days |
| (3) order construction + timestamped bridge | 3–5 days (the risk) |
| (4) liveness | 1–2 days |
| assembly into `kv_spec` | 1–2 days |
| **total** | **about 2 weeks** |

No new combinator or semantics change is needed with (A).

## 5. Decision: shared state as a pure effect handler (`with_store`)

Approved by the user (2026-10-15). This replaces §4's (A), "the loop
performs Kv on a ref".

**What it is.** `with_store δ s0 m` (`http-kv/asyncWithStore`) is a library
combinator.
- Its argument `m` may emit `Sock a` (socket actions) and `Kv q`
  (queries).
- `with_store` emits only `m`'s `Sock` actions.
- It answers `m`'s queries itself, on a store that starts as `s0` and is
  updated by `δ`. A round's queries are answered in the next snapshot, at
  their positions among the round's results, exactly as the world answers
  socket actions.

It is an ordinary computation, a function of its history. The history `m`
sees (`inner_hist`) is the outer history with the store's answers merged
in. In CakeML (`asyncKvProg`), the store is an argument of the residual's
closure, passed on round by round. There are no refs, and every spec stays
`emp`.

**Why, rather than the loop performing Kv on a ref (or as a loop
argument).** Everything from M3 down is reused unchanged:
- M3/M4 speak a socket vocabulary in which each action is exactly one FFI
  socket call: `sact`, `sock_do`, `act_event`, `grounds`, `asyncM4SockInv`,
  the loop's `perform`/`run_i` and their specs.
- The trace bridge (`asyncRunOkGen`'s `gen_rounds_bytes`/`gen_fresh`) is
  generic in the computation.
- A Kv action performed by the loop is no socket call and produces no FFI
  event. So it would have needed a variant of every one of those
  theories, several thousand lines, whether the store sat in a ref or in a
  loop argument.

With `with_store`, the program still only emits socket actions. `both`,
`server_with` and the per-connection handlers are unchanged in kind:
`server_with_k` is `server_with` with Sock/Kv tags.

**How it differs from §4's rejected (B)** ("a store computation that
handlers message"). (B) needs communication between two computations
running under `both`, which `both` does not have. `with_store` is not a
second computation running beside the handlers. It is a wrapper around
the whole server: an effect handler for one kind of action, in the
algebraic-effects sense. No new kind of composition is needed.

**The linearization point** is the model round in which `with_store`
answers a query. The global order of all queries is the order in which it
answered them (`kv_answers`: every answer is the store's answer at its
position in that order).

**MAIN lemmas of `with_store`** (`asyncWithStore`, `asyncWithStoreStep`):

| lemma | says |
|---|---|
| `wf_with_store` | preserves well-formedness |
| `with_store_agree`, `nonexpansive_with_store` | preserves the guardedness bookkeeping of `fix` |
| `new_actions_with_store` | each round, emits `m`'s Sock actions |
| `trans_with_store` | its transcript is `m`'s on the inner history, without the Kv entries |
| `kv_answers` | every answer `m` got is `run_store δ s0` over all queries, at its position |
| `with_store_suspended` | polled once, it is `with_store` of `m` polled once, on the store after the round's queries (what the CakeML code does) |
| `relabel_with_store` | relabelling commutes with it |

**The order construction** (`asyncKvSafe`'s `kv_comp_safe`, with
`asyncKvOrder`/`asyncKvLabel`) is as planned in §4:
- A query first answered in round k commits at the start of round k's
  events.
- A complete request not queried yet commits at the end of the point
  `evs`.
- Commit points give real time (`commits_at_real_time`).

The "timestamped bridge" turned out not to need a new trace lemma. It
uses the existing `gen_rounds_bytes` at every round k ≤ n, together with
`kv_server_serves` (the per-connection invariant) at every history `TAKE
k`.

## Assumptions made

1. The store starts empty. Keys are paths. GET ignores any body. POST
   answers 200 with an empty body.
2. Real time is measured from the first byte read to the last byte
   written (§2). The fully-read variant is a one-line alternative.
3. Liveness counts whole responses (`LENGTH ans = LENGTH rs`), not their
   content. Safety fixes the content.
4. Methods other than GET and POST stay invalid, as in HttpSpecBodies.
