# The concurrent echo server, in the model

This note covers M4's core property, proved in pure HOL before any CakeML
plumbing: a concurrent echo server that gives every client back exactly
its own data, in order. The scripts are:

- `asyncServerScript.sml`: the server;
- `asyncTranscriptScript.sml`: transcripts;
- `asyncServerSafetyScript.sml`: the safety theorem;
- `asyncServer2Script.sml`: Level 2 (quiet; no busy-waiting).

All proved, with no `cheat`.

## 1. The server

```
handler fd = wait until fd is readable; read fd;
             on Data d: write d to fd, then handler fd
             on Eof:    stop
             otherwise: handler fd                      (e.g. "would block")

server lfd = wait until lfd (the listener) is readable; accept on lfd;
             on Accepted fd: both (handler fd) (server lfd)
             otherwise:      server lfd
```

Both are defined with `fix` (`handler_unfold`, `server_unfold`). Each
accepted connection's handler runs alongside the rest of the server: the
recursive call sits inside `both`. This is the "fork per connection by
recursion" pattern of `06-scheduler.md` §4, so the scheduler's pool stays
fixed (the whole server is one task).

The definition is accepted by the recursion rule: the recursive call comes
after waiting for the listener (`server_body_contractive`).

**Assumption: vocabulary.** The actions and responses of `asyncEcho`,
extended conservatively:
- the action `Accept lfd`;
- the responses `Accepted fd` (a new connection) and `NoConn` (nothing to
  accept).

`asyncServer` defines its own copies of the types, with the same
constructor names as `asyncEcho` plus these, and does not build on
`asyncEcho`.

**Well-formed and settled** (`wf_server`, `settled_server`): the server's
log only grows, and it never loses a response.

## 2. Transcripts: actions paired with their responses

To talk about "the data read from fd" we need to know which response
belongs to which action. With positional routing (semantics note §3), the
response to an action emitted in round n is in snapshot n+1, at the
action's position in round n's batch. The **transcript** pairs them:

```
zipr [] rs = []
zipr (a :: as) rs = (a, oHD rs) :: zipr as (DROP 1 rs)

trans m h = FLAT (GENLIST (λn. zipr (new_actions (log_of m) (TAKE n h))
                                    (responses_at h n)) (SUC (LENGTH h)))
```

`MAP FST (trans m h) = (m h).actions` (`MAP_FST_trans`): the transcript is
the action log, annotated with responses. Actions whose response hasn't
arrived are paired with `NONE`.

**How transcripts compose** (`asyncTranscriptScript.sml`):

- `trans_bind_continues` (MAIN): for a settled `m` that has first finished
  after `h1`,
  `trans (bind m f) (h1 ++ h2) = trans m h1 ++ trans (f x) h2`.
- `trans_both_filter_left` / `_right` (MAIN): each round, `both`'s
  transcript is the left side's pairs, then the right side's. So if one
  side's transcript has no pair satisfying `Q`, filtering `both`'s
  transcript by `Q` gives the other side's, filtered:

  ```
  FILTER Q (trans m2 (right_view m1 m2 h)) = [] ⇒
  FILTER Q (trans (both m1 m2) h) = FILTER Q (trans m1 (left_view m1 m2 h))
  ```

  This keeps connections apart: filtering by "reads or writes fd" isolates
  fd's handler.
- Primitives: `trans_wait`, `trans_return`, `trans_emit`, `trans_map`.

## 3. Safety (M4's core property)

```
written fd tr = the strings written to fd in tr, in order
read fd tr    = the strings in Data responses to reads of fd in tr, in order
accepted tr   = the connections handed out (Accepted responses to Accept)
fresh tr ⇔ ALL_DISTINCT (accepted tr)

(* MAIN *) echo_server_safety:
  fresh (trans (server lfd) h) ⇒
  ∀fd. written fd (trans (server lfd) h) = read fd (trans (server lfd) h)
```

On **every** history in which the world hands out distinct connections, and
for **every** connection fd, the data the server has written to fd is
*exactly* the data it has read from fd, in order.

**Why this formulation.**
- It is stated over the server's own transcript: its action log plus the
  responses the history delivered to those actions. That is exactly what
  the server sees and does; no extra world state is needed.
- Equality, not just "written is a prefix of read", is what the model
  gives, because `bind` continues in the same round. The write of `d` is
  emitted in the very round in which the response `Data d` arrives. So:
  - **only its own data**: everything written to fd was read from fd;
  - **never reordered**: the order of writes is the order of reads;
  - **nothing held back**: every line read from fd has been written back by
    the end of that round. This is the liveness-shaped statement the model
    can make relative to the history (§4).
- The single assumption, `fresh`, is a property of the world, visible in
  the transcript: the connections it hands out are distinct. The model has
  no `close`, so fd numbers are never reused. Without it, two handlers
  could share an fd and interleave their writes.

**How it is proved.**

- `handler_echoes`: a connection's handler only reads and writes its own
  fd, and writes back exactly what it has read. The proof is by induction
  on the history's length, unfolding the handler and using
  `trans_bind_continues`.
- `server_echoes`: the server's invariant. On every connection, written =
  read, and the server only touches connections it has accepted. Also by
  induction: after `Accepted fd`, the transcript of
  `both (handler fd) (server lfd)`, filtered to fd, is the handler's
  (the rest of the server never touches fd: it only touches connections it
  accepted itself, which by `fresh` are not fd). Filtered to any other fd,
  it is the rest of the server's.

**EVAL check: two clients** (`example_two_clients_*`). Client 5 connects
and sends "hi". While it is being served, client 6 connects and sends "yo".

```
(server 0 two_clients).actions =
  [Accept 0; Read 5; Accept 0; Write 5 "hi"; Read 6; Write 6 "yo"]

trans (server 0) two_clients =
  [(Accept 0, SOME (Accepted 5)); (Read 5, SOME (Data "hi"));
   (Accept 0, SOME (Accepted 6)); (Write 5 "hi", SOME Written);
   (Read 6, SOME (Data "yo")); (Write 6 "yo", NONE)]

written 5 … = read 5 … = ["hi"],   written 6 … = read 6 … = ["yo"]
```

## 4. What the model can say about liveness

Relative to a history, `echo_server_safety` already says that **every line
received is echoed in the same round**: the equality includes the lines
whose `Data` response is in the last snapshot.

What the model cannot say on its own is that lines *will* be received, or
that writes complete. That needs assumptions about the world, which are
M3/M4 material (semantics note §10):

- a connection with pending data is eventually reported readable, and a
  read then returns data (`data_live`);
- `one_response_per_action`;
- pending connections are eventually accepted.

Partial writes are out of scope (a `Write` either completes or the world
answers otherwise). With those assumptions, "every line a client sends is
eventually echoed" should follow from the safety equality plus progress of
the handler. That is planned for M4.

## 5. Level 2: no busy-waiting for the server

`server2` is the same server written with `wait_on`, `emit2`, `bind2`,
`both2` and `map2`:

- `erase_server2: erase (server2 lfd) = server lfd`, so the safety theorem
  holds for it;
- `wf2_server2`: well-formed and quiet;
- `server_no_busy_waiting` (MAIN): M2's `no_busy_waiting` theorem,
  instantiated. A scheduler running the server that blocks through every
  idle round emits exactly the same actions as one that polls every round.
  Idle means: no request in flight, no responses, neither the listener nor
  any connection readable.

So the select loop of the eventual implementation may block until the
listener or some connection becomes readable.

New helper lemmas: `both2_agree`, `nonexpansive2_both2`,
`nonexpansive2_map2`, `wf2_map2`, `wf2_both2`.

## 6. Assumptions, recorded for the user

1. **Vocabulary extension**: `Accept` / `Accepted` / `NoConn` (§1).
2. **Distinct connections** (`fresh`): no `close`, so no fd reuse. Adding
   `close` would need a refined statement, e.g. per connection *instance*
   rather than per fd number.
3. **Readiness of the listener** is reported as `Readable lfd`, as `select`
   does for listening sockets.
4. **One task**: the whole server is a single scheduler task that forks per
   connection with `both` (no dynamic spawn, `06-scheduler.md` §4).

## 7. What is left for M4 at the CakeML level

- The CakeML implementation of the library and of this server, and the CF
  refinement proof against the model (semantics note §11).
- The FFI world model for sockets: `accept`, readiness via `select`, reads
  and writes, with the assumptions of §4 named and shown non-vacuous.
- The whole-program theorem: the I/O trace of the CakeML server, run by
  the M3 event loop, is the transcript of `server lfd` on the history the
  world produced. `echo_server_safety` then gives the end-to-end
  guarantee.
- Liveness under the world's fairness assumptions (§4).

## 8. Proposed MAIN theorems

| Theorem | File | Meaning |
|---|---|---|
| `server_body_contractive`, `server_unfold` | asyncServer | the server is well-defined |
| `wf_server`, `settled_server` | asyncServer | well-formed; never loses a response |
| `trans_bind_continues` | asyncTranscript | transcripts of bind |
| `trans_both_filter_left`, `trans_both_filter_right` | asyncTranscript | transcripts of both, per filter |
| `handler_echoes` | asyncServerSafety | one connection echoes exactly its data |
| `server_echoes`, `echo_server_safety` | asyncServerSafety | **every client gets back exactly its own data, in order** |
| `erase_server2`, `wf2_server2`, `server_no_busy_waiting` | asyncServer2 | the Level 2 server is the same server, quiet, and may be run by a blocking scheduler |

Suggested headline: `echo_server_safety`.
