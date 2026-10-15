# 25: HTTP liveness in the model: requests that arrive are answered

Status: **done (model level).** No cheats; `Holmake -j2` is green in
`async/http-liveness/`. Branch `spike/http-liveness`, stacked on
`spike/http-impl`. It merges `spike/async-closed-loop` (the closed-loop
world model and the echo server's liveness, 09). No merged files were edited.

This is the counterpart, for the buffering HTTP handler (18), of the
echo server's closed-loop liveness (09, `closed_loop_echo_accepted`). The
difficulty is that the HTTP handler buffers. A request may arrive in pieces,
and the handler answers only once a request is complete. So the statement
is about the *complete requests* in what has arrived, not about bytes.

## 1. The result

```
(* MAIN *)
Theorem closed_loop_http_accepted:
  closed_loop (http_server files lfd) (start_world lfd sch) n = (h, w, perf) ∧
  ALOOKUP w.conns c = SOME cn ∧ MEM c (accepted (sperf perf)) ∧
  n + 2 * LENGTH (parse_all cn.received) + 3 ≤ N ∧
  closed_loop (http_server files lfd) (start_world lfd sch) N = (hN, wN, pN) ⇒
  ∃cnN. ALOOKUP wN.conns c = SOME cnN ∧
        FLAT (responses_to files cn.received) ≼ cnN.outgoing
```

Suppose that by round n the server has accepted connection c and the data
D = `cn.received` has arrived on it. Let K be the number of complete
requests at the front of D (`parse_all D`). Then from round n + 2K + 3 on,
the responses to those K requests, in order, are a prefix of everything
written to c. As in 09, there is no assumption beyond the world model.
The schedule `sch` is arbitrary, and D may have arrived in any number of
pieces.

The same result, in HttpSpec's terms (requests `rs` followed by anything):

```
(* MAIN *)
Theorem closed_loop_http_requests:
  ... ∧ cn.received = FLAT (MAP print_request rs) ++ rest ∧ EVERY valid_request rs ∧
  n + 2 * LENGTH (parse_all cn.received) + 3 ≤ N ∧ ... ⇒
  ∃cnN. ALOOKUP wN.conns c = SOME cnN ∧
        FLAT (MAP (print_response o handle files) rs) ≼ cnN.outgoing
```

With 18's safety (`http_server_safety`: what is written is a prefix of
the responses to what has been read), this means that on an accepted
connection the server writes exactly the responses to the complete
requests, eventually all of them, and nothing else.

## 2. The chain

| step | theorem | file |
|---|---|---|
| a handler's own view of the generic server `server_with hf` | `sw_handler_view` (per-prefix transcript equality) | asyncSWProgress |
| closed-loop facts for `server_with hf` (09's, generalised) | `sw_consistent`, `sw_fresh`, `sw_round_conn`, `sw_eof`, `sw_received_later` | asyncSWClosedLoop |
| the handler as a three-state machine | `hmachine_trans`, `hmachine_inv` | asyncHttpMachine |
| **machine-level liveness, given four environment facts** | `hmachine_live` | asyncHttpDrain |
| the handler's view in the closed loop | `sw_closed_loop_view`, `http_view` | asyncHttpLiveness |
| **closed-loop liveness** | `closed_loop_http_accepted`, `closed_loop_http_requests` | asyncHttpLiveness |

### 2.1 The handler as a machine (asyncHttpMachine)

Between rounds, the handler of fd is in one of three states. It can be
`HA b`, about to act on buffer b: answer its first request, wait for
readability, or stop on invalid input. It can be `HB b`, reading this
round. Or it can be `HD b`, stopped. `hstep` is the step for a snapshot,
and `hrun` iterates it. On a history where the world answers promptly, the
handler's transcript is the machine's (`hmachine_trans`). The accounting
invariant `hmachine_inv` says what the handler has read is
`print rs ++ hbuf st`, and what it has written is
`MAP resp rs ++ hpend st`, for the requests rs it has completed.

### 2.2 Machine-level liveness (asyncHttpDrain)

`hmachine_live` (overloads: `Sj`/`Rj`/`Wj` are the state, the data read
and the data written after j snapshots). It has four environment
hypotheses:

0. D extends what the handler has read by round j0;
1. whenever the handler waits (incomplete buffer) and fd is not reported
   readable, it has already read all of D;
2. whenever it reads, it has then read all of D;
3. whenever it stops at end-of-file, it has read all of D.

Then within 2K + 2 rounds it has written the responses to all K complete
requests of D. The rounds are: answer the requests already buffered (at
most K rounds, one response per round), wait one round for readiness, read
(one round), then answer the rest (at most K rounds). Facts used:
`hdrain` (a buffered request is answered each round), `drain_after`,
`responses_by_length` (responses are a prefix of the responses to what has
been read, so having enough of them suffices), and `responses_invalid` (an
invalid request ends what can be answered).

### 2.3 The environment facts in the closed loop (asyncHttpLiveness)

`http_view` puts c's handler on its own history g, starting at the round
a ≤ n in which c was accepted. At round a + j:

- what it has read is what the world performed (`sw_trans_read`);
- an unanswered action of its is one of the server's new actions
  (`sw_trans_none`), and an answered one was performed (`sw_trans_some`);
- what it has written is what the world holds after the round
  (`sw_trans_written`).

The world's consistency (`sw_consistent`) gives received = read ++
incoming. Hypotheses 1–3 then come from properties of the world:

1. not reported readable ⇒ nothing unread (`incoming_ready`, with
   `closed_loop_snapshot` and `g`'s ready sets matching the server's);
2. a read takes everything that has arrived (`sw_round_conn`); the
   handler's outstanding read is the server's (`hmachine_reading`);
3. end-of-file comes after all the data (`sw_eof`). A handler stopped on a
   non-invalid buffer has read end-of-file (`hmachine_stopped_eof`,
   `hmachine_eof`).

Hypothesis D ≽ (read by round n) is consistency at round n. Writes persist
(`sw_outgoing_later`).

The bound: `hmachine_live` runs the machine on rounds a + j0 = n to
n + 2K + 2. The responses written in round n + 2K + 2 are in the world
after it, so they are there by round n + 2K + 3.

## 3. Not done

- **Pending connections.** The theorem is about a connection already
  accepted by round n. For the echo server, 09's `closed_loop_liveness`
  adds the queue bound (a connection with q ahead of it is accepted within
  3(q + 1) rounds). The analogue for `server_with` needs
  `sw_accept_progress` (proved, asyncSWProgress) lifted to the closed loop,
  as 09 lifts `accept_soon`. That is mechanical but not done here.
- **The CakeML program.** This is model-level, like 09. Connecting it to
  the verified HTTP program (20, spike/http-impl) follows the M4 echo
  route (17, 19).

## 4. Assumptions made

1. **Bound shape.** I proved the bound n + 2K + 3 with K counted on all of
   D. That is simple and enough for "eventually". A tighter bound (K of the
   requests not yet answered) would need a more detailed statement.
2. **Generic server facts.** The closed-loop lemmas are proved for any
   well-behaved handler (`hok hf`: wf, settled, touches only its own fd).
   Then they are instantiated to HTTP (`hok_http`). The echo server's
   lemmas in asyncLiveness (async-spike's) are left untouched, and mine
   are separate `sw_` copies.
3. **D is `cn.received`** (everything that has arrived, the world's ghost
   field), as in 09.
