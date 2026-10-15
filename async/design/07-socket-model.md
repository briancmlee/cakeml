# 07: A socket world model for CakeML (for M4, the concurrent echo server)

Branch `spike/socket-model`, stacked on `spike/ffi-integration` (PR #4).
Code: `async/ffi-spike/ffiSpikeSocket*`, `ffiSpikeDivMain`. Same modular
route as the clock (04-ffi-integration.md): a new FFI part plus our own
composed world. Nothing in `basis_ffi`, the clock spike or the base was
edited. (Two clock-spike lemmas are reused, and three `[local]` lemmas of
this branch were made public.) Full `Holmake -j1` is green with no cheats
(about 1 min for the socket theories on top of the prebuilt base).

## Summary

| item of the brief | status | where |
|---|---|---|
| 1. HOL model (byte streams, listeners, schedule; honest reads; full writes) | done | `ffiSpikeSocketFFI` |
| 2. FFI functions on byte arrays, encodings, `ffi_part`, `SOCKETS` | done | `ffiSpikeSocketFFI`, `ffiSpikeSocketProof` |
| 3. Fairness assumptions, named, plus non-vacuity | done (one assumption, liveness as lemmas) | `ffiSpikeSocketFair` |
| 4. CakeML `Socket` module with CF specs | done (4 specs) | `ffiSpikeSocketProg`, `ffiSpikeSocketProof` |
| 5. Composed world cl+fs+clock+sockets, whole-program theorem | done: terminating **and** diverging | `ffiSpikeSocketWorld`, `ffiSpikeDivMain` |
| 6. Tiny example, end to end | done: one-shot echo (terminating), and a never-ending poll loop (sockets-only world) | `ffiSpikeSocketExample`, `ffiSpikeSocketDiv` |
| 7. This write-up | done | |

Main gap: the diverging whole-program theorem of the *composed* world has
no instance yet. cfDiv's loop rules only work in a single-part world (see
Gaps).

## 1. The model (`ffiSpikeSocketFFI`)

```
arrival = Connect word64 word64      (* Connect l c: connection c pending on listener l *)
        | Data word64 (word8 list)   (* bytes arrive on connection c *)
        | Eof word64                 (* the peer of c closes its side *)

conn    = <| incoming : word8 list; peer_closed : bool; outgoing : word8 list |>
sockets = <| listeners : (word64 # word64 list) list     (* fd, pending queue *)
           ; conns     : (word64 # conn) list
           ; sched     : arrival list llist |>            (* the future *)
```

- **fds** are `word64`, so they always fit the 8-byte encoding. No
  `< 2^64` side conditions are needed, unlike the clock's `clock_fits`.
- **Connections** are abstract byte streams. `incoming` holds the bytes
  that have arrived but not been read. `peer_closed` means EOF comes after
  them. `outgoing` logs everything written. That log is what the peer
  sees, and the echo example's theorem is stated on it.
- **Listening fds** have a FIFO of pending connections.
- **The schedule** is an arbitrary lazy list of *steps*, each a list of
  arrivals. It plays the role of fsFFI's `numchars` or the clock's
  readings. Theorems quantify over it.
- **Time is the schedule, advanced by polls.** `tick s` delivers the next
  step (`deliver = FOLDL deliver1`). After a finite schedule ends, nothing
  more arrives. Only the readiness call advances time. This matches §10
  of 01-semantics.md, where one snapshot is one round.
- An arrival that makes no sense in the current state is **dropped** by
  `deliver1`: data for an unknown fd, data after EOF, or a connection on a
  non-listener or reusing an fd. The assumption `sched_wf` excludes such
  schedules (§3).

Operations on the model's own types (`NONE` means misuse, an fd of the
wrong kind, and the FFI call then fails):

| operation | result |
|---|---|
| `sock_poll fds s` | `(FILTER (is_ready (tick s)) fds, tick s)`: one round, then the ready fds |
| `sock_accept l s` | `SOME (SOME c, s')` (oldest pending), `SOME (NONE, s)` (would block) |
| `sock_read c n s` | `SOME (SOME data, s')` (≤ n bytes, non-empty), `SOME (SOME [], s)` (EOF), `SOME (NONE, s)` (would block) |
| `sock_write c bs s` | `SOME s'`: `bs` appended to `outgoing` (always in full) |

`is_ready s fd` holds for a listener with a pending connection, or a
connection with unread bytes or EOF. Unknown fds are never ready.

**Byte level.** These are four FFI names. Each FFI function returns a
buffer of the length it got (`ffi_sock_length`) and never diverges
(`ffi_sock_not_diverge`).

| name | `conf` | buffer in → out |
|---|---|---|
| `sock_poll` | fds, 8 bytes each | k bytes → one flag per fd (1 ready / 0 not) |
| `sock_accept` | listener (8) | 9 bytes → `1 :: fd` or `0 :: _` |
| `sock_read` | connection (8) | 9+n bytes, n > 0 → `0 :: count(8) ++ data ++ _`, `1 :: _` (block), `2 :: _` (EOF) |
| `sock_write` | connection (8) ++ data | unused |

**FFI part.** `sockets_ffi_part = (sockets_encode, sockets_decode, [4
names])`. The encoding puts the finite part in `Cons`/`List`/`Num` (via
`encode_list`/`encode_pair`). The schedule becomes a `Stream` of numbers,
one per step, by an explicit Cantor-style encoding (`arrival_num`,
`step_num` with `npair`/`nlist_of`) that has a left inverse. So
injectivity is a short proof. `SOCKETS s = IOx sockets_ffi_part s`
(`ffiSpikeSocketProof`).

## 2. The Socket module and its CF specs (`ffiSpikeSocketProg`, `ffiSpikeSocketProof`)

```
Socket.poll   : int list -> int list          (the ready fds among the given)
Socket.accept : int -> int option              (NONE: would block)
Socket.read   : int -> int -> string option    (≤ n bytes; SOME "": EOF; NONE: would block)
Socket.write  : int -> string -> unit
```
Each is a single FFI call. All marshalling is done by pure HOL functions
translated into CakeML (`fd_conf`, `fds_conf`, `ready_of`,
`decode_accept`, `decode_read`), so their specs come from the translator.
Specs, generic in `p:'ffi ffi_proj` like the basis specs:

```
Socket_poll_spec:   LIST_TYPE NUM (MAP w2n fds) fdsv ⇒
  app p Socket_poll_v [fdsv] (SOCKETS s)
    (POSTv v. &LIST_TYPE NUM (MAP w2n (FST (sock_poll fds s))) v * SOCKETS (SND (sock_poll fds s)))
Socket_accept_spec: NUM (w2n l) lv ∧ sock_accept l s = SOME (r, s') ⇒
  app p Socket_accept_v [lv] (SOCKETS s) (POSTv v. &OPTION_TYPE NUM (OPTION_MAP w2n r) v * SOCKETS s')
Socket_read_spec:   NUM (w2n c) cv ∧ NUM n nv ∧ 0 < n ∧ n < 256 ** 8 ∧ sock_read c n s = SOME (r, s') ⇒
  app p Socket_read_v [cv; nv] (SOCKETS s)
    (POSTv v. &OPTION_TYPE STRING_TYPE (OPTION_MAP (λd. implode (MAP (CHR o w2n) d)) r) v * SOCKETS s')
Socket_write_spec:  NUM (w2n c) cv ∧ STRING_TYPE str sv ∧
                    sock_write c (MAP (n2w o ORD) (explode str)) s = SOME s' ⇒
  app p Socket_write_v [cv; sv] (SOCKETS s) (POSTv v. &UNIT_TYPE () v * SOCKETS s')
```

## 3. Assumptions on the schedule ("fairness") (`ffiSpikeSocketFair`)

**There is one named assumption, `sched_wf`.**

```
arrival_ok s (Connect l c) ⇔ is_listener s l ∧ ¬is_listener s c ∧ ¬is_conn s c
arrival_ok s (Data c bs)   ⇔ ∃cn. ALOOKUP s.conns c = SOME cn ∧ ¬cn.peer_closed
arrival_ok s (Eof c)       ⇔ (same)
step_ok s as               : every arrival of the step is ok when it is delivered
ticks n s                  : the world left alone for n rounds
sched_wf s ⇔ ∀n. step_ok (ticks n s) (next_step (ticks n s))
```
In words, the world never drops an arrival.

**Why the liveness facts are lemmas, not assumptions.** In this model an
arrival is delivered at the first poll after it is scheduled. A network
delay is just a later position in the schedule, and data that is never
delivered is, to the program, data never sent. So the two liveness
properties in the brief are **lemmas** under `sched_wf`:

- `tick_ready` (one round): whatever arrives in the next step (data, EOF,
  or a connection on listener l) makes its fd ready after the next poll.
- `ticks_ready` ("data sent eventually becomes readable", "pending
  connections are eventually acceptable"): left alone, an arrival
  scheduled for round k is ready after every round m > k.
- `tick_ready_mono`, §9's `readiness_honest`: a ready fd stays ready
  across rounds until it is read.
- `ready_read_not_block`, `ready_accept`: on a ready fd, read does not
  block and accept returns a connection.
- `sched_wf_preserved`: the assumption survives all four operations. The
  program's operations change only queues and buffers, never the "shape"
  of the world (`same_shape`, `sched_wf_shape`), so it holds for as long
  as the program runs.

**Non-vacuity.**
- `hello_world_sched_wf`: a world with listener 3 where, in round 1,
  connection 4 arrives with "hi\n" and then EOF, satisfies `sched_wf`.
- `quiet_sched_wf`: every world in which nothing ever arrives (for
  example an infinite schedule of empty steps) satisfies it.

**If a weaker world is wanted** (for the user to decide), the alternative
is a model that separates *sent* from *delivered*. Each connection would
carry the peer's whole stream, and the schedule would only say how many
bytes are delivered per round, like `numchars`. Then a real fairness
assumption is needed: "every sent byte is eventually delivered", the
analogue of fsFFI's `live_numchars`. It would cost roughly a day more, and
it only matters if we want to model partial delivery as something other
than a later arrival.

## 4. The composed world (`ffiSpikeSocketWorld`)

It is layered on the clock world exactly as the clock world is layered on
`basis_ffi`. The state is `((cl,fs),clk), sk`. The oracle sends the four
socket names to the socket part and everything else to
`clock_world_oracle`. The projections are `clock_proj1 cst |++ mk_proj1
sockets_ffi_part sk` and `clock_proj2 ++ [mk_proj2 sockets_ffi_part]`.
`parts_ok_socket_world_ffi` reuses the clock world's `parts_ok` lemmas.
The "clock view" of a run (socket events filtered out) is a run of the
clock world, so the file system is still replayed by basis_ffi's
`extract_fs` (`socket_world_extract`).

**Terminating** (MAIN `socket_whole_prog_spec_semantics`). Suppose main
satisfies
```
app (socket_proj1, socket_proj2) main_v [()]
  (COMMANDLINE cl * STDIO fs * CLOCK clk * SOCKETS sk)
  (POSTv uv. &UNIT_TYPE () uv * (STDIO fs' * SOCKETS sk'))   ∧ post (fs' with numchars := fs.numchars) sk'
```
Then the whole program terminates with `io_events`.
`socket_extract_fs cl fs io_events = SOME fs'`, and there is an FFI state
`ffi'` with `call_FFI_rel^* (socket_world_ffi cl fs clk sk) ffi'`,
`ffi'.io_events = io_events` and `post fs' (SND ffi'.ffi_state)`.

**Diverging** (MAIN `socket_whole_prog_div_spec_semantics`). If `app ...
main_v [()] (COMMANDLINE cl * STDIO fs * CLOCK clk * SOCKETS sk) ($POSTd
Q)`, then the whole program diverges with an infinite trace `io` such
that `Q io`. This rests on a new, world-independent lemma
`call_main_thm_div` (`ffiSpikeDivMain`, 255 lines), the `POSTd` analogue
of cfMain's `call_main_thm2`. It is a candidate for upstreaming, together
with its helper `evaluate_dec_list_add_to_clock_io_events_mono`.

`ffiSpikeSocketWorldLib.prove_sem_thm` is the clock's version with one
more argument.

## 5. Examples

**One-shot echo** (`ffiSpikeSocketExample`, MAIN `echo_example_semantics`):
```
fun main u = let val ready = Socket.poll [3] in
  case Socket.accept 3 of
    Some c => (case Socket.read c 100 of Some s => Socket.write c s | None => ())
  | None => () end
```
Take a world where, in round 1, connection c ≠ 3 arrives on listener 3
with 1–100 bytes `bs`. Then the whole program terminates successfully,
the file system is unchanged, and the run ends with
`ALOOKUP (SND ffi'.ffi_state).conns c = SOME <| incoming := []; peer_closed
:= F; outgoing := bs |>`, i.e. exactly `bs` was echoed.

**Never-ending loop** (`ffiSpikeSocketDiv`, MAIN `serve_semantics`):
```
fun tick3 u = let val r = Socket.poll [3] in () end
fun serve u = serve (tick3 u)
```
In a sockets-only world, the whole program diverges, and its trace is
exactly `LGENLIST (λi. poll_event [3w] (ticks i sk)) NONE`, i.e. poll i
reports the readiness of listener 3 after i+1 rounds. It goes through
cfDiv's `IMP_app_POSTd_one_FFI_part_FLATTEN` (as in cf-spike's
`run_spec`), an events-exposing poll spec `Socket_poll_spec_ev`, and
`call_main_thm_div`.

## 6. Gaps

1. **Divergence in the composed world.** cfDiv's FFI-part loop rules
   (`repeat_POSTd_one_FFI_part*`) require `limited_parts ns p`, i.e. a
   world with a single FFI part. A server in the composed world (which
   logs to stdout, say) therefore cannot yet prove its `POSTd` spec. The
   whole-program theorem for that case exists, but there is no instance.
   **Needed:** a multi-part variant of `repeat_POSTd_one_FFI_part_FLATTEN`.
   It would track one part's events while the other parts are framed and
   their events are filtered out of the trace. Estimate: 300–600 lines in
   cfDiv's style, 1–2 weeks supervised. The alternative used here, a
   sockets-only world, needs no CF work but cannot print.
2. **Not modelled:** errors beyond EOF, partial writes, `close`, the
   accepted/not-accepted distinction (a pending connection's data could be
   read before `accept`; harmless, as programs learn fds from accept),
   readiness for writing, timeouts in poll (poll never blocks; a busy loop
   is the program's choice), and the clock interacting with sockets (the
   clock is a separate schedule).
3. **The final socket state** is stated via `call_FFI_rel^*` to an FFI
   state with the run's events, not via a replay function as the file
   system is (`extract_fs`). The oracle is deterministic, so it is
   determined. A `socket_replay` function plus lemma is ~60 lines.
4. **No liveness theorem about a program** yet. The world lemmas are
   there (`ticks_ready`, `sched_wf_preserved`), but "the echo server
   eventually echoes every line" belongs to M4, and it needs the
   async library's loop on top of this world.
5. Compiler correctness was not instantiated for the new oracle (as in
   the clock spike, and as in basis's examples at this level).

## 7. Connecting to the async library's emitted actions (spike/cf-actions)

`spike/cf-actions` builds the action-performing event loop against a
self-contained, oblivious one-part world: names `act` and `ready` over one
byte stream. Each round performs the round's actions (one `act` call
each), then reads one ready byte, then polls the computation with the
snapshot `<| ready; now; results |>`. Its MAIN `run_spec` gives the trace
as `LFLATTEN` of per-round events. That is the same cfDiv rule as
`serve_spec` here, so the socket part fits its loop as follows:

- **Actions → Socket calls.** `Read fd`, `Write fd bs` and `Accept l`
  become `Socket.read`, `Socket.write` and `Socket.accept`. Each action's
  response is the call's result: data / would-block / EOF, unit, or new
  fd / would-block. This is §10's `one_response_per_action`, and it holds
  by construction (one call per action, in order).
- **`ready` → `Socket.poll`.** The snapshot's `ready` set is
  `Socket.poll` on the fds that the round's waits mention, and the poll
  also advances the world one round. `now` would come from `Clock.now`.
  In the composed world that is cheap, but it brings back gap 1, since
  the clock is another part. A sockets-only world needs `now` from
  elsewhere, e.g. the round number, as in §10's non-vacuity world.
- **The world.** cf-actions' `IOS ws evs` (stream plus events) is
  replaced by `SOCKETS_EV s evs` (`ffiSpikeSocketDiv`). Its "next byte"
  lemma is replaced by the four model operations, and its per-round
  events by the actual calls' events. The trace lemma
  (`trace_actions_rounds`) would say that the trace's actions are the
  model's action log after the snapshots `(sock_poll ...)` that the
  socket world produces.
- **What changes in their proofs.** Mostly the world-facing specs
  (`do_act_spec`, `get_ready_spec`) and the invariant `ss i`, which
  becomes `sockets_encode` of the world after round i's actions. The
  model-level (`STEPA`/`COMP`) specs are unaffected.
- **Assumptions.** Their oblivious world needs none. With sockets, a
  liveness theorem about the echo server will assume `sched_wf`, plus a
  client-side assumption such as "each connection eventually sends a
  newline or EOF". That one is about the client, not the network.

## 8. Estimates

- M4's world part is done here.
- Plugging the socket part into the cf-actions loop (sockets-only world):
  ~400–700 lines (world-facing specs, the round invariant, the trace
  lemma with real responses). That is 3–6 days supervised, depending on
  how the action encoding is fixed.
- Gap 1 (multi-part divergence, so the server can also log and use the
  clock): 1–2 weeks supervised.
- An echo-server liveness theorem on top: 1–2 weeks. The world lemmas
  exist; the work is the model-level argument plus connecting it to the
  trace.
- This spike: 9 theories, ~2.7 kLOC including comments. Wall clock from
  the commit log: start 10:12; model + module + specs 10:37; assumptions
  10:40; composed world 10:50; echo example 10:56; diverging example
  11:05; write-up and PR after that. The forked `call_main_thm_div` took
  13 minutes, in parallel. Check-waiting: 7 Holmake runs of 30–60 s,
  plus hol-lsp diagnostics of 10–120 s per edit.

## Assumptions made

1. Time = the schedule, advanced only by `sock_poll` (one step per poll).
   `accept`/`read`/`write` don't advance it, and `poll` never blocks.
2. fds are `word64`. The CakeML side uses `int`, with `NUM (w2n fd)`.
3. Misuse (an fd of the wrong kind for accept/read/write, a malformed
   buffer) makes the FFI call fail (`FFI_failed`). Polling an unknown fd
   reports "not ready".
4. Ill-formed arrivals are dropped by the model and excluded by
   `sched_wf`, the single schedule assumption. Liveness is by lemmas,
   since delivery happens at the next poll. The weaker sent/delivered
   model is described in §3, not built.
5. Pending connections are created as connection fds on arrival, and
   there is no "accepted" flag.
6. `read` returns `min(n, available)` bytes and requires `0 < n < 2^64`.
   `write` takes the data as part of `conf`.
7. Buffer layouts as in §1 (status bytes, 8-byte big-endian counts and
   fds).
8. The composed world is layered on the clock world (cl+fs+clock), not on
   basis_ffi directly. The final socket state is stated via
   `call_FFI_rel^*`, not replay.
9. The diverging example uses a sockets-only world (the cfDiv limitation
   in Gap 1).
10. Three lemmas were made public (`CHR_o_w2n`, `ALOOKUP_MAP_const`,
    `FUPDATE_LIST_same_keys`). Four lazy-list lemmas were copied from
    cf-spike's `asyncCfSnap`.
11. Names are prefixed `ffiSpike`/`ffiSpikeSocket`, as in the clock spike.
