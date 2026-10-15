# 19: M4 liveness: the verified echo program satisfies EchoSpec's `echo_live`, and so all of `echo_spec`

Status: **done.** No cheats; `Holmake -j2` green in `async/m4-liveness/` and
`async/m4-echospec-live/`. Branch `spike/m4-liveness`, stacked on
`spike/async-closed-loop` (PR #19). Merged in, unedited:
`origin/spike/final-spec` (EchoSpec), `origin/spike/m3-assembly`,
`origin/spike/m4-server` and `origin/spike/m4-safety` (which brings
spike/runnable's `echo_prog` and spike/machine-code's `echo_semantics_prog`).
EchoSpec's definitions are untouched.

## 1. The result

```
(* MAIN: the verified echo program meets EchoSpec on listener 3w: in every
   server world it runs forever, never writes on a connection more than it
   has read from it, and eventually echoes everything every client sends *)
Theorem echo_prog_spec:
  echo_spec 3w echo_prog
```

(`async/m4-echospec-live/asyncM4EchoSpec`). The statement is EchoSpec's
`echo_spec` applied to the program; nothing else. Unfolded:

```
∀sk. server_world 3w sk ⇒      (* one listener 3w, nothing pending, no
                                  connections, sched_wf *)
  ∃io. semantics_prog (init_state (socket_ffi sk)) init_env echo_prog (Diverge io) ∧
       echo_safe io ∧
       echo_live sk io          (* ∀c n. ∃evs. LPREFIX (fromList evs) io ∧
                                     sent_upto c n sk ≼ bytes_written_to c evs *)
```

The proof is three lines. `echo_semantics_prog` (machine-code) gives
divergence with io = `echo_trace sk`, the event loop's run, and `echo_safe`;
`echo_live_rounds` (this branch) gives `echo_live sk (echo_trace sk)`.

## 2. The program: a dynamic-interest loop

M3's loop polls a **fixed** list of fds, so it never polls a connection
accepted later, and a program built on it would violate `echo_live`. M4
uses `run_i` (`async/m4-common/asyncM4Loop`, mine). Round n polls the initial
fds plus every connection an accept has returned so far:

```
interest fds0 h = FOLDL add_accepted fds0 (results of h)
```

`run_i_spec` is M3's `run_spec` for the history `grounds (interest fds0) m s0`.
`interest_accepted` says the listener, and every connection handed out by
round n, are polled in round n.

## 3. The chain

| step | theorem | file |
|---|---|---|
| the world consumes one schedule step per round; `sent_upto` round by round | `grounds_arrivals`, `sent_upto_SUC` | asyncM4Sched |
| `sched_wf` holds throughout, so every arrival is effective (`arrival_ok`) | `grounds_sched_wf`, `grounds_step_ok` | asyncM4Sched |
| per connection: sent = read ++ unread; outgoing = written | `grounds_acct` | asyncM4Account |
| the model server's view of the run is prompt; what is polled | `prompt_ghist`, `ready_EL_ghist`, `interest_accepted` | asyncM4LiveProg |
| unread data only grows until c is read; EOF is final | `quiet_rounds_s`, `grounds_eof` | asyncM4LiveWorld |
| an accepted connection with unread data is read within rounds n..n+3 | `read_soon_s` | asyncM4ReadSoon |
| everything sent by round k is eventually read (bounded reads); then written back | `drain`, `accepted_live` | asyncM4Drain |
| every connection is handed out or pending; a pending one moves forward per accept | `grounds_known`, `round_queued` | asyncM4Queue |
| while connections are pending, the server accepts within two rounds | `accept_soon_s` | asyncM4AcceptSoon |
| every connection is eventually handed out | `queue_progress`, `conn_accepted` | asyncM4AcceptSoon |
| everything sent by step n is written back within finitely many rounds | `echo_comp_live` | asyncM4EchoLive |
| `echo_live` for the run's I/O | `echo_live_rounds` | asyncM4EchoLive |
| **`echo_spec 3w echo_prog`** | `echo_prog_spec` | m4-echospec-live/asyncM4EchoSpec |

The program-level progress facts are the closed-loop model's
(`asyncProgress`: `handler_progress` via `server_handler_view`, and
`server_accept_progress`). They are transported to the socket world through
m4-safety's relabelling (`echo_trans_split`, `TREL_*`, `accepted_TS`).

## 4. The schedule (EchoSpec's world vs the loop's)

EchoSpec states liveness against the **initial** world's schedule:
`sent_upto c n sk` is what c's client sends in the first n steps. The loop
lets exactly one step arrive per round, in its poll, and the socket
operations never touch the schedule. So round n's arrivals are step n
(`sent_upto_SUC`). `sched_wf` is preserved by the socket operations and by
`tick` (the socket worker's `sched_wf_preserved`, `sched_wf_tick`), so every
step of the run is `step_ok`: no arrival is dropped (`grounds_step_ok`).
This is what makes `sent_upto` equal the data that actually reached the
world (`grounds_acct`).

## 5. Bounds (they depend on the backlog)

`echo_live` is purely existential, and so are the proofs. The bounds inside
them are:

- a connection pending at position k in the listener's queue is handed out
  within about 3(k+1) rounds (each accept moves it one place; while it is
  pending, the server accepts within two rounds);
- an accepted connection with unread data is read within four rounds;
  each read takes at most `bufsz` bytes, so draining d bytes takes about
  4·⌈d/bufsz⌉ rounds;
- what is read is written back in the same round (`echo_rounds_written_read`).

These depend on the backlog (queue position, bytes outstanding). This
matches the closed-loop model's `closed_loop_liveness` (n + 3q + 5) and
was agreed with the coordinator.

## 6. Assumptions and decisions

- `echo_prog`, `echo_semantics_prog`, `echo_prog_safe`'s pieces are adopted
  from runnable/machine-code/m4-safety unchanged.
- The listener number in the liveness lemmas is any `lfdn < dimword (:64)`
  (needed so that `w2n (n2w lfdn) = lfdn`); the program uses 3.
- `echo_prog_spec` lives in its own directory, `async/m4-echospec-live/`,
  so that no other worker's directory is edited. Its Holmakefile includes
  `runnable` and `machine-code`, so its first build compiles those
  theories.
- Shared lemmas: `asyncM4Loop` (m4-common) is mine; everything else in
  m4-common is m4-safety's. The liveness files are all in
  `async/m4-liveness/`.
