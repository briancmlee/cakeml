# 25: EchoSpec2: echo with close and fd reuse (SPEC FIRST, for your review)

Status: **statements written and typechecked; bite and non-vacuity lemmas
proved.** Reviewed: decisions 1, 3, 4, 5 approved; decision 2
generalised to any allocation policy; the closing clause added. No cheats, and `Holmake -j2` in
`async/spec/` is green. Branch `spike/echospec2`, stacked on
`spike/m4-liveness` (PR #30, which proves `echo_spec 3w echo_prog`).
EchoSpec is unchanged.

| file | role |
|---|---|
| `socket-v2/socketV2FFIScript.sml` | **trusted**: the version-2 socket world (close, lowest-free fd reuse) and its FFI functions |
| `socket-v2/socketV2FairScript.sml` | **trusted**: the assumption `sched_wf2` |
| `spec/EchoSpec2Script.sml` | **trusted**: oracle, `server_world2`, episodes, `echo_spec2` (no proofs) |
| `spec/EchoSpec2BiteScript.sml` | proved: bite per episode, the reuse bug, non-vacuity with reuse |

## 1. The statement

```
echo_spec2 lfd prog ⇔
  ∀sk. server_world2 lfd sk ⇒
       ∃io. semantics_prog (init_state (socket2_ffi sk)) init_env prog (Diverge io) ∧
            echo_safe2 io ∧ echo_live2 sk io

echo_safe2 io     ⇔ ∀evs j. LPREFIX (fromList evs) io ⇒ ep_written j evs ≼ ep_read j evs
echo_live2 sk io  ⇔ ∀j n. ∃evs. LPREFIX (fromList evs) io ∧ sent2_upto j n sk ≼ ep_written j evs
echo_closes2 io   ⇔ ∀evs j. LPREFIX (fromList evs) io ∧ ep_eof_read j evs ⇒
                            ∃evs'. LPREFIX (fromList evs') io ∧ ep_closed j evs'
```

`echo_closes2` (added after review): once the server has read the EOF of
episode j's client, it eventually closes episode j's fd. Without it, a
server that never closes (so never frees an fd) would meet the spec.

It has EchoSpec's shape, with per-fd projections replaced by per-**episode**
ones. Episode j is the life of the j-th accepted connection: from the accept
that returned its fd f to the next close of f. `ep_read j evs` and
`ep_written j evs` are EchoSpec's `bytes_read_from f` and `bytes_written_to f`
of the events in that window. The target is `echo_spec2 3w <program>`.

## 2. The world (decisions for you)

1. **Clients, not fds, in the schedule.** Arrivals are `Connect2 l`,
   `Data2 j bs`, `Eof2 j`, with clients numbered 0, 1, 2, … in order of
   connection. In version 1 the schedule picked each connection's fd in
   advance (`Connect l c`). That cannot model reuse, because which fd a
   client gets depends on what the program has closed.
2. **The kernel picks ANY free fd at accept** (revised after review).
   "In use" covers `reserved` (the process's other fds, e.g. 0, 1, 2),
   the listeners and the open connections. The choice is the world's
   allocation function `alloc j used`, and `server_world2` assumes only
   `alloc_ok` (it returns a free fd), so the theorem holds for every
   allocation policy. POSIX's rule, the lowest free fd (`lowest_free`), is
   one instance (`lowest_free_alloc_ok`). With `reserved = [0w;1w;2w]` and
   listener 3 it matches what `socket_ffi.c` sees, as long as the program
   opens no other fds. The generality costs the proof nothing: it only
   uses that the fd is free.
3. **Liveness per client.** With one listener, accept takes the oldest
   pending client, so the j-th accept serves client j. `echo_live2` says
   that client j's data is written back in episode j. The data a client
   sends after the server has closed its connection is never read; a
   server that closes before EOF therefore violates liveness, as it should.
4. **Fairness** is version 1's `sched_wf` (every arrival makes sense when it
   arrives), plus one bound: reserved + listeners + clients < 2^64, so an
   accept always finds a free fd. Version 1 has the same bound implicitly,
   since every connection takes a fresh 64-bit fd for good. It also lets the
   proof give every connection a distinct, never-reused handle.
5. `«sock_close»` takes the 8-byte fd. Closing anything but an open
   connection is a misuse, and the FFI call fails.

## 3. Bite (`EchoSpec2BiteScript.sml`)

| theorem | meaning |
|---|---|
| `broken_swaps_clients2`, `broken_drops_a_byte2`, `broken_duplicates_a_byte2`, `broken_writes_before_reading2` | EchoSpec's broken servers, per episode, violate `echo_safe2` |
| `broken_leaks_across_reuse` | **new**: reading "a" on fd 4, closing it, accepting a new client on fd 4 and writing "a" to it violates `echo_safe2` |
| `v1_misses_leak` | ... while EchoSpec's per-fd `echo_safe` holds of that trace: why EchoSpec2 projects per episode |
| `broken_never_echoes2` | never echoing violates `echo_live2` |
| `broken_never_closes` | **new**: version 1's behaviour (echo, read EOF, never close) is safe and live but violates `echo_closes2` |
| `lowest_free_alloc_ok` | POSIX's lowest-free policy is an allocation policy |
| `hello_world2_sched_wf`, `server_world2_exists` | a fair world exists: two clients, one after the other |
| `hello_world2_reuses` | in it, the kernel really reuses an fd: accept gives 4, close 4, accept gives 4 again |
| `ideal2_trace_spec` | an ideal echo trace with two episodes on fd 4 is safe, live and closes |

## 4. The plan for the proof (next branches)

1. **v2 world model, CF layer.** The `«sock_close»` FFI part (the four
   other calls on the v2 world), the CakeML `Socket.close` with its CF
   spec, and `sched_wf2` lemmas.
2. **Handle layer.** An event-loop variant that keeps a verified table
   handle ↦ current fd. Handles are never reused, and the loop closes a
   connection automatically once its read returns EOF and then drops the
   handle. The verified server is unchanged; it sees handles. The only new
   C is a plain `close(2)` in `socket_ffi.c`.
3. **Simulation.** The handle-layer loop in a v2 world produces, per
   episode, exactly the per-connection streams the version-1 loop produces
   in the version-1 world where client j's connection has fd = handle j.
   Then `echo_spec2` follows from `echo_prog_spec` without touching a
   version-1 proof.

Out of scope: HTTP's explicit close-after-response (a new Close action,
later, via an embedding).
