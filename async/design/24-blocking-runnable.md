# 24: The blocking echo server, running

Branch `spike/blocking-runnable` (PR #29), stacked on `spike/m4-blocking`
(PR #27). It merges `spike/runnable` (PR #23) and uses it read-only,
except for one addition to the trusted `socket_ffi.c` (§1). The verified
fix of §6 is on `spike/m4-blocking-live`, stacked on it.

- New directory: `async/blocking-runnable/`.
- `Holmake` there exports `echo_blocking.sexp` and (with §6)
  `echo_live.sexp`; `make` builds the four servers of §3.

**Headline status (user decision).** EchoSpec stays unchanged, and the
polling program remains the headline. `echo_blocking_spec`
(`async/m4-blocking`, 17) is the official refinement/companion theorem,
presented directly under it.

## 1. The C side of `«sock_select»` (TRUST ITEM)

`ffisock_select` is added to `async/runnable/socket_ffi.c`, with a row in
the file's mapping table. The model is `ffi_sock_select`
(`asyncM4BlkLoop`):

- **config:** k fds, 8 bytes each (`fds_bytes`, as for `sock_poll`);
- **buffer:** empty, and nothing is consumed;
- **behaviour:** block until a poll of the fds would report one ready, or
  forever if that never happens (`FFIdiverge`).

The C function calls `poll(2)` with no timeout on the fds, for
`POLLIN`, `POLLHUP` or `POLLERR` (the same readiness as `sock_poll`). It
retries on `EINTR`, and aborts on `POLLNVAL` or bad lengths, as the model
rejects those. With k = 0 it blocks forever.

**Trust item:** `ffisock_select` behaves as `ffi_sock_select`. The
following `sock_poll` reports the ready set, as in the model.

`socket_ffi.c` also gains a compile-time switch, `-DNO_IDLE_WAIT`. It
turns off #23's idle-wait heuristic in `sock_poll` (§4), so that
`sock_poll` never waits, exactly as the model's poll. The default build is
unchanged.

## 2. The program, compiled and running

`asyncEchoBlkExportScript.sml` exports exactly the program that
`echo_blocking_semantics` and `echo_blocking_spec` are about:
`SNOC (main_call «main») echo_b_prog`, with
`fun main u = run_b ([3], server 3)`. It is compiled with release v3479
(arm8, native), as #23 does.

The demo (`make demo`) has three concurrent clients and a late one. Each
gets back exactly its own lines, as with the polling server. There is one
transcript per blocking program: `demo-transcript.txt` (`run_b`) and
`demo-transcript-live.txt` (`run_l`, §6).

## 3. CPU usage (indicative)

`make cpu` (`cpu_bench.py`) runs each server through three 30 s phases:

1. **idle-fresh:** no client has ever connected;
2. **light load:** one client sends a 64-byte line every 100 ms and reads
   the echo;
3. **idle-after:** that client has disconnected.

CPU% = process CPU time / wall time, from `ps -o cputime`, with 100% = one
core.

```
calibration: a C busy-polling loop (non-blocking polls) measures 16.2% here
(a pure arithmetic C loop measures 99.4% in the same session)
server                  idle-fresh  light-load  idle-after  rtt median
echo_live                     0.0%        0.1%        0.0%       227us
echo_blocking                 0.0%        0.1%       99.5%       231us
echo_polling                  0.1%        0.2%        0.1%       229us
echo_polling_nowait          24.2%       28.3%       73.5%       239us
```

| build | program | `sock_poll` (C) |
|---|---|---|
| `echo_live` | blocking, select on the **live** connections (§6, `run_l`) | never waits (`-DNO_IDLE_WAIT`) |
| `echo_blocking` | blocking, select on the whole interest list (#27, `run_b`) | never waits |
| `echo_polling` | #23's polling program (`run_i`) | #23's 50 ms idle-wait heuristic (§4) |
| `echo_polling_nowait` | #23's polling program | never waits: exactly the model's poll |

**About the environment.** These runs were made from a background session
on macOS (processes niced, background QoS).

- There, a loop of non-blocking `poll` calls measures only ~16–20% CPU,
  while a pure arithmetic loop measures 99%. So busy *polling* shows up
  well below 100% here; in a normal terminal it would be a full core.
- Compare the polling rows with the busy-polling calibration row, not with
  100%.
- `make cpu` in a normal terminal gives absolute numbers.

**What the numbers show.**

- **The model-faithful polling server busy-polls in every phase:** at or
  above the busy-polling calibration.
- **The fixed blocking server (`echo_live`) sleeps whenever it is idle,**
  before and after clients, and uses ~0.1% under light load.
- **The first blocking server (`echo_blocking`, #27) sleeps only until the
  first client disconnects.** After that it spins (99.5%).
  - Its loop's interest list only grows, and a closed connection stays
    ready forever (EOF; the model has no `close`).
  - A model-faithful `select` on the whole list therefore returns at once,
    every round.
  - This is a property of the verified loop, not of the C side, and §6
    fixes it in the verified program.
- **#23's polling build is quiet** only because of its C-side heuristic
  (§4), which nothing verified accounts for.
- **Round-trip latency** under light load is the same for all four
  (~230 µs, Python client).

## 4. #23's idle-wait heuristic in `sock_poll` (a deviation in trusted code)

#23's `sock_poll` waits up to 50 ms when the program looks idle: no
socket operation since the last poll, and the same ready set for 2 polls
in a row.

- **Semantically harmless.** The model's poll delivers one step of an
  arbitrary arrival schedule, and there is no time inside a poll. So how
  long the real poll waits is unobservable in the model.
- **It must be listed** as a deviation in trusted code.
  - It is a scheduling heuristic, not a refinement of anything proved.
  - It adds up to 50 ms of latency when a quiet period ends.
- **Recommendation.** With the blocking program available, remove it (or
  build with `-DNO_IDLE_WAIT`). If it stays, keep it with the
  justification above.

## 5. Connections are never closed (limitation, future work)

The socket model has no `close`, so the server never closes a finished
connection's fd. A long-running server therefore leaks one fd per
connection, and its interest list grows with every connection.

Future work: add `close` to the socket model and the server (and remove
the fd from the interest list), with the matching C call.

## 6. The fix: select only on the live connections (`spike/m4-blocking-live`)

**Code.** The loop keeps one more list, the live fds (`asyncM4LiveLoop`):

```sml
fun step_l (fds, live, c) =                  (* c = (acts, s) *)
  let val rs = perform acts
      val u  = case acts of [] => wait_ready live | _ => ()
      val rdy = Socket.poll fds
  in (add_accepted fds rs, upd_live live acts rs, Async.poll c (rdy, 0, rs)) end
fun main u = run_l ([3], [3], server 3)
```

- `upd_live` processes the round's (action, response) pairs.
  - An accept that hands out `c` adds `c`.
  - A read of `c` that returns EOF removes one occurrence of `c`.
- `select` waits on the live list only. The poll still polls the whole
  interest list, so the computation sees exactly the polling loop's
  snapshots.

**Why it is sound.** A snapshot may be skipped when the computation
ignores it. asyncM4BlkWorld only skipped snapshots with nothing ready. A
closed connection is always ready, so its snapshots were never skipped.

The model has the finer notion. The Level 2 server declares what it waits
for, and it is quiet: it ignores snapshots in which none of that is ready
(`wf2_server2`). A finished handler declares nothing. So it is enough for
the select set to *cover* the declared interest:

- `server_live` (`asyncM4LiveServer`): every event the Level 2 server
  waits for is the listener, or a connection that has been accepted more
  often than a read on it has returned EOF. It is proved by counting
  accepts and EOFs in the transcript, through `both`'s transcript
  (`trans_both_counts`). There is no freshness assumption.
- `sel_covers_echo`: the live list, computed from the same transcript in
  the socket vocabulary, therefore covers the server's declared interest.
  `trans_relabel` relates the two transcripts.
- `quiet_secho`: the relabelled server is quiet for that interest.
- `asyncM4LiveWorld`: asyncM4BlkWorld/Trace generalised to any select set
  that covers a quiet Level 2 computation's interest.
  - The skipped polling rounds are those in which nothing in the select
    set is ready.
  - Those rounds are `irrelevant`, so `same_for_step` drops them.
  - Everything else is as before: the same actions as polling, the two
    outcomes, and the echo transfer.

**Headline (`asyncM4LiveMain.echo_live_spec`).** It is
`echo_blocking_spec` for the fixed program, with the same two outcomes and
the same hypotheses (only the initial world). `echo_safe` holds
unconditionally, and `echo_live` holds whenever the polling loop's trace
is live.

**Assumption made.** The select set is computed by the loop from the
transcript, a superset of the declared interest. The computation's own
Level 2 interest is not read out of the CakeML value. Reading it would need
the Async library (`both`/`map`) at Level 2 in CakeML and the server
re-proved over it. The proof uses the declared interest, and the code
uses the transcript, which is sound and simple.
