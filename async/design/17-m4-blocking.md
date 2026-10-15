# 17: The blocking echo program (M4 + select)

Branch `spike/m4-blocking`, stacked on `spike/l2-blocking` (PR #21). It
merges `spike/m4-liveness` and `spike/m4-safety` and uses them read-only:
`async/m4-common`, `async/m4-server`, `async/m4-safety`, `async/spec`.

- New code: `async/m4-blocking/` (5 theories, ~2000 lines).
- No existing file changed. `EchoSpec` is untouched.

Full `Holmake` in `async/m4-blocking` is green. There are no cheats.
Handoff: `async/design/HANDOFF-m4-blocking.md`.

## Result in one paragraph

The echo server now has a blocking version of M4's dynamic-interest event
loop. When the server has nothing to do, the loop sleeps in a `select` on
its interest fds instead of polling. It is verified end to end, down to
CakeML's `semantics_dec_list`. The world is EchoSpec's socket world with
one more FFI call, `«sock_select»`.

There is **no liveness assumption**: `blk_live` is gone. Instead, the
theorem has two outcomes:

1. **The program runs forever.** Its I/O trace is `echo_safe`, and it is
   `echo_live` whenever the polling program's trace is.
2. **The program blocks forever in `select`,** after a finite trace.
   - This happens only when the polling program would never perform
     another action from that point on.
   - The finite trace is `echo_safe`, and it is `echo_live` whenever the
     polling program's trace is.

Safety holds unconditionally, via m4-safety's `echo_comp_safe` for the
polling trace. The only remaining hypotheses are those of the world: one
listener 3 with nothing pending, and no connections.

```
echo_blocking_spec:
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ⇒
  (∃io. semantics_dec_list (init_state (ssel_ffi sk)) init_env
          (SNOC (main_call «main») echo_b_prog) (Diverge io) ∧
        echo_safe io ∧
        (echo_live sk (poll_io [3w] echo_m sk) ⇒ echo_live sk io)) ∨
  (∃c io. semantics_dec_list (init_state (ssel_ffi sk)) init_env
            (SNOC (main_call «main») echo_b_prog)
            (Terminate (FFI_outcome (Final_event (ExtCall «sock_select») c []
                                       FFI_diverged)) io) ∧
          echo_safe (fromList io) ∧
          (echo_live sk (poll_io [3w] echo_m sk) ⇒ echo_live sk (fromList io)))
```

Here `echo_m = srelabel (server 3)` is the computation the polling program
runs. `poll_io [3w] echo_m sk` is the polling loop's trace, which
asyncM4Loop's `run_i_spec` produces.

## 1. The loop (`asyncM4BlkLoop`)

```sml
fun wait_ready fds = (#(sock_select) (sel_conf fds) <empty buffer>; ())
fun step_b (fds, c) =                          (* c = (acts, s) *)
  let val rs = perform acts
      val u  = case acts of [] => wait_ready fds | _ => ()
      val rdy = Socket.poll fds
  in (add_accepted fds rs, Async.poll c (rdy, 0, rs)) end
fun run_b st = run_b (step_b st)
fun main u = run_b ([3], server 3)             (* asyncM4BlkMain *)
```

This is asyncM4Loop's `step_i` with one extra line. The code extends
m4-safety's `asyncM4SockServer`, so `server` is the verified echo server.

**`select` waits; it does not report readiness.** `ffi_sock_select`
lets the world's rounds pass (`ticks k`) until a poll of the fds would
return something (`sock_wait`), and returns nothing. If that never
happens it returns `FFIdiverge`. The next `Socket.poll` then reports
readiness as usual. This keeps every readiness report in the existing
`Socket.poll` code and spec. The pair `select; poll` is exactly
"skip the polls that would return nothing, then poll".

**The loop blocks when there are no actions** (`acts = []`). It does not
check whether the computation has finished. The server never finishes,
and a finished computation that is never polled again emits no actions
either way.

## 2. Why blocking is sound (`asyncM4BlkWorld`)

`bgrounds fds0 m s0 n = SOME (kept, N, s)` models n rounds of the
blocking loop:

- `kept` is the history the computation was polled with;
- `N` is the number of polling-loop rounds the world went through;
- `s` is the world.

It is `NONE` if the loop blocked forever in `select`.

The invariant `binv` holds after every round (`bgrounds_inv`):

- `kept` and the polling loop's history `ghist (interest fds0) m s0 N`
  are indistinguishable for m (the model's `same_for`);
- they declare the same interest fds;
- the worlds agree (`gstate … N = s`).

The rounds `select` lets pass are polling rounds in which m had nothing
to do and the poll returned nothing. Each such round adds an idle
snapshot, with nothing ready and no responses. m ignores idle snapshots
while it has nothing to do (`idle_quiet`, the model's `quiet` for the
interest `K UNIV`), so `same_for_step` absorbs them (`idle_rounds`).

Consequences:

- `bgrounds_same_actions`: m is in the same state as under polling.
- `bgrounds_stuck_quiet`: if `select` never returns, all later polling
  rounds are idle, so the polling loop never performs another action.
- `bgrounds_runs`: otherwise every polling round is reached.

## 3. The trace (`asyncM4BlkTrace`)

`bround_events` gives each round's events:

- a round with actions has the socket calls, then the poll;
- an idle round has `select_event fds`, then the poll.

Remove the waiting events (polls and selects, `unwaited`), and the
blocking trace equals the polling trace at the corresponding round
boundary (`bround_unwaited`, `stuck_unwaited`). Waiting events read and
write nothing (`bytes_unwaited`), so:

- `echo_safe_unwaited`: safety carries over to a trace whose finite
  prefixes are covered by the other trace's prefixes, modulo waiting
  events;
- `echo_live_unwaited`: liveness carries over to a trace that reaches
  every prefix of the other.

Results:

- `blocking_echo_div` is outcome 1 at trace level.
- `blocking_echo_stuck` is outcome 2 at trace level.
- `blocking_echo` combines them, using `bgrounds_two_outcomes`.

## 4. The echo server is idle-quiet (`asyncM4BlkEcho`)

`idle_quiet_echo: idle_quiet (srelabel (server lfd))` is discharged from
the model, so there is **no gap**:

- `quiet_idle_quiet`: if c is quiet, then so is `c.run` for the interest
  `K UNIV`. An idle snapshot has nothing ready, so it is disjoint from
  any interest.
- `idle_quiet_relabel`: relabelling keeps this, provided the snapshot
  translation maps idle snapshots to idle ones. `sfs` does (`sfs_idle`).
- `wf2_server2` and `erase_server2` (asyncServer2) give the server as
  the run of a quiet Level 2 computation.

`blocking_echo_server` is `blocking_echo` for the echo server, with no
hypotheses.

## 5. The FFI part with select

The blocking program calls a fifth FFI name, so its CF heap uses the part
`SSEL s evs`: the socket part with `«sock_select»` added. CF specs are
tied to their FFI part. The four socket calls, `do_act` and `perform` are
therefore re-proved for `SSEL`. The proofs are M3's verbatim, with
`SOCKETS_EV` replaced by `SSEL` (~170 lines). The code values are reused
unchanged.

At the semantics level, `ssel_ffi sk` is EchoSpec's `socket_ffi sk` with
`«sock_select»` added. A `select` that would block forever ends the run
with `FFI_diverged`. `parts_ok_ssel` and `ssel_init_heap` connect it to
`SSEL`, as `ffiSpikeSocketDiv` does for the sockets-only world.

## 6. Statements, in order

| theory | MAIN |
|---|---|
| asyncM4BlkWorld | `bgrounds_inv`, `bgrounds_same_actions`, `bgrounds_stuck_quiet`, `bgrounds_runs` |
| asyncM4BlkTrace | `bround_unwaited`, `stuck_unwaited`, `blocking_echo_div`, `blocking_echo_stuck`, `bgrounds_two_outcomes`, `blocking_echo` |
| asyncM4BlkEcho | `idle_quiet_echo`, `wf_echo`, `blocking_echo_server` |
| asyncM4BlkLoop | `wait_ready_spec`, `wait_ready_stuck_spec` (POSTf), `step_b_spec`, `step_b_wait_spec`, `step_b_stuck_spec`, `run_b_spec` (POSTd), `run_b_stuck_spec` (POSTf), `run_b_two_outcomes` |
| asyncM4BlkMain | `main_spec_div`, `main_spec_stuck`, `parts_ok_ssel`, `echo_blocking_semantics`, `echo_blocking_spec` |

## 7. For the user to decide (not decided here)

- **The headline.** Two options; this work serves both, and EchoSpec is
  unchanged.
  - (a) Keep `echo_spec` about the polling program, and present
    `echo_blocking_spec` as a companion theorem.
  - (b) Amend EchoSpec so the world may include `«sock_select»`, and
    allow the "blocked in select" outcome. That outcome would read: "the
    run ends in an FFI divergence of select, after a finite trace that is
    safe and live".
- **Trust base.** The C side of `«sock_select»` must behave like
  `ffi_sock_select`: block until some fd in the config is readable, then
  return without consuming anything.
- **`blk_live` in PR #21 (`async/l2-blocking`).** The same two-outcome
  structure would remove it there too. Not done; that PR is under review.

## Assumptions made

- The new code extends m4-safety's `asyncM4SockServer`, so this branch
  merges `spike/m4-safety` and `spike/m4-liveness` read-only. Ownership
  was agreed by message:
  - async-spike owns asyncM4Loop and will not restate it without
    telling me;
  - m4-server owns grounds, GRounds and the server.
- The program's interest starts as `[3]` with listener 3, matching
  `echo_spec 3w`.
- The liveness hypothesis is about the polling trace
  `poll_io [3w] echo_m sk`, the trace of asyncM4Loop's `run_i_spec` for
  the same computation and world. If the final polling program uses a
  different initial interest or computation, restate it with the same
  proof.
