# 13: M3 assembly: a whole CakeML program's socket I/O, proved against the model

Status: **all three tasks done.** There are no cheats, and `Holmake -j2` in
`async/m3-assembly/` is green. Branch `spike/m3-assembly`, stacked on
`spike/cf-reactive` (PR #14). It **merges `origin/spike/cfdiv-multipart`**
(which contains `spike/socket-model`): the socket model, the Socket
module and its CF specs, the sockets-only world and `call_main_thm_div`
(see `07-socket-model.md`, `11-cfdiv-multipart.md`).

This is the first theorem about a real CakeML program's socket I/O in
terms of the async model: **the program diverges, and its trace of socket
calls corresponds, round by round, to the library computation's action
log on the history the socket world generates.**

Files (`async/m3-assembly/`):

| file | lines | contents |
|---|---|---|
| `asyncM3WorldScript.sml` | 273 | socket actions/responses, performing them with the socket model, the history the socket world generates, the trace lemma |
| `asyncM3ProgScript.sml` | 303 | the async library declared again in the socket program (module `Async`), its specs replayed |
| `asyncM3LoopScript.sml` | 419 | the event loop calling the Socket module, event-exposing Socket specs, `step_spec`, `run_spec` |
| `asyncM3ExampleModelScript.sml` | 125 | the example computation `accept3` and its no-misuse proof |
| `asyncM3ExampleScript.sml` | 211 | the example program, `main_spec`, the whole-program theorem |

## 1. The route (task 1)

Two routes were possible:
- (a) instantiate the generic reactive world of 10 (one `round` FFI call
  per round);
- (b) let the loop call the Socket functions directly, one per emitted
  action.

**I took (b).** It uses the socket worker's real FFI interface (four FFI
names in **one** FFI part, `SOCKETS_EV`), so cfDiv's one-part rule
`IMP_app_POSTd_one_FFI_part_FLATTEN` applies directly, as in their
`serve_spec`. Route (a) would have needed a new, round-level FFI
interface for sockets, i.e. a different program interface from the
one the socket worker verified. The generic reactive theorem of 10 stays
as the abstract statement. This instance re-does its proof shape for
the socket interface.

**Actions and responses** (`asyncM3World`):

```
Datatype: sact  = Accept word64 | Read word64 num | Write word64 (word8 list) End
Datatype: sresp = Accepted (word64 option) | Got ((word8 list) option) | Wrote End
```

`sock_do s a` performs one action with the socket model's `sock_accept`,
`sock_read` or `sock_write`. It returns `NONE` on misuse, where the real FFI
call would fail. `sock_acts s acts` performs a round's actions in order,
collecting the responses, the I/O events (`act_event`) and the next
state.

**The loop** (`asyncM3Loop`):

```sml
fun do_act a = case a of
    Accept l  => Accepted (Socket.accept l)
  | Read c n  => Got (Socket.read c n)
  | Write c s => (Socket.write c s; Wrote)
fun perform acts = (do_act on each action, in order)
fun step (fds, c) = case c of (acts, s) =>
  let val rs = perform acts
      val rdy = Socket.poll fds
  in (fds, Async.poll c (rdy, 0, rs)) end
fun run st = run (step st)
```

Each round performs the computation's emitted actions (one Socket call
each). It then polls the fixed interest fds, which also lets one step of
the world's schedule arrive, and finally polls the computation with the
snapshot `<| ready := the ready fds; now := 0; results := the responses
|>`.

**The history the socket world generates** iterates this with the model's
actions:

```
srounds fds m s0 0 = ([], s0)
srounds fds m s0 (SUC n) =
  let (h, s) = srounds fds m s0 n;
      (rs, evs, s1) = sock_acts_tot s (new_actions (log_of m) h);
      (rdy, s2) = sock_poll fds s1
  in (h ++ [ssnap rdy rs], s2)
sround_events fds m s0 n = evs ++ [spoll_event fds s1]     (same names)
srun_ok fds m s0 ⇔ ∀n. sock_acts (state n) (actions n) ≠ NONE    (no misuse)
```

### One translation chain

The library (`asyncCfActProg`) and the Socket module
(`ffiSpikeSocketProg`) were built on separate translation chains, both on
`basisProg`, but one program needs both. `asyncM3Prog` extends the
socket chain (`ffiSpikeSocketDiv`). It declares the `step` datatype at
the top level and the library functions in a module `Async`, using the
same code text. The Socket module declares no types, so the new
constructors get **the same stamps** as in `asyncCfActProg`:

```
Theorem step_stamps_agree:
  OPTION_MAP SND (nsLookup (^step_env).c (Short «Done»)) = SOME ^done_stamp_old ∧
  OPTION_MAP SND (nsLookup (^step_env).c (Short «Pending»)) = SOME ^pending_stamp_old
```

So `STEPA`, `COMP`, `app_COMP_of_approx` and every model lemma are
reused unchanged. Only the per-function CF specs are replayed for the new
closures, with the same proofs as `asyncCfActSpecScript.sml`
(`Async_return_spec`, `Async_poll_spec`, `Async_wait_spec`,
`Async_emit_spec`, `Async_bind_spec`, ...). `both`/`choose` can be
replayed the same way when needed. If the library is ever moved into the
basis-level build, this duplication goes away.

### What is proved (verbatim)

```
(* MAIN: the socket trace and the model agree.  If no action of the run
   is a misuse, the actions performed by the socket calls in the first n+1
   rounds of the loop's trace are exactly the model computation's action
   log on the history the socket world generates. *)
Theorem strace_actions_rounds:
  srun_ok fds m s0 ∧ wf m ⇒
  strace_actions (FLAT (GENLIST (sround_events fds m s0) (SUC n))) =
  (m (shist fds m s0 n)).actions

(* MAIN: one loop iteration against the socket world. ... *)
Theorem step_spec:
  COMP p SACT A (SNAPSHOT SREADY SRESP) m cv ∧
  LIST_TYPE NUM (MAP w2n fds) fdsv ∧
  sock_acts s (m []).actions = SOME (rs, evs1, s1) ⇒
  app (p:'ffi ffi_proj) step_v [Conv NONE [fdsv; cv]] (SOCKETS_EV s [])
    (POSTv v.
       &(∃cv'. v = Conv NONE [fdsv; cv'] ∧
               COMP p SACT A (SNAPSHOT SREADY SRESP)
                 (suspended m [ssnap (FST (sock_poll fds s1)) rs]) cv') *
       SOCKETS_EV (SND (sock_poll fds s1)) (evs1 ++ [spoll_event fds s1]))

(* MAIN: the async event loop against the socket model. ... *)
Theorem run_spec:
  limited_parts socket_names p ∧ wf m ∧ srun_ok fds m s0 ∧
  LIST_TYPE NUM (MAP w2n fds) fdsv ∧
  COMP p SACT A (SNAPSHOT SREADY SRESP) m cv ⇒
  app (p:'ffi ffi_proj) run_v [Conv NONE [fdsv; cv]] (SOCKETS_EV s0 [])
    (POSTd io. io = LFLATTEN (LGENLIST (λi. fromList (sround_events fds m s0 i)) NONE))
```

`strace_actions` decodes the action from each socket event: the
listener fd from `sock_accept`'s config; the connection fd and the
requested length from `sock_read`'s config and buffer size; the
connection and the data from `sock_write`'s config. Poll events
contribute no actions. The decoding uses the socket worker's
`bytes_fd_fd_bytes`. Helpers: `Socket_accept_spec_ev`,
`Socket_read_spec_ev` and `Socket_write_spec_ev` (the socket worker's
specs, re-proved with the events exposed, in the style of their
`Socket_poll_spec_ev`), `do_act_spec` and `perform_spec`.

## 2. The whole program (task 2) and the example (task 3)

A whole-program theorem needs a concrete program, so tasks 2 and 3 meet in
one example. The computation:

```
accept3 = bind (wait ready3) (λu. emit (Accept 3w))
ready3 sn = if 3w ∈ sn.ready then SOME () else NONE
```

It waits until listener 3 is ready, then accepts a connection. In
CakeML, written with the library:

```sml
fun ready3 w = case w of (rdy, t, res) => if has3 rdy then Some () else None
fun accept3 u = Async.emit (Accept 3)
fun main u = run ([3], Async.bind (Async.wait ready3) accept3)
```

The no-misuse obligation is discharged from one fact about the initial
world. accept3's only action is `Accept 3w` (`new_actions_accept3`), and
listeners are never removed (`is_listener_tick`,
`is_listener_sock_accept`):

```
(* MAIN: if 3 is a listener in the initial world, no run of accept3 against
   the socket world contains a misuse. *)
Theorem srun_ok_accept3:
  is_listener s0 3w ⇒ srun_ok fds accept3 s0

Theorem main_spec:
  limited_parts socket_names p ∧ is_listener sk 3w ∧ UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) main_v [uv] (SOCKETS_EV sk [])
    (POSTd io. io = LFLATTEN (LGENLIST
                      (λi. fromList (sround_events [3w] accept3 sk i)) NONE))

(* MAIN: in a sockets-only world in which 3 is a listener, the whole
   program (basis, Socket, the Async library, the event loop, the example,
   and a call to main) diverges, and its I/O trace is, round by round, the
   socket calls performing accept3's actions followed by the poll of
   listener 3, for the history the socket world generates. *)
Theorem m3_semantics:
  is_listener sk 3w ⇒
  ∃io. semantics_dec_list (init_state (socket_only_ffi sk)) init_env
         (SNOC (main_call «main») m3_prog) (Diverge io) ∧
       io = LFLATTEN (LGENLIST
              (λi. fromList (sround_events [3w] accept3 sk i)) NONE)

(* MAIN: and the trace agrees with the model ... *)
Theorem m3_trace_actions:
  is_listener sk 3w ⇒
  strace_actions (FLAT (GENLIST (sround_events [3w] accept3 sk) (SUC n))) =
  (accept3 (shist [3w] accept3 sk n)).actions
```

`m3_semantics` is proved exactly like the socket worker's
`serve_semantics`: `call_main_thm_div`, `sonly_init_heap` and
`limited_parts_sonly` from `ffiSpikeSocketDiv`, with `main_spec` as the
program's `POSTd` spec. `main_spec` composes the replayed library specs
(`Async_wait_spec` with `ready3_spec`, then `Async_bind_spec` with
`accept3_spec`) and `run_spec`.

The chain, end to end:
- **source semantics** (`Diverge io`) ← `call_main_thm_div` ← cfDiv
  (`run_spec`);
- **trace = per-round socket events** of the model's new actions on the
  socket world's history (`srounds`);
- **socket events' actions = the model's action log** (`strace_actions_rounds`);
- **the model computation** (`accept3`) is built with the library, whose
  CakeML values implement the model's `wait`, `emit` and `bind` (`STEPA`).

## 3. What is not done, and estimates

1. **A richer example (e.g. the echo handler).** The obstacle is not CF
   but `srun_ok`: for a handler that reads from and writes to an accepted
   connection c, no-misuse needs "c is a connection in the world from
   the round after accept onwards". That takes:
   - a world invariant "every pending connection in a listener's queue is
     a connection" (true for `deliver1`, preserved by every operation, but
     to be assumed of the initial world);
   - an argument about the computation's actions over the generated
     history: each `Read c`/`Write c` comes after an `Accept` that returned
     `c`. This is a property of the model computation, best stated as a
     model-level lemma ("the computation only uses fds it has
     accepted") and proved once per program.

   Estimate: ~200–300 lines for the echo handler, mostly the model-level
   lemma. The M4 worker's server (`spike/m4-server`) gives the CF side
   ("the CakeML server value implements the model's `server lfd`"). Then
   `run_spec` here consumes it: plug its `COMP` into `run_spec` and
   discharge `srun_ok`.
2. **A dynamic interest set.** The interest fds are fixed per run (loop
   state). A server polling its connections needs the interest set to
   grow. Either the loop computes it from the computation (Level 2's
   declared interest, 01 §7), or the program passes a list that it
   updates. With Level 2 this is the natural next step.
3. **`now`** is 0, as in the sockets-only world, which has no clock part.
   With the multi-part rule of 11 the clock part can be added, and `now`
   taken from `Clock.now`.
4. **Errors as responses.** Misuse makes the FFI call fail, so it is a
   hypothesis (`srun_ok`) rather than an error response. Changing the
   socket FFI to report misuse as an error code would remove the
   hypothesis, but that is a change to the socket worker's interface.
5. **The replayed library specs** (`asyncM3Prog`): a duplication forced by
   the two translation chains. It disappears once the library is part
   of a common translation chain with the Socket module.

## 4. Assumptions made

1. **Route (b)**: the loop calls the Socket functions directly, one per
   emitted action, then `Socket.poll` once per round, all in the socket
   worker's single FFI part. Simpler and more faithful than wrapping the
   socket model into the generic `round` interface of 10.
2. **A fixed interest list** of fds is polled each round (part of the loop
   state).
3. **`now = 0`** (the sockets-only world has no clock).
4. **No misuse is a hypothesis** (`srun_ok`), since the real FFI fails on
   misuse. It is discharged for the example from `is_listener sk 3w`.
5. **The library code is declared a second time**, in a module `Async`, in
   the socket program. The step datatype is at the top level so that its
   stamps match (checked by `step_stamps_agree`), and the specs are
   replayed with the same proofs.
6. **The example is `accept3`** ("wait until listener 3 is ready, then
   accept"), chosen so that the whole chain, including `srun_ok`, is proved
   with one assumption about the initial world. The echo handler is
   estimated in §3.
7. **Socket action/response encodings**: reads are `Read c n` with
   `0 < n < 256 ** 8` (otherwise misuse); data are byte lists in the model
   and CakeML strings in the code (`bytes_str`), as in the socket
   worker's specs.
8. **Additive**: the new directory `async/m3-assembly/`, plus
   `13-m3-assembly.md` and `HANDOFF-m3.md`. The merge of
   `spike/cfdiv-multipart` had one trivial conflict (a comment in
   `async/.gitignore`), resolved by keeping both sides. The socket
   worker's files are unchanged.
