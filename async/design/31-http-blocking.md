# 31: The HTTP blocking refinement (live-fd select loop)

Branch `spike/http-blocking`, based on `review/11-docs` (the review
series' tip). Code is in `async/http-blocking/`. Nothing outside that
directory changed.

## 1. The result

The header-tolerant HTTP server, run under #46's live-fd select loop
(`run_l`), in EchoSpec's socket world with `«sock_select»` (`ssel_ffi`):

```
Theorem http_blk_spec:              (* echo_live_spec's shape *)
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ⇒
  (∃io. semantics_dec_list (init_state (ssel_ffi sk)) init_env
          (SNOC (main_call «main») http_l_prog) (Diverge io) ∧
        http_safe_h demo_files io ∧
        (http_live_h demo_files sk (poll_io [3w] http_c.run sk) ⇒
         http_live_h demo_files sk io)) ∨
  (∃c io. … Terminate (FFI_outcome (Final_event (ExtCall «sock_select») c [] FFI_diverged)) io ∧
          http_safe_h demo_files (fromList io) ∧
          (http_live_h … (poll_io …) ⇒ http_live_h demo_files sk (fromList io)))

Theorem http_blk_spec_fair:         (* the same, with sched_wf: both outcomes are safe AND live *)
```

`http_blk_spec_fair` is stronger than echo's companion theorem. The
polling HTTP program's liveness is already proved in a fair world
(`http_live_h_rounds`, layer 9), so the condition can be discharged.

## 2. The pieces

| file | what | reuse |
|---|---|---|
| `asyncSWLiveServer` | `sw_live`: what `server_with2 h2` waits for is the listener or an fd accepted more often than a read of it returned EOF, for any handler meeting `handler_live_ok` | #46's `server_live`, made handler-generic |
| `asyncHttpLiveSel` | the HTTP handler meets `handler_live_ok` (`http_handler_eofs`, `http_handler_interest`); `quiet_shttp`; `sel_covers_http` | #46's `asyncM4LiveEcho` |
| `asyncHttpBlkTransfer` | `http_safe_h` / `http_live_h` carry over from the polling trace to both outcomes (`lblocking_http_div/_stuck`) | #46's `lblocking_echo_*`, via `bytes_unwaited` |
| `asyncHttpBlkProg`, `asyncHttpBlkSpec` | the HTTP code and its CF specs, declared again on top of `run_l` (one CakeML program is one translation chain) | verbatim from layer 9 |
| `asyncHttpBlkMain` | `main`, `http_blk_semantics`, `http_blk_spec`, `http_blk_spec_fair` | #46's `asyncM4LiveMain` |

A bodies handler (cf-actions' `http_prog_b_spec`) would reuse
`asyncSWLiveServer` unchanged. It needs its own `handler_live_ok` proof:
the handler stops when a read returns EOF and waits only on its own fd.

## 3. The live list

The loop keeps a list of live fds. An accept adds the new connection, and
a read that returns EOF removes it. The loop selects on that list, and
`sel_covers_http` shows the list contains everything the server waits for.

## 4. Caveat: an invalid request can make the blocking server busy-poll

**What happens.** The HTTP handler stops (`return ()`) in two cases:
- a read returns EOF, which removes its fd from the live list;
- its buffer is `HInvalid`: a request that can never become valid,
  including, since #48, any request with Content-Length or
  Transfer-Encoding. This does not remove the fd, because the loop sees
  no EOF.

After an invalid request, the client may then **close** the connection
(EOF arrives) or **send more bytes**. The fd is then ready forever, nobody
reads it, and `select` on the live list returns at once on every round.
The whole server busy-polls, at about one core, until it is restarted. A
client that stays idle after the invalid request does not trigger this.

**What it does not affect.** Correctness: `sel_covers` only needs the
select set to *contain* what the server waits for, and `http_blk_spec`
holds as stated. It also does not affect well-formed clients; the
README's CPU row uses them.

**Is there a "stalled Incomplete" case too?** No. With `HIncomplete` the
handler always waits for readability and reads again, so an EOF is
always observed and the fd leaves the list. `HComplete` answers and
continues, and so ends in one of the other cases. `HInvalid` is the only
way to stop without an EOF.

### Fix options (costed, not implemented)

**A. The handler drains an invalid connection until EOF (recommended).**
On `HInvalid`, instead of `return ()`:

```
drain fd = bind (readable fd) (λu. bind (emit (Read fd)) (λr.
             case r of Eof => return () | _ => drain fd))
```

The fd then reaches EOF and leaves the live list. A client that keeps
sending is read and discarded at the rate it sends, which is not a spin.

- **The specification allows it unchanged.**
  - *Safety* (`http_safe_h`): drained bytes are read, and nothing more is
    written. What has been read is still `hrequests rs ++ rest` with `rs`
    the requests answered before the invalid one, and `rest` still starts
    with the invalid prefix. So `no_full_hrequest rest` still holds: an
    invalid prefix stays invalid when extended (`asyncHttpParseHExt`).
  - *Liveness* (`http_live_h`) has no new obligations: requests sent after
    an invalid one never decompose as `hrequests rs`
    (`print_hrequest_unique`).
- **Proofs to redo.** The statements `http_prog_h_safe`,
  `http_prog_h_spec` and `http_blk_spec` keep their exact text; their
  proofs are re-run.
  - Layer 9:
    - `asyncHttpServerH`: the handler's definition and unfolding, wf,
      settled, and `http_handler_serves_h` (one more branch, which writes
      nothing);
    - `asyncHttpServer2H` (#53);
    - `asyncHttpSockModelH`, `asyncHttpSockProgH` (the CakeML `drain`) and
      `asyncHttpSockSpecH` (a depth-indexed spec for `drain`, like the
      handler's);
    - `asyncHttpMachineH` / `asyncHttpDrainH`: the handler machine gets a
      fourth state. `hmachine_live`'s answers are unaffected, but the
      invariant gains a case;
    - the remaining files (`asyncHttpSafeH`, `asyncHttpLiveH`,
      `asyncHttpSemanticsH`, the headline) just rebuild.
  - This branch: `http_handler_eofs` and `http_handler_interest` (one more
    case each), and the replayed code and specs.
- **Estimate:** 350–500 changed lines of proof, mostly mechanical
  (another recursive branch like the existing `HIncomplete` one), plus a
  rebuild of layer 9. The spec does not change.

**B. The loop drops an fd once its handler has finished.** The loop
cannot observe this. It sees only the round's (action, response) pairs,
and a finished handler is indistinguishable from one that is waiting.
Making it observable needs a new action, such as `Close fd`: a new
constructor in the socket action vocabulary (`asyncM3World`), handled in
`sock_do`, with the no-misuse (`sinv`/`gen_grun_ok`) and trace-bridge
proofs extended. That is large in the v1 world, but it is exactly what
close-v2 adds. There the handler would close the fd on `HInvalid`, and
the loop would drop it, with no drain.

**C. Select on the computation's exact declared interest.** This needs
the Level 2 interest of the residual computation as a CakeML value. That
in turn needs a Level 2 CakeML library with `both2`/`map2`/`fix2` specs;
`loop/blocking-l2` only has `return2`/`bind2`/`wait_on`/`emit2`. This is
the most general fix and the largest (a new CF layer).

**Recommendation:** A now. It is local, the spec is unchanged, and it
re-runs the existing headline proofs. Or fold it into close-v2 via B, if
that branch lands soon.
