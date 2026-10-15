# 16: The final top-level specifications (spec first)

Status: **statements written and typechecked; bite and non-vacuity lemmas
proved.** The top-level theorems themselves are *not* proved yet; they are
the target of the final proof push. There are no cheats, and `Holmake -j2`
in `async/spec/` is green. Branch `spike/final-spec`, stacked on
`spike/m3-assembly`.

The goal: statements small and self-evident enough that a reviewer needs to
trust no intermediate definition. The async model, `STEPA`/`COMP`, the
event loop and the scheduler do **not** appear in them.

| file | lines | role |
|---|---|---|
| `async/spec/EchoSpecScript.sml` | 155 | **trusted**: world, projections, `echo_spec` (no proofs) |
| `async/spec/HttpSpecScript.sml` | 115 | **trusted**: HTTP subset, printers, `http_spec` (no proofs) |
| `async/spec/EchoSpecBiteScript.sml` | 146 | proved: broken echo servers violate the spec; non-vacuity |
| `async/spec/HttpSpecBiteScript.sml` | 298 | proved: broken HTTP servers violate the spec; non-vacuity |

## 1. The statements

```
(* in every fair world with one listener lfd, the program runs forever, and
   its I/O trace is safe and live on every connection. *)
echo_spec lfd prog ⇔
  ∀sk. server_world lfd sk ⇒
       ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog (Diverge io) ∧
            echo_safe io ∧ echo_live sk io

echo_safe io ⇔                       (* never ahead of what was read *)
  ∀evs c. LPREFIX (fromList evs) io ⇒ bytes_written_to c evs ≼ bytes_read_from c evs

echo_live sk io ⇔                    (* everything sent comes back *)
  ∀c n. ∃evs. LPREFIX (fromList evs) io ∧ sent_upto c n sk ≼ bytes_written_to c evs
```

**The theorem to prove is `echo_spec 3w echo_prog`**, for the echo
server's whole program `echo_prog`. Read aloud: *for every fair schedule
of connections and data, the program never stops. At every moment, on
every connection, it has written back a prefix of exactly what it read
from that connection. Every byte any client sends is eventually written
back to that client.*

`http_spec lfd files prog` has the same shape, with:

```
http_safe files io ⇔
  ∀evs c rs rest. LPREFIX (fromList evs) io ∧ EVERY valid_request rs ∧
    bytes_read_from c evs = requests rs ++ rest ∧ no_full_request rest ⇒
    bytes_written_to c evs ≼ responses files rs
http_live files sk io ⇔
  ∀c n rs. EVERY valid_request rs ∧ requests rs ≼ sent_upto c n sk ⇒
    ∃evs. LPREFIX (fromList evs) io ∧ responses files rs ≼ bytes_written_to c evs

requests rs        = bytes (print_request r1 ++ print_request r2 ++ ...)
responses files rs = bytes (print_response (handle files r1) ++ ...)
```

*If a client has sent complete requests r1 … rk (and then possibly part
of another), the server has written a prefix of their responses, in order.
Eventually it writes all of them, on every connection at once.*

## 2. The trusted surface, piece by piece

Everything a reader must trust, and why it is there.

**From CakeML (imported):**
- `semantics_prog st env prog (Diverge io)`: CakeML's top-level source
  semantics. `Diverge io` means that the program runs forever (times out
  for every clock) and that `io` is the (lazy) list of all its I/O events.
- `init_state ffi`, `init_env`: the initial semantic state and environment
  (`ml_prog`).
- `IO_event name conf bytes`: one FFI call; `bytes` pairs each buffer byte
  before and after the call.

**The socket world (imported from `ffiSpikeSocketFFI`, the socket worker's
model; see `07-socket-model.md`):**
- `sockets`: listeners with pending-connection queues, connections (bytes
  arrived but unread, peer closed, bytes written), and `sched`, the
  future as a lazy list of steps of arrivals (`Connect`, `Data`, `Eof`).
- `sock_poll`/`sock_accept`/`sock_read`/`sock_write` and their byte-level
  FFI functions `ffi_sock_*`, with the encodings `fd_bytes`/`bytes_fd`
  (8 bytes per fd) and `n2w8`/`w82n`. These are the contract between
  CakeML programs and the C side.

**Fairness (imported from `ffiSpikeSocketFair`):**
- `sched_wf sk`: every scheduled arrival is effective when it arrives. A
  connection only arrives on a listener and with a fresh fd; data and EOF
  only arrive on open connections. In words: the world never drops an
  arrival. This is the only assumption on schedules; delivery happens at
  the next poll, so no separate "eventually delivered" assumption is needed
  (see 07 §3).

**In `EchoSpec` itself:**
- `socket_fn`, `socket_oracle`, `socket_ffi sk`: the sockets-only FFI. A
  socket call runs the model's function on the world's state; any other
  call, or a failing one, ends the program with an FFI failure. (This
  restates the socket worker's `socket_only_ffi` in 10 lines, so that the
  spec doesn't depend on a translator theory.)
- `server_world lfd sk`: the initial world. Exactly one listener `lfd`
  with nothing pending, no connections, and a fair schedule.
- `event_read c e`, `event_written c e`: the bytes one raw I/O event read
  from / wrote to connection `c`, read directly off the FFI's byte
  protocol. A `sock_read` buffer comes back as status `0`, an 8-byte length
  `k`, then `k` data bytes. A `sock_write`'s config is the 8-byte
  connection followed by the data. `bytes_read_from c evs` and
  `bytes_written_to c evs` concatenate them over a finite trace.
- `arrivals_upto n sched`, `sent_upto c n sk`: the data the client of
  connection `c` sends in the first `n` steps of the schedule.
- `echo_safe`, `echo_live`, `echo_spec`: the statement (§1).

**In `HttpSpec`:** `request`/`response`, `valid_path` (no space, CR or
LF, so that requests are unambiguous), `print_request`
(`"GET " ++ p ++ " HTTP/1.0\r\n\r\n"`), `print_response` (status line,
`Content-Length`, blank line, body), `handle` (the file from the map, or
404), `bytes` (characters as bytes), `requests`, `responses`,
`no_full_request`, `http_safe`, `http_live`, `http_spec`.

## 3. The trust base (outside the statements)

1. **The C FFI** implements the four socket calls as `ffi_sock_*` say
   (byte protocol and behaviour), on top of the OS.
2. **Socket-model fidelity.** The model has no errors beyond EOF, no partial
   writes, no `close`, and readiness only for reading (07 §6). A real
   network that does more is outside the statements.
3. **CakeML's trust base.** The HOL4 kernel; the CakeML compiler
   correctness theorem, which lifts `semantics_prog` behaviour to machine
   code for a given FFI oracle (here `socket_oracle`); the assembler and
   the target machine model. The statements are at the source level. The
   compiled program inherits them through the compiler theorem, which has
   not yet been instantiated for this oracle (as in the socket worker's
   examples).
4. **The program text**: `echo_prog` / `http_prog` is what gets compiled.

## 4. The spec bites (proved)

**Echo (`EchoSpecBiteScript.sml`)**, with concrete events built exactly as
the model's FFI functions produce them (`rd c bs n`, `wr c bs`):

| bug | lemma |
|---|---|
| swaps two clients' data | `broken_swaps_clients` (safety) |
| drops a byte | `broken_drops_a_byte` (safety) |
| duplicates a byte | `broken_duplicates_a_byte` (safety) |
| writes before reading | `broken_writes_before_reading` (safety) |
| never echoes | `broken_never_echoes` (liveness, in `hello_world`) |

Non-vacuity: `server_world_exists` (`server_world 3w hello_world`, with one
connection sending `"hi\n"`), and `ideal_trace_safe_and_live`: the ideal
two-event trace for it satisfies both predicates.

**HTTP (`HttpSpecBiteScript.sml`)**, with the site `[("/a", "hi")]`:

| bug | lemma |
|---|---|
| answers in the wrong order | `broken_wrong_order` |
| 200 for a missing file | `broken_200_for_missing_file` |
| wrong `Content-Length` | `broken_wrong_content_length` |
| answers a request before it fully arrived | `broken_answers_partial_request` |
| never answers | `broken_never_answers` (liveness) |

Non-vacuity: `server_world_one_client` (a fair world in which one client
sends a request) and `ideal_http_trace_safe_and_live`. The proof uses
`request_prefix_unique` (valid requests can be read back uniquely),
which is also why `valid_path` excludes spaces and line breaks.

## 5. How the existing results should compose into a proof of `echo_spec`

1. **The program and its divergence** (M3, `13-m3-assembly.md`).
   - `run_spec` (the event loop on the socket part) and the
     `m3_semantics` pattern (`call_main_thm_div`) give
     `Diverge io` with `io = LFLATTEN (LGENLIST (λi. fromList
     (sround_events fds m s0 i)) NONE)` for the server computation `m`.
     Two small bridges are needed: `semantics_dec_list` vs
     `semantics_prog`, and `socket_ffi sk = socket_only_ffi sk` (a
     definitional check).
   - `run_spec` needs the server's `COMP`. That is the M4 server worker's
     CF spec ("the CakeML server value implements the model's
     `server lfd`", `spike/m4-server`).
   - It also needs `srun_ok`: the server only reads from and writes to
     connections it has accepted. This is a model-level lemma about
     `server lfd` (in the spirit of `server_echoes`, which already tracks
     accepted connections) plus a world invariant ("pending connections
     are connections"; preserved by `deliver1` and every operation, and
     true initially in `server_world`, where nothing is pending).
2. **Bookkeeping: raw events vs the model's transcript.**
   - Per event, `event_read c (act_event (Read c n) (Got (SOME d))) = d`
     and `event_written c (act_event (Write c bs) Wrote) = bs`; poll and
     accept events contribute nothing.
   - So `bytes_read_from c` and `bytes_written_to c` of a round prefix
     of the trace are the model transcript's `read c` and `written c`
     (`asyncTranscript`), as byte lists, on the history the socket world
     generates (`srounds`). These are short lemmas in the style of
     `strace_actions_rounds`.
3. **Safety** from `echo_server_safety` (`spike/async-echo-server`):
   `fresh (trans (server lfd) h) ⇒ ∀fd. written fd (trans …) = read fd
   (trans …)`.
   - `fresh` holds in the socket world: `sched_wf` makes every `Connect`
     use a fresh fd, and there is no `close`.
   - Equality at round boundaries gives `≼` at every finite prefix of the
     trace. Within a round, the events of the round's actions come in
     order, and a write of `d` is emitted only after the read that
     returned `d`. This needs a small lemma.
   - `every_client_receives_what_it_sent` (`spike/world-async-multi`) is the
     same property seen from the clients' side, in a closed world. It is
     not needed for `echo_spec`, but it confirms the reading.
4. **Liveness** from the closed-loop work (`spike/async-closed-loop`:
   `server_accept_progress`, `server_handler_view`, …) plus the socket
   world's fairness lemmas (`ticks_ready`, `ready_read_not_block`,
   `ready_accept`, `sched_wf_preserved`, 07 §3):
   - every `Connect c` is followed by `Accepted c`;
   - every byte delivered on `c` is eventually returned by a read on `c`;
   - the handler writes it back in the same round (as `bind` continues in
     the same round), so it appears in `bytes_written_to c` one round
     later.
   - Remaining gap: the model's polling is driven by *our* event loop (one
     poll per round, fixed interest fds). The interest set must cover new
     connections, i.e. Level 2 declared interest or a loop that polls all
     accepted fds (13 §3, item 2).
5. **HTTP** follows the same route, with a model-level server whose
   per-connection handler parses `print_request` and emits
   `print_response (handle files r)`. `request_prefix_unique` is the parsing
   fact that the handler's correctness lemma needs.

## 6. Assumptions made

1. **Source-level statements** (`semantics_prog`). The machine-code level
   is the compiler theorem's job (trust base, §3).
2. **The sockets-only world** (no stdout and no clock), so that the
   statement needs only the socket part. With the multi-part rule (11), a
   composed world could be used instead.
3. **The oracle is restated** in `EchoSpec` from the model's FFI functions
   (10 lines), rather than imported from `ffiSpikeSocketDiv`.
4. **The initial world** has exactly one listener with an empty queue and no
   connections. Fairness is `sched_wf`, the socket worker's single
   assumption.
5. **Projections are defined on raw `IO_event`s** via the FFI byte protocol
   (status byte, 8-byte length, data; 8-byte fd prefix for writes).
6. **Liveness counts schedule data** (`sent_upto`): everything a client sends
   in the first n steps is eventually written back, for every n.
7. **HTTP subset**: GET only, a fixed file map, HTTP/1.0 framing, a
   `Content-Length` header, no request headers, no chunking. Paths contain
   no space, CR or LF. Safety constrains the server only when the bytes
   read so far are complete valid requests followed by an incomplete one.
   On anything else (garbage, invalid paths) the server must not write
   more than the responses to the complete requests so far.
8. **The listener fd and the file map are parameters** (`lfd`, `files`).
   The intended instances are `echo_spec 3w echo_prog` and
   `http_spec 3w files http_prog`.
