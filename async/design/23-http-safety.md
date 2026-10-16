# 23: HttpSpec's http_safe for the whole HTTP program

Status: **done, and the HTTP server also runs.** `http_semantics_prog` is
proved: in the sockets-only world with listener 3w, the whole HTTP program
diverges with the server's socket trace, and that trace satisfies
HttpSpec's `http_safe`. There are no cheats, and `Holmake -j1` in
`async/http-safety/` is green. HttpSpec is unchanged.

The server is compiled with the release compiler, as in #23, and a
curl-based transcript is recorded (§6).

Branch `spike/http-safety`, from `spike/machine-code` (PR #24). It
**merges `origin/spike/http-impl`** (286a0a950). The merge was clean.

This follows the route of `echo_semantics_prog` (22 §1) and the plan in
20-http-impl.md §4. Two pieces of the echo proof are generalized on the
way, so the echo instance is now one case of generic results.

| file | lines | contents |
|---|---|---|
| `asyncServerWithUsesScript.sml` | 104 | `server_with_uses_accepted`: the skeleton never misuses sockets, for any handler that only touches its own fd |
| `asyncRunOkGenScript.sml` | 240 | the no-misuse argument and trace bridge of asyncM4EchoRunOk/EchoSafe, for any `uses_ok` computation |
| `asyncHttpSafeScript.sml` | 169 | `parse_all_mono`, `http_comp_safe` (HttpSpec's `http_safe` for the loop's trace) |
| `asyncHttpSockModelScript.sml` | 95 | `sserver_with_unfold`, `shttp_handler_unfold` (socket vocabulary) |
| `asyncHttpSockProgScript.sml` | 81 | the CakeML code in M3's program (re-translated parser and `respond`) |
| `asyncHttpSockSpecScript.sml` | 338 | `sserver_with_spec` (generic), the echo instance, `shttp_handler_spec`, `shttp_server_spec` |
| `asyncHttpMainScript.sml` | 83 | `demo_files`, `main`, `http_prog`, the export to `http_server.sexp` |
| `asyncHttpSemanticsScript.sml` | 128 | `main_spec`, `http_semantics`, `http_semantics_prog` |
| `Makefile`, `http_demo.sh`, `http-demo-transcript.txt` | | the runnable server and its demo |

## 1. The final statement

```
start_world s0 ⇔ s0.listeners = [(3w, [])] ∧ s0.conns = []
http_trace s0 = LFLATTEN (LGENLIST
                  (λi. fromList (grounds_events (interest [3w])
                                   (srelabel (http_server demo_files 3)) s0 i))
                  NONE)

(* MAIN: the same, in the form CakeML's compiler correctness theorem
   (compile_correct) takes: the HTTP program's semantics_prog behaviour in
   the world socket_only_ffi s0 is the divergent trace http_trace s0, which
   satisfies http_safe. *)
http_semantics_prog:
  start_world s0 ⇒
  semantics_prog (init_state (socket_only_ffi s0)) init_env http_prog
    (Diverge (http_trace s0)) ∧
  http_safe demo_files (http_trace s0)
```

- **`http_safe`** is HttpSpec's, verbatim. At every point of the run and
  on every connection: if the bytes read so far are complete valid
  requests `rs` followed by a rest without a full request, then the bytes
  written are a prefix of the responses to `rs`.
- **`http_prog`** is the whole program: the basis, Socket, the Async
  library, M4's dynamic-interest loop, the echo server's code (present
  but unused), the translated parser and responder, the HTTP server,
  `demo_files`, `main`, then `main ()`.
- **`demo_files`** is the file map, three files. The theorem is about this
  map. Any other map works the same way: it is translated and passed to
  the server, and `http_comp_safe` holds for every `files`.
- **`http_semantics`** is the same statement in `semantics_dec_list`
  form. `main_spec` is the CF spec of `main`.

## 2. The model layer

### 2.1 No misuse, generically (`asyncServerWithUses`, `asyncRunOkGen`)

Echo's no-misuse proof (`echo_sinv`, `echo_grun_ok`, `echo_fresh`)
depends on the server only through m4-server's `server_uses_accepted`.
So:

```
uses_ok lfd m ⇔ ∀hh. accepts_on lfd (trans m hh) ∧ ∀fd. acc_first fd (trans m hh)

(* MAIN: if every handler h fd only reads and writes fd, the server
   skeleton uses the socket API correctly, on every history *)
server_with_uses_accepted:
  (∀fd hh. EVERY (on_fd fd) (trans (h fd) hh)) ⇒
  ∀hh. accepts_on lfd (trans (server_with h lfd) hh) ∧
       ∀fd. acc_first fd (trans (server_with h lfd) hh)

http_server_uses_accepted   (from http_handler_serves' first conjunct)
uses_ok_server              (echo: uses_ok lfd (server lfd))
```

`asyncRunOkGen` is asyncM4EchoRunOk with `uses_ok lfdn m` in place of
`server lfdn`. In a world with listener `n2w lfdn` and no connections,
for any interest function:

- `gen_grun_ok`: no misuse;
- `gen_fresh`: distinct connections;
- `gen_fds_bounded`;
- `gen_rounds_bytes`: the trace bridge, i.e. the bytes written and read on
  `c` at a round boundary are those of the model transcript on fd `w2n c`.

### 2.2 The trace bridge to http_safe (`asyncHttpSafe`)

```
(* MAIN (helper): reading more can only add complete requests at the end *)
parse_all_mono:  ∀s t. parse_all s ≼ parse_all (s ++ t)

(* MAIN: HttpSpec's safety for the HTTP server's trace: in a world with one
   listener n2w lfdn and no connections, for any interest function, at
   every point of the run and on every connection, if the bytes read so
   far are complete valid requests rs followed by a rest without a full
   request, the bytes written are a prefix of the responses to rs. *)
http_comp_safe:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  http_safe files (LFLATTEN (LGENLIST
    (λi. fromList (grounds_events ifds (srelabel (http_server files lfdn)) s0 i))
    NONE))
```

The proof works at a prefix `evs` lying between round boundaries `n` and
`n+1`, on connection `c`. Write `TT` for the model transcript of `n`
rounds, and `s` for the string of `evs`'s read bytes. The chain is:

```
written_to c evs ≼ written_to c (rounds 0..n)
                 = bytes (written (w2n c) TT)                     [gen_rounds_bytes]
                 ≼ bytes (responses_to files (read (w2n c) TT))   [http_server_safety, gen_fresh]
                 ≼ bytes (responses_to files s)                   [read (w2n c) TT ≼ s; parse_all_mono]
                 = responses files rs                              [parse_all_requests]
```

The last step turns HttpSpec's byte-level hypotheses
(`bytes_read_from c evs = requests rs ++ rest`, `no_full_request rest`)
into `parse_all s = rs`. It uses that `bytes` is injective on strings
(`ORD < 256`).

## 3. The CakeML layer (M3's program)

- **`sserver_with_unfold`, `shttp_handler_unfold`**: the socket-vocabulary
  unfoldings.
  - The handler writes `MAP (n2w o ORD) (print_response …)`.
  - It reads at most `bufsz` bytes.
  - `Got (SOME [])` is EOF.
  - Read bytes are appended to the buffer as characters.
- **The code** (`asyncHttpSockProg`) extends `asyncM4SockServer`. That is
  the M3 chain, the program `run_i` runs in.
  - `parse_request`, its helpers and `respond` are translated again in
    this chain.
  - The CakeML strings of the socket responses convert with
    `String.explode` and `String.implode`.

The specs:

```
SHANDLER p h hv ⇔ (∀fd. wf (h fd)) ∧
  ∀fd fdv. NUM fd fdv ∧ fd < dimword(:64) ⇒
    app p hv [fdv] emp (POSTv v. &COMP p SACT UNIT_TYPE SSNAP (srelabel (h fd)) v)

(* MAIN: for any handler value hv implementing a model handler h (in the
   socket vocabulary), the CakeML skeleton sserver_with hv implements
   srelabel (server_with h lfd) *)
sserver_with_spec:
  SHANDLER p h hv ∧ NUM lfd lfdv ∧ lfd < dimword(:64) ⇒
  app p sserver_with_v [hv; lfdv] emp
    (POSTv v. &COMP p SACT UNIT_TYPE SSNAP (srelabel (server_with h lfd)) v)

sserver_with_handler_spec   (echo instance)

(* MAIN: the CakeML HTTP handler implements the model's handler, in the
   socket vocabulary *)
shttp_handler_spec:
  FILES files filesv ∧ NUM fd fdv ∧ fd < dimword(:64) ∧ LIST_TYPE CHAR buf bufv ⇒
  app p http_handler_v [filesv; fdv; bufv] emp
    (POSTv v. &COMP p SACT UNIT_TYPE SSNAP (srelabel (http_handler files (fd, buf))) v)

(* MAIN: the CakeML HTTP server implements the model's http_server, in the
   socket vocabulary *)
shttp_server_spec:
  FILES files filesv ∧ NUM lfd lfdv ∧ lfd < dimword(:64) ⇒
  app p http_server_v [filesv; lfdv] emp
    (POSTv v. &COMP p SACT UNIT_TYPE SSNAP (srelabel (http_server files lfd)) v)
```

(`http_handler_v` and `http_server_v` here are `asyncHttpSockProg`'s; the
theory qualifies them, because asyncHttpImplProg's model-vocabulary
versions have the same names.)

## 4. The whole program (`asyncHttpSemantics`)

This is `asyncEchoSemantics` with the HTTP pieces swapped in:

- `main_spec` uses `shttp_server_spec`, `run_i_spec`, and `gen_grun_ok`
  (via `http_server_uses_accepted`);
- `http_semantics` uses `call_main_thm_div` and `sonly_init_heap`, then
  `http_comp_safe` for the trace;
- `http_semantics_prog` adds `prog_syntax_ok` (by evaluation).

For a machine-code theorem, `machine-code/compile/`'s scripts apply with
`http_prog` in place of `echo_prog`, once the compiler build is available
(22 §3).

## 5. What is left

- **`http_live`.** Not attempted. It follows m4-liveness's route, plus
  the handler's fact that a buffered complete request is answered in the
  next round, with no wait in between.
- **The machine-code theorem.** It is blocked on the same compiler build
  as echo (22 §3).

## 6. Running it

```
cd async/http-safety
Holmake          # writes http_server.sexp (33 declarations after the basis)
make             # release cake v3479, arm8; links runnable/socket_ffi.c
make demo        # writes http-demo-transcript.txt
```

The transcript (`http-demo-transcript.txt`) shows:

- `/`, `/index.html` and a missing file (404) over curl;
- three concurrent curls;
- two pipelined requests over nc, answered in order;
- a request with a header, which gets no response.

**curl's default headers** (`Host`, `User-Agent`, `Accept`) are outside
HttpSpec's request subset, `GET <path> HTTP/1.0\r\n\r\n`. The demo removes
them with `-H 'Name:'`, after which curl sends exactly the subset. A plain
`curl` request is therefore `Invalid`, and the server stops serving that
connection without answering (18 §7.3).

The trusted base is the same as #23's: `runnable/socket_ffi.c`, unchanged.
Its banner still says "echo server", and the port variable is still
`CAKE_ECHO_PORT`. I left the trusted file untouched to keep it identical
across both servers.

## 7. Assumptions made

1. **The base is `spike/machine-code`, merged with `spike/http-impl`.**
   PR base: `spike/machine-code`.
2. **The program contains the echo server's code**, unused. It extends
   `asyncM4SockServer`, whose `sreadable` and `has_fd` it reuses. This
   also allows the echo instance of the generic skeleton.
3. **A fixed demo file map** (`demo_files`). `http_comp_safe` is proved for
   every `files`, and only the whole-program theorem fixes this map,
   because the program has to.
4. **Generic copies, not edits.** `asyncRunOkGen` copies
   asyncM4EchoRunOk's proofs, generalized, rather than editing m4-common,
   which other branches also touch. Echo's own theorems are unchanged.
5. **HttpSpec is unchanged.** The bridge works on its definitions as they
   are (`requests`, `responses`, `no_full_request`, `bytes`).
6. **`runnable/socket_ffi.c` is reused unchanged** (§6).
