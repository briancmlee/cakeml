# 20: The HTTP server in CakeML

Status: **tasks 1 and 2 done, and task 3 written up (§4).** There are no
cheats, and `Holmake -j2` in `async/http-impl/` is green. Branch
`spike/http-impl`, stacked on `spike/http-model` (PR #20). It **merges
`origin/spike/m4-server`** (PR #17: the CakeML echo server, `STEPAd`/`COMPd`,
`handler_spec`/`server_spec`). The merge was clean.

This is for HTTP what `15-m4-server.md` did for echo: CakeML code that
implements the model's `http_handler` and `http_server` (`18-http-model.md`),
with CF specs in the same form as `handler_spec`/`server_spec`. The new
point is that the accept/fork skeleton is verified **once**, for any
handler that has a spec. The echo server and the HTTP server are both
instances.

| file | lines | contents |
|---|---|---|
| `asyncHttpImplProgScript.sml` | 79 | the pure functions translated (`parse_request`, `respond`); the CakeML `server_with`, `http_handler`, `http_server` |
| `asyncHttpImplSpecScript.sml` | 319 | `server_with_spec` (generic), the echo instance, `http_handler_spec`, `http_server_spec` |

## 1. The pure functions, translated (task 1)

- `parse_request` and its helpers (`split_path`, `get_sp`, `after_path`) go
  through `translate`. The only change is `DROP` rewritten as
  `mllist$drop`, which the translator knows.
- HttpSpec's `request` and the parser's `parse_result` become CakeML
  datatypes (`register_type`).
- **The response.** `print_response (handle files req)` would need
  HttpSpec's response datatype and `toString` in CakeML. Instead the
  theory defines `respond files p` directly, with `ALOOKUP` (the file
  map) and `num_to_str`, and proves:

  ```
  respond_thm: respond files p = print_response (handle files (Get p))
  ```

  So the translated code computes exactly the spec's printed response.
- **The file map** is a CakeML association list of strings:
  `FILES = LIST_TYPE (PAIR_TYPE (LIST_TYPE CHAR) (LIST_TYPE CHAR))`.

## 2. The CakeML code

The code mirrors the model's equations (`server_with_unfold`,
`http_handler_unfold`) line for line:

```sml
fun server_with h lfd =
  bind (readable lfd) (fn u =>
  bind (emit (Accept lfd)) (fn res =>
    case res of
      Accepted fd => map (fn p => ()) (both (h fd) (server_with h lfd))
    | _ => server_with h lfd));

fun http_handler files fd buf =
  case parse_request buf of
    Complete (Get p) rest =>
      bind (emit (Write fd (respond files p))) (fn w =>
        http_handler files fd rest)
  | Incomplete =>
      bind (readable fd) (fn u =>
      bind (emit (Read fd)) (fn res =>
        case res of
          Data d => http_handler files fd (buf @ d)
        | Eof => return ()
        | _ => http_handler files fd buf))
  | Invalid => return ();

fun http_server files lfd = server_with (fn fd => http_handler files fd []) lfd;
```

- `readable`, `map`, `bind`, `emit`, `both`, `return` are the library's
  CakeML combinators (`asyncCfActProg`, `asyncCfActBoth`, `asyncM4ServerProg`).
- The model's handler takes the pair `(fd, buf)`. The CakeML one is
  curried.

## 3. The specs (task 2)

The technique is m4-server's (15 §2): for every depth `n`, prove that the
code implements the model up to depth `n`, by induction on `n`, then take
the limit with `app_COMP_of_approxd`.

### 3.1 The skeleton, once

```
(* the CakeML value hv implements the model handler h on every connection *)
HANDLER p h hv ⇔
  (∀fd. wf (h fd)) ∧
  ∀fd fdv. NUM fd fdv ⇒ app p hv [fdv] emp (POSTv v. &COMP p ACTION UNIT_TYPE SNAP (h fd) v)

(* MAIN: for any handler value hv implementing a model handler h, the
   CakeML skeleton server_with hv implements the model's server_with h *)
server_with_spec:
  HANDLER p h hv ∧ NUM lfd lfdv ⇒
  app p server_with_v [hv; lfdv] emp
    (POSTv v. &COMP p ACTION UNIT_TYPE SNAP (server_with h lfd) v)

(* MAIN: the echo server is an instance: server_with applied to the CakeML
   echo handler implements the model's echo server *)
server_with_handler_spec:
  NUM lfd lfdv ⇒
  app p server_with_v [handler_v; lfdv] emp
    (POSTv v. &COMP p ACTION UNIT_TYPE SNAP (server lfd) v)
```

- The proof of `server_with_spec_d` is `server_spec_d`'s, with the
  handler's spec taken from `HANDLER` instead of `handler_spec`.
- The echo instance combines `server_with_handler` (the model's
  `server_with handler = server`, from 18) with m4-server's `handler_spec`.
- m4-server's own `server_v` and `server_spec` are untouched.

### 3.2 The HTTP handler and server

```
(* MAIN: the CakeML HTTP handler implements the model's handler: for a
   connection fd and a buffer buf, http_handler files fd buf returns a
   computation value that, round by round, emits exactly the model's actions
   (Write fd response, Read fd) and finishes exactly when the model's
   http_handler files (fd, buf) does. *)
http_handler_spec:
  FILES files filesv ∧ NUM fd fdv ∧ LIST_TYPE CHAR buf bufv ⇒
  app p http_handler_v [filesv; fdv; bufv] emp
    (POSTv v. &COMP p ACTION UNIT_TYPE SNAP (http_handler files (fd, buf)) v)

(* MAIN: the CakeML HTTP server implements the model's http_server: for a
   file map and a listener lfd, http_server files lfd returns a computation
   value that, round by round, emits exactly the model's actions (Accept
   lfd, and the actions of every accepted connection's HTTP handler) and
   never finishes, exactly as the model's http_server files lfd.  It is the
   instance of server_with_spec for the HTTP handler. *)
http_server_spec:
  FILES files filesv ∧ NUM lfd lfdv ⇒
  app p http_server_v [filesv; lfdv] emp
    (POSTv v. &COMP p ACTION UNIT_TYPE SNAP (http_server files lfd) v)
```

The handler's induction differs from echo's in two ways:

- **Two guarded binds.** The `Complete` branch emits a `Write` with no
  `readable` before it, so its outer bind is guarded by `emit`
  (`emit_needs_snapshot`) rather than by `readable`. A small lemma,
  `bind_guarded_spec_any`, packages `bind_guarded_spec_0` and
  `bind_guarded_spec_d` for any depth `n`: the continuation is needed at
  depth `n - 1`, and only when `0 < n`. With it the proof is a single
  `completeInduct_on ‘n’`, with no separate case for depth 0.
- **The buffer is universally quantified** in the induction, because the
  recursive calls change it (`rest`, `buf ++ d`).

`http_server_spec` is short: `server_with_spec`, where the `HANDLER`
obligation is the closure `fn fd => http_handler files fd []` and
`http_handler_spec`.

## 4. What is left for HttpSpec's `http_safe` (task 3; not started)

These specs are in the **model vocabulary**: the model's actions and
responses as CakeML datatypes, with strings. The program-level route for
echo (spike/m4-safety and spike/m4-liveness, `async/m4-common`) runs the
server in M3's socket vocabulary under the dynamic-interest event loop
(`asyncM4Loop`: `add_accepted`, `step_i`, `run_i`, `run_i_spec`). HTTP
takes the same route. What remains, in order:

1. **The HTTP server in the socket vocabulary (model).**
   `relabel sfa sfs (http_server files lfd)` (asyncM4SockModel's `sfa`/`sfs`:
   fds as `n2w`, strings as bytes, `Read fd` as `Read c bufsz`,
   `Got (SOME [])` as `Eof`).
   - asyncM4RelabelDist's distribution lemmas (relabel commutes with
     `bind`, `both`, `map`, `wait`, `emit`) give unfolding equations
     `shttp_handler_unfold` and `sserver_with_unfold`, as for
     `shandler_unfold` and `sserver_unfold`.
   - The one new point: the handler's buffer is a string, and the socket
     handler sees bytes. Either keep the buffer as a string and convert
     each chunk (`MAP (CHR o w2n)`), or run the parser on bytes. The first
     is the smaller change.
   - Estimate: about 100 lines.
2. **The CakeML code in the socket vocabulary, in M3's program chain**
   (asyncM3Prog / asyncM4SockApprox). That program is a separate
   translation chain from this one, so `parse_request`, its helpers and
   `respond` must be translated again there.
   - The CF proofs of §3 are replayed with the `Async_`/`async_` specs of
     asyncM4SockApprox, as asyncM4SockServer did for echo.
   - Proving the socket `server_with` generically there too, as in §3.1,
     would also give echo's `sserver_spec` as an instance.
   - Estimate: about 350 lines, most of it a copy of
     `asyncHttpImplSpecScript.sml` with renamed specs.
3. **The program.** `run_i` on `http_server files lfd` with interest
   `[lfd]`, as m4-liveness assembles it for echo. Its `run_i_spec` gives
   divergence and the per-round trace over `grounds (interest fds0)`.
   - `srun_ok` (no misuse) comes from `server_with_isolates`' second
     conjunct (the server only touches accepted fds) and asyncM4SockInv's
     `sock_do_ok`.
   - Estimate: about 100 lines, once echo's assembly exists to copy.
4. **The bridge to HttpSpec's `http_safe`** (the m4-safety route for
   `echo_safe`).
   - asyncM4GTrans relates the transcript to the performed pairs and to the
     raw events (`trans_ghist`, `bytes_written_to_rounds`,
     `bytes_read_from_rounds`, `rounds_LPREFIX`).
   - Combined with `http_server_safety_requests` (18 §4) and
     `parse_all_requests`, the per-connection written bytes are a prefix of
     `MAP (print_response o handle files) rs`, given
     `requests rs ++ rest` and `no_full_request rest` on the bytes read.
   - Strings ↔ bytes is `MAP (n2w o ORD)`, injective, so prefixes and
     concatenations carry over.
   - Estimate: about 200 lines, mostly mirroring echo_safe's proof with
     `≼ responses_to` in place of equality.
5. **`http_live`** (eventually every complete request is answered). This
   follows m4-liveness's route plus one handler fact: a buffered complete
   request is answered in the next round, with no wait in between. Not
   estimated here, since echo's liveness assembly is still being built.

## 5. Assumptions made

1. **Model vocabulary.** The specs are in the model's vocabulary, the
   same as m4-server's `handler_spec`/`server_spec`. The socket vocabulary
   is §4's step 1–2.
2. **`respond` instead of translating `print_response`/`handle`.** It is
   proved equal (`respond_thm`), so nothing is lost. It avoids registering
   HttpSpec's response type and translating `toString`.
3. **The generic skeleton is a new CakeML function `server_with`.**
   m4-server's `server` and its spec are kept as they are, and the echo
   instance (`server_with_handler_spec`) is proved alongside.
4. **`HANDLER` includes `∀fd. wf (h fd)`**, because `both_spec_d` and
   `map_spec_d` need well-formedness of both sides.
5. **The file map is an association list of strings**, as HttpSpec's
   `handle` (`ALOOKUP`) has it.
