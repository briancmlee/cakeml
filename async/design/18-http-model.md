# 18: The HTTP server in the async model

Status: **tasks 1–4 done; the optional extras (Level 2 quiet, a
closed-system result) are estimated, not done.** There are no cheats,
and `Holmake -j2` in `async/http-model/` is green. Branch
`spike/http-model`, stacked on `spike/final-spec` (PR #18). It
**merges `origin/spike/async-echo-server`** (the model echo server,
transcripts, `echo_server_safety`). The merge was clean.

This is the model-level core of the HTTP stretch goal: a parser for
HttpSpec's request subset, an HTTP handler and server written with the
async library, and the HTTP analogue of `echo_server_safety`. Everything is
pure HOL, except that the parser and the server use HttpSpec's own
printers, so the model and the trusted statement cannot drift apart.

| file | lines | contents |
|---|---|---|
| `asyncHttpParseScript.sml` | 305 | the incremental parser, proved against `print_request` |
| `asyncServerWithScript.sml` | 179 | `server_with h`: the echo server's skeleton for any handler; isolation |
| `asyncHttpServerScript.sml` | 265 | the HTTP handler and server, wf/settled, safety, EVAL checks |

## 1. The parser (task 1)

```
parse_request s = Complete r rest   s starts with a complete valid request r
                | Incomplete        s could still become one
                | Invalid           no extension of s starts with one
```

It is incremental in the simplest way: the handler keeps a buffer of the
bytes it has read but not yet consumed, and re-parses after every read.
`parse_all s` is the list of complete requests at the front of `s`.
Proved, against HttpSpec's printer (verbatim):

```
(* MAIN: a printed valid request, followed by anything, parses back *)
parse_print:    valid_request r ⇒ parse_request (print_request r ++ rest) = Complete r rest
(* MAIN: Complete means a printed valid request followed by the rest *)
parse_complete: parse_request s = Complete r rest ⇒ valid_request r ∧ s = print_request r ++ rest
(* MAIN: a strict prefix of a printed valid request is Incomplete *)
parse_prefix:   valid_request r ∧ s ≼ print_request r ∧ s ≠ print_request r ⇒
                parse_request s = Incomplete
(* MAIN: Invalid input can never be extended into a printed valid request *)
parse_invalid:  parse_request s = Invalid ⇒
                ∀t r rest. valid_request r ⇒ s ++ t ≠ print_request r ++ rest
(* MAIN: printed valid requests, then a rest that does not start with one,
   parse to exactly those requests *)
parse_all_requests:
  ∀rs. EVERY valid_request rs ∧ (∀r more. valid_request r ⇒ rest ≠ print_request r ++ more) ⇒
       parse_all (FLAT (MAP print_request rs) ++ rest) = rs
```

Together these say that `Complete`, `Incomplete` and `Invalid` mean exactly
what their names say. The "rejected in a stated way" behaviour for garbage
is `parse_invalid`. `parse_all_requests` is the bridge to HttpSpec's
`requests rs ++ rest` (with `no_full_request rest`).

## 2. The generic server (task 3)

`asyncServer` hard-codes the echo handler, so I added a generic version
**without editing it**:

```
server_with h lfd = wait until lfd is readable; accept;
                    on Accepted fd: both (h fd) (server_with h lfd)
                    otherwise:      server_with h lfd

(* MAIN: the echo server is the instance for the echo handler *)
server_with_handler: server_with handler = server
```

and the generic form of the echo server's invariant `server_echoes`:

```
(* MAIN: if each handler h fd only reads and writes its own fd, and the
   connections the world hands out are distinct, then on every connection fd
   the server's reads and writes on fd are those of one run of h fd (on some
   history L), or there are none; and the server only touches connections it
   has accepted. *)
server_with_isolates:
  (∀fd hh. EVERY (on_fd fd) (trans (h fd) hh)) ⇒
  ∀hh. fresh (trans (server_with h lfd) hh) ⇒
       (∀fd. FILTER (on_fd fd) (trans (server_with h lfd) hh) = [] ∨
             ∃L. FILTER (on_fd fd) (trans (server_with h lfd) hh) = trans (h fd) L) ∧
       (∀fd. EXISTS (on_fd fd) (trans (server_with h lfd) hh) ⇒
             MEM fd (accepted (trans (server_with h lfd) hh)))
```

So **any per-connection property of a handler transfers to the whole
server**. Echo safety could now be re-derived as a corollary of
`handler_echoes`. I did not do that, to leave the existing proof untouched.

## 3. The HTTP handler and server (task 2)

```
(* MAIN: the handler satisfies its recursive equation *)
http_handler files (fd, buf) =
  case parse_request buf of
    Complete req rest =>
      bind (emit (Write fd (print_response (handle files req))))
           (λw. http_handler files (fd, rest))
  | Incomplete =>
      bind (readable fd) (λu.
      bind (emit (Read fd)) (λres.
        case res of
          Data d => http_handler files (fd, buf ++ d)
        | Eof => return ()
        | _ => http_handler files (fd, buf)))
  | Invalid => return ()

http_server files lfd = server_with (λfd. http_handler files (fd, "")) lfd
```

- It is defined with the recursion rule (`fix` of a contractive body,
  `http_body_contractive`). Every recursive call comes after an `emit` or a
  `wait`.
- If the buffer holds several complete requests, it answers one per round,
  without reading in between, so pipelined requests are served from the
  buffer.
- Well-formed and settled: `wf_http_handler`, `settled_http_handler`,
  `wf_http_server`, `settled_http_server`.
- EVAL sanity checks: parser examples; a request that arrives in two pieces
  is read twice and then answered (`example_two_piece_request`).

## 4. Safety (task 4)

```
responses_to files s = MAP (print_response o handle files) (parse_all s)

(* MAIN: one connection: the handler only reads and writes its own fd, and
   what it has written is a prefix of the responses to the complete requests
   in its buffer followed by everything it has read. *)
http_handler_serves:
  ∀hh buf. EVERY (on_fd fd) (trans (http_handler files (fd, buf)) hh) ∧
           written fd (trans (http_handler files (fd, buf)) hh) ≼
           responses_to files (buf ++ CONCAT (read fd (trans (http_handler files (fd, buf)) hh)))

(* MAIN: the HTTP analogue of echo_server_safety *)
http_server_safety:
  fresh (trans (http_server files lfd) hh) ⇒
  ∀fd. written fd (trans (http_server files lfd) hh) ≼
       responses_to files (CONCAT (read fd (trans (http_server files lfd) hh)))

(* MAIN: the same in HttpSpec's terms *)
http_server_safety_requests:
  fresh (trans (http_server files lfd) hh) ∧
  CONCAT (read fd (trans (http_server files lfd) hh)) = FLAT (MAP print_request rs) ++ rest ∧
  EVERY valid_request rs ∧ (∀r more. valid_request r ⇒ rest ≠ print_request r ++ more) ⇒
  written fd (trans (http_server files lfd) hh) ≼ MAP (print_response o handle files) rs
```

On every connection, the strings the server has written are a prefix of the
printed responses to the complete requests it has read so far, in order.
The proof is `http_handler_serves` (by induction on the history, as for
`handler_echoes`, using `parse_extend` and `parse_all_Complete`) plus
`server_with_isolates`.

**Why a prefix, not equality** (unlike echo): with several complete
requests in one read, the handler writes one response per round. So a
response can be due but not yet written. Liveness ("eventually all of
them") is about the rounds after that, as in HttpSpec's `http_live`.

## 5. How this composes into a proof of `http_spec` (the same pipeline as echo)

1. **CF**: a CakeML implementation of `http_handler` and `http_server`,
   written with the library's CakeML combinators, and their `COMP` specs.
   This is the same work as the M4 server worker's (`spike/m4-server`), with
   `server_with` taking the handler as a parameter. The parser is a pure
   function, so it can be translated with CakeML's translator (`translate
   parse_request_def`) rather than proved with CF.
2. **M3** (`13-m3-assembly.md`): `run_spec` on the socket part gives
   divergence and the per-round socket trace for the server's `COMP`,
   given `srun_ok` (the server only touches connections it has accepted:
   `server_with_isolates`' second conjunct).
3. **Bookkeeping** (as for echo, 16 §5): raw events ↔ the transcript's
   `read`/`written`. Strings ↔ bytes is `bytes = MAP (n2w o ORD)`, which is
   injective on characters, so prefixes and concatenations carry over.
   `parse_all_requests` turns HttpSpec's `requests rs ++ rest` (with
   `no_full_request rest`, on bytes) into `parse_all` on strings.
4. **Safety**: `http_server_safety_requests` gives `http_safe` at round
   boundaries. Within a round, a response is written only after the read
   that completed its request, as for echo.
5. **Liveness**: the closed-loop work (`spike/async-closed-loop`), with the
   handler's extra fact that a buffered complete request is answered in the
   next round (no wait in between). The same interest-set gap as echo
   remains (16 §5, item 4).

## 6. Not done, with estimates

- **Level 2 quiet** for `http_handler`. It mirrors `asyncServer2`'s echo at
  Level 2 (`comp2`, `wait_on`, `quiet`). The new part is that the
  `Complete` branch emits without waiting, which is quiet since `emit`
  declares no interest. Estimate: about 150–200 lines (mostly mirroring
  `asyncServer2Script.sml`), plus a Level 2 `server_with`.
- **The world-async closed-system result** ("any client program sending
  printed requests receives the printed responses", in the style of
  `every_client_receives_what_it_sent`). It needs the HTTP server in the
  network kernel of `spike/world-async-multi` and a lemma that the
  kernel's per-connection queues carry `read`/`written`. Estimate: about
  200–300 lines, most of it adapting `closed_echo`'s invariant from
  equality to "prefix of `responses_to`".

## 7. Assumptions made

1. **Strings in the model.** The echo model and its vocabulary use strings
   (`Data string`, `Write fd string`). HttpSpec's bytes are `MAP (n2w o
   ORD)` of them, bridged at the M3 level.
2. **The parser and server use HttpSpec's definitions directly**
   (`request`, `print_request`, `print_response`, `handle`,
   `valid_request`). The `http-model` directory therefore depends on
   `../spec`, which sits on CakeML's semantics (basis heap).
3. **On invalid input the handler stops** (`return ()`): it neither answers
   nor reads further. HttpSpec's safety then holds trivially for that
   connection.
4. **Several buffered requests are answered one per round**, from the
   buffer, without reading in between.
5. **Additive**: `server_with` is new. `asyncServer` and
   `asyncServerSafety` are unchanged, and the echo server is related to the
   new definition by `server_with_handler`.
