# 24: A header-tolerant HttpSpec (DRAFT, for your decision): fully proved

`spec/HttpSpecScript.sml` is unchanged. This note goes with two new files.

**`spec/HttpSpecHeadersScript.sml`** is the variant spec. A request is
```
GET <path> HTTP/<1.0|1.1>\r\n
<name>: <value>\r\n          (any number of well-formed header lines)
\r\n
```
- The server ignores the headers and the version: the response is
  HttpSpec's `print_response (handle files (Get path))`.
- The style is still printer-based. The spec quantifies over printed valid
  requests with any header list, and never mentions a parser.
- World, projections, and the shapes of `http_safe_h`, `http_live_h` and
  `http_spec_h` are HttpSpec's, with `hrequest` for `request`.

**`spec/HttpSpecHeadersBiteScript.sml`** holds the proved lemmas, with no
cheats:

| theorem | meaning |
|---|---|
| `plain_requests` | HttpSpec's requests are the special case of no headers and version 1.0: same validity, same bytes, same responses |
| `curl_request` | the request curl 8 sends by default (`Host`, `User-Agent`, `Accept`, HTTP/1.1) is a printed valid request |
| `print_hrequest_unique` | a printed valid request followed by anything determines the request and the rest, so reads decompose into requests in at most one way |
| `broken_header_changes_response` | letting a header change the response violates safety |
| `broken_answers_before_blank_line` | answering before the blank line that ends the headers violates safety |
| `broken_never_answers_h` | never answering violates liveness |
| `ideal_h_trace_safe_and_live` | non-vacuity: a fair world with one client sending a request with a header exists, and the ideal trace is safe and live |

## Status: both HttpSpec options are now fully proved (branch `spike/http-headers`)

The proofs meet the variant: the whole header-tolerant HTTP program
diverges, with a trace satisfying `http_safe_h`. There are no cheats, and
`Holmake -j1` in `async/http-headers/` is green. The original HttpSpec
program and its theorems are **untouched**. This is a separate program
and a separate set of theories, so you can keep either option, or both.

```
(* MAIN *)
http_semantics_prog_headers:
  start_world s0 ⇒
  semantics_prog (init_state (socket_only_ffi s0)) init_env http_prog_h
    (Diverge (http_trace_h s0)) ∧
  http_safe_h demo_files (http_trace_h s0)

(* MAIN, in HttpSpecHeaders' own world *)
http_prog_h_safe:
  ∀sk. server_world 3w sk ⇒
       ∃io. semantics_prog (init_state (socket_ffi sk)) init_env http_prog_h
              (Diverge io) ∧
            http_safe_h demo_files io
```

| theory (`async/http-headers/`) | contents |
|---|---|
| `asyncHttpParseH` | **new**: the header-tolerant parser `parse_hrequest` (request line with HTTP/1.0 or 1.1, then `parse_headers` up to the blank line), proved against `print_hrequest`: `parse_hprint`, `parse_hcomplete`, `parse_hextend`, `parse_all_hrequests`, `parse_all_h_mono`; helpers `parse_headers_print` / `parse_headers_done`; EVAL check on curl's real request |
| `asyncHttpServerH` | `asyncHttpServer` with `parse_hrequest` and `handle files (hpath req)`: `http_handler_serves_h`, `http_server_safety_h`, `http_server_safety_hrequests` |
| `asyncHttpSafeH` | `http_server_h_uses_accepted`, `http_comp_safe_h` (the trace bridge, with `hrequests`/`hresponses`/`no_full_hrequest`) |
| `asyncHttpSockModelH` | `shttp_handler_h_unfold` |
| `asyncHttpSockProgH` | the parser translated into CakeML; `http_handler_h`, `http_server_h` (reusing `sserver_with`) |
| `asyncHttpSockSpecH` | `shttp_handler_h_spec`, `shttp_server_h_spec` (reusing `sserver_with_spec`) |
| `asyncHttpMainH`, `asyncHttpSemanticsH` | `main`, `http_prog_h`, the export, `main_spec`, `http_semantics_headers`, `http_semantics_prog_headers` |
| `asyncHeadlineH` | `http_prog_h_safe` |

**How the work divided:**
- **New:** only the parser and its proofs, `asyncHttpParseH` (≈470
  lines).
- **Copied:** everything else is the http-safety pipeline with `_h`
  names. The generic pieces are reused unchanged: the server skeleton and
  its spec, the no-misuse argument (`asyncRunOkGen`), the event loop, and
  the trusted socket FFI.

**The two options are alternatives, not refinements.**
- The header-tolerant server answers e.g. `GET / HTTP/1.1\r\n\r\n`.
- Strict HttpSpec counts that as "rest", so it requires that request
  *not* to be answered.
- So neither server satisfies the other's spec, and each satisfies its
  own.

**Runnable:** `make demo` in `async/http-headers` writes
`http-headers-demo-transcript.txt`. It shows plain `curl` (HTTP/1.1, with
its default headers, plus a custom header and a custom User-Agent),
HTTP/1.0 with headers, concurrent clients, and pipelined requests with
and without headers. A malformed header line is rejected.

## The original estimate (kept for reference)


The structure of the proofs is unchanged. Only the request grammar
changes.

1. **Parser** (`http-model/asyncHttpParse`).
   - Accept the two versions, then skip header lines until the blank line.
     `parse_request` returns an `hrequest` (or just the path).
   - Re-prove `parse_print`, `parse_complete`, `parse_prefix`,
     `parse_invalid`, `parse_extend` and `parse_all_requests` against
     `print_hrequest`.
   - `print_hrequest_unique` above is the key lemma, and it is already
     done.
   - Estimate: about 200 lines, mostly adapting the existing 305.
2. **Handler and model safety** (`asyncHttpServer`).
   - Respond with `handle files (hpath r)`; `http_handler_serves` and
     `http_server_safety` go through with `responses_to` defined via
     `hpath`.
   - Estimate: about 30 lines of changes.
3. **CakeML.**
   - The new parser is translated automatically. `respond` is unchanged
     because it takes the path.
   - The handler's match changes from `Complete (Get p) rest` to the new
     constructor.
   - The CF proofs (`shttp_handler_spec_d`) change only at that match.
   - Estimate: about 20 lines.
4. **Trace bridge** (`asyncHttpSafe`): `http_comp_safe` with
   `hrequests`/`hresponses`/`no_full_hrequest`, using the new
   `parse_all_hrequests`. Estimate: about 40 lines of renaming.
5. **Whole program**: `http_semantics_prog` against `http_safe_h`. This
   is mechanical.

In total, about 300 lines and roughly one worker-day. The demo would then
work with plain `curl` and with browsers, which send HTTP/1.1 with
headers.

**Notes for the decision:**
- The responses stay HTTP/1.0, which is a valid answer to an HTTP/1.1
  request.
- The server already keeps connections open and serves pipelined
  requests, so HTTP/1.1 clients that read `Content-Length` behave.
- Header values may contain `:` and leading spaces; this is unambiguous
  because a header name cannot contain `:`.
