# 27: Request bodies (Content-Length): spec and feasibility

Status: **step 1 (spec) is done and proved. Step 2 (this note) concludes
it is feasible, with no blocking issue.** Branch `spike/http-bodies`,
stacked on `spike/http-liveness` (which has `http_prog_h_spec`).

## 1. The spec (done)

`spec/HttpSpecBodiesScript.sml` is 131 lines, against HttpSpecHeaders'
121. It is a new file; HttpSpec and HttpSpecHeaders are unchanged.

A request is:
- a method `GET` or `POST`, a path, and a version 1.0 or 1.1;
- header lines;
- a blank line;
- exactly n body octets, where n is the value of the single
  case-insensitive `Content-Length` header (canonical decimal), or 0 if
  there is none.

Two `Content-Length` headers, or any `Transfer-Encoding` header, make the
request invalid. The server answers `GET` as HttpSpec does, `POST /echo`
with the body, and any other `POST` with 404. Header lines have their own
character rules (`valid_bheader`), so later restrictions of HttpSpecHeaders'
`valid_header` do not affect this spec.

`spec/HttpSpecBodiesBiteScript.sml` holds 24 proofs, with no cheats:

| theorem | meaning |
|---|---|
| `print_brequest_unique` | framing is unique: a printed valid request followed by anything determines the request and the rest, so the Content-Length framing is the only reading the spec accepts |
| `broken_body_as_request` | a POST /echo whose body is literally `GET /a HTTP/1.0\r\n\r\n`, answered as if the body were a request, violates safety |
| `broken_answers_before_body` | answering before the last body byte arrives violates safety |
| `broken_never_answers_b` | never answering violates liveness |
| `bodiless_requests`, `valid_header_bheader` | HttpSpecHeaders' requests without Content-Length / Transfer-Encoding are the bodiless GET case here (same bytes, same response) |
| `curl_post_request` | `curl -d hello …/echo` is valid and gets `Ok "hello"` |
| `ideal_b_trace_safe_and_live` | non-vacuity |

## 2. Feasibility

### 2.1 The key observation: the machine does not change

The header-tolerant handler keeps a buffer, re-parses it after every read,
answers one complete request per round, reads while the buffer is
incomplete, and stops on an invalid one.

That design already copes with bodies that span many reads. Suppose the
headers are complete but fewer than n body bytes have arrived. The parser
says *incomplete*, the handler reads, and it re-parses. **No separate
length-driven body state is needed in the handler or in the
per-connection machine.** The body state lives inside the (stateless)
parser, which looks at the header block's Content-Length and compares it
with the length of what follows.

So the handler, the server (`server_with`), the per-connection machine
(`asyncHttpMachineH`) and the partial-read drain argument
(`asyncHttpDrainH`, `hmachine_live_p`) carry over as mechanical ports.
They use the parser only through these facts:

| fact needed | H version | bodies version |
|---|---|---|
| print → complete | `parse_hprint` | `parse_bprint`: new proof, same shape |
| complete → printed | `parse_hcomplete` (+ `_shorter`) | `parse_bcomplete`: new proof |
| complete is stable under extension | `parse_hextend` | follows from the two above (as for H) |
| printed requests parse to themselves | `parse_all_hrequests`, `parse_all_h_print(ed)` | same proofs |
| invalid stays invalid when extended | `parse_hrequest_invalid_ext`, `parse_hinvalid` (asyncHttpParseHExt) | `parse_binvalid`: **the hardest lemma**, see 2.3 |
| monotonicity of `parse_all` | `parse_all_h_mono` / `parse_all_prefix` | same proofs |

What carries over as is:
- `asyncSWSock` (generic in `server_with hf`: `TSg_*`,
  `sw_conn_accepted`);
- `asyncRunOkGen` (no misuse, fresh, trace bridge);
- `server_with_uses_accepted`;
- the socket FFI and the loop.

The handler's `hok` (it only touches its own fd) is a 5-line port.

### 2.2 The parser

`parse_brequest s`:
1. **Method.** `"GET "` or `"POST "`: a prefix of either is incomplete,
   anything else is invalid.
2. **Request line and header lines.** As `parse_hrequest`, reusing
   `split_path`, the version constants and `parse_headers` (proved in
   asyncHttpParseH).
3. **On `HDone hs rest`:**
   - any `Transfer-Encoding`, or two or more `Content-Length` headers →
     invalid;
   - one `Content-Length` whose value is not canonical decimal → invalid;
   - otherwise n is the value (or 0). If `LENGTH rest < n` → incomplete,
     else complete, with body `TAKE n rest` and rest `DROP n rest`.

The canonical-decimal check needs an executable decimal reader. I would
use `dec_value v = if v ≠ "" ∧ EVERY isDigit v then SOME (fold) else NONE`
together with `toString n = v`, proved against `num_to_dec_string` via
`toNum_toString` and the digits of `toString`. Small, but it is new.
`MAP toLower` translates to CakeML with the basis's `Char.toLower`.

### 2.3 The hardest lemma: `parse_binvalid`

"If `parse_brequest s = BInvalid`, no extension of s is a printed valid
request followed by anything." It is needed by the liveness drain
(`stopped_invalid`).

- **Up to the end of the headers**, this is asyncHttpParseHExt's argument
  (`parse_headers_bad_ext`, `split_path_append`, the prefix lemmas). Those
  theorems are exported, so they are reused, not redone. The new part is
  the method prefix (`"GET "`/`"POST "`).
- **The new case** is an invalid *header block*: `HDone hs rest` with a
  Transfer-Encoding header, duplicate Content-Length headers, or a
  non-canonical value. Extending s does not change `hs`, because `HDone`
  is stable under extension (`parse_headers_print`/`_done`). If
  `s ++ t = print_brequest r ++ rest'` for a valid r, then
  `print_brequest_unique`-style reasoning makes r's headers equal to
  `hs`, which contradicts validity.
- **Estimate:** about 250 lines, mostly case analysis like
  `parse_hrequest_invalid_ext`.

The other new proofs are ordinary:
- `parse_bprint` / `parse_bcomplete` (the body is `TAKE n` / `DROP n`;
  `framed` gives n);
- the decimal reader;
- the `Hcomplete`/`Geth`-style constructor renaming in CakeML (known from
  http-headers).

### 2.4 Estimate

| part | size | kind |
|---|---|---|
| parser + print/complete/extend/parse_all | ~450 lines | new |
| `parse_binvalid` + decimal reader | ~300 lines | new (the hardest part) |
| model server, safety bridge, socket model (`_b` copies of http-headers) | ~600 lines | mechanical |
| CakeML translation, code, CF specs, main, semantics (`_b` copies) | ~700 lines | mechanical, plus translator quirks |
| machine, drain, socket-level liveness, `http_prog_b_spec` (`_b` copies of http-liveness-h) | ~1,700 lines | mechanical |

That is roughly 3–4 worker-days in total, with the parser being 1 day and
the rest mostly porting. The dominant risk is build time and memory: the
machine is at its limit, so I use `-j1`. The proof structure is not a
risk.

## 3. Assumptions made

1. **The Content-Length value must be canonical decimal** (as
   `num_to_dec_string` prints it: no leading zeros, no whitespace).
   Simplest for a printer-based spec; a value like `007` makes the request
   invalid.
2. **GET may carry a framed body**, which is consumed and ignored.
3. **Any Transfer-Encoding header** (chunked or not) makes the request
   invalid.
4. **POST /echo returns the body**; any other POST path gets 404. This is
   cheap: the response is computed from the parsed request, and it makes
   a nice `curl -d` demo.
5. **Methods are GET and POST only.**
6. **Own header validity (`valid_bheader`)**: today's character rules,
   decoupled from HttpSpecHeaders' `valid_header` (spike/http-nobody
   restricts it).
7. **Copies, not generalization**, as in 24 and 26: the bodies pipeline
   is a `_b` copy with the new parser. The H and strict pipelines stay
   untouched.
