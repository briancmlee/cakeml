# RFC 9112 request framing: an independent reference and its agreement with HttpSpec

> **In this repository (`async/spec-rfc/`).** Imported from spec review 2 and stated
> against the REAL `HttpSpec`, which now has the tchar fix and the RFC
> character sets (H-CHARS):
> - `rfc9112FramingScript.sml`: unchanged. It is the trusted reference, and every
>   clause cites the RFC.
> - `HttpSpecBodiesTcharScript.sml`: now a small shim. It keeps the names
>   `valid_brequest_t` and `valid_bheader_t` that `rfcAgree` uses, defined on the
>   real spec, and proves `valid_brequest_t_eq : valid_brequest_t r ⇔ valid_brequest r`.
> - `rfcAgreeScript.sml`: as written, with three changes:
>   - `tchar_is_tchar` is re-proved for the real `tchar`;
>   - a local `valid_bheader_exp` stands in for the review copy's `valid_bheader_def`;
>   - `uri_char_is_target` and `field_char_is` relate our character sets to the
>     RFC's.
>
>   The examples `tab_path_valid_but_not_rfc` and `nul_value_valid_but_not_rfc` are
>   removed: since H-CHARS, those requests are not valid (`rfc_chars_bites`).
> - `rfcAgreeValidScript.sml` (new): `valid_rfc_chars : valid_brequest r ⇒ rfc_chars r`.
>   It also gives `rfc_frames_exactly_valid`, `rfc_frames_list_exactly_valid` and
>   `rfc_octets_frames_exactly_valid`, the agreement for EVERY valid request with no
>   side condition.
> - The build directory here is `async/spec-rfc` (INCLUDES `../ffi-spike ../spec`).

I wrote the reference (`rfc9112FramingScript.sml`) from the text of RFC 9112 and the parts of
RFC 9110 it uses. It imports nothing from the project's specifications, and every clause cites
its section. `HttpSpecBodiesTcharScript.sml` is HttpSpec with the agreed tchar fix
(header names are RFC tokens). `rfcAgreeScript.sml` proves that the two agree and
characterises exactly where they differ.

All three theories build with `holslot timeout 3000 arch -arm64 Holmake -j1` in
`~/Programming/cakeml-worktrees/spec-review-2/async/rfc`. The Holmakefile has INCLUDES
`../world/sockets ../spec`, and the worktree is based on origin/spike/quiet-spec, whose
HttpSpec is byte-identical to origin/review/01-spec. A grep finds no `cheat`, `mk_thm`
or `new_axiom`.

## The reference (theory `rfc9112Framing`)

| RFC | Modelled as |
|---|---|
| 9112 §2.1 message | `start-line CRLF *(field-line CRLF) CRLF body` (`rfc_request_lines`) |
| 9112 §2.2 line ends | CRLF only. CHOICE: no bare-LF lines (RFC: MAY accept); no leading empty lines (RFC: SHOULD skip one); a bare CR makes the message invalid (allowed) |
| 9112 §2.3 version | `HTTP/` DIGIT `.` DIGIT |
| 9112 §3 request-line | method SP request-target SP HTTP-version; method = token (9110 §9.1) |
| 9112 §3.2 request-target | CHOICE: only the characters are checked (RFC 3986 §2 reserved/unreserved/`%`, no `#`). Which form (origin, absolute, ...) is not checked, since framing does not depend on it |
| 9112 §5, 9110 §5.1/§5.5 field line | name = token; value = text after the first colon with leading/trailing OWS removed; characters VCHAR / obs-text / SP / HTAB; case-insensitive names (ASCII lowercase). An obs-fold line has no token name, so it is invalid (allowed by §5.2) |
| 9112 §6.3 body length | rules 3/4: Transfer-Encoding overrides Content-Length; chunked final coding gives `Chunked` (CHOICE: chunked bodies are not parsed, so no message is framed), anything else is `Invalid`. Rule 5: an invalid value or several Content-Length fields give `Invalid` (CHOICE: 9110 §8.6 lets a recipient accept identical duplicates; the reference rejects them). Rule 6: a valid Content-Length gives the length. Rule 7: no field means length 0 |

`rfc_request s m rest` holds when the stream `s` starts with request message `m`, followed by
`rest`. `rfc_requests` is the list version, and `rfc_requests_octets` works on `word8` lists.

Proved about the reference:
- `rfc_request_unique`: the framing is a function. A stream starts with at most one message.
- `rfc_requests_unique`: the same for lists.

## Agreement (theory `rfcAgree`)

`reading (Req m p ver hs b)` is how the RFC reads one of our requests: the same method,
target, version and body, and the header values with surrounding OWS stripped.
`rfc_chars r` says that the target's and header values' characters are ones the RFC allows.

MAIN theorems:
- **`rfc_frames_exactly`**: `valid_brequest_t r ∧ rfc_chars r ⇒
  (rfc_request (print_brequest r ++ rest) m rest' ⇔ m = reading r ∧ rest' = rest)`.
- **`rfc_frames_list_exactly`**: the same for lists, and **`rfc_octets_frames_exactly`** on the
  wire. For every list `rs` of such requests and any `rest`, the RFC framing of
  `brequests rs ++ rest` splits off exactly `rs`: same boundaries, same bodies, followed by
  that `rest`.
- **`reading_agrees`**: the RFC's reading has our method, target, version, body and header
  names. Its Content-Length values are exactly our `FILTER is_cl hs` values, and
  `body_framing` gives `Length (LENGTH b)`.

Where we are **looser** than the RFC, which is a new finding (H-CHARS):
- **`rfc_rejects_unclean`**: `valid_brequest_t r ∧ rfc_request (print_brequest r ++ z) m rest ⇒ rfc_chars r`.
  If a valid request has a target character outside the URI set, or a header-value character
  outside VCHAR/obs-text/SP/HTAB, the RFC frames no message at all.
- Examples: `tab_path_valid_but_not_rfc` (path `/a<TAB>b`) and `nul_value_valid_but_not_rfc`
  (header value NUL). Both are valid for us, and RFC 9110 §5.5 requires a recipient of NUL in a
  value to reject or replace it. Our liveness forces a 200/404 answer instead. Boundaries never
  disagree here, since CR and LF are already excluded, so this is a compliance gap, not a
  smuggling vector.
- Suggested fix: `valid_path` characters = RFC 3986 characters (or at least VCHAR), and header
  value characters = VCHAR / obs-text / SP / HTAB. With that fix, `rfc_chars` follows from
  validity and the agreement theorems hold for every valid request.

Where we are **stricter** than the RFC (acceptable; characterised exactly):
- **`rfc_subset_exact`**: a stream starts with one of our requests, read as ours, **iff** the RFC
  frames it with a message such that `subset_ok`:
  - the method is GET or POST, and the version is 1.0 or 1.1;
  - every field line has a SP right after the colon (`Host:x` is RFC-valid but not ours);
  - the raw Content-Length value is canonical decimal after that SP: no leading zeros
    (`Content-Length: 05`) and no trailing OWS (`Content-Length: 5 `).
- Example: `host_no_space_rfc` / `host_no_space_not_ours`.
- Also stricter, by the reference's CHOICEs above (not separate theorems): chunked bodies,
  identical duplicate Content-Length fields, bare-LF line ends and leading empty lines are
  accepted by lenient RFC recipients and rejected by us. Rejecting them is RFC-conformant.

## Not modelled
- Request-target form validity (origin-form must start with `/`, asterisk-form only with
  OPTIONS, and so on): our `GET a HTTP/1.1` is accepted by both the reference and us, but the
  RFC would reject it. This does not affect framing.
- The HTTP/1.1 `Host` requirement (9112 §3.2): semantics, not framing.
- Chunked transfer coding (§7.1).
