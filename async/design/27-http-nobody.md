# 27: No request bodies: HttpSpecHeaders forbids body-framing headers

Status: **done.** Branch `spike/http-nobody`, stacked on `spike/http-liveness`.
This is a user-approved spec change, relayed by the coordinator.

## The problem

`valid_header` accepted names such as `Content-Length` and
`Transfer-Encoding`, but the grammar has no request bodies. Take a client
that sends `Content-Length: n` followed by n body bytes. The spec read
those body bytes as the start of the next request, and liveness then
obliged the server to answer them. So an RFC-conforming server (one that
frames the body) could not satisfy `http_live_h`. Behind a proxy, our
server would also disagree with the proxy about where requests end, which
is a request-smuggling-shaped gap.

## The change (spec, verbatim)

```
(* Header names that frame a request body.  This subset has NO request
   bodies, so a request carrying one of these headers is not a valid
   request: otherwise its body bytes would be read as the start of the
   next request, and liveness would oblige the server to answer them.
   Header names are case-insensitive (RFC 9110, section 5.1), so they are
   compared after ASCII lowercasing. *)
Definition body_header_def:
  body_header n ⇔
    MAP toLower n = "content-length" ∨ MAP toLower n = "transfer-encoding"
End

Definition valid_header_def:
  valid_header (n, v) ⇔
    n ≠ [] ∧ EVERY (λc. c ≠ #":" ∧ c ≠ #" " ∧ c ≠ #"\r" ∧ c ≠ #"\n") n ∧
    ¬body_header n ∧
    EVERY (λc. c ≠ #"\r" ∧ c ≠ #"\n") v
End
```

A request carrying such a header is no longer a valid request. Safety then
forbids answering it, exactly as the strict HttpSpec already does for any
header.

## Bites (HttpSpecHeadersBite)

- `body_headers_invalid`: `Content-Length` and `Transfer-Encoding` are
  rejected in any letter case; `Host` and `Content-Type` are accepted.
- `broken_answers_body_request`: a server that answers
  `GET /a HTTP/1.1\r\nContent-Length: 0\r\n\r\n` violates `http_safe_h`.
  The proof shows that no valid request is a prefix of those bytes.
- `curl_request` (unchanged) still holds: curl sends no body headers on GET.

## The program

- The parser (`asyncHttpParseH`, cf-actions') gets one more `HBad` case
  in `parse_headers`: `else if body_header n then HBad`, after the header
  name is complete.
- `parse_headers_print`/`parse_headers_done` are re-proved; one local
  lemma gained the hypothesis `¬body_header n`.
- The translation (`asyncHttpSockProgH`) also translates `isUpper`,
  `toLower` (its side condition `ORD c + 32 < 256` holds on upper-case
  letters: `tolower_side_proof`) and `body_header`.
- Re-proved without other changes: `http_semantics_prog_headers`,
  `http_prog_h_safe`, and the liveness chain (`asyncHttpParseHExt`'s
  extension lemma still goes through) up to
  `http_prog_h_spec : ⊢ http_spec_h 3w demo_files http_prog_h`.

## Runnable

`http_server_h.sexp` is re-exported, compiled with the CakeML release
compiler (`make`), and demoed (`make demo`,
`http-headers-demo-transcript.txt`). The plain-curl requests behave as
before. A new demo step sends `Content-Length: 5` plus a 5-byte body and
gets no response. Checked by hand: lowercase `transfer-encoding: chunked`
also gets no response, and `Content-Type: text/plain` is answered.

## Assumptions made

1. **Case-insensitivity via ASCII lowercasing**: HOL's `toLower`
   (`stringTheory`) maps A–Z to a–z and leaves every other character
   alone. The names are compared after `MAP toLower`.
2. **Exactly two names**: `Content-Length` and `Transfer-Encoding`, the
   two body-framing headers in HTTP/1.1. Other headers are unaffected.
3. **A request with such a header is invalid**, not "ignored with the
   body skipped". This is the simplest honest choice, since the subset
   has no bodies, and it matches the strict spec's behaviour on any
   header.
