(*
  rfcAgreeValid: the agreement theorems of rfcAgree for EVERY valid request
  of HttpSpec, with no extra hypothesis.  Since HttpSpec'
  RFC character sets (uri_char for paths, field_char for header values),
  every valid request has the characters the RFC allows (valid_rfc_chars),
  so "our subset frames like real HTTP" holds without side conditions.
*)
Theory rfcAgreeValid
Ancestors
  rfc9112Framing rfcAgree HttpSpecRfcNames HttpSpec HttpHeadersSpec
  HttpGetSpec
Libs
  preamble

(* Valid requests use only characters the RFC allows *)
Theorem valid_rfc_chars:
  valid_brequest r ⇒ rfc_chars r
Proof
  Cases_on ‘r’ >>
  rw[valid_brequest_def, rfc_chars_def, EVERY_MEM, FORALL_PROD] >>
  res_tac >> fs[valid_bheader_def, EVERY_MEM, uri_char_is_target, field_char_is]
QED

(* MAIN: the RFC frames a printed valid request followed by anything as
   exactly that request, read as ours *)
Theorem rfc_frames_exactly_valid:
  valid_brequest r ⇒
  (rfc_request (print_brequest r ++ rest) m rest' ⇔
   m = reading r ∧ rest' = rest)
Proof
  strip_tac >> irule rfc_frames_exactly >>
  simp[valid_brequest_t_eq, valid_rfc_chars]
QED

Theorem every_valid_t[local]:
  EVERY valid_brequest rs ⇒ EVERY (λr. valid_brequest_t r ∧ rfc_chars r) rs
Proof
  rw[EVERY_MEM, valid_brequest_t_eq, valid_rfc_chars]
QED

(* MAIN: the RFC splits printed valid requests rs, followed by any rest,
   into exactly rs (read as ours) and that rest *)
Theorem rfc_frames_list_exactly_valid:
  EVERY valid_brequest rs ⇒
  (rfc_requests (FLAT (MAP print_brequest rs) ++ rest) ms rest' ∧
   LENGTH ms = LENGTH rs ⇔
   ms = MAP reading rs ∧ rest' = rest)
Proof
  strip_tac >> irule rfc_frames_list_exactly >> simp[every_valid_t]
QED

(* MAIN (on the wire): the same for brequests, on octets *)
Theorem rfc_octets_frames_exactly_valid:
  EVERY valid_brequest rs ⇒
  (rfc_requests_octets (brequests rs ++ rest) ms rest' ∧
   LENGTH ms = LENGTH rs ⇔
   ms = MAP reading rs ∧ rest' = rest)
Proof
  strip_tac >> irule rfc_octets_frames_exactly >> simp[every_valid_t]
QED
