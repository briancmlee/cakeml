(*
  An independent reference for HTTP/1.1 REQUEST FRAMING, transcribed from
  RFC 9112 (HTTP/1.1) and the parts of RFC 9110 (HTTP Semantics) it uses.
  Written from the RFC text only: it imports nothing of the project's
  specifications.

  Scope: where a request message starts and ends in a byte stream, and how
  its request line, field lines and body are read.  Choices where the RFC
  leaves the recipient a choice (each a MAY or SHOULD) are marked CHOICE.

  - §2.1  HTTP-message = start-line CRLF *( field-line CRLF ) CRLF [ message-body ]
  - §2.2  line terminator: CRLF only.  CHOICE: no bare-LF terminators (a
          recipient MAY accept them), no empty lines before the request line
          (a server SHOULD skip at least one), a bare CR makes the message
          invalid (allowed: "MUST either treat as invalid or replace").
  - §2.3  HTTP-version = "HTTP/" DIGIT "." DIGIT
  - §3    request-line = method SP request-target SP HTTP-version,
          method = token (RFC 9110 §9.1)
  - §3.2  request-target: CHOICE: only its CHARACTERS are checked (those of
          RFC 3986 §2, minus "#": a target has no fragment).  Which form
          (origin-form "/...", absolute-form, ...) it has does not affect
          framing and is not checked.
  - §5    field-line = field-name ":" OWS field-value OWS, field-name =
          token (RFC 9110 §5.1), field-value = *field-content (RFC 9110 §5.5,
          characters VCHAR / obs-text / SP / HTAB).  §5.1: the value read is
          the text after the colon without leading and trailing OWS.
          Field names are case-insensitive (RFC 9110 §5.1), compared after
          ASCII lowercasing.  §5.2 obs-fold: a line starting with SP/HTAB has
          no token name, so the message is invalid (the RFC allows rejecting).
  - §6.3  the body length of a REQUEST:
          rule 3/4: Transfer-Encoding present: it overrides Content-Length;
            the body is chunked if chunked is the final coding, otherwise
            the request is invalid (400).  CHOICE: chunked bodies are NOT
            parsed here: such a message is classified Chunked and no request
            is framed (a reference "unsupported").
          rule 5: an invalid Content-Length (not 1*DIGIT, RFC 9110 §8.6) or
            several Content-Length fields: invalid.  CHOICE: RFC 9110 §8.6
            lets a recipient accept duplicates with identical values; here
            they are rejected.
          rule 6: a valid Content-Length gives the body length.
          rule 7: neither field: the body is empty.
*)
Theory rfc9112Framing
Ancestors
  string list rich_list ASCIInumbers words
Libs
  preamble

(* ------------------------------------------------------------------------
   Characters: RFC 5234 Appendix B.1 core rules, RFC 9110 §5.6
   ------------------------------------------------------------------------ *)

Definition is_digit_def:
  is_digit (c:char) ⇔ 48 ≤ ORD c ∧ ORD c ≤ 57          (* %x30-39 *)
End

Definition is_alpha_def:
  is_alpha (c:char) ⇔ (65 ≤ ORD c ∧ ORD c ≤ 90) ∨ (97 ≤ ORD c ∧ ORD c ≤ 122)
End

Definition is_vchar_def:
  is_vchar (c:char) ⇔ 33 ≤ ORD c ∧ ORD c ≤ 126         (* %x21-7E *)
End

(* RFC 9110 §5.6.3: OWS = *( SP / HTAB ) *)
Definition is_ows_def:
  is_ows c ⇔ c = #" " ∨ c = #"\t"
End

(* RFC 9110 §5.6.2: tchar, token = 1*tchar *)
Definition is_tchar_def:
  is_tchar c ⇔ MEM c "!#$%&'*+-.^_`|~" ∨ is_digit c ∨ is_alpha c
End

Definition is_token_def:
  is_token s ⇔ s ≠ [] ∧ EVERY is_tchar s
End

(* RFC 9110 §5.5: field-vchar = VCHAR / obs-text, obs-text = %x80-FF *)
Definition is_field_vchar_def:
  is_field_vchar c ⇔ is_vchar c ∨ 128 ≤ ORD c
End

(* RFC 3986 §2.2-2.3 (reserved, unreserved) and "%" (§2.1), without "#" *)
Definition is_target_char_def:
  is_target_char c ⇔ is_alpha c ∨ is_digit c ∨ MEM c "-._~:/?[]@!$&'()*+,;=%"
End

(* RFC 9110 §5.1: field names are case-insensitive (ASCII) *)
Definition lower_def:
  lower c = if 65 ≤ ORD c ∧ ORD c ≤ 90 then CHR (ORD c + 32) else c
End

(* ------------------------------------------------------------------------
   The request line (§3) and field lines (§5)
   ------------------------------------------------------------------------ *)

(* §2.3: the "x.y" of HTTP-version = "HTTP/" DIGIT "." DIGIT *)
Definition version_ok_def:
  version_ok v ⇔ ∃a b. v = [a; #"."; b] ∧ is_digit a ∧ is_digit b
End

Definition target_ok_def:
  target_ok t ⇔ t ≠ [] ∧ EVERY is_target_char t
End

(* A field line: the name is the text before the first colon, the raw
   value the text after it; the value read is the raw value without
   leading and trailing OWS (§5.1) *)
Definition fname_def:
  fname [] = [] ∧
  fname (c :: cs) = if c = #":" then [] else c :: fname cs
End

Definition fraw_def:
  fraw [] = [] ∧
  fraw (c :: cs) = if c = #":" then cs else fraw cs
End

Definition strip_ows_def:
  strip_ows s = REVERSE (dropWhile is_ows (REVERSE (dropWhile is_ows s)))
End

(* §5: field-line = field-name ":" OWS field-value OWS *)
Definition field_line_ok_def:
  field_line_ok l ⇔
    MEM #":" l ∧ is_token (fname l) ∧
    EVERY (λc. is_field_vchar c ∨ is_ows c) (fraw l)
End

Definition field_of_def:
  field_of l = (fname l, strip_ows (fraw l))
End

(* ------------------------------------------------------------------------
   The body length (§6.3)
   ------------------------------------------------------------------------ *)

Datatype:
  framing = Length num | Chunked | Invalid
End

Definition values_named_def:
  values_named nm (fs : (string # string) list) =
    MAP SND (FILTER (λ(n, v). MAP lower n = nm) fs)
End

(* §6.3 rule 4, RFC 9112 §7: chunked is the final transfer coding of the
   (combined, comma-separated) Transfer-Encoding list *)
Definition final_chunked_def:
  final_chunked vs ⇔
    vs ≠ [] ∧
    ∃pre. MAP lower (LAST vs) = pre ++ "chunked" ∧
          (pre = [] ∨ ∃p w. pre = p ++ "," ++ w ∧ EVERY is_ows w)
End

Definition body_framing_def:
  body_framing fs =
    if values_named "transfer-encoding" fs ≠ [] then         (* rules 3, 4 *)
      (if final_chunked (values_named "transfer-encoding" fs)
       then Chunked else Invalid)
    else
      case values_named "content-length" fs of
      | [] => Length 0                                          (* rule 7 *)
      | [v] => if v ≠ [] ∧ EVERY is_digit v                     (* rule 6 *)
               then Length (num_from_dec_string v) else Invalid (* rule 5 *)
      | _ => Invalid                                     (* rule 5, CHOICE *)
End

(* ------------------------------------------------------------------------
   Request messages (§2.1)
   ------------------------------------------------------------------------ *)

Datatype:
  rfc_req = <| meth : string; target : string; version : string;
               fields : (string # string) list; body : string |>
End

Definition crlf_lines_def:
  crlf_lines [] = "" ∧
  crlf_lines (l :: ls) = l ++ "\r\n" ++ crlf_lines ls
End

(* s starts with the request message m, framed by Content-Length (or with
   no body), with field lines ls; rest follows it *)
Definition rfc_request_lines_def:
  rfc_request_lines s ls m rest ⇔
    s = m.meth ++ " " ++ m.target ++ " HTTP/" ++ m.version ++ "\r\n" ++
        crlf_lines ls ++ "\r\n" ++ m.body ++ rest ∧
    is_token m.meth ∧ target_ok m.target ∧ version_ok m.version ∧
    EVERY field_line_ok ls ∧ m.fields = MAP field_of ls ∧
    body_framing m.fields = Length (LENGTH m.body)
End

Definition rfc_request_def:
  rfc_request s m rest ⇔ ∃ls. rfc_request_lines s ls m rest
End

(* s starts with the request messages ms, in order; rest follows them *)
Definition rfc_requests_def:
  rfc_requests s [] rest = (rest = s) ∧
  rfc_requests s (m :: ms) rest = ∃s1. rfc_request s m s1 ∧ rfc_requests s1 ms rest
End

(* The same on octets *)
Definition octets_def:
  octets (ws : 8 word list) = MAP (CHR o w2n) ws
End

Definition rfc_requests_octets_def:
  rfc_requests_octets ws ms rest ⇔ rfc_requests (octets ws) ms (octets rest)
End

(* ------------------------------------------------------------------------
   The framing is a function: at most one way to read a message
   ------------------------------------------------------------------------ *)

Theorem split_sep:
  ∀a b x y c. ¬MEM c a ∧ ¬MEM c b ∧ a ++ c :: x = b ++ c :: y ⇒ a = b ∧ x = y
Proof
  Induct >> Cases_on ‘b’ >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem split_crlf:
  ¬MEM #"\r" a ∧ ¬MEM #"\r" b ∧ a ++ "\r\n" ++ x = b ++ "\r\n" ++ y ⇒
  a = b ∧ x = y
Proof
  strip_tac >>
  ‘a ++ #"\r" :: (#"\n" :: x) = b ++ #"\r" :: (#"\n" :: y)’
    by fs[] >>
  drule_all split_sep >> simp[]
QED

Theorem lines_unique:
  ∀ls1 ls2 x y.
    EVERY (λl. l ≠ [] ∧ ¬MEM #"\r" l) ls1 ∧
    EVERY (λl. l ≠ [] ∧ ¬MEM #"\r" l) ls2 ∧
    crlf_lines ls1 ++ "\r\n" ++ x = crlf_lines ls2 ++ "\r\n" ++ y ⇒
    ls1 = ls2 ∧ x = y
Proof
  Induct >> Cases_on ‘ls2’ >> simp[crlf_lines_def] >> rpt gen_tac >> strip_tac >>
  TRY (Cases_on ‘h’ >> gvs[] >> NO_TAC) >>
  qpat_x_assum ‘_ = _’ (assume_tac o REWRITE_RULE[GSYM APPEND_ASSOC]) >>
  drule_at (Pos last) (REWRITE_RULE[GSYM APPEND_ASSOC] split_crlf) >>
  impl_tac >- fs[] >> strip_tac >> gvs[] >>
  first_x_assum irule >> fs[]
QED

Theorem token_no_sep:
  is_token s ⇒ ¬MEM #"\r" s ∧ ¬MEM #" " s ∧ ¬MEM #":" s ∧ s ≠ []
Proof
  rw[is_token_def, EVERY_MEM] >> strip_tac >> res_tac >>
  gvs[is_tchar_def, is_digit_def, is_alpha_def]
QED

Theorem target_no_sep:
  target_ok t ⇒ ¬MEM #"\r" t ∧ ¬MEM #" " t
Proof
  rw[target_ok_def, EVERY_MEM] >> strip_tac >> res_tac >>
  gvs[is_target_char_def, is_digit_def, is_alpha_def]
QED

Theorem split_colon:
  ∀l. MEM #":" l ⇒ l = fname l ++ #":" :: fraw l
Proof
  Induct >> rw[fname_def, fraw_def] >> gvs[fname_def, fraw_def]
QED

Theorem field_line_shape:
  field_line_ok l ⇒ l ≠ [] ∧ ¬MEM #"\r" l
Proof
  strip_tac >> fs[field_line_ok_def] >>
  ‘l = fname l ++ #":" :: fraw l’ by simp[split_colon] >>
  drule token_no_sep >> strip_tac >>
  pop_assum mp_tac >> pop_assum mp_tac >>
  ‘¬MEM #"\r" (fraw l)’
    by (fs[EVERY_MEM] >> strip_tac >> res_tac >>
        gvs[is_field_vchar_def, is_vchar_def, is_ows_def]) >>
  ntac 2 strip_tac >> ONCE_ASM_REWRITE_TAC[] >> simp[]
QED

Theorem request_line_no_cr:
  is_token m ∧ target_ok t ∧ version_ok v ⇒
  ¬MEM #"\r" (m ++ " " ++ t ++ " HTTP/" ++ v)
Proof
  rw[version_ok_def] >> imp_res_tac token_no_sep >> imp_res_tac target_no_sep >>
  simp[] >> gvs[is_digit_def] >> rpt strip_tac >> gvs[]
QED

(* The request line splits in only one way *)
Theorem request_line_unique:
  is_token m1 ∧ target_ok t1 ∧ is_token m2 ∧ target_ok t2 ∧
  m1 ++ " " ++ t1 ++ " HTTP/" ++ v1 = m2 ++ " " ++ t2 ++ " HTTP/" ++ v2 ⇒
  m1 = m2 ∧ t1 = t2 ∧ v1 = v2
Proof
  strip_tac >> imp_res_tac token_no_sep >> imp_res_tac target_no_sep >>
  ‘m1 = m2 ∧ t1 ++ #" " :: ("HTTP/" ++ v1) = t2 ++ #" " :: ("HTTP/" ++ v2)’
    by (irule split_sep >> qexists_tac ‘#" "’ >> fs[]) >>
  ‘t1 = t2 ∧ "HTTP/" ++ v1 = "HTTP/" ++ v2’
    by (irule split_sep >> qexists_tac ‘#" "’ >> fs[]) >>
  fs[]
QED

Theorem rfc_request_lines_unique:
  rfc_request_lines s ls1 m1 r1 ∧ rfc_request_lines s ls2 m2 r2 ⇒
  m1 = m2 ∧ r1 = r2 ∧ ls1 = ls2
Proof
  REWRITE_TAC[rfc_request_lines_def] >> strip_tac >>
  ‘¬MEM #"\r" (m1.meth ++ " " ++ m1.target ++ " HTTP/" ++ m1.version) ∧
   ¬MEM #"\r" (m2.meth ++ " " ++ m2.target ++ " HTTP/" ++ m2.version)’
    by simp[request_line_no_cr] >>
  ‘m1.meth ++ " " ++ m1.target ++ " HTTP/" ++ m1.version =
     m2.meth ++ " " ++ m2.target ++ " HTTP/" ++ m2.version ∧
   crlf_lines ls1 ++ "\r\n" ++ m1.body ++ r1 =
     crlf_lines ls2 ++ "\r\n" ++ m2.body ++ r2’
    by (irule split_crlf >> rpt conj_tac >- fs[] >- fs[] >>
        qpat_x_assum ‘s = _’ mp_tac >> qpat_x_assum ‘s = _’ mp_tac >>
        REWRITE_TAC[GSYM APPEND_ASSOC] >> rpt strip_tac >> fs[]) >>
  ‘m1.meth = m2.meth ∧ m1.target = m2.target ∧ m1.version = m2.version’
    by (irule request_line_unique >> fs[]) >>
  ‘EVERY (λl. l ≠ [] ∧ ¬MEM #"\r" l) ls1 ∧ EVERY (λl. l ≠ [] ∧ ¬MEM #"\r" l) ls2’
    by (fs[EVERY_MEM] >> metis_tac[field_line_shape]) >>
  ‘ls1 = ls2 ∧ m1.body ++ r1 = m2.body ++ r2’
    by (irule lines_unique >> fs[] >>
        qpat_x_assum ‘crlf_lines _ ++ _ = _’ mp_tac >>
        REWRITE_TAC[GSYM APPEND_ASSOC] >> disch_then ACCEPT_TAC) >>
  ‘m1.fields = m2.fields’ by fs[] >>
  ‘LENGTH m1.body = LENGTH m2.body’ by (fs[] >> rfs[]) >>
  ‘m1.body = m2.body ∧ r1 = r2’ by metis_tac[APPEND_11_LENGTH] >>
  fs[theorem "rfc_req_component_equality"]
QED

(* MAIN (determinism): a stream starts with at most one request message *)
Theorem rfc_request_unique:
  rfc_request s m1 r1 ∧ rfc_request s m2 r2 ⇒ m1 = m2 ∧ r1 = r2
Proof
  rw[rfc_request_def] >> metis_tac[rfc_request_lines_unique]
QED

Theorem rfc_requests_unique:
  ∀ms1 ms2 s r1 r2.
    rfc_requests s ms1 r1 ∧ rfc_requests s ms2 r2 ∧ LENGTH ms1 = LENGTH ms2 ⇒
    ms1 = ms2 ∧ r1 = r2
Proof
  Induct >> Cases_on ‘ms2’ >> simp[rfc_requests_def] >> rpt gen_tac >>
  strip_tac >> ‘h' = h ∧ s1' = s1’ by metis_tac[rfc_request_unique] >>
  gvs[] >> metis_tac[]
QED
