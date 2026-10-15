(*
  FRAMING AGREEMENT between HttpSpecBodies (with the tchar fix,
  HttpSpecBodiesTchar) and the independent RFC 9112 reference
  (rfc9112Framing).

  MAIN results:
  - rfc_frames_exactly / rfc_frames_list_exactly / rfc_octets_frames_exactly:
    for valid requests whose characters the RFC allows (rfc_chars), the
    RFC framing of the printed requests followed by ANY rest splits off
    exactly those requests (same boundaries, same bodies), and reads each
    as ours: same method, target, version, body, header names, header
    values up to surrounding OWS, Content-Length.
  - rfc_rejects_unclean (FINDING H-CHARS): a valid request whose target or
    header values contain characters the RFC forbids is not an RFC message
    at all.  Since the fix, valid requests have no such characters
    (rfcAgreeValid.valid_rfc_chars), so this is now a consistency check.
  - rfc_subset_exact: our subset is EXACTLY the RFC messages with method
    GET/POST, version 1.0/1.1, a space right after every field colon, and
    a canonical Content-Length value (no leading zeros, no OWS); in
    particular we are stricter than the RFC on those points (example
    host_no_space_rfc, host_no_space_not_ours).
*)
Theory rfcAgree
Ancestors
  rfc9112Framing HttpSpecBodiesTchar HttpSpecBodies HttpSpecHeaders HttpSpec
  ASCIInumbers words
Libs
  preamble

(* ------------------------------------------------------------------------
   How the RFC reads one of our requests
   ------------------------------------------------------------------------ *)

Definition reading_def:
  reading (Req m p ver hs b) =
    <| meth := m; target := p; version := ver;
       fields := MAP (λ(n, v). (n, strip_ows v)) hs; body := b |>
End

Definition our_lines_def:
  our_lines hs = MAP (λ(n, v). n ++ ": " ++ v) hs
End

(* The characters the RFC allows in a target and in a field value *)
Definition rfc_chars_def:
  rfc_chars (Req m p ver hs b) ⇔
    EVERY is_target_char p ∧
    EVERY (λh. EVERY (λc. is_field_vchar c ∨ is_ows c) (SND h)) hs
End

(* ------------------------------------------------------------------------
   Lemmas
   ------------------------------------------------------------------------ *)

Theorem print_brequest_lines:
  print_brequest (Req m p ver hs b) =
    m ++ " " ++ p ++ " HTTP/" ++ ver ++ "\r\n" ++ crlf_lines (our_lines hs) ++
    "\r\n" ++ b
Proof
  ‘FLAT (MAP print_header hs) = crlf_lines (our_lines hs)’
    by (Induct_on ‘hs’ >> simp[our_lines_def, crlf_lines_def] >>
        Cases >> fs[print_header_def, our_lines_def]) >>
  simp[print_brequest_def]
QED

(* valid_bheader, with the character facts it implies (the review's copy
   of HttpSpecBodies stated these directly) *)
Theorem valid_bheader_exp[local]:
  valid_bheader (n, v) ⇔
    n ≠ [] ∧ EVERY tchar n ∧ EVERY field_char v ∧
    EVERY (λc. c ≠ #":" ∧ c ≠ #" " ∧ c ≠ #"\r" ∧ c ≠ #"\n") n ∧
    EVERY (λc. c ≠ #"\r" ∧ c ≠ #"\n") v
Proof
  eq_tac >> strip_tac >- (drule valid_bheader_chars >> fs[valid_bheader_def]) >>
  fs[valid_bheader_def]
QED

Theorem uri_char_is_target:
  uri_char c ⇔ is_target_char c
Proof
  simp[uri_char_def, is_target_char_def, isAlpha_def, isLower_def, isUpper_def,
       isDigit_def, is_digit_def, is_alpha_def] >> metis_tac[]
QED

Theorem field_char_is:
  field_char c ⇔ is_field_vchar c ∨ is_ows c
Proof
  simp[field_char_def, is_field_vchar_def, is_vchar_def, is_ows_def] >>
  metis_tac[]
QED

Theorem tchar_is_tchar:
  tchar c ⇔ is_tchar c
Proof
  simp[tchar_def, is_tchar_def, isAlpha_def, isLower_def, isUpper_def,
       isDigit_def, is_digit_def, is_alpha_def] >> metis_tac[]
QED

Theorem lower_toLower:
  lower = toLower
Proof
  simp[FUN_EQ_THM, lower_def, toLower_def, isUpper_def]
QED

Theorem is_digit_isDigit:
  is_digit = isDigit
Proof
  simp[FUN_EQ_THM, is_digit_def, isDigit_def]
QED

Theorem fname_fraw_line:
  ∀n. ¬MEM #":" n ⇒
      fname (n ++ ":" ++ s) = n ∧ fraw (n ++ ":" ++ s) = s ∧
      fname (n ++ ": " ++ v) = n ∧ fraw (n ++ ": " ++ v) = #" " :: v
Proof
  Induct >> fs[fname_def, fraw_def]
QED

Theorem strip_ows_space:
  strip_ows (#" " :: v) = strip_ows v
Proof
  simp[strip_ows_def, is_ows_def]
QED

Theorem dropWhile_none[local]:
  ∀s. EVERY (λc. ¬P c) s ⇒ dropWhile P s = s
Proof
  Cases >> simp[]
QED

Theorem strip_ows_digits:
  EVERY is_digit s ⇒ strip_ows s = s
Proof
  strip_tac >>
  ‘EVERY (λc. ¬is_ows c) s’
    by (rw[EVERY_MEM, is_ows_def] >> strip_tac >> gvs[EVERY_MEM, is_digit_def] >>
        res_tac >> fs[]) >>
  simp[strip_ows_def, dropWhile_none, EVERY_REVERSE]
QED

Theorem values_named_ours:
  ∀hs. values_named nm (MAP (λ(n, v). (n, strip_ows v)) hs) =
       MAP (λ(n, v). strip_ows v) (FILTER (λ(n, v). MAP toLower n = nm) hs)
Proof
  Induct >> simp[values_named_def] >> Cases >>
  simp[lower_toLower] >> rw[] >> fs[values_named_def, lower_toLower]
QED

Theorem filter_is_cl:
  FILTER is_cl hs = FILTER (λ(n, v). MAP toLower n = "content-length") hs
Proof
  AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM, FORALL_PROD, is_cl_def]
QED

Theorem filter_no_te:
  ∀hs. ¬EXISTS is_te hs ⇒
       FILTER (λ(n, v). MAP toLower n = "transfer-encoding") hs = []
Proof
  Induct >> simp[] >> Cases >> simp[is_te_def]
QED

Theorem body_framing_ours:
  valid_brequest (Req m p ver hs b) ⇒
  body_framing (MAP (λ(n, v). (n, strip_ows v)) hs) = Length (LENGTH b) ∧
  values_named "content-length" (MAP (λ(n, v). (n, strip_ows v)) hs) =
    MAP SND (FILTER is_cl hs)
Proof
  simp[valid_brequest_def, framed_def] >> strip_tac >>
  simp[body_framing_def, values_named_ours, filter_no_te] >>
  fs[filter_is_cl] >>
  Cases_on ‘FILTER (λ(n, v). MAP toLower n = "content-length") hs’ >> fs[] >>
  Cases_on ‘t’ >> fs[] >> PairCases_on ‘h’ >> fs[] >>
  ‘EVERY is_digit (toString (STRLEN b))’
    by simp[is_digit_isDigit, EVERY_isDigit_num_to_dec_string] >>
  simp[strip_ows_digits] >>
  simp[is_digit_isDigit, EVERY_isDigit_num_to_dec_string] >>
  assume_tac num_dec_string >> fs[FUN_EQ_THM]
QED

Theorem our_line_field:
  valid_bheader_t (n, v) ∧ EVERY (λc. is_field_vchar c ∨ is_ows c) v ⇒
  field_line_ok (n ++ ": " ++ v) ∧ field_of (n ++ ": " ++ v) = (n, strip_ows v)
Proof
  simp[valid_bheader_t_def, valid_bheader_exp] >> strip_tac >>
  ‘¬MEM #":" n’ by (fs[EVERY_MEM] >> metis_tac[]) >>
  simp[field_line_ok_def, field_of_def, fname_fraw_line, strip_ows_space,
       is_token_def, is_ows_def] >>
  fs[EVERY_MEM, tchar_is_tchar, is_ows_def]
QED

(* ------------------------------------------------------------------------
   Agreement, one request
   ------------------------------------------------------------------------ *)

Theorem rfc_agrees_lines:
  valid_brequest_t (Req m p ver hs b) ∧ rfc_chars (Req m p ver hs b) ⇒
  rfc_request_lines (print_brequest (Req m p ver hs b) ++ rest)
    (our_lines hs) (reading (Req m p ver hs b)) rest
Proof
  rw[valid_brequest_t_def, rfc_chars_def] >>
  drule body_framing_ours >> strip_tac >>
  fs[valid_brequest_def] >>
  simp[rfc_request_lines_def, reading_def, print_brequest_lines] >>
  rpt conj_tac
  >- (fs[valid_method_def] >> rw[] >> EVAL_TAC)
  >- fs[target_ok_def, valid_path_def]
  >- (qpat_x_assum ‘valid_version ver’
        (strip_assume_tac o REWRITE_RULE [valid_version_def]) >>
      gvs[version_ok_def, is_digit_def])
  >- (simp[our_lines_def, EVERY_MAP] >> fs[EVERY_MEM, FORALL_PROD] >>
      rw[] >> irule (cj 1 our_line_field) >> res_tac >> fs[EVERY_MEM])
  >- (simp[our_lines_def, MAP_MAP_o, MAP_EQ_f, FORALL_PROD] >> rw[] >>
      ONCE_REWRITE_TAC[EQ_SYM_EQ] >> irule (cj 2 our_line_field) >>
      fs[EVERY_MEM, FORALL_PROD] >> res_tac >> fs[EVERY_MEM])
QED

(* MAIN: the RFC frames a valid request followed by anything as exactly
   that request, read as ours *)
Theorem rfc_frames_exactly:
  valid_brequest_t r ∧ rfc_chars r ⇒
  (rfc_request (print_brequest r ++ rest) m rest' ⇔
   m = reading r ∧ rest' = rest)
Proof
  Cases_on ‘r’ >> strip_tac >> drule_all rfc_agrees_lines >>
  disch_then (qspec_then ‘rest’ assume_tac) >>
  eq_tac >> rw[rfc_request_def]
  >- (‘rfc_request (print_brequest (Req s s0 s1 l s2) ++ rest) m rest' ∧
       rfc_request (print_brequest (Req s s0 s1 l s2) ++ rest)
         (reading (Req s s0 s1 l s2)) rest’ by metis_tac[rfc_request_def] >>
      metis_tac[rfc_request_unique])
  >- (‘rfc_request (print_brequest (Req s s0 s1 l s2) ++ rest) m rest' ∧
       rfc_request (print_brequest (Req s s0 s1 l s2) ++ rest)
         (reading (Req s s0 s1 l s2)) rest’ by metis_tac[rfc_request_def] >>
      metis_tac[rfc_request_unique]) >>
  metis_tac[]
QED

(* MAIN: the RFC's reading agrees with ours: method, target, version,
   body, header names (values up to surrounding OWS), Content-Length *)
Theorem reading_agrees:
  valid_brequest_t (Req m p ver hs b) ⇒
  (reading (Req m p ver hs b)).meth = m ∧
  (reading (Req m p ver hs b)).target = p ∧
  (reading (Req m p ver hs b)).version = ver ∧
  (reading (Req m p ver hs b)).body = b ∧
  MAP FST (reading (Req m p ver hs b)).fields = MAP FST hs ∧
  values_named "content-length" (reading (Req m p ver hs b)).fields =
    MAP SND (FILTER is_cl hs) ∧
  body_framing (reading (Req m p ver hs b)).fields = Length (LENGTH b)
Proof
  rw[valid_brequest_t_def] >> drule body_framing_ours >>
  simp[reading_def, MAP_MAP_o, MAP_EQ_f, FORALL_PROD]
QED

(* ------------------------------------------------------------------------
   Agreement, lists of requests, and octets
   ------------------------------------------------------------------------ *)

Theorem rfc_frames_list:
  ∀rs rest.
    EVERY (λr. valid_brequest_t r ∧ rfc_chars r) rs ⇒
    rfc_requests (FLAT (MAP print_brequest rs) ++ rest) (MAP reading rs) rest
Proof
  Induct >> simp[rfc_requests_def] >> rpt strip_tac >>
  qexists_tac ‘FLAT (MAP print_brequest rs) ++ rest’ >> simp[] >>
  ‘print_brequest h ++ FLAT (MAP print_brequest rs) ++ rest =
   print_brequest h ++ (FLAT (MAP print_brequest rs) ++ rest)’ by simp[] >>
  metis_tac[rfc_frames_exactly]
QED

(* MAIN: the RFC splits printed valid requests rs followed by any rest
   into exactly rs (read as ours) and that rest *)
Theorem rfc_frames_list_exactly:
  EVERY (λr. valid_brequest_t r ∧ rfc_chars r) rs ⇒
  (rfc_requests (FLAT (MAP print_brequest rs) ++ rest) ms rest' ∧
   LENGTH ms = LENGTH rs ⇔
   ms = MAP reading rs ∧ rest' = rest)
Proof
  strip_tac >> drule rfc_frames_list >> disch_then (qspec_then ‘rest’ assume_tac) >>
  eq_tac >> rw[] >> metis_tac[rfc_requests_unique, LENGTH_MAP]
QED

Theorem octets_bytes:
  octets (bytes s ++ ws) = s ++ octets ws
Proof
  simp[octets_def, bytes_def, MAP_MAP_o, combinTheory.o_DEF] >>
  simp[MAP_EQ_ID] >> rw[] >>
  ‘ORD x < 256’ by simp[ORD_BOUND] >> simp[CHR_ORD]
QED

Theorem octets_11:
  ∀a b. octets a = octets b ⇔ a = b
Proof
  Induct >> Cases_on ‘b’ >> simp[octets_def] >> rpt gen_tac >>
  ‘w2n h < 256 ∧ w2n h' < 256’
    by (assume_tac (INST_TYPE [alpha |-> “:8”] w2n_lt) >> fs[]) >>
  simp[CHR_11] >> fs[octets_def]
QED

(* MAIN (on the wire): the same for brequests, on octets *)
Theorem rfc_octets_frames_exactly:
  EVERY (λr. valid_brequest_t r ∧ rfc_chars r) rs ⇒
  (rfc_requests_octets (brequests rs ++ rest) ms rest' ∧
   LENGTH ms = LENGTH rs ⇔
   ms = MAP reading rs ∧ rest' = rest)
Proof
  strip_tac >> drule rfc_frames_list_exactly >>
  simp[rfc_requests_octets_def, brequests_def, octets_bytes, octets_11]
QED

(* ------------------------------------------------------------------------
   Where we are LOOSER than the RFC (finding H-CHARS)
   ------------------------------------------------------------------------ *)

Theorem no_sp_sep[local]:
  ¬MEM #" " m1 ∧ ¬MEM #" " t1 ∧ ¬MEM #" " m2 ∧ ¬MEM #" " t2 ∧
  m1 ++ " " ++ t1 ++ " HTTP/" ++ v1 = m2 ++ " " ++ t2 ++ " HTTP/" ++ v2 ⇒
  m1 = m2 ∧ t1 = t2 ∧ v1 = v2
Proof
  strip_tac >>
  ‘m1 = m2 ∧ t1 ++ #" " :: ("HTTP/" ++ v1) = t2 ++ #" " :: ("HTTP/" ++ v2)’
    by (irule split_sep >> qexists_tac ‘#" "’ >> fs[]) >>
  ‘t1 = t2 ∧ "HTTP/" ++ v1 = "HTTP/" ++ v2’
    by (irule split_sep >> qexists_tac ‘#" "’ >> fs[]) >>
  fs[]
QED

Theorem our_line_shape[local]:
  valid_bheader (n, v) ⇒ n ++ ": " ++ v ≠ [] ∧ ¬MEM #"\r" (n ++ ": " ++ v)
Proof
  simp[valid_bheader_exp, EVERY_MEM] >> metis_tac[]
QED

(* If the RFC frames the bytes of one of our valid requests at all, it
   reads its request line and its field lines as ours *)
Theorem rfc_lines_are_ours:
  valid_brequest_t (Req m p ver hs b) ∧
  rfc_request_lines (print_brequest (Req m p ver hs b) ++ z) ls mr rest ⇒
  mr.meth = m ∧ mr.target = p ∧ mr.version = ver ∧ ls = our_lines hs ∧
  mr.body ++ rest = b ++ z
Proof
  simp[valid_brequest_t_def, rfc_request_lines_def, print_brequest_lines] >>
  strip_tac >> fs[valid_brequest_def] >>
  ‘¬MEM #" " m ∧ ¬MEM #"\r" m’ by (qpat_x_assum ‘valid_method m’ (strip_assume_tac o REWRITE_RULE [valid_method_def]) >> gvs[]) >>
  ‘¬MEM #" " p ∧ ¬MEM #"\r" p’ by (fs[valid_path_def, EVERY_MEM] >> metis_tac[]) >>
  ‘¬MEM #"\r" ver’ by (qpat_x_assum ‘valid_version ver’ (strip_assume_tac o REWRITE_RULE [valid_version_def]) >> gvs[]) >>
  ‘¬MEM #"\r" (m ++ " " ++ p ++ " HTTP/" ++ ver)’ by simp[] >>
  ‘¬MEM #"\r" (mr.meth ++ " " ++ mr.target ++ " HTTP/" ++ mr.version)’
    by simp[request_line_no_cr] >>
  ‘mr.meth ++ " " ++ mr.target ++ " HTTP/" ++ mr.version =
     m ++ " " ++ p ++ " HTTP/" ++ ver ∧
   crlf_lines ls ++ "\r\n" ++ mr.body ++ rest =
     crlf_lines (our_lines hs) ++ "\r\n" ++ b ++ z’
    by (irule split_crlf >> rpt conj_tac >- fs[] >- fs[] >>
        qpat_x_assum ‘_ ++ z = _ ++ rest’ mp_tac >> REWRITE_TAC[GSYM APPEND_ASSOC] >>
        disch_then (ACCEPT_TAC o SYM)) >>
  ‘mr.meth = m ∧ mr.target = p ∧ mr.version = ver’
    by (irule no_sp_sep >> fs[] >>
        metis_tac[token_no_sep, target_no_sep]) >>
  ‘EVERY (λl. l ≠ [] ∧ ¬MEM #"\r" l) ls ∧
   EVERY (λl. l ≠ [] ∧ ¬MEM #"\r" l) (our_lines hs)’
    by (fs[EVERY_MEM, our_lines_def, MEM_MAP, FORALL_PROD, PULL_EXISTS] >>
        rw[] >> fs[field_line_shape] >> res_tac >>
        fs[valid_bheader_exp, EVERY_MEM] >> metis_tac[]) >>
  ‘ls = our_lines hs ∧ mr.body ++ rest = b ++ z’
    by (irule lines_unique >> fs[] >>
        qpat_x_assum ‘crlf_lines _ ++ _ = _’ mp_tac >>
        REWRITE_TAC[GSYM APPEND_ASSOC] >> disch_then ACCEPT_TAC) >>
  fs[]
QED

(* MAIN (FINDING H-CHARS): a valid request whose characters the RFC
   forbids is not framed by the RFC at all *)
Theorem rfc_rejects_unclean:
  valid_brequest_t r ∧ rfc_request (print_brequest r ++ z) mr rest ⇒
  rfc_chars r
Proof
  Cases_on ‘r’ >> rw[rfc_request_def] >>
  drule_all rfc_lines_are_ours >> strip_tac >>
  fs[rfc_request_lines_def] >> gvs[] >>
  simp[rfc_chars_def] >> conj_tac
  >- fs[target_ok_def] >>
  fs[our_lines_def, EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> rw[] >>
  first_x_assum drule >>
  ‘¬MEM #":" p_1’
    by (fs[valid_brequest_t_def, valid_brequest_def, EVERY_MEM, FORALL_PROD,
           valid_bheader_exp] >> metis_tac[]) >>
  ‘fraw (p_1 ++ ": " ++ p_2) = #" " :: p_2’ by metis_tac[fname_fraw_line] >>
  simp[field_line_ok_def, EVERY_MEM]
QED

(* The review's examples tab_path_valid_but_not_rfc and
   nul_value_valid_but_not_rfc (a TAB in the path, NUL in a header value)
   showed this gap; with the RFC character sets in HttpSpecBodies they are
   no longer valid requests (HttpSpecBodiesBite's rfc_chars_bites), and
   every valid request has rfc_chars (rfcAgreeValid). *)

(* ------------------------------------------------------------------------
   Where we are STRICTER than the RFC: the exact characterisation
   ------------------------------------------------------------------------ *)

(* The RFC messages our subset contains: method GET or POST, version 1.0
   or 1.1, a SP right after every field colon, and the Content-Length
   raw value (after that SP) canonical decimal: no leading zeros, no OWS *)
Definition subset_ok_def:
  subset_ok mr ls ⇔
    MEM mr.meth ["GET"; "POST"] ∧ MEM mr.version ["1.0"; "1.1"] ∧
    EVERY (λl. ∃v. fraw l = #" " :: v) ls ∧
    EVERY (λl. MAP lower (fname l) = "content-length" ⇒
               ∃k. fraw l = #" " :: num_to_dec_string k) ls
End

Theorem ours_subset_ok[local]:
  valid_brequest_t (Req m p ver hs b) ⇒ subset_ok (reading (Req m p ver hs b)) (our_lines hs)
Proof
  simp[valid_brequest_t_def, subset_ok_def, reading_def] >> strip_tac >>
  fs[valid_brequest_def] >>
  ‘∀n v. MEM (n, v) hs ⇒
         fname (n ++ ": " ++ v) = n ∧ fraw (n ++ ": " ++ v) = #" " :: v’
    by (rpt gen_tac >> strip_tac >>
        ‘¬MEM #":" n’ by (fs[EVERY_MEM, FORALL_PROD, valid_bheader_exp] >> metis_tac[]) >>
        metis_tac[fname_fraw_line]) >>
  rpt conj_tac
  >- (fs[valid_method_def] >> simp[])
  >- (fs[valid_version_def] >> simp[])
  >- (simp[our_lines_def, EVERY_MAP] >> simp[EVERY_MEM, FORALL_PROD] >> rw[] >>
      res_tac >> fs[]) >>
  simp[our_lines_def, EVERY_MAP] >> simp[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
  ‘fname (p_1 ++ ": " ++ p_2) = p_1 ∧ fraw (p_1 ++ ": " ++ p_2) = #" " :: p_2’
    by metis_tac[] >>
  fs[lower_toLower] >>
  ‘MEM (p_1, p_2) (FILTER is_cl hs)’ by simp[MEM_FILTER, is_cl_def] >>
  fs[framed_def] >>
  Cases_on ‘FILTER is_cl hs’ >> fs[] >>
  Cases_on ‘t’ >> fs[] >> PairCases_on ‘h’ >> gvs[] >>
  qexists_tac ‘STRLEN b’ >> fs[]
QED

Theorem split_colon_space[local]:
  MEM #":" l ∧ fraw l = #" " :: v ⇒ l = fname l ++ ": " ++ v
Proof
  rw[] >> drule split_colon >> simp[]
QED

(* MAIN (exact characterisation): a stream starts with one of our
   (tchar-fixed, RFC-character) requests, read as ours, iff the RFC frames
   it with a message satisfying subset_ok *)
Theorem rfc_subset_exact:
  (∃r. valid_brequest_t r ∧ rfc_chars r ∧ s = print_brequest r ++ rest ∧
       reading r = mr) ⇔
  ∃ls. rfc_request_lines s ls mr rest ∧ subset_ok mr ls
Proof
  eq_tac
  >- (rw[] >> Cases_on ‘r’ >> qexists_tac ‘our_lines l’ >>
      metis_tac[rfc_agrees_lines, ours_subset_ok]) >>
  REWRITE_TAC[subset_ok_def] >> disch_then (qx_choose_then ‘ls’ strip_assume_tac) >>
  qexists_tac ‘Req mr.meth mr.target mr.version
                 (MAP (λl. (fname l, TL (fraw l))) ls) mr.body’ >>
  qpat_x_assum ‘rfc_request_lines _ _ _ _’
    (strip_assume_tac o REWRITE_RULE [rfc_request_lines_def]) >>
  ‘∀l. MEM l ls ⇒ field_line_ok l ∧ ∃v. fraw l = #" " :: v’
    by fs[EVERY_MEM] >>
  ‘∀l. MEM l ls ⇒ l = fname l ++ ": " ++ TL (fraw l)’
    by (rpt strip_tac >> res_tac >> fs[field_line_ok_def] >>
        irule split_colon_space >> fs[]) >>
  ‘our_lines (MAP (λl. (fname l, TL (fraw l))) ls) = ls’
    by (simp[our_lines_def, MAP_MAP_o, combinTheory.o_DEF] >>
        irule (iffRL MAP_EQ_ID) >> rpt strip_tac >> simp[] >> metis_tac[]) >>
  ‘MAP (λ(n, v). (n, strip_ows v)) (MAP (λl. (fname l, TL (fraw l))) ls) =
   MAP field_of ls’
    by (simp[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f, field_of_def] >> rw[] >>
        res_tac >> simp[strip_ows_space]) >>
  ‘∀l. MEM l ls ⇒
       fname l ≠ [] ∧ EVERY is_tchar (fname l) ∧
       EVERY (λc. is_field_vchar c ∨ is_ows c) (TL (fraw l))’
    by (rw[] >> res_tac >> fs[field_line_ok_def, is_token_def] >> gvs[]) >>
  (* the Content-Length lines, on both sides *)
  qabbrev_tac ‘P = λl. MAP toLower (fname l) = "content-length"’ >>
  ‘FILTER is_cl (MAP (λl. (fname l, TL (fraw l))) ls) =
   MAP (λl. (fname l, TL (fraw l))) (FILTER P ls)’
    by (simp[filter_is_cl, FILTER_MAP, combinTheory.o_DEF, Abbr ‘P’]) >>
  ‘values_named "content-length" (MAP field_of ls) =
   MAP (λl. strip_ows (fraw l)) (FILTER P ls)’
    by (simp[values_named_def, FILTER_MAP, MAP_MAP_o, combinTheory.o_DEF,
             field_of_def, lower_toLower, Abbr ‘P’]) >>
  ‘values_named "transfer-encoding" (MAP field_of ls) =
   MAP (λl. strip_ows (fraw l))
     (FILTER (λl. MAP toLower (fname l) = "transfer-encoding") ls)’
    by (simp[values_named_def, FILTER_MAP, MAP_MAP_o, combinTheory.o_DEF,
             field_of_def, lower_toLower]) >>
  ‘FILTER (λl. MAP toLower (fname l) = "transfer-encoding") ls = []’
    by (CCONTR_TAC >> qpat_x_assum ‘body_framing _ = _’ mp_tac >>
        simp[body_framing_def] >> rw[]) >>
  rpt conj_tac
  >- (simp[valid_brequest_t_def, valid_brequest_def] >> rpt conj_tac
      >- fs[valid_method_def]
      >- (fs[valid_path_def, target_ok_def, EVERY_MEM] >> rpt strip_tac >> res_tac >>
          gvs[is_target_char_def, is_alpha_def, is_digit_def])
      >- fs[target_ok_def, EVERY_MEM, uri_char_is_target]
      >- fs[valid_version_def]
      >- (simp[EVERY_MAP, EVERY_MEM, valid_bheader_def] >> rw[] >> res_tac >>
          fs[EVERY_MEM, tchar_is_tchar, field_char_is])
      >- (qpat_x_assum ‘FILTER _ ls = []’ mp_tac >>
          simp[FILTER_EQ_NIL, EVERY_MEM, EXISTS_MEM, MEM_MAP, PULL_EXISTS, is_te_def])
      >- (simp[framed_def] >>
          qpat_x_assum ‘body_framing _ = _’ mp_tac >> simp[body_framing_def] >>
          Cases_on ‘FILTER P ls’ >> simp[] >>
          Cases_on ‘t’ >> simp[] >> rw[] >>
          ‘MEM h (FILTER P ls)’ by fs[] >>
          ‘MEM h ls ∧ MAP toLower (fname h) = "content-length"’
            by fs[MEM_FILTER, Abbr ‘P’] >>
          qpat_x_assum ‘EVERY (λl. MAP lower _ = _ ⇒ _) ls’
            (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
          disch_then drule >> simp[lower_toLower] >> strip_tac >>
          fs[strip_ows_space] >>
          ‘EVERY is_digit (num_to_dec_string k)’
            by simp[is_digit_isDigit, EVERY_isDigit_num_to_dec_string] >>
          fs[strip_ows_digits] >>
          assume_tac num_dec_string >> fs[FUN_EQ_THM])
      >- (simp[EVERY_MAP, EVERY_MEM, valid_bheader_t_def, valid_bheader_def] >>
          rw[] >> res_tac >> fs[EVERY_MEM, tchar_is_tchar, field_char_is]))
  >- (simp[rfc_chars_def, EVERY_MAP] >> fs[target_ok_def, EVERY_MEM] >> metis_tac[])
  >- simp[print_brequest_lines]
  >- simp[reading_def, rfc_req_component_equality]
QED

(* Example: "Host:x" (no SP after the colon) is a valid RFC field line,
   so this is an RFC request; no valid request of ours starts the stream *)
Overload host_no_space = “"GET /a HTTP/1.1\r\nHost:x\r\n\r\n"”

Overload host_reading =
  “<| meth := "GET"; target := "/a"; version := "1.1";
      fields := [("Host", "x")]; body := "" |>”

Theorem host_no_space_lines:
  rfc_request_lines host_no_space ["Host:x"] host_reading ""
Proof
  simp[rfc_request_lines_def] >>
  rpt conj_tac >> TRY (simp[version_ok_def, is_digit_def] >> NO_TAC) >>
  EVAL_TAC
QED

(* MAIN (stricter): "Host:x" is an RFC request *)
Theorem host_no_space_rfc:
  rfc_request host_no_space host_reading ""
Proof
  metis_tac[rfc_request_def, host_no_space_lines]
QED

(* MAIN (stricter): ... but no valid request of ours starts the stream *)
Theorem host_no_space_not_ours:
  ¬∃r z. valid_brequest_t r ∧ host_no_space = print_brequest r ++ z
Proof
  rpt strip_tac >> Cases_on ‘r’ >>
  ‘rfc_request_lines (print_brequest (Req s s0 s1 l s2) ++ z) ["Host:x"]
     host_reading ""’ by metis_tac[host_no_space_lines] >>
  drule_all rfc_lines_are_ours >> strip_tac >>
  ‘subset_ok (reading (Req s s0 s1 l s2)) (our_lines l)’
    by metis_tac[ours_subset_ok] >>
  pop_assum mp_tac >> qpat_x_assum ‘["Host:x"] = _’ (SUBST1_TAC o SYM) >>
  ‘fraw "Host:x" = "x"’ by EVAL_TAC >>
  simp[subset_ok_def]
QED
