(*
  An incremental parser for HttpSpec' requests (Content-Length
  framed bodies), proved against the spec's printer.  Internal.

     parse_brequest s = BComplete r rest | BIncomplete | BInvalid

  Method "GET " or "POST "; then the request line and header lines as in
  httpHeadersParse (split_path, the version constants);
  (parse_bheaders: its own header-line parser, the character rules only);
  then the body (bbody): any Transfer-Encoding header or two
  Content-Length headers is invalid; a single Content-Length value must be
  canonical decimal (dec_fold reads it, toString checks it); the body is
  the next n octets, or the request is incomplete until they have arrived.

  Main facts:
   - parse_bprint:     parse_brequest (print_brequest r ++ rest) = BComplete r rest
   - parse_bcomplete:  BComplete r rest means s = print_brequest r ++ rest
   - parse_all_brequests, parse_all_b_mono, parse_bextend
*)
Theory httpParse
Ancestors
  HttpGetSpec HttpHeadersSpec HttpSpec httpGetParse httpHeadersParse
  list rich_list ASCIInumbers
Libs
  preamble

Datatype:
  bparse_result = BComplete brequest string | BIncomplete | BInvalid
End

Definition post_sp_def:
  post_sp = "POST "
End

(* The header lines, up to and including the blank line.  The bodies
   protocol has its own header-line parser: httpHeadersParse's parse_headers
   rejects the body-framing headers (spike/http-nobody), which this
   protocol needs.  parse_bheaders is that parser before the restriction,
   with HttpSpec' header names: RFC 9110 tokens (tchar). *)
Theorem split_at_LENGTH_b[local]:
  ∀s. LENGTH (SND (split_at c s)) ≤ LENGTH s
Proof
  Induct >> rw[split_at_def]
QED

Definition parse_bheaders_def:
  parse_bheaders s =
    if crlf ≼ s then HDone [] (DROP 2 s)
    else if s ≼ crlf then HMore
    else
      let n = FST (split_at #":" s);
          u = SND (split_at #":" s)
      in
        if EXISTS (λc. ¬tchar c) n then HBad
        else if u = [] then HMore
        else if n = [] then HBad
        else if ¬(colon_sp ≼ u) then (if u ≼ colon_sp then HMore else HBad)
        else
          let v = FST (split_at #"\r" (DROP 2 u));
              w = SND (split_at #"\r" (DROP 2 u))
          in
            if EXISTS (λc. ¬field_char c) v then HBad
            else if w = [] then HMore
            else if ¬(crlf ≼ w) then (if w ≼ crlf then HMore else HBad)
            else
              case parse_bheaders (DROP 2 w) of
                HDone hs r => HDone ((n, v) :: hs) r
              | HMore => HMore
              | HBad => HBad
Termination
  WF_REL_TAC ‘measure LENGTH’ >> rw[] >>
  qspecl_then [‘#":"’, ‘s’] assume_tac (GEN_ALL split_at_LENGTH_b) >>
  qspecl_then [‘#"\r"’, ‘DROP 2 (SND (split_at #":" s))’] assume_tac
    (GEN_ALL split_at_LENGTH_b) >>
  fs[IS_PREFIX_APPEND, colon_sp_def] >> gvs[]
End

(* The value of a decimal numeral (meaningful when every character is a
   digit) *)
Definition dec_fold_def:
  dec_fold (s : string) = FOLDL (λn c. 10 * n + (ORD c - 48)) 0 s
End

(* The body, once the header lines hs are complete and rest follows *)
Definition bbody_def:
  bbody m p ver hs rest =
    if EXISTS is_te hs then BInvalid
    else
      case FILTER is_cl hs of
        [] => BComplete (Req m p ver hs "") rest
      | [(n, v)] =>
          if v ≠ "" ∧ EVERY isDigit v ∧ toString (dec_fold v) = v then
            (if LENGTH rest < dec_fold v then BIncomplete
             else BComplete (Req m p ver hs (TAKE (dec_fold v) rest))
                            (DROP (dec_fold v) rest))
          else BInvalid
      | _ => BInvalid
End

Definition bfinish_def:
  bfinish m p ver r =
    case r of
      HDone hs rest => bbody m p ver hs rest
    | HMore => BIncomplete
    | HBad => BInvalid
End

(* After the method and its space *)
Definition bline_def:
  bline m t =
    let p = FST (split_path t);
        u = SND (split_path t)
    in
      if EXISTS (λc. ¬uri_char c) p then BInvalid
      else if u = [] then BIncomplete
      else if p = [] then BInvalid
      else if sp_http10 ≼ u then bfinish m p "1.0" (parse_bheaders (DROP 11 u))
      else if sp_http11 ≼ u then bfinish m p "1.1" (parse_bheaders (DROP 11 u))
      else if u ≼ sp_http10 ∨ u ≼ sp_http11 then BIncomplete
      else BInvalid
End

Definition parse_brequest_def:
  parse_brequest s =
    if get_sp ≼ s then bline "GET" (DROP 4 s)
    else if post_sp ≼ s then bline "POST" (DROP 5 s)
    else if s ≼ get_sp ∨ s ≼ post_sp then BIncomplete
    else BInvalid
End

(* ------------------------------------------------------------------------
   Small facts
   ------------------------------------------------------------------------ *)

Theorem split_at_char[local]:
  ∀p x. ¬MEM c p ⇒ split_at c (p ++ c :: x) = (p, c :: x)
Proof
  Induct >> simp[split_at_def]
QED

Theorem split_at_join[local]:
  ∀s. FST (split_at c s) ++ SND (split_at c s) = s
Proof
  Induct >> rw[split_at_def]
QED

Theorem split_at_notmem[local]:
  ∀s. ¬MEM c (FST (split_at c s))
Proof
  Induct >> rw[split_at_def]
QED

Theorem DROP_2_CONS[local]:
  DROP 2 (a :: b :: x) = x
Proof
  simp[]
QED

Theorem crlf_prefix[local]:
  crlf ≼ #"\r" :: #"\n" :: Y
Proof
  simp[crlf_def]
QED

Theorem colon_sp_prefix[local]:
  colon_sp ≼ #":" :: #" " :: Y
Proof
  simp[colon_sp_def]
QED

Theorem DROP_crlf[local]:
  DROP 2 (crlf ++ l) = l ∧ DROP 2 (colon_sp ++ l) = l
Proof
  simp[crlf_def, colon_sp_def]
QED

(* ------------------------------------------------------------------------
   Header lines against the printer, with valid_bheader
   ------------------------------------------------------------------------ *)

Theorem parse_bheaders_line[local]:
  n ≠ [] ∧ EVERY tchar n ∧ EVERY field_char v ⇒
  parse_bheaders (n ++ #":" :: #" " :: (v ++ #"\r" :: #"\n" :: Y)) =
  case parse_bheaders Y of
    HDone hs r => HDone ((n, v) :: hs) r
  | HMore => HMore
  | HBad => HBad
Proof
  strip_tac >>
  ‘EVERY (λc. c ≠ #":" ∧ c ≠ #" " ∧ c ≠ #"\r" ∧ c ≠ #"\n") n’
    by (irule EVERY_MONOTONIC >> qexists_tac ‘tchar’ >> simp[] >>
        metis_tac[tchar_not_sep]) >>
  ‘¬(crlf ≼ n ++ #":" :: #" " :: (v ++ #"\r" :: #"\n" :: Y)) ∧
   ¬(n ++ #":" :: #" " :: (v ++ #"\r" :: #"\n" :: Y) ≼ crlf)’
    by (Cases_on ‘n’ >> gvs[crlf_def]) >>
  ‘split_at #":" (n ++ #":" :: #" " :: (v ++ #"\r" :: #"\n" :: Y)) =
   (n, #":" :: #" " :: (v ++ #"\r" :: #"\n" :: Y))’
    by (irule split_at_char >> fs[EVERY_MEM] >> strip_tac >> res_tac >> fs[]) >>
  ‘¬EXISTS (λc. ¬tchar c) n’ by fs[EVERY_MEM, EXISTS_MEM] >>
  ‘EVERY (λc. c ≠ #"\r" ∧ c ≠ #"\n") v’
    by (irule EVERY_MONOTONIC >> qexists_tac ‘field_char’ >>
        rw[field_char_def] >> rpt strip_tac >> gvs[]) >>
  ‘split_at #"\r" (v ++ #"\r" :: #"\n" :: Y) = (v, #"\r" :: #"\n" :: Y)’
    by (irule split_at_char >> fs[EVERY_MEM] >> strip_tac >> res_tac >> fs[]) >>
  ‘¬EXISTS (λc. ¬field_char c) v’ by fs[EVERY_MEM, EXISTS_MEM] >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [parse_bheaders_def])) >>
  asm_simp_tac std_ss [LET_THM, crlf_prefix, colon_sp_prefix, DROP_2_CONS] >>
  simp[]
QED

(* MAIN (helper): printed valid header lines, then the blank line *)
Theorem parse_bheaders_print:
  ∀hs rest. EVERY valid_bheader hs ⇒
    parse_bheaders (FLAT (MAP print_header hs) ++ crlf ++ rest) = HDone hs rest
Proof
  Induct
  >- simp[Once parse_bheaders_def, crlf_def] >>
  PairCases >> rw[valid_bheader_def] >>
  simp[print_header_def] >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC[parse_bheaders_line] >> simp[]
QED

(* MAIN (helper): HDone means printed valid header lines, then the blank line *)
Theorem parse_bheaders_done:
  ∀s hs r. parse_bheaders s = HDone hs r ⇒
           EVERY valid_bheader hs ∧ s = FLAT (MAP print_header hs) ++ crlf ++ r
Proof
  gen_tac >> completeInduct_on ‘LENGTH s’ >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> simp[Once parse_bheaders_def] >>
  qabbrev_tac ‘nm = FST (split_at #":" s)’ >>
  qabbrev_tac ‘uu = SND (split_at #":" s)’ >>
  qabbrev_tac ‘vl = FST (split_at #"\r" (DROP 2 uu))’ >>
  qabbrev_tac ‘ww = SND (split_at #"\r" (DROP 2 uu))’ >>
  rw[AllCaseEqs()]
  >- (qpat_x_assum ‘crlf ≼ s’ (strip_assume_tac o REWRITE_RULE[IS_PREFIX_APPEND]) >>
      gvs[DROP_crlf])
  >- (qpat_x_assum ‘crlf ≼ s’ (strip_assume_tac o REWRITE_RULE[IS_PREFIX_APPEND]) >>
      gvs[DROP_crlf]) >>
  ‘s = nm ++ uu’ by simp[Abbr ‘nm’, Abbr ‘uu’, split_at_join] >>
  ‘DROP 2 uu = vl ++ ww’ by simp[Abbr ‘vl’, Abbr ‘ww’, split_at_join] >>
  qpat_x_assum ‘colon_sp ≼ uu’ (strip_assume_tac o REWRITE_RULE[IS_PREFIX_APPEND]) >>
  rename1 ‘uu = colon_sp ++ l1’ >>
  qpat_x_assum ‘crlf ≼ ww’ (strip_assume_tac o REWRITE_RULE[IS_PREFIX_APPEND]) >>
  rename1 ‘ww = crlf ++ l2’ >>
  ‘DROP 2 uu = l1’
    by (qpat_x_assum ‘uu = colon_sp ++ l1’ (fn th => REWRITE_TAC[th, DROP_crlf])) >>
  ‘DROP 2 ww = l2’
    by (qpat_x_assum ‘ww = crlf ++ l2’ (fn th => REWRITE_TAC[th, DROP_crlf])) >>
  ‘LENGTH s = LENGTH nm + LENGTH uu’
    by (qpat_x_assum ‘s = nm ++ uu’ (fn th => REWRITE_TAC[th, LENGTH_APPEND])) >>
  ‘LENGTH uu = 2 + LENGTH l1’
    by (qpat_x_assum ‘uu = colon_sp ++ l1’ (fn th => REWRITE_TAC[th, LENGTH_APPEND]) >>
        simp[]) >>
  ‘LENGTH l1 = LENGTH vl + LENGTH ww’
    by (‘l1 = vl ++ ww’ by metis_tac[] >> simp[]) >>
  ‘LENGTH ww = 2 + LENGTH l2’
    by (qpat_x_assum ‘ww = crlf ++ l2’ (fn th => REWRITE_TAC[th, LENGTH_APPEND]) >>
        simp[]) >>
  ‘parse_bheaders l2 = HDone hs' r’ by metis_tac[] >>
  first_x_assum (qspec_then ‘LENGTH l2’ mp_tac) >>
  (impl_tac >- fs[]) >>
  disch_then (qspec_then ‘l2’ mp_tac) >> simp[] >>
  TRY (disch_then drule) >> strip_tac >>
  ‘¬MEM #":" nm’ by simp[Abbr ‘nm’, split_at_notmem] >>
  ‘¬MEM #"\r" vl’ by simp[Abbr ‘vl’, split_at_notmem] >>
  TRY (simp[valid_bheader_def] >> fs[EVERY_MEM, EXISTS_MEM] >> metis_tac[] >> NO_TAC) >>
  ‘l1 = vl ++ crlf ++ l2’ by metis_tac[APPEND_ASSOC] >>
  qpat_x_assum ‘s = nm ++ uu’ SUBST1_TAC >>
  qpat_x_assum ‘uu = colon_sp ++ l1’ SUBST1_TAC >>
  qpat_x_assum ‘l1 = vl ++ crlf ++ l2’ SUBST1_TAC >>
  qpat_x_assum ‘l2 = _’ SUBST1_TAC >>
  simp[print_header_def, colon_sp_def, crlf_def]
QED

(* ------------------------------------------------------------------------
   Decimal values
   ------------------------------------------------------------------------ *)

Theorem dec_fold_SNOC[local]:
  dec_fold (s ++ [c]) = 10 * dec_fold s + (ORD c - 48)
Proof
  simp[dec_fold_def, FOLDL_APPEND]
QED

Theorem isDigit_UNHEX[local]:
  isDigit c ⇒ UNHEX c = ORD c - 48
Proof
  rw[isDigit_def] >>
  ‘∃k. k < 10 ∧ c = CHR (k + 48)’
    by (qexists_tac ‘ORD c - 48’ >> simp[CHR_ORD]) >>
  rw[] >>
  ‘k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨
   k = 8 ∨ k = 9’ by decide_tac >>
  rw[] >> EVAL_TAC
QED

Theorem dec_fold_toNum[local]:
  ∀s. EVERY isDigit s ⇒ dec_fold s = toNum s
Proof
  ho_match_mp_tac SNOC_INDUCT >> rw[]
  >- EVAL_TAC >>
  fs[SNOC_APPEND, dec_fold_SNOC, EVERY_APPEND, num_from_dec_string_def,
     s2n_def, REVERSE_APPEND, numposrepTheory.l2n_def, isDigit_UNHEX] >>
  ‘ORD x - 48 < 10’ by fs[isDigit_def] >> simp[]
QED

Theorem dec_fold_toString[local]:
  dec_fold (toString n) = n
Proof
  simp[dec_fold_toNum, EVERY_isDigit_num_to_dec_string]
QED

(* ------------------------------------------------------------------------
   The body
   ------------------------------------------------------------------------ *)

(* A framed body, then anything, is read back *)
Theorem bbody_framed[local]:
  framed hs b ∧ ¬EXISTS is_te hs ⇒
  bbody m p ver hs (b ++ rest) = BComplete (Req m p ver hs b) rest
Proof
  rpt strip_tac >> simp[bbody_def] >>
  qpat_x_assum ‘¬EXISTS _ _’ (fn th => simp[th]) >>
  qpat_x_assum ‘framed _ _’ mp_tac >> simp[framed_def] >>
  Cases_on ‘FILTER is_cl hs’ >> simp[] >>
  Cases_on ‘t’ >> simp[] >> PairCases_on ‘h’ >> rw[] >>
  fs[dec_fold_toString, EVERY_isDigit_num_to_dec_string, TAKE_APPEND, DROP_APPEND] >>
  metis_tac[EVERY_isDigit_num_to_dec_string, NOT_EVERY]
QED

(* BComplete from the body means a framed body followed by the rest *)
Theorem bbody_complete[local]:
  bbody m p ver hs rest = BComplete r rest' ⇒
  ∃b. r = Req m p ver hs b ∧ rest = b ++ rest' ∧ framed hs b ∧ ¬EXISTS is_te hs
Proof
  rw[bbody_def, AllCaseEqs()] >> simp[framed_def] >>
  qexists_tac ‘TAKE (dec_fold v) rest’ >> simp[TAKE_DROP] >>
  ‘LENGTH (TAKE (dec_fold v) rest) = dec_fold v’ by simp[LENGTH_TAKE] >>
  simp[]
QED

(* ------------------------------------------------------------------------
   Requests against the printer
   ------------------------------------------------------------------------ *)

Theorem split_path_space_h[local]:
  ∀p x. EVERY (λc. c ≠ #" ") p ⇒ split_path (p ++ #" " :: x) = (p, #" " :: x)
Proof
  Induct >> simp[split_path_def]
QED

Theorem split_path_join_h[local]:
  ∀t. FST (split_path t) ++ SND (split_path t) = t
Proof
  Induct >> rw[split_path_def]
QED

Theorem split_path_every_h[local]:
  ∀t. EVERY (λc. c ≠ #" ") (FST (split_path t))
Proof
  Induct >> rw[split_path_def]
QED

Theorem sp_http_space[local]:
  (∃x. sp_http10 = #" " :: x) ∧ (∃x. sp_http11 = #" " :: x)
Proof
  simp[sp_http10_def, sp_http11_def]
QED

Theorem sp_http_distinct[local]:
  ¬(sp_http10 ≼ sp_http11 ++ x)
Proof
  simp[sp_http10_def, sp_http11_def]
QED

Theorem DROP_sp_http[local]:
  DROP 11 (sp_http10 ++ x) = x ∧ DROP 11 (sp_http11 ++ x) = x
Proof
  ‘11 = LENGTH sp_http10 ∧ 11 = LENGTH sp_http11’ by simp[] >>
  metis_tac[DROP_LENGTH_APPEND]
QED

Theorem LENGTH_post_sp[simp]:
  LENGTH post_sp = 5
Proof
  EVAL_TAC
QED

(* Request-target characters exclude the separators *)
Theorem uri_char_not_sep[local]:
  uri_char c ⇒ c ≠ #" " ∧ c ≠ #"\r" ∧ c ≠ #"\n"
Proof
  rw[uri_char_def] >> fs[stringTheory.isAlpha_def, stringTheory.isLower_def,
                         stringTheory.isUpper_def, stringTheory.isDigit_def] >>
  rpt strip_tac >> gvs[]
QED

(* The request line after the method, in bline's terms *)
Theorem bline_line[local]:
  valid_path p ∧ EVERY uri_char p ∧ (sp_http10 ≼ u ∨ sp_http11 ≼ u) ⇒
  bline m (p ++ u) =
    if sp_http10 ≼ u then bfinish m p "1.0" (parse_bheaders (DROP 11 u))
    else bfinish m p "1.1" (parse_bheaders (DROP 11 u))
Proof
  strip_tac >>
  ‘EVERY (λc. c ≠ #" ") p ∧ ¬EXISTS (λc. ¬uri_char c) p ∧ p ≠ []’
    by (fs[valid_path_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  ‘split_path (p ++ u) = (p, u) ∧ u ≠ []’
    by (‘∃y. u = sp_http10 ++ y ∨ u = sp_http11 ++ y’
          by (fs[IS_PREFIX_APPEND] >> metis_tac[]) >>
        fs[sp_http10_def, sp_http11_def] >> simp[split_path_space_h]) >>
  simp[bline_def] >> rw[] >> fs[]
QED

Theorem print_brequest_alt[local]:
  print_brequest (Req m p "1.0" hs b) ++ rest =
    m ++ " " ++ (p ++ (sp_http10 ++ (FLAT (MAP print_header hs) ++ (crlf ++ (b ++ rest))))) ∧
  print_brequest (Req m p "1.1" hs b) ++ rest =
    m ++ " " ++ (p ++ (sp_http11 ++ (FLAT (MAP print_header hs) ++ (crlf ++ (b ++ rest)))))
Proof
  simp[print_brequest_def, sp_http10_def, sp_http11_def, crlf_def]
QED

Theorem method_dispatch[local]:
  parse_brequest ("GET " ++ x) = bline "GET" x ∧
  parse_brequest ("POST " ++ x) = bline "POST" x
Proof
  conj_tac
  >- (‘get_sp ≼ "GET " ++ x ∧ DROP 4 ("GET " ++ x) = x’
        by simp[get_sp_def] >> simp[parse_brequest_def] >> fs[get_sp_def]) >>
  ‘¬(get_sp ≼ "POST " ++ x) ∧ post_sp ≼ "POST " ++ x ∧ DROP 5 ("POST " ++ x) = x’
    by simp[get_sp_def, post_sp_def] >>
  simp[parse_brequest_def] >> fs[get_sp_def, post_sp_def]
QED

Theorem method_dispatch_cons[local]:
  parse_brequest (#"G" :: #"E" :: #"T" :: #" " :: x) = bline "GET" x ∧
  parse_brequest (#"P" :: #"O" :: #"S" :: #"T" :: #" " :: x) = bline "POST" x
Proof
  simp[parse_brequest_def, get_sp_def, post_sp_def]
QED

(* MAIN: a printed valid request, followed by anything, parses back *)
Theorem parse_bprint:
  valid_brequest r ⇒ parse_brequest (print_brequest r ++ rest) = BComplete r rest
Proof
  Cases_on ‘r’ >> rename1 ‘Req m p ver hs b’ >>
  rw[valid_brequest_def, valid_method_def, valid_version_def] >>
  REWRITE_TAC[print_brequest_alt] >>
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
  REWRITE_TAC[method_dispatch_cons] >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC[bline_line] >>
  REWRITE_TAC[DROP_sp_http] >>
  dep_rewrite.DEP_REWRITE_TAC[parse_bheaders_print |> REWRITE_RULE [GSYM APPEND_ASSOC]] >>
  REWRITE_TAC[bfinish_def, httpHeadersParseTheory.headers_result_case_def] >>
  fs[IS_PREFIX_APPEND3, sp_http_distinct] >>
  irule bbody_framed >> fs[EVERY_MEM, EXISTS_MEM]
QED

(* MAIN: BComplete means a printed valid request followed by the rest *)
Theorem parse_bcomplete:
  parse_brequest s = BComplete r rest ⇒
  valid_brequest r ∧ s = print_brequest r ++ rest
Proof
  simp[parse_brequest_def] >>
  qabbrev_tac ‘m0 = if get_sp ≼ s then "GET" else "POST"’ >>
  qabbrev_tac ‘t = if get_sp ≼ s then DROP 4 s else DROP 5 s’ >>
  strip_tac >>
  ‘bline m0 t = BComplete r rest ∧ s = m0 ++ " " ++ t ∧ valid_method m0’
    by (Cases_on ‘get_sp ≼ s’ >> gvs[AllCaseEqs(), Abbr ‘m0’, Abbr ‘t’, valid_method_def]
        >- (qpat_x_assum ‘get_sp ≼ s’ (strip_assume_tac o REWRITE_RULE[IS_PREFIX_APPEND]) >>
            gvs[get_sp_def])
        >> qpat_x_assum ‘post_sp ≼ s’ (strip_assume_tac o REWRITE_RULE[IS_PREFIX_APPEND]) >>
        gvs[post_sp_def]) >>
  qpat_x_assum ‘bline _ _ = _’ mp_tac >>
  simp[bline_def, bfinish_def] >>
  qabbrev_tac ‘p = FST (split_path t)’ >>
  qabbrev_tac ‘u = SND (split_path t)’ >>
  rw[AllCaseEqs()] >>
  drule parse_bheaders_done >> strip_tac >>
  drule bbody_complete >> strip_tac >> gvs[] >>
  ‘t = p ++ u’ by simp[Abbr ‘p’, Abbr ‘u’, split_path_join_h] >>
  ‘EVERY (λc. c ≠ #" ") p’ by simp[Abbr ‘p’, split_path_every_h] >>
  FIRST [qpat_x_assum ‘sp_http10 ≼ u’ (strip_assume_tac o REWRITE_RULE[IS_PREFIX_APPEND]),
         qpat_x_assum ‘sp_http11 ≼ u’ (strip_assume_tac o REWRITE_RULE[IS_PREFIX_APPEND])] >>
  rename1 ‘u = _ ++ l1’ >>
  ‘DROP 11 u = l1’ by (qpat_x_assum ‘u = _ ++ l1’ (fn th => REWRITE_TAC[th, DROP_sp_http])) >>
  simp[valid_brequest_def, valid_version_def, valid_path_def] >>
  rpt conj_tac >>
  TRY (fs[EVERY_MEM, EXISTS_MEM, combinTheory.o_DEF] >>
       metis_tac[uri_char_not_sep] >> NO_TAC) >>
  simp[print_brequest_def] >>
  qpat_x_assum ‘t = _’ SUBST1_TAC >> qpat_x_assum ‘u = _’ SUBST1_TAC >>
  ‘l1 = FLAT (MAP print_header hs) ++ crlf ++ (b ++ rest)’ by metis_tac[APPEND_ASSOC] >>
  pop_assum SUBST1_TAC >> simp[sp_http10_def, sp_http11_def, crlf_def]
QED

Theorem parse_bcomplete_shorter:
  parse_brequest s = BComplete r rest ⇒ LENGTH rest < LENGTH s
Proof
  strip_tac >> drule parse_bcomplete >> Cases_on ‘r’ >>
  rw[print_brequest_def]
QED

(* BComplete is stable under extension *)
Theorem parse_bextend:
  parse_brequest s = BComplete r rest ⇒
  parse_brequest (s ++ x) = BComplete r (rest ++ x)
Proof
  strip_tac >> drule parse_bcomplete >> rw[] >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >> simp[parse_bprint]
QED

(* ------------------------------------------------------------------------
   All complete requests at the front of a buffer
   ------------------------------------------------------------------------ *)

Definition parse_all_b_def:
  parse_all_b s =
    case parse_brequest s of
    | BComplete r rest => r :: parse_all_b rest
    | _ => []
Termination
  WF_REL_TAC ‘measure LENGTH’ >> metis_tac[parse_bcomplete_shorter]
End

Theorem parse_all_b_Complete:
  parse_brequest s = BComplete r rest ⇒ parse_all_b s = r :: parse_all_b rest
Proof
  simp[Once parse_all_b_def]
QED

(* MAIN: printed valid requests, followed by a rest that does not start
   with a printed valid request, parse to exactly those requests *)
Theorem parse_all_brequests:
  ∀rs. EVERY valid_brequest rs ∧
       (∀r more. valid_brequest r ⇒ rest ≠ print_brequest r ++ more) ⇒
       parse_all_b (FLAT (MAP print_brequest rs) ++ rest) = rs
Proof
  Induct
  >- (rw[Once parse_all_b_def] >> CASE_TAC >> drule parse_bcomplete >> rw[] >>
      metis_tac[])
  >> rw[] >>
  ‘parse_brequest (print_brequest h ++ (FLAT (MAP print_brequest rs) ++ rest)) =
   BComplete h (FLAT (MAP print_brequest rs) ++ rest)’ by simp[parse_bprint] >>
  drule parse_all_b_Complete >> REWRITE_TAC[APPEND_ASSOC] >> simp[]
QED

(* MAIN (helper): reading more can only add complete requests at the end *)
Theorem parse_all_b_mono:
  ∀s t. parse_all_b s ≼ parse_all_b (s ++ t)
Proof
  gen_tac >> completeInduct_on ‘LENGTH s’ >> rw[] >>
  Cases_on ‘parse_brequest s’ >> simp[Once parse_all_b_def] >>
  drule parse_bextend >> disch_then (qspec_then ‘t’ assume_tac) >>
  simp[Once parse_all_b_def] >>
  ‘STRLEN s' < STRLEN s’ by metis_tac[parse_bcomplete_shorter] >>
  first_x_assum (qspec_then ‘STRLEN s'’ mp_tac) >> simp[]
QED

(* ------------------------------------------------------------------------
   Sanity checks
   ------------------------------------------------------------------------ *)

Theorem example_post_echo:
  parse_brequest
    "POST /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\n\r\nhelloGET"
  = BComplete (Req "POST" "/echo" "1.1" [("Host", "x"); ("Content-Length", "5")]
                   "hello") "GET"
Proof
  EVAL_TAC
QED

Theorem example_partial_body:
  parse_brequest "POST /echo HTTP/1.1\r\ncontent-length: 5\r\n\r\nhel" = BIncomplete
Proof
  EVAL_TAC
QED

Theorem example_bad_length:
  parse_brequest "POST /echo HTTP/1.1\r\nContent-Length: 05\r\n\r\nhello" = BInvalid
Proof
  EVAL_TAC
QED

Theorem example_chunked:
  parse_brequest "POST /echo HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\n" = BInvalid
Proof
  EVAL_TAC
QED
