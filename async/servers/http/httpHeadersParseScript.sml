(*
  An incremental parser for HttpHeadersSpec' requests (header-tolerant),
  proved against the variant's printer.  Internal: not part of any spec.

     parse_hrequest s = HComplete r rest   s starts with a complete valid
                                           request r, followed by rest
                      | HIncomplete        s could still become one
                      | HInvalid           s cannot

  Request line:  "GET " path " HTTP/1.0\r\n" or " HTTP/1.1\r\n"  (the path
  split as in httpGetParse), then header lines "name: value\r\n" up to a
  blank line "\r\n" (parse_headers).

  Main facts:
   - parse_hprint:     parse_hrequest (print_hrequest r ++ rest) = HComplete r rest
   - parse_hcomplete:  HComplete r rest means s = print_hrequest r ++ rest
   - parse_all_hrequests: parse_all_h of printed requests followed by a rest
                       that does not start with a request is the requests
*)
Theory httpHeadersParse
Ancestors
  HttpGetSpec HttpHeadersSpec httpGetParse list rich_list
Libs
  preamble

Datatype:
  hparse_result = HComplete hrequest string | HIncomplete | HInvalid
End

Datatype:
  headers_result = HDone ((string # string) list) string | HMore | HBad
End

(* The fixed pieces, as constants *)
Definition crlf_def:
  crlf = "\r\n"
End

Definition colon_sp_def:
  colon_sp = ": "
End

Definition sp_http10_def:
  sp_http10 = " HTTP/1.0\r\n"
End

Definition sp_http11_def:
  sp_http11 = " HTTP/1.1\r\n"
End

(* split_at c s = (p, u): p is s up to its first c, u the rest (starting
   with that c, or empty if there is none) *)
Definition split_at_def:
  split_at c [] = ([], []) ∧
  split_at c (d :: cs) =
    if d = c then ([], d :: cs)
    else (d :: FST (split_at c cs), SND (split_at c cs))
End

Theorem split_at_LENGTH[local]:
  ∀s. LENGTH (SND (split_at c s)) ≤ LENGTH s
Proof
  Induct >> rw[split_at_def]
QED

(* Header lines, up to and including the blank line *)
Definition parse_headers_def:
  parse_headers s =
    if crlf ≼ s then HDone [] (DROP 2 s)
    else if s ≼ crlf then HMore
    else
      let n = FST (split_at #":" s);
          u = SND (split_at #":" s)
      in
        if EXISTS (λc. c = #" " ∨ c = #"\r" ∨ c = #"\n") n then HBad
        else if u = [] then HMore
        else if n = [] then HBad
        else if body_header n then HBad
        else if ¬(colon_sp ≼ u) then (if u ≼ colon_sp then HMore else HBad)
        else
          let v = FST (split_at #"\r" (DROP 2 u));
              w = SND (split_at #"\r" (DROP 2 u))
          in
            if EXISTS (λc. c = #"\n") v then HBad
            else if w = [] then HMore
            else if ¬(crlf ≼ w) then (if w ≼ crlf then HMore else HBad)
            else
              case parse_headers (DROP 2 w) of
                HDone hs r => HDone ((n, v) :: hs) r
              | HMore => HMore
              | HBad => HBad
Termination
  WF_REL_TAC ‘measure LENGTH’ >> rw[] >>
  qspecl_then [‘#":"’, ‘s’] assume_tac (GEN_ALL split_at_LENGTH) >>
  qspecl_then [‘#"\r"’, ‘DROP 2 (SND (split_at #":" s))’] assume_tac
    (GEN_ALL split_at_LENGTH) >>
  fs[IS_PREFIX_APPEND, colon_sp_def] >> gvs[]
End

Definition hfinish_def:
  hfinish p v r =
    case r of
      HDone hs rest => HComplete (GetH p v hs) rest
    | HMore => HIncomplete
    | HBad => HInvalid
End

Definition parse_hrequest_def:
  parse_hrequest s =
    if ¬(get_sp ≼ s) then (if s ≼ get_sp then HIncomplete else HInvalid)
    else
      let t = DROP 4 s;
          p = FST (split_path t);
          u = SND (split_path t)
      in
        if EXISTS (λc. c = #"\r" ∨ c = #"\n") p then HInvalid
        else if u = [] then HIncomplete
        else if p = [] then HInvalid
        else if sp_http10 ≼ u then hfinish p "1.0" (parse_headers (DROP 11 u))
        else if sp_http11 ≼ u then hfinish p "1.1" (parse_headers (DROP 11 u))
        else if u ≼ sp_http10 ∨ u ≼ sp_http11 then HIncomplete
        else HInvalid
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

Theorem prefix_drop[local]:
  ∀p s. p ≼ s ⇒ s = p ++ DROP (LENGTH p) s
Proof
  rw[IS_PREFIX_APPEND] >> simp[DROP_LENGTH_APPEND]
QED

Theorem LENGTH_crlf[simp]:
  LENGTH crlf = 2
Proof
  EVAL_TAC
QED

Theorem LENGTH_colon_sp[simp]:
  LENGTH colon_sp = 2
Proof
  EVAL_TAC
QED

Theorem DROP_2_CONS[local]:
  DROP 2 (a :: b :: x) = x
Proof
  simp[]
QED

(* ------------------------------------------------------------------------
   Header lines against the printer
   ------------------------------------------------------------------------ *)

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

(* One header line, then the rest *)
Theorem parse_headers_line[local]:
  n ≠ [] ∧ EVERY (λc. c ≠ #":" ∧ c ≠ #" " ∧ c ≠ #"\r" ∧ c ≠ #"\n") n ∧
  ¬body_header n ∧ EVERY (λc. c ≠ #"\r" ∧ c ≠ #"\n") v ⇒
  parse_headers (n ++ #":" :: #" " :: (v ++ #"\r" :: #"\n" :: Y)) =
  case parse_headers Y of
    HDone hs r => HDone ((n, v) :: hs) r
  | HMore => HMore
  | HBad => HBad
Proof
  strip_tac >>
  ‘¬(crlf ≼ n ++ #":" :: #" " :: (v ++ #"\r" :: #"\n" :: Y)) ∧
   ¬(n ++ #":" :: #" " :: (v ++ #"\r" :: #"\n" :: Y) ≼ crlf)’
    by (Cases_on ‘n’ >> gvs[crlf_def]) >>
  ‘split_at #":" (n ++ #":" :: #" " :: (v ++ #"\r" :: #"\n" :: Y)) =
   (n, #":" :: #" " :: (v ++ #"\r" :: #"\n" :: Y))’
    by (irule split_at_char >> fs[EVERY_MEM] >> strip_tac >> res_tac >> fs[]) >>
  ‘¬EXISTS (λc. c = #" " ∨ c = #"\r" ∨ c = #"\n") n’
    by (fs[EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  ‘split_at #"\r" (v ++ #"\r" :: #"\n" :: Y) = (v, #"\r" :: #"\n" :: Y)’
    by (irule split_at_char >> fs[EVERY_MEM] >> strip_tac >> res_tac >> fs[]) >>
  ‘¬EXISTS (λc. c = #"\n") v’ by (fs[EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [parse_headers_def])) >>
  asm_simp_tac std_ss [LET_THM, crlf_prefix, colon_sp_prefix, DROP_2_CONS] >>
  simp[]
QED

(* MAIN (helper): printed valid header lines and the blank line, followed
   by anything, parse back *)
Theorem parse_headers_print:
  ∀hs rest. EVERY valid_header hs ⇒
    parse_headers (FLAT (MAP print_header hs) ++ crlf ++ rest) = HDone hs rest
Proof
  Induct
  >- simp[Once parse_headers_def, crlf_def] >>
  PairCases >> rw[valid_header_def] >>
  simp[print_header_def] >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC[parse_headers_line] >> simp[]
QED

(* MAIN (helper): HDone means printed valid header lines and the blank
   line, followed by the rest *)
Theorem DROP_crlf[local]:
  DROP 2 (crlf ++ l) = l ∧ DROP 2 (colon_sp ++ l) = l
Proof
  simp[crlf_def, colon_sp_def]
QED

Theorem parse_headers_done:
  ∀s hs r. parse_headers s = HDone hs r ⇒
           EVERY valid_header hs ∧ s = FLAT (MAP print_header hs) ++ crlf ++ r
Proof
  gen_tac >> completeInduct_on ‘LENGTH s’ >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> simp[Once parse_headers_def] >>
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
  ‘parse_headers l2 = HDone hs' r’ by metis_tac[] >>
  first_x_assum (qspec_then ‘LENGTH l2’ mp_tac) >>
  (impl_tac >- fs[]) >>
  disch_then (qspec_then ‘l2’ mp_tac) >> simp[] >>
  TRY (disch_then drule) >> strip_tac >>
  ‘¬MEM #":" nm’ by simp[Abbr ‘nm’, split_at_notmem] >>
  ‘¬MEM #"\r" vl’ by simp[Abbr ‘vl’, split_at_notmem] >>
  TRY (simp[valid_header_def] >> fs[EVERY_MEM, EXISTS_MEM] >> metis_tac[] >> NO_TAC) >>
  ‘l1 = vl ++ crlf ++ l2’ by metis_tac[APPEND_ASSOC] >>
  qpat_x_assum ‘s = nm ++ uu’ SUBST1_TAC >>
  qpat_x_assum ‘uu = colon_sp ++ l1’ SUBST1_TAC >>
  qpat_x_assum ‘l1 = vl ++ crlf ++ l2’ SUBST1_TAC >>
  qpat_x_assum ‘l2 = _’ SUBST1_TAC >>
  simp[print_header_def, colon_sp_def, crlf_def]
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

Theorem LENGTH_sp_http[simp]:
  LENGTH get_sp = 4 ∧ LENGTH sp_http10 = 11 ∧ LENGTH sp_http11 = 11
Proof
  EVAL_TAC
QED

Theorem print_hrequest_alt[local]:
  print_hrequest (GetH p "1.0" hs) =
    get_sp ++ p ++ sp_http10 ++ FLAT (MAP print_header hs) ++ crlf ∧
  print_hrequest (GetH p "1.1" hs) =
    get_sp ++ p ++ sp_http11 ++ FLAT (MAP print_header hs) ++ crlf
Proof
  simp[print_hrequest_def, get_sp_def, sp_http10_def, sp_http11_def, crlf_def]
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

(* The request line, in parse_hrequest's terms *)
Theorem parse_hrequest_line[local]:
  valid_path p ∧ (sp_http10 ≼ u ∨ sp_http11 ≼ u) ⇒
  parse_hrequest (get_sp ++ (p ++ u)) =
    if sp_http10 ≼ u then hfinish p "1.0" (parse_headers (DROP 11 u))
    else hfinish p "1.1" (parse_headers (DROP 11 u))
Proof
  strip_tac >>
  ‘EVERY (λc. c ≠ #" ") p ∧ ¬EXISTS (λc. c = #"\r" ∨ c = #"\n") p ∧ p ≠ []’
    by (fs[valid_path_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  ‘get_sp ≼ get_sp ++ (p ++ u)’ by REWRITE_TAC[IS_PREFIX_APPEND3] >>
  ‘DROP 4 (get_sp ++ (p ++ u)) = p ++ u’
    by (‘4 = LENGTH get_sp’ by simp[] >> pop_assum SUBST1_TAC >>
        REWRITE_TAC[DROP_LENGTH_APPEND]) >>
  ‘split_path (p ++ u) = (p, u) ∧ u ≠ []’
    by (‘∃y. u = sp_http10 ++ y ∨ u = sp_http11 ++ y’
          by (fs[IS_PREFIX_APPEND] >> metis_tac[]) >>
        fs[sp_http10_def, sp_http11_def] >> simp[split_path_space_h]) >>
  simp[parse_hrequest_def] >> rw[] >> fs[]
QED

(* MAIN: a printed valid request, followed by anything, parses back *)
Theorem parse_hprint:
  valid_hrequest r ⇒ parse_hrequest (print_hrequest r ++ rest) = HComplete r rest
Proof
  Cases_on ‘r’ >> rw[valid_hrequest_def, valid_version_def] >>
  simp[print_hrequest_alt] >> REWRITE_TAC[GSYM APPEND_ASSOC] >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC[parse_hrequest_line] >>
  simp[IS_PREFIX_APPEND3, sp_http_distinct, DROP_sp_http, hfinish_def,
       parse_headers_print]
QED

(* MAIN: HComplete means a printed valid request followed by the rest *)
Theorem parse_hcomplete:
  parse_hrequest s = HComplete r rest ⇒
  valid_hrequest r ∧ s = print_hrequest r ++ rest
Proof
  simp[parse_hrequest_def, hfinish_def] >>
  qabbrev_tac ‘t = DROP 4 s’ >>
  qabbrev_tac ‘p = FST (split_path t)’ >>
  qabbrev_tac ‘u = SND (split_path t)’ >>
  rw[AllCaseEqs()] >>
  drule parse_headers_done >> strip_tac >>
  ‘s = get_sp ++ t’
    by (qpat_x_assum ‘get_sp ≼ s’ (strip_assume_tac o REWRITE_RULE[IS_PREFIX_APPEND]) >>
        simp[Abbr ‘t’] >> ‘4 = LENGTH get_sp’ by simp[] >>
        pop_assum SUBST1_TAC >> REWRITE_TAC[DROP_LENGTH_APPEND]) >>
  ‘t = p ++ u’ by simp[Abbr ‘p’, Abbr ‘u’, split_path_join_h] >>
  ‘EVERY (λc. c ≠ #" ") p’ by simp[Abbr ‘p’, split_path_every_h] >>
  FIRST [qpat_x_assum ‘sp_http10 ≼ u’ (strip_assume_tac o REWRITE_RULE[IS_PREFIX_APPEND]),
         qpat_x_assum ‘sp_http11 ≼ u’ (strip_assume_tac o REWRITE_RULE[IS_PREFIX_APPEND])] >>
  rename1 ‘u = _ ++ l1’ >>
  ‘DROP 11 u = l1’ by (qpat_x_assum ‘u = _ ++ l1’ (fn th => REWRITE_TAC[th, DROP_sp_http])) >>
  simp[valid_hrequest_def, valid_version_def, valid_path_def, print_hrequest_alt] >>
  rpt conj_tac >> TRY (fs[EVERY_MEM, EXISTS_MEM] >> metis_tac[] >> NO_TAC) >>
  qpat_x_assum ‘s = _’ SUBST1_TAC >> qpat_x_assum ‘t = _’ SUBST1_TAC >>
  qpat_x_assum ‘u = _’ SUBST1_TAC >>
  ‘l1 = FLAT (MAP print_header hs) ++ crlf ++ rest’ by metis_tac[] >>
  pop_assum SUBST1_TAC >> simp[]
QED

Theorem parse_hcomplete_shorter:
  parse_hrequest s = HComplete r rest ⇒ LENGTH rest < LENGTH s
Proof
  strip_tac >> drule parse_hcomplete >> Cases_on ‘r’ >>
  rw[print_hrequest_def]
QED

(* HComplete is stable under extension *)
Theorem parse_hextend:
  parse_hrequest s = HComplete r rest ⇒
  parse_hrequest (s ++ x) = HComplete r (rest ++ x)
Proof
  strip_tac >> drule parse_hcomplete >> rw[] >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >> simp[parse_hprint]
QED

(* ------------------------------------------------------------------------
   All complete requests at the front of a buffer
   ------------------------------------------------------------------------ *)

Definition parse_all_h_def:
  parse_all_h s =
    case parse_hrequest s of
    | HComplete r rest => r :: parse_all_h rest
    | _ => []
Termination
  WF_REL_TAC ‘measure LENGTH’ >> metis_tac[parse_hcomplete_shorter]
End

Theorem parse_all_h_Complete:
  parse_hrequest s = HComplete r rest ⇒ parse_all_h s = r :: parse_all_h rest
Proof
  simp[Once parse_all_h_def]
QED

(* MAIN: printed valid requests, followed by a rest that does not start
   with a printed valid request, parse to exactly those requests *)
Theorem parse_all_hrequests:
  ∀rs. EVERY valid_hrequest rs ∧
       (∀r more. valid_hrequest r ⇒ rest ≠ print_hrequest r ++ more) ⇒
       parse_all_h (FLAT (MAP print_hrequest rs) ++ rest) = rs
Proof
  Induct
  >- (rw[Once parse_all_h_def] >> CASE_TAC >> drule parse_hcomplete >> rw[] >>
      metis_tac[])
  >> rw[] >>
  ‘parse_hrequest (print_hrequest h ++ (FLAT (MAP print_hrequest rs) ++ rest)) =
   HComplete h (FLAT (MAP print_hrequest rs) ++ rest)’ by simp[parse_hprint] >>
  drule parse_all_h_Complete >> REWRITE_TAC[APPEND_ASSOC] >> simp[]
QED

(* MAIN (helper): reading more can only add complete requests at the end *)
Theorem parse_all_h_mono:
  ∀s t. parse_all_h s ≼ parse_all_h (s ++ t)
Proof
  gen_tac >> completeInduct_on ‘LENGTH s’ >> rw[] >>
  Cases_on ‘parse_hrequest s’ >> simp[Once parse_all_h_def] >>
  drule parse_hextend >> disch_then (qspec_then ‘t’ assume_tac) >>
  simp[Once parse_all_h_def] >>
  ‘STRLEN s' < STRLEN s’ by metis_tac[parse_hcomplete_shorter] >>
  first_x_assum (qspec_then ‘STRLEN s'’ mp_tac) >> simp[]
QED

(* ------------------------------------------------------------------------
   Sanity checks
   ------------------------------------------------------------------------ *)

Theorem example_curl:
  parse_hrequest
    "GET / HTTP/1.1\r\nHost: localhost:7777\r\nUser-Agent: curl/8.7.1\r\nAccept: */*\r\n\r\nGET"
  = HComplete (GetH "/" "1.1" [("Host", "localhost:7777");
                               ("User-Agent", "curl/8.7.1"); ("Accept", "*/*")]) "GET"
Proof
  EVAL_TAC
QED

Theorem example_incomplete_headers:
  parse_hrequest "GET /a HTTP/1.1\r\nHost: x\r\n" = HIncomplete
Proof
  EVAL_TAC
QED

Theorem example_bad_header:
  parse_hrequest "GET /a HTTP/1.1\r\nno colon here\r\n\r\n" = HInvalid
Proof
  EVAL_TAC
QED
