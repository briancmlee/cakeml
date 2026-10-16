(*
  Extension facts for the header-tolerant request parser of
  httpHeadersParse: once a buffer is HInvalid, it stays HInvalid however
  much more is read, so it can never become a printed valid request, and
  parse_all_h finds no requests in it.

  Liveness needs "an invalid buffer stays invalid": this is the
  counterpart, for parse_hrequest, of httpGetParse's parse_invalid.

  Main facts:
   - parse_hrequest_invalid_ext: HInvalid persists under extension
   - parse_hinvalid:             an HInvalid buffer is never the start of
                                 a printed valid request
   - parse_all_h_invalid_ext:    parse_all_h of an extended HInvalid buffer
                                 is []
*)
Theory httpHeadersParseExt
Ancestors
  HttpGetSpec HttpHeadersSpec httpGetParse httpHeadersParse list rich_list
Libs
  preamble

(* ------------------------------------------------------------------------
   Prefixes and splits under extension
   ------------------------------------------------------------------------ *)

(* Two lists that diverge still diverge after extending one of them *)
Theorem prefix_diverge:
  ∀a b t. ¬(a ≼ b) ∧ ¬(b ≼ a) ⇒ ¬(a ≼ b ++ t) ∧ ¬(b ++ t ≼ a)
Proof
  Induct >> rw[] >> Cases_on ‘b’ >> gvs[]
QED

(* A prefix of s is a prefix of s ++ t, and dropping it commutes with ++ *)
Theorem prefix_append_drop:
  ∀p s t. p ≼ s ⇒ p ≼ s ++ t ∧ DROP (LENGTH p) (s ++ t) = DROP (LENGTH p) s ++ t
Proof
  rw[IS_PREFIX_APPEND] >> simp[DROP_APPEND1, DROP_LENGTH_APPEND] >>
  metis_tac[APPEND_ASSOC]
QED

(* split_at on an extended list: if s contains the separator, only the
   rest grows; otherwise all of s is in the first component *)
Theorem split_at_append:
  ∀s t. split_at c (s ++ t) =
        if SND (split_at c s) = [] then
          (FST (split_at c s) ++ FST (split_at c t), SND (split_at c t))
        else (FST (split_at c s), SND (split_at c s) ++ t)
Proof
  Induct >> rw[split_at_def] >> gvs[]
QED

(* The same for split_path, which splits at the first space *)
Theorem split_path_append:
  ∀s t. split_path (s ++ t) =
        if SND (split_path s) = [] then
          (FST (split_path s) ++ FST (split_path t), SND (split_path t))
        else (FST (split_path s), SND (split_path s) ++ t)
Proof
  Induct >> rw[split_path_def] >> gvs[]
QED

(* prefix_append_drop for the two-character constants *)
Theorem colon_sp_crlf_prefix:
  (colon_sp ≼ u ⇒ colon_sp ≼ u ++ t ∧ DROP 2 (u ++ t) = DROP 2 u ++ t) ∧
  (crlf ≼ u ⇒ crlf ≼ u ++ t ∧ DROP 2 (u ++ t) = DROP 2 u ++ t)
Proof
  metis_tac[prefix_append_drop, LENGTH_colon_sp, LENGTH_crlf]
QED

(* ------------------------------------------------------------------------
   Header lines
   ------------------------------------------------------------------------ *)

(* Bad header lines stay bad however they are extended *)
Theorem parse_headers_bad_ext:
  ∀s t. parse_headers s = HBad ⇒ parse_headers (s ++ t) = HBad
Proof
  recInduct parse_headers_ind >> rpt gen_tac >> strip_tac >> gen_tac >>
  simp[Once parse_headers_def] >>
  qabbrev_tac ‘n = FST (split_at #":" s)’ >>
  qabbrev_tac ‘u = SND (split_at #":" s)’ >>
  qabbrev_tac ‘v = FST (split_at #"\r" (DROP 2 u))’ >>
  qabbrev_tac ‘w = SND (split_at #"\r" (DROP 2 u))’ >>
  ‘split_at #":" (s ++ t) =
   if u = [] then (n ++ FST (split_at #":" t), SND (split_at #":" t))
   else (n, u ++ t)’ by simp[Abbr ‘n’, Abbr ‘u’, split_at_append] >>
  ‘split_at #"\r" (DROP 2 u ++ t) =
   if w = [] then (v ++ FST (split_at #"\r" t), SND (split_at #"\r" t))
   else (v, w ++ t)’ by simp[Abbr ‘v’, Abbr ‘w’, split_at_append] >>
  rw[AllCaseEqs()] >>
  ‘¬(crlf ≼ s ++ t) ∧ ¬(s ++ t ≼ crlf)’ by metis_tac[prefix_diverge] >>
  simp[Once parse_headers_def] >>
  TRY (qpat_x_assum ‘parse_headers (DROP 2 w) = HBad’ assume_tac >>
       first_x_assum (qspecl_then [‘n’, ‘u’, ‘v’, ‘w’] mp_tac) >>
       impl_tac >- fs[markerTheory.Abbrev_def] >>
       disch_then (qspec_then ‘t’ mp_tac) >> simp[] >> strip_tac) >>
  TRY (qpat_x_assum ‘colon_sp ≼ u’ assume_tac >>
       drule_then (qspec_then ‘t’ strip_assume_tac) (CONJUNCT1 colon_sp_crlf_prefix)) >>
  TRY (qpat_x_assum ‘crlf ≼ w’ assume_tac >>
       drule_then (qspec_then ‘t’ strip_assume_tac) (CONJUNCT2 colon_sp_crlf_prefix)) >>
  Cases_on ‘u = []’ >> Cases_on ‘w = []’ >> simp[EXISTS_APPEND] >>
  metis_tac[prefix_diverge]
QED

(* ------------------------------------------------------------------------
   Requests
   ------------------------------------------------------------------------ *)

(* hfinish is HInvalid exactly when the header lines are bad *)
Theorem hfinish_HInvalid:
  hfinish p v r = HInvalid ⇔ r = HBad
Proof
  Cases_on ‘r’ >> simp[hfinish_def]
QED

(* prefix_append_drop for "GET " *)
Theorem get_sp_prefix_ext:
  get_sp ≼ s ⇒ get_sp ≼ s ++ t ∧ DROP 4 (s ++ t) = DROP 4 s ++ t
Proof
  metis_tac[prefix_append_drop, LENGTH_sp_http]
QED

(* prefix_append_drop for the version suffixes *)
Theorem sp_http_prefix_ext:
  (sp_http10 ≼ u ⇒ sp_http10 ≼ u ++ t ∧ DROP 11 (u ++ t) = DROP 11 u ++ t) ∧
  (sp_http11 ≼ u ⇒ sp_http11 ≼ u ++ t ∧ DROP 11 (u ++ t) = DROP 11 u ++ t)
Proof
  metis_tac[prefix_append_drop, LENGTH_sp_http]
QED

(* The two version suffixes exclude each other *)
Theorem sp_http11_not_10:
  sp_http11 ≼ u ⇒ ∀t. ¬(sp_http10 ≼ u ++ t)
Proof
  rw[IS_PREFIX_APPEND] >> simp[sp_http10_def, sp_http11_def]
QED

(* invalid input stays invalid however it is extended *)
Theorem parse_hrequest_invalid_ext:
  parse_hrequest s = HInvalid ⇒ parse_hrequest (s ++ t) = HInvalid
Proof
  simp[SimpL “$==>”, parse_hrequest_def] >>
  qabbrev_tac ‘p = FST (split_path (DROP 4 s))’ >>
  qabbrev_tac ‘u = SND (split_path (DROP 4 s))’ >>
  ‘split_path (DROP 4 s ++ t) =
   if u = [] then (p ++ FST (split_path t), SND (split_path t))
   else (p, u ++ t)’ by simp[Abbr ‘p’, Abbr ‘u’, split_path_append] >>
  rw[hfinish_HInvalid] >>
  TRY (simp[parse_hrequest_def] >> metis_tac[prefix_diverge] >> NO_TAC) >>
  drule_then (qspec_then ‘t’ strip_assume_tac) get_sp_prefix_ext >>
  simp[parse_hrequest_def] >>
  TRY (qpat_x_assum ‘sp_http10 ≼ u’ assume_tac >>
       drule_then (qspec_then ‘t’ strip_assume_tac) (CONJUNCT1 sp_http_prefix_ext)) >>
  TRY (qpat_x_assum ‘sp_http11 ≼ u’ assume_tac >>
       drule_then (qspec_then ‘t’ strip_assume_tac) (CONJUNCT2 sp_http_prefix_ext) >>
       qpat_x_assum ‘sp_http11 ≼ u’
         (qspec_then ‘t’ assume_tac o MATCH_MP sp_http11_not_10)) >>
  TRY (qpat_x_assum ‘¬(u ≼ sp_http10 ∨ u ≼ sp_http11)’ assume_tac >>
       ‘¬(sp_http10 ≼ u ++ t) ∧ ¬(u ++ t ≼ sp_http10) ∧
        ¬(sp_http11 ≼ u ++ t) ∧ ¬(u ++ t ≼ sp_http11)’
         by metis_tac[prefix_diverge]) >>
  Cases_on ‘u = []’ >> fs[] >>
  simp[EXISTS_APPEND, hfinish_HInvalid, parse_headers_bad_ext]
QED

(* so it can never be extended into a printed valid request *)
Theorem parse_hinvalid:
  parse_hrequest s = HInvalid ⇒
  ∀t r rest. valid_hrequest r ⇒ s ++ t ≠ print_hrequest r ++ rest
Proof
  rpt strip_tac >>
  drule_then (qspec_then ‘t’ mp_tac) parse_hrequest_invalid_ext >>
  simp[parse_hprint]
QED

(* the complete requests at the front of an invalid buffer, however extended *)
Theorem parse_all_h_invalid_ext:
  parse_hrequest b = HInvalid ⇒ parse_all_h (b ++ x) = []
Proof
  strip_tac >> drule_then (qspec_then ‘x’ assume_tac) parse_hrequest_invalid_ext >>
  simp[Once parse_all_h_def]
QED
