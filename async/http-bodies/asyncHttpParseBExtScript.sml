(*
  Extension facts for the bodies request parser of asyncHttpParseB: once
  a buffer is BInvalid, it stays BInvalid however much more is read, so it
  can never become a printed valid request, and parse_all_b finds no
  requests in it.  The counterpart of asyncHttpParseHExt, which it reuses
  for the request line and header lines; the new cases are the method and
  an invalid header block (Transfer-Encoding, duplicate or non-canonical
  Content-Length), which reading more cannot change.

  Main facts:
   - parse_brequest_invalid_ext: BInvalid persists under extension
   - parse_binvalid:             a BInvalid buffer is never the start of a
                                 printed valid request
   - parse_all_b_invalid_ext
*)
Theory asyncHttpParseBExt
Ancestors
  HttpSpec HttpSpecHeaders HttpSpecBodies asyncHttpParse asyncHttpParseH
  asyncHttpParseB asyncHttpParseHExt list rich_list
Libs
  preamble

(* An invalid header block stays invalid: the body stage does not look at
   what follows to decide invalidity *)
Theorem bbody_invalid_ext:
  bbody m p v hs rest = BInvalid ⇒ bbody m p v hs (rest ++ t) = BInvalid
Proof
  rw[bbody_def, AllCaseEqs()] >> gvs[]
QED

(* Complete header lines stay complete, with the same lines *)
Theorem parse_headers_done_ext:
  parse_headers s = HDone hs r ⇒ parse_headers (s ++ t) = HDone hs (r ++ t)
Proof
  strip_tac >> drule parse_headers_done >> strip_tac >> gvs[] >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >>
  simp[parse_headers_print |> REWRITE_RULE [GSYM APPEND_ASSOC]]
QED

Theorem bfinish_invalid_ext:
  bfinish m p v r = BInvalid ⇒
  ∀t r'. (r = HBad ⇒ r' = HBad) ∧
         (∀hs rest. r = HDone hs rest ⇒ r' = HDone hs (rest ++ t)) ⇒
         bfinish m p v r' = BInvalid
Proof
  Cases_on ‘r’ >> rw[bfinish_def] >> simp[bfinish_def, bbody_invalid_ext]
QED

(* After the method: invalid stays invalid *)
Theorem bline_invalid_ext:
  bline m t0 = BInvalid ⇒ bline m (t0 ++ t) = BInvalid
Proof
  simp[SimpL “$==>”, bline_def] >>
  qabbrev_tac ‘p = FST (split_path t0)’ >>
  qabbrev_tac ‘u = SND (split_path t0)’ >>
  ‘split_path (t0 ++ t) =
   if u = [] then (p ++ FST (split_path t), SND (split_path t))
   else (p, u ++ t)’ by simp[Abbr ‘p’, Abbr ‘u’, split_path_append] >>
  rw[] >>
  TRY (simp[bline_def] >> metis_tac[prefix_diverge] >> NO_TAC) >>
  simp[bline_def] >>
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
  Cases_on ‘u = []’ >> fs[EXISTS_APPEND] >>
  qpat_x_assum ‘bfinish _ _ _ _ = BInvalid’ mp_tac >>
  Cases_on ‘parse_headers (DROP 11 u)’ >> simp[bfinish_def] >>
  imp_res_tac parse_headers_bad_ext >> imp_res_tac parse_headers_done_ext >>
  simp[bbody_invalid_ext]
QED

Theorem post_sp_prefix_ext[local]:
  post_sp ≼ s ⇒ post_sp ≼ s ++ t ∧ DROP 5 (s ++ t) = DROP 5 s ++ t
Proof
  metis_tac[prefix_append_drop, LENGTH_post_sp]
QED

(* MAIN (helper): invalid input stays invalid however it is extended *)
Theorem parse_brequest_invalid_ext:
  parse_brequest s = BInvalid ⇒ parse_brequest (s ++ t) = BInvalid
Proof
  simp[SimpL “$==>”, parse_brequest_def] >> rw[]
  >- (drule_then (qspec_then ‘t’ strip_assume_tac) get_sp_prefix_ext >>
      simp[parse_brequest_def, bline_invalid_ext])
  >- (drule_then (qspec_then ‘t’ strip_assume_tac) post_sp_prefix_ext >>
      ‘¬(get_sp ≼ s ++ t)’
        by (fs[IS_PREFIX_APPEND, get_sp_def, post_sp_def] >> gvs[]) >>
      simp[parse_brequest_def, bline_invalid_ext]) >>
  ‘¬(get_sp ≼ s ++ t) ∧ ¬(s ++ t ≼ get_sp) ∧
   ¬(post_sp ≼ s ++ t) ∧ ¬(s ++ t ≼ post_sp)’ by metis_tac[prefix_diverge] >>
  simp[parse_brequest_def]
QED

(* MAIN: an invalid buffer can never be extended into a printed valid
   request (followed by anything) *)
Theorem parse_binvalid:
  parse_brequest s = BInvalid ⇒
  ∀t r rest. valid_brequest r ⇒ s ++ t ≠ print_brequest r ++ rest
Proof
  rpt strip_tac >>
  drule_then (qspec_then ‘t’ mp_tac) parse_brequest_invalid_ext >>
  simp[parse_bprint]
QED

Theorem parse_all_b_invalid_ext:
  parse_brequest b = BInvalid ⇒ parse_all_b (b ++ x) = []
Proof
  strip_tac >> drule_then (qspec_then ‘x’ assume_tac) parse_brequest_invalid_ext >>
  simp[Once parse_all_b_def]
QED
