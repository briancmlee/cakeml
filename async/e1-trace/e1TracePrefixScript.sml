(*
  The shared E1 trace layer (close-v2's part (a1)): every finite prefix of
  a run's trace, a start followed by its rounds' events, lies inside the
  start and the events of finitely many rounds.  A claim on every LPREFIX
  of the trace whose clauses are prefix-closed is thus a claim on the
  trace at round boundaries (e1_lprefix_rounds; e1_lprefix_fromList for a
  run that terminates).

  The llist lemmas up to LPREFIX_rounds_any are verbatim copies of
  m4-common's asyncM4GTrans (LFLATTEN_LGENLIST_chunk, rounds_LPREFIX,
  LPREFIX_comparable) and honest-echo's honestEchoL0Safe
  (LPREFIX_rounds_any), copied to keep e1-trace off those directories'
  ancestries; to be merged into one place when the branches meet.
*)
Theory e1TracePrefix
Ancestors
  llist
Libs
  preamble

(* ------------------------------------------------------------------------
   Copies (see the header)
   ------------------------------------------------------------------------ *)

Theorem LFLATTEN_fromList_GENLIST[local]:
  ∀n. LFLATTEN (fromList (GENLIST (λi. fromList (f i)) n)) =
      fromList (FLAT (GENLIST f n))
Proof
  Induct >> simp[GENLIST, SNOC_APPEND, GSYM LAPPEND_fromList,
                 LFLATTEN_APPEND_FINITE1] >>
  simp[LAPPEND_fromList, FLAT_APPEND, LAPPEND_NIL_2ND]
QED

Theorem LFLATTEN_LGENLIST_chunk:
  LFLATTEN (LGENLIST (λi. fromList (f i)) NONE) =
  LAPPEND (fromList (FLAT (GENLIST f n)))
          (LFLATTEN (LGENLIST (λi. fromList (f (n + i))) NONE))
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV
    [Q.SPEC ‘n’ (Q.GEN ‘n’ LGENLIST_CHUNK_GENLIST)])) >>
  simp[LFLATTEN_APPEND_FINITE1] >>
  simp[LFLATTEN_fromList_GENLIST, combinTheory.o_DEF] >>
  AP_TERM_TAC >> AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM]
QED

Theorem rounds_LPREFIX:
  LPREFIX (fromList (FLAT (GENLIST f n)))
          (LFLATTEN (LGENLIST (λi. fromList (f i)) NONE))
Proof
  ONCE_REWRITE_TAC[LFLATTEN_LGENLIST_chunk] >> simp[LPREFIX_APPEND] >>
  metis_tac[]
QED

Theorem LPREFIX_LTAKE[local]:
  LPREFIX (fromList l) ll ⇒ LTAKE (LENGTH l) ll = SOME l
Proof
  rw[LPREFIX_APPEND] >>
  qspecl_then [‘ll'’, ‘l’, ‘0’] mp_tac LTAKE_LAPPEND_fromList >> simp[]
QED

(* Two finite prefixes of the same lazy list are comparable *)
Theorem LPREFIX_comparable:
  LPREFIX (fromList a) ll ∧ LPREFIX (fromList b) ll ∧ LENGTH a ≤ LENGTH b ⇒
  a ≼ b
Proof
  rw[] >> imp_res_tac LPREFIX_LTAKE >>
  drule_all LTAKE_TAKE_LESS >> rw[] >> gvs[] >>
  ‘a = TAKE (LENGTH a) b’ by gvs[] >> pop_assum SUBST1_TAC >>
  simp[IS_PREFIX_APPEND] >> qexists_tac ‘DROP (LENGTH a) b’ >> simp[]
QED

Theorem FLAT_GENLIST_mono[local]:
  ∀d n. FLAT (GENLIST f n) ≼ FLAT (GENLIST f (n + d))
Proof
  Induct >> simp[] >> rpt gen_tac >>
  first_x_assum (qspec_then ‘n’ mp_tac) >>
  simp[GSYM ADD_SUC, GENLIST, SNOC_APPEND] >>
  rw[rich_listTheory.IS_PREFIX_APPEND] >> simp[]
QED

(* Every finite prefix of a trace made of rounds lies between the end of
   some round and the end of the next (rounds may be empty) *)
Theorem LPREFIX_rounds_any:
  LPREFIX (fromList evs) (LFLATTEN (LGENLIST (λi. fromList (f i)) NONE)) ⇒
  ∃n. FLAT (GENLIST f n) ≼ evs ∧ evs ≼ FLAT (GENLIST f (SUC n))
Proof
  strip_tac >>
  Cases_on ‘∃m. ¬(FLAT (GENLIST f m) ≼ evs)’
  >- (qpat_x_assum ‘∃m. _’ (strip_assume_tac o HO_MATCH_MP arithmeticTheory.WOP) >>
      rename1 ‘¬(FLAT (GENLIST f m) ≼ evs)’ >>
      Cases_on ‘m’ >> gvs[] >> rename1 ‘GENLIST f (SUC n)’ >>
      qexists_tac ‘n’ >> simp[] >>
      Cases_on ‘LENGTH evs ≤ LENGTH (FLAT (GENLIST f (SUC n)))’
      >- (irule LPREFIX_comparable >> metis_tac[rounds_LPREFIX]) >>
      ‘FLAT (GENLIST f (SUC n)) ≼ evs’
        by (irule LPREFIX_comparable >> simp[] >> metis_tac[rounds_LPREFIX]) >>
      gvs[]) >>
  gvs[] >>
  (* every round boundary is inside evs: the rounds are eventually empty *)
  ‘∃N. ∀p. N ≤ p ⇒ f p = []’
    by (CCONTR_TAC >> gvs[] >>
        ‘∀m. ∃n. m ≤ LENGTH (FLAT (GENLIST f n))’
          by (Induct >> simp[] >> gvs[] >>
              first_x_assum (qspec_then ‘n’ strip_assume_tac) >>
              qexists_tac ‘SUC p’ >> simp[GENLIST, SNOC_APPEND] >>
              ‘FLAT (GENLIST f n) ≼ FLAT (GENLIST f (n + (p − n)))’
                by simp[FLAT_GENLIST_mono] >>
              gvs[] >> imp_res_tac rich_listTheory.IS_PREFIX_LENGTH >>
              Cases_on ‘f p’ >> gvs[]) >>
        first_x_assum (qspec_then ‘SUC (LENGTH evs)’ strip_assume_tac) >>
        qpat_x_assum ‘∀m. FLAT _ ≼ evs’ (qspec_then ‘n’ assume_tac) >>
        imp_res_tac rich_listTheory.IS_PREFIX_LENGTH >> fs[]) >>
  qexists_tac ‘N’ >> simp[GENLIST, SNOC_APPEND] >>
  ‘LFLATTEN (LGENLIST (λi. fromList (f i)) NONE) = fromList (FLAT (GENLIST f N))’
    by (ONCE_REWRITE_TAC [Q.SPEC ‘N’ (Q.GEN ‘n’ LFLATTEN_LGENLIST_chunk)] >>
        ‘LFLATTEN (LGENLIST (λi. fromList (f (N + i))) NONE) = LNIL’
          by simp[LFLATTEN_EQ_NIL, every_LGENLIST] >>
        simp[LAPPEND_NIL_2ND]) >>
  gvs[LPREFIX_fromList, from_toList]
QED

(* ------------------------------------------------------------------------
   The run's start, then its rounds
   ------------------------------------------------------------------------ *)

Theorem LPREFIX_LAPPEND_fromList:
  LPREFIX (fromList (pre ++ l)) (LAPPEND (fromList pre) ll) ⇔ LPREFIX (fromList l) ll
Proof
  Induct_on ‘pre’ >> simp[LPREFIX_LCONS]
QED

(* A diverging run: a finite prefix of start ++ rounds is within the start
   and the first n rounds, for some n *)
Theorem e1_lprefix_rounds:
  LPREFIX (fromList evs)
    (LAPPEND (fromList pre) (LFLATTEN (LGENLIST (λi. fromList (f i)) NONE))) ⇒
  ∃n. evs ≼ pre ++ FLAT (GENLIST f n)
Proof
  strip_tac >>
  ‘LPREFIX (fromList pre)
     (LAPPEND (fromList pre) (LFLATTEN (LGENLIST (λi. fromList (f i)) NONE)))’
    by (simp[LPREFIX_APPEND] >> metis_tac[]) >>
  Cases_on ‘LENGTH evs ≤ LENGTH pre’
  >- (‘evs ≼ pre’ by (irule LPREFIX_comparable >> metis_tac[]) >>
      qexists_tac ‘0’ >> simp[]) >>
  ‘pre ≼ evs’ by (irule LPREFIX_comparable >> simp[] >> metis_tac[]) >>
  qpat_x_assum ‘pre ≼ evs’ (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
  rename1 ‘evs = pre ++ l’ >> gvs[] >>
  qpat_x_assum ‘LPREFIX (fromList (pre ++ l)) _’
    (assume_tac o REWRITE_RULE [LPREFIX_LAPPEND_fromList]) >>
  drule LPREFIX_rounds_any >> strip_tac >> qexists_tac ‘SUC n’ >> simp[]
QED

(* A terminating run *)
Theorem e1_lprefix_fromList:
  LPREFIX (fromList evs) (fromList l) ⇔ evs ≼ l
Proof
  simp[LPREFIX_fromList, from_toList]
QED
