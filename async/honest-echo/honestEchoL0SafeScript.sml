(*
  Route (d), S4 (design/46): echo_l0_safe.  Every finite prefix of the
  program's trace lies between the end of some round and the end of the
  next (the loop's rounds may be empty once it stops for lack of handle
  room); at a round boundary and inside a round, what each episode sent is
  a prefix of what it received (honestEchoL0Run's round_safe).
*)
Theory honestEchoL0Safe
Ancestors
  llist ffi honestL0 honestL0World honestL0WorldProps honestL0Rely
  asyncHLModel honestL1Model honestL1Steps honestL1PFModel
  asyncM3World honestEchoL0Spec honestEchoL0Trace honestEchoL0Events
  honestEchoL0Model honestEchoL0Inv honestEchoL0Round honestEchoL0Out honestEchoL0Run
  asyncCore asyncLevel1 asyncTranscript honestL1PFProg honestL1PFSpec
  asyncServer asyncServerSafety asyncM4GTrans
Libs
  preamble

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
  >- (drule arithmeticTheory.WOP >> strip_tac >> rename1 ‘¬(FLAT (GENLIST f m) ≼ evs)’ >>
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
        first_x_assum (qspec_then ‘n’ assume_tac) >>
        imp_res_tac rich_listTheory.IS_PREFIX_LENGTH >> fs[]) >>
  qexists_tac ‘N’ >> simp[GENLIST, SNOC_APPEND] >>
  ‘LFLATTEN (LGENLIST (λi. fromList (f i)) NONE) = fromList (FLAT (GENLIST f N))’
    by (ONCE_REWRITE_TAC [Q.SPEC ‘N’ (Q.GEN ‘n’ LFLATTEN_LGENLIST_chunk)] >>
        ‘LFLATTEN (LGENLIST (λi. fromList (f (N + i))) NONE) = LNIL’
          by simp[LFLATTEN_EQ_NIL, every_LGENLIST] >>
        simp[LAPPEND_NIL_2ND]) >>
  gvs[LPREFIX_fromList, from_toList]
QED
