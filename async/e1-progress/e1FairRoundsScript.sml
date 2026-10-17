(*
  [F1] from the trace to the rounds (close-v2, shared E1 progress layer):
  on a run's trace, a start followed by its rounds' events, the trace
  fairness F1_io (a call on f attempted infinitely often goes through
  infinitely often) gives rfair at round granularity, the form
  e1FlushLift's flush_lift takes.

  MAIN: F1_io_rfair.
*)
Theory e1FairRounds
Ancestors
  e1FlushLift e1TracePrefix clientLiveCopy llist
Libs
  preamble

(* arithmetic, clear of the quantified hypotheses *)
val ar_tac = rpt (qpat_x_assum ‘∀x. _’ kall_tac) >> decide_tac

(* A run's trace: its start, then its rounds' events *)
Definition rio_def:
  rio (pre : 'a list) r = LAPPEND (fromList pre) (LFLATTEN (LGENLIST (λi. fromList (r i)) NONE))
End

(* Where round k starts in it *)
Definition rbl_def:
  rbl (pre : 'a list) (r : num -> 'a list) k = LENGTH pre + LENGTH (FLAT (GENLIST r k))
End

Theorem FLAT_GENLIST_split:
  ∀d k. FLAT (GENLIST r (k + d)) = FLAT (GENLIST r k) ++ FLAT (GENLIST (λi. r (k + i)) d)
Proof
  Induct >> fs[GENLIST, ADD_CLAUSES, FLAT_SNOC]
QED

Theorem rbl_mono:
  k ≤ k' ⇒ rbl pre r k ≤ rbl pre r k'
Proof
  strip_tac >> ‘∃d. k' = k + d’ by (qexists_tac ‘k' − k’ >> decide_tac) >>
  pop_assum SUBST1_TAC >>
  REWRITE_TAC[rbl_def, FLAT_GENLIST_split, LENGTH_APPEND] >> decide_tac
QED

Theorem rbl_SUC:
  rbl pre r (SUC k) = rbl pre r k + LENGTH (r k)
Proof
  simp[rbl_def, GENLIST, FLAT_SNOC]
QED

Theorem rio_chunk:
  rio pre r =
  LAPPEND (fromList (pre ++ FLAT (GENLIST r k)))
          (LFLATTEN (LGENLIST (λi. fromList (r (k + i))) NONE))
Proof
  REWRITE_TAC[rio_def, GSYM LAPPEND_fromList, LAPPEND_ASSOC] >>
  AP_TERM_TAC >> MATCH_ACCEPT_TAC LFLATTEN_LGENLIST_chunk
QED

(* Round k's p-th event, in the trace *)
Theorem rio_LNTH:
  p < LENGTH (r k) ⇒ LNTH (rbl pre r k + p) (rio pre r) = SOME (EL p (r k))
Proof
  strip_tac >>
  once_rewrite_tac [Q.INST [‘k’ |-> ‘SUC k’] rio_chunk] >>
  simp[LNTH_LAPPEND, LNTH_fromList, rbl_def, GENLIST, FLAT_SNOC] >>
  simp[EL_APPEND2, EL_APPEND_EQN]
QED

(* An event at or after round j's start, within the first K rounds, is in
   some round k with j ≤ k *)
Theorem rio_locate:
  ∀Kb. rbl pre r j ≤ i ∧ i < rbl pre r Kb ∧ LNTH i (rio pre r) = SOME ev ⇒
      ∃k. j ≤ k ∧ MEM ev (r k)
Proof
  Induct
  >- (rpt strip_tac >> qpat_x_assum ‘i < _’ mp_tac >> qpat_x_assum ‘_ ≤ i’ mp_tac >> simp[rbl_def]) >>
  rpt strip_tac >>
  Cases_on ‘i < rbl pre r Kb’ >- (qpat_x_assum ‘_ ⇒ _’ mp_tac >> asm_rewrite_tac[]) >>
  qexists_tac ‘Kb’ >>
  ‘j ≤ Kb’
    by (CCONTR_TAC >> ‘SUC Kb ≤ j’ by decide_tac >>
        ‘rbl pre r (SUC Kb) ≤ rbl pre r j’ by simp[rbl_mono] >> decide_tac) >>
  ‘i − rbl pre r Kb < LENGTH (r Kb)’ by fs[rbl_SUC] >>
  drule rio_LNTH >> disch_then (qspec_then ‘pre’ mp_tac) >>
  ‘rbl pre r Kb + (i − rbl pre r Kb) = i’ by decide_tac >>
  simp[] >> strip_tac >> fs[] >>
  simp[MEM_EL] >> qexists_tac ‘i − rbl pre r Kb’ >> fs[]
QED

(* With nonempty rounds infinitely often, round starts are unbounded *)
Theorem rbl_unbounded:
  (∀i. ∃k. i ≤ k ∧ r k ≠ []) ⇒ ∀m. ∃Kb. m ≤ rbl pre r Kb
Proof
  strip_tac >> Induct
  >- (qexists_tac ‘0’ >> simp[]) >>
  pop_assum strip_assume_tac >>
  first_x_assum (qspec_then ‘Kb’ strip_assume_tac) >>
  qexists_tac ‘SUC k’ >> simp[rbl_SUC] >>
  ‘rbl pre r Kb ≤ rbl pre r k’ by simp[rbl_mono] >>
  Cases_on ‘r k’ >> fs[]
QED

(* MAIN *)
Theorem F1_io_rfair:
  F1_io (rio pre r) ⇒
  rfair (λk. ∃ev. MEM ev (r k) ∧ ev_on nm f ev)
        (λk. ∃ev. MEM ev (r k) ∧ ev_on nm f ev ∧ ¬retried ev)
Proof
  rw[rfair_def] >>
  ‘∀i. ∃k. i ≤ k ∧ r k ≠ []’
    by (gen_tac >> first_x_assum (qspec_then ‘i’ strip_assume_tac) >>
        qexists_tac ‘k’ >> Cases_on ‘r k’ >> fs[]) >>
  drule rbl_unbounded >> strip_tac >>
  (* the calls on f, attempted infinitely often in the trace *)
  ‘∀i. ∃i' ev. i ≤ i' ∧ LNTH i' (rio pre r) = SOME ev ∧ ev_on nm f ev’
    by (gen_tac >> first_assum (qspecl_then [‘pre’, ‘i’] strip_assume_tac) >>
        qpat_x_assum ‘∀i. ∃k. i ≤ k ∧ ∃ev. _’ (qspec_then ‘Kb’ strip_assume_tac) >>
        fs[MEM_EL] >> rename1 ‘p < LENGTH (r k)’ >>
        qexistsl_tac [‘rbl pre r k + p’, ‘EL p (r k)’] >>
        simp[rio_LNTH] >>
        ‘rbl pre r Kb ≤ rbl pre r k’ by simp[rbl_mono] >>
        qpat_x_assum ‘ev = _’ (SUBST_ALL_TAC o SYM) >> conj_tac >- ar_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘F1_io _’ (mp_tac o REWRITE_RULE [F1_io_def]) >>
  disch_then (qspecl_then [‘nm’, ‘f’] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (qspec_then ‘rbl pre r i’ strip_assume_tac) >>
  qpat_x_assum ‘∀pre m. ∃Kb. m ≤ rbl pre r Kb’ (qspecl_then [‘pre’, ‘SUC i'’] strip_assume_tac) >>
  ‘i' < rbl pre r Kb’ by decide_tac >>
  drule_all rio_locate >> strip_tac >>
  qexists_tac ‘k’ >> simp[] >> metis_tac[]
QED
