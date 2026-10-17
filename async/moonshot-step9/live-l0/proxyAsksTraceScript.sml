(*
  proxy_asks_claim on the raw L0 trace, part (3): asks on the trace.
  The proxy's io (proxySem.proxy_div_n_semantics) is the startup events
  then round i's events eround_evs … i, flattened.  If infinitely many
  rounds hold an event with P, then infinitely many positions of io do
  (lflatten_inf_often).  The EP run's round events (honestL1EPAsksRun's
  erevs) are e1DriverLoop's eround_evs (erevs_eround_evs), so a front fd
  asked in infinitely many rounds (easked_at) is asked on the trace
  infinitely often in proxyL0Stmts' asks_io sense (easked_inf_asks).
*)
Theory proxyAsksTrace
Ancestors
  llist rich_list e1TracePrefix e1DriverLoop honestL1EPAsksRun honestL1EPModel
Libs
  preamble

(* ------------------------------------------------------------------------
   Generic: infinitely many rounds with P ⇒ P infinitely often on the trace
   ------------------------------------------------------------------------ *)

Theorem LENGTH_FLAT_GENLIST_SUC:
  LENGTH (FLAT (GENLIST f (SUC k))) = LENGTH (FLAT (GENLIST f k)) + LENGTH (f k)
Proof
  simp[GENLIST, SNOC_APPEND, FLAT_APPEND]
QED

Theorem LENGTH_FLAT_GENLIST_mono:
  ∀k n. n ≤ k ⇒ LENGTH (FLAT (GENLIST f n)) ≤ LENGTH (FLAT (GENLIST f k))
Proof
  Induct >> rw[] >> Cases_on ‘n = SUC k’ >> gvs[] >>
  ‘n ≤ k’ by simp[] >> first_x_assum drule >>
  simp[LENGTH_FLAT_GENLIST_SUC]
QED

(* Infinitely many non-empty rounds make the flattened prefix arbitrarily long *)
Theorem FLAT_GENLIST_unbounded:
  (∀N. ∃k ev. N ≤ k ∧ MEM ev (f k)) ⇒ ∀i. ∃n. i ≤ LENGTH (FLAT (GENLIST f n))
Proof
  strip_tac >> Induct >- (qexists_tac ‘0’ >> simp[]) >>
  pop_assum strip_assume_tac >>
  first_x_assum (qspec_then ‘n’ strip_assume_tac) >>
  qexists_tac ‘SUC k’ >> simp[LENGTH_FLAT_GENLIST_SUC] >>
  ‘LENGTH (FLAT (GENLIST f n)) ≤ LENGTH (FLAT (GENLIST f k))’
    by simp[LENGTH_FLAT_GENLIST_mono] >>
  ‘0 < LENGTH (f k)’ by (Cases_on ‘f k’ >> gvs[]) >>
  simp[]
QED

(* An event of round k sits at position |pre| + |rounds before k| + j *)
Theorem LNTH_rounds:
  j < LENGTH (f k) ⇒
  LNTH (LENGTH pre + LENGTH (FLAT (GENLIST f k)) + j)
       (LAPPEND (fromList pre) (LFLATTEN (LGENLIST (λi. fromList (f i)) NONE))) =
  SOME (EL j (f k))
Proof
  strip_tac >>
  ONCE_REWRITE_TAC [Q.SPEC ‘SUC k’ (Q.GEN ‘n’ LFLATTEN_LGENLIST_chunk)] >>
  REWRITE_TAC [GSYM LAPPEND_fromList, LAPPEND_ASSOC] >>
  simp[LNTH_LAPPEND, LLENGTH_fromList, LNTH_fromList, LENGTH_FLAT_GENLIST_SUC] >>
  simp[GENLIST, SNOC_APPEND, FLAT_APPEND, EL_APPEND2, EL_APPEND1]
QED

Theorem lflatten_inf_often:
  (∀N. ∃k ev. N ≤ k ∧ MEM ev (f k) ∧ P ev) ⇒
  ∀i. ∃i' ev. i ≤ i' ∧
              LNTH i' (LAPPEND (fromList pre) (LFLATTEN (LGENLIST (λi. fromList (f i)) NONE))) =
                SOME ev ∧ P ev
Proof
  strip_tac >> gen_tac >>
  ‘∀N. ∃k ev. N ≤ k ∧ MEM ev (f k)’ by metis_tac[] >>
  drule FLAT_GENLIST_unbounded >> disch_then (qspec_then ‘i’ strip_assume_tac) >>
  qpat_x_assum ‘∀N. ∃k ev. N ≤ k ∧ MEM ev (f k) ∧ P ev’ (qspec_then ‘n’ strip_assume_tac) >>
  qpat_x_assum ‘MEM ev (f k)’ (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  rename1 ‘ev = EL j (f k)’ >> pop_assum SUBST_ALL_TAC >>
  qexistsl [‘LENGTH pre + LENGTH (FLAT (GENLIST f k)) + j’, ‘EL j (f k)’] >>
  ‘LENGTH (FLAT (GENLIST f n)) ≤ LENGTH (FLAT (GENLIST f k))’
    by simp[LENGTH_FLAT_GENLIST_mono] >>
  simp[LNTH_rounds]
QED

(* ------------------------------------------------------------------------
   The EP run's rounds are the driver's rounds
   ------------------------------------------------------------------------ *)

Theorem nrun_erun:
  nrun lfd ifds m w0 n = erun lfd pol_never ifds m (w0, einit) n
Proof
  simp[nrun_def, e1DriverLoopTheory.erun_def]
QED

Theorem erevs_eround_evs:
  erun_ok lfd ifds m w0 ⇒
  erevs lfd ifds m w0 n = eround_evs lfd pol_never ifds m (w0, einit) n
Proof
  strip_tac >>
  ‘erounds lfd pol_never ifds m (w0, einit) (SUC n) ≠ NONE’ by fs[erun_ok_def] >>
  drule erun_SUC >> strip_tac >>
  simp[erevs_def, erhist_def, erworld_def, erstate_def, nrun_erun] >>
  Cases_on ‘SND (erun lfd pol_never ifds m (w0,einit) n)’ >> gvs[] >>
  rename1 ‘SND (erun _ _ _ _ _ _) = (ws, _)’ >> PairCases_on ‘ws’ >> gvs[]
QED

(* A front fd asked in infinitely many rounds is asked infinitely often on
   the proxy's io (asks_io's body, in_ask's poll disjunct) *)
Theorem easked_inf_asks:
  erun_ok lfd ifds m w0 ∧ (∀N. ∃k. N ≤ k ∧ easked_at lfd ifds m w0 k f) ⇒
  ∀i. ∃i' ev. i ≤ i' ∧
              LNTH i' (LAPPEND (fromList pre)
                         (LFLATTEN (LGENLIST (λi. fromList (eround_evs lfd pol_never ifds m (w0, einit) i))
                                             NONE))) = SOME ev ∧
              ∃conf bs. ev = IO_event (ExtCall «sys_poll») conf bs ∧
                        ∃e. MEM (f, e) (MAP pe_fe (pollfd_entries (DROP 16 (MAP FST bs)))) ∧ ODD e
Proof
  strip_tac >>
  ho_match_mp_tac lflatten_inf_often >>
  gen_tac >>
  qpat_x_assum ‘∀N. ∃k. N ≤ k ∧ _’ (qspec_then ‘N’ strip_assume_tac) >>
  qpat_x_assum ‘easked_at _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [easked_at_def]) >>
  qpat_x_assum ‘erun_ok _ _ _ _’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [MATCH_MP erevs_eround_evs th])) >>
  qexistsl [‘k’, ‘IO_event (ExtCall «sys_poll») [0w] bs’] >>
  ASM_REWRITE_TAC [] >>
  qexistsl [‘[0w]’, ‘bs’] >> REWRITE_TAC [] >>
  qexists_tac ‘e’ >> ASM_REWRITE_TAC []
QED
