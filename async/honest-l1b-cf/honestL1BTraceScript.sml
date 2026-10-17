(*
  The CakeML loop's traces are the blocking model's (honestL1BTransfer's
  btrace), while the D25 guard holds (it always holds unless the handle
  counter runs out):
   - the loop never sleeps: its trace, the rounds' events flattened, is
     the model run's trace;
   - the loop sleeps in round n: the events before the final poll are.
  For a server never busy (bz = K F).

  Under the PF run's standing facts (run_ok, which includes D25's bound
  on every PF round) the guard never fires in the CakeML loop
  (bt_guard_ok); and the PF model run has a trace (pf_trace_exists).

  MAIN: div_btrace, sleep_btrace, bt_guard_ok, pf_trace_exists.
*)
Theory honestL1BTrace
Ancestors
  llist rich_list honestL0 honestL0World honestL1Model honestL1PFModel honestL1PFProg
  honestL1BModel honestL1BCorr honestL1BDrains honestL1BSim honestL1BTransfer honestL1BSpec
  honestL1BRefine honestL1BNoFail honestL1PFInv honestL1PFLive asyncM4GTrans
Libs
  preamble

(* ------------------------------------------------------------------------
   Prefixes of a flattened list of rounds
   ------------------------------------------------------------------------ *)

Theorem LENGTH_FLAT_GENLIST_mono[local]:
  ∀n m. n ≤ m ⇒ LENGTH (FLAT (GENLIST f n)) ≤ LENGTH (FLAT (GENLIST f m))
Proof
  Induct_on ‘m’ >> rw[] >> Cases_on ‘n = SUC m’ >> gvs[GENLIST, FLAT_SNOC] >>
  first_x_assum (qspec_then ‘n’ mp_tac) >> simp[]
QED

(* A bounded flattening ends: from some round on, the rounds are empty *)
Theorem FLAT_GENLIST_bounded[local]:
  (∀n. LENGTH (FLAT (GENLIST f n)) < b) ⇒ ∃N. ∀i. N ≤ i ⇒ f i = []
Proof
  strip_tac >>
  ‘∃n. ∀m. LENGTH (FLAT (GENLIST f m)) ≤ LENGTH (FLAT (GENLIST f n))’
    by (CCONTR_TAC >> fs[NOT_LESS_EQUAL] >>
        ‘∀k. ∃m. k ≤ LENGTH (FLAT (GENLIST f m))’
          by (Induct >- simp[] >>
              pop_assum strip_assume_tac >>
              qpat_assum ‘∀n. ∃m. _’ (qspec_then ‘m’ strip_assume_tac) >>
              qexists_tac ‘m'’ >> simp[]) >>
        pop_assum (qspec_then ‘b’ strip_assume_tac) >>
        qpat_x_assum ‘∀n. LENGTH _ < b’ (qspec_then ‘m’ mp_tac) >> simp[]) >>
  qexists_tac ‘n’ >> rpt strip_tac >>
  ‘LENGTH (FLAT (GENLIST f n)) ≤ LENGTH (FLAT (GENLIST f i))’
    by (irule LENGTH_FLAT_GENLIST_mono >> simp[]) >>
  first_x_assum (qspec_then ‘SUC i’ mp_tac) >>
  simp[GENLIST, FLAT_SNOC] >> strip_tac >> Cases_on ‘f i’ >> fs[]
QED

Theorem LFLATTEN_LGENLIST_nils[local]:
  (∀i. f i = []) ⇒ LFLATTEN (LGENLIST (λi. fromList (f i)) NONE) = [||]
Proof
  rw[LFLATTEN_EQ_NIL, every_LGENLIST]
QED

Theorem LPREFIX_fromList_LAPPEND:
  ∀X p. LPREFIX (fromList p) (LAPPEND (fromList X) R) ⇔
          p ≼ X ∨ ∃t. p = X ++ t ∧ LPREFIX (fromList t) R
Proof
  Induct >> simp[]
  >- (Cases >> simp[]) >>
  rpt gen_tac >> Cases_on ‘p’ >> simp[LPREFIX_LCONS] >> metis_tac[]
QED

Theorem LPREFIX_LFLATTEN:
  LPREFIX (fromList p) (LFLATTEN (LGENLIST (λi. fromList (f i)) NONE)) ⇔
    ∃n. p ≼ FLAT (GENLIST f n)
Proof
  eq_tac >> strip_tac
  >- (Cases_on ‘∃n. LENGTH p ≤ LENGTH (FLAT (GENLIST f n))’
      >- (fs[] >> qexists_tac ‘n’ >>
          qpat_x_assum ‘LPREFIX _ _’ mp_tac >>
          ONCE_REWRITE_TAC [Q.SPEC ‘n’ (Q.GEN ‘n’ LFLATTEN_LGENLIST_chunk)] >>
          rw[LPREFIX_fromList_LAPPEND] >> fs[] >>
          ‘t = []’ by (Cases_on ‘t’ >> fs[]) >> simp[]) >>
      fs[NOT_LESS_EQUAL] >>
      drule FLAT_GENLIST_bounded >> strip_tac >>
      qexists_tac ‘N’ >>
      qpat_x_assum ‘LPREFIX _ _’ mp_tac >>
      ONCE_REWRITE_TAC [Q.SPEC ‘N’ (Q.GEN ‘n’ LFLATTEN_LGENLIST_chunk)] >>
      ‘LFLATTEN (LGENLIST (λi. fromList (f (N + i))) NONE) = [||]’
        by simp[LFLATTEN_EQ_NIL, every_LGENLIST] >>
      simp[LPREFIX_fromList_LAPPEND] >> rw[] >> simp[] >>
      Cases_on ‘t’ >> fs[LPREFIX_LCONS]) >>
  ONCE_REWRITE_TAC [Q.SPEC ‘n’ (Q.GEN ‘n’ LFLATTEN_LGENLIST_chunk)] >>
  simp[LPREFIX_fromList_LAPPEND]
QED

(* ------------------------------------------------------------------------
   The guarded run's events, while it is awake
   ------------------------------------------------------------------------ *)

Theorem bt_run_evs:
  bt_awake lfd hw ifds m ws0 ⇒
  ∀n. FST (SND (SND (bt_run lfd hw ifds m ws0 n))) =
      FLAT (GENLIST (bround_evs lfd hw ifds m ws0) n)
Proof
  strip_tac >> Induct >> simp[] >>
  drule bt_run_SUC >> disch_then (qspec_then ‘n’ mp_tac) >>
  IF_CASES_TAC >> rw[] >> simp[GENLIST, FLAT_SNOC]
QED

(* The guard holds in every round the guarded run runs *)
Definition bt_guard_def:
  bt_guard lfd hw ifds m ws0 ⇔
    ∀i h ws evs logs. brounds_t lfd hw ifds m ws0 i = SOME (BRun h ws evs logs) ⇒
                      hdl_room lfd (SND ws) (naccepts (new_actions (log_of m) h))
End

Theorem bt_guard_brounds:
  bt_guard lfd hw ifds m ws0 ⇒
  ∀n. brounds_t lfd hw ifds m ws0 n = brounds lfd (pol_self hw) ifds (K F) m ws0 n
Proof
  rw[bt_guard_def] >> irule brounds_t_brounds >> metis_tac[]
QED

(* MAIN: the loop never sleeps, and the guard holds: its trace is the
   blocking model run's *)
Theorem div_btrace:
  bt_awake lfd hw ifds m (w0, ps0) ∧ bt_guard lfd hw ifds m (w0, ps0) ⇒
  btrace lfd (pol_self hw) ifds (K F) m w0 ps0
    (LFLATTEN (LGENLIST (λi. fromList (bround_evs lfd hw ifds m (w0, ps0) i)) NONE))
Proof
  strip_tac >> drule bt_guard_brounds >> strip_tac >>
  drule bt_run_evs >> strip_tac >>
  simp[btrace_def, LPREFIX_LFLATTEN, bpre_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  fs[bt_awake_def] >> rw[] >> eq_tac >> rw[]
  >- (disj1_tac >>
      qpat_assum ‘∀n. ∃h ws evs logs. _’ (qspec_then ‘n’ strip_assume_tac) >>
      qexistsl [‘n’, ‘h’, ‘ws’, ‘evs'’, ‘logs’] >> simp[] >>
      qpat_x_assum ‘∀n. FST _ = _’ (qspec_then ‘n’ mp_tac) >>
      simp[bt_run_def] >> strip_tac >> gvs[combinTheory.o_DEF, ETA_THM])
  >- (qexists_tac ‘n’ >>
      qpat_x_assum ‘∀n. FST _ = _’ (qspec_then ‘n’ mp_tac) >>
      simp[bt_run_def] >> strip_tac >> gvs[ETA_THM])
  >> qpat_x_assum ‘∀n. ∃h ws evs logs. _’ (qspec_then ‘n’ strip_assume_tac) >> gvs[]
QED

(* After sleeping in round n, every round before it is a prefix of the
   final events *)
Theorem brounds_before_slept[local]:
  ∀n n' h' ws' e' logs'.
    brounds lfd hw ifds bz mm ws0 n = SOME (BSlept h evs cb) ∧
    brounds lfd hw ifds bz mm ws0 n' = SOME (BRun h' ws' e' logs') ⇒ e' ≼ evs
Proof
  Induct >- simp[brounds_def] >>
  rpt strip_tac >>
  Cases_on ‘brounds lfd hw ifds bz mm ws0 n’ >> gvs[brounds_def] >>
  Cases_on ‘x’ >> gvs[]
  >- (rename1 ‘brounds _ _ _ _ _ _ n = SOME (BRun l p l0 l1)’ >>
      qpat_x_assum ‘_ = SOME (BSlept _ _ _)’ mp_tac >> simp[AllCaseEqs()] >> strip_tac >>
      gvs[] >>
      Cases_on ‘n' ≤ n’
      >- (‘e' ≼ l0’ by metis_tac[brounds_evs_mono] >>
          metis_tac[IS_PREFIX_TRANS, IS_PREFIX_APPEND3]) >>
      ‘∃h2 e2 c2. brounds lfd hw ifds bz mm ws0 (SUC n) = SOME (BSlept h2 e2 c2)’
        by fs[brounds_def] >>
      drule brounds_after_slept >> disch_then (qspec_then ‘n'’ mp_tac) >> simp[]) >>
  metis_tac[]
QED

(* MAIN: the loop sleeps in round n, and the guard held: the events before
   the final poll are the blocking model run's trace *)
Theorem sleep_btrace:
  bt_guard lfd hw ifds m (w0, ps0) ∧
  brounds_t lfd hw ifds m (w0, ps0) n = SOME (BSlept h evs cb) ⇒
  btrace lfd (pol_self hw) ifds (K F) m w0 ps0 (fromList evs)
Proof
  strip_tac >> drule bt_guard_brounds >> strip_tac >> gvs[] >>
  rw[btrace_def, LPREFIX_fromList, from_toList, bpre_def] >> eq_tac >> rw[]
  >- metis_tac[]
  >- (drule_all brounds_before_slept >> metis_tac[IS_PREFIX_TRANS])
  >> rename1 ‘brounds _ _ _ _ _ _ n2 = SOME (BSlept h2 evs2 cb2)’ >>
  ‘evs2 = evs’ suffices_by (rw[] >> fs[]) >>
  Cases_on ‘n ≤ n2’
  >- (drule_all brounds_after_slept >> gvs[])
  >> ‘n2 ≤ n’ by simp[] >>
  qpat_x_assum ‘brounds _ _ _ _ _ _ n2 = _’ assume_tac >>
  drule_all brounds_after_slept >> gvs[]
QED

(* ------------------------------------------------------------------------
   Under the PF run's standing facts the guard never fires
   ------------------------------------------------------------------------ *)

(* Every blocking round has well-formed actions and room for its accepts
   (honestL1BNoFail's brounds_ok, its room fact): the PF round matching it
   has the same state and actions *)
Theorem brounds_room:
  ∀m ifds bz w0 lfd hw.
  bquiet m ifds bz ∧ l0_rely w0 ∧
  run_ok lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ⇒
  ∀n h w ps evs logs. brounds lfd hw ifds bz m (w0, pinit) n = SOME (BRun h (w, ps) evs logs) ⇒
    EVERY (pact_ok lfd) (new_actions (log_of m) h) ∧
    ps.b.nxt + naccepts (new_actions (log_of m) h) < dimword (:64)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> disch_tac >>
  ‘binv lfd hw ifds bz m w0 pinit h w ps evs’
    by (qpat_assum ‘brounds _ _ _ _ _ _ n = _’ mp_tac >>
        qpat_assum ‘bquiet _ _ _’ (fn th => REWRITE_TAC[MATCH_MP l1b_refines_pf th])) >>
  pop_assum (strip_assume_tac o REWRITE_RULE[binv_def, binv_at_def]) >>
  fs[run_ok_def] >>
  qpat_x_assum ‘pl2_ok _ _ _ _ _’ (mp_tac o REWRITE_RULE[pl2_ok_def]) >>
  disch_then drule >> strip_tac >>
  ‘new_actions (log_of m) full = new_actions (log_of m) h’
    by (fs[sfor_def] >> first_x_assum (qspec_then ‘[]’ mp_tac) >> simp[]) >>
  fs[]
QED

(* MAIN: the CakeML loop's guard never fires (a server never busy) *)
Theorem bt_guard_ok:
  bquiet m ifds (K F) ∧ l0_rely w0 ∧
  run_ok lfd (pol_self hw) ifds m
    (reindex (btr lfd (pol_self hw) ifds (K F) m (w0, pinit)) w0) ⇒
  bt_guard lfd hw ifds m (w0, pinit)
Proof
  strip_tac >>
  qspecl_then [‘m’, ‘ifds’, ‘K F’, ‘w0’, ‘lfd’, ‘pol_self hw’] mp_tac brounds_room >>
  simp[] >> strip_tac >>
  simp[bt_guard_def] >> completeInduct_on ‘i’ >> rpt strip_tac >>
  ‘brounds_t lfd hw ifds m (w0, pinit) i = brounds lfd (pol_self hw) ifds (K F) m (w0, pinit) i’
    by (irule brounds_t_brounds >> metis_tac[]) >>
  PairCases_on ‘ws’ >> gvs[] >>
  first_x_assum drule >> simp[hdl_room_def]
QED

(* ------------------------------------------------------------------------
   The PF model run has a trace
   ------------------------------------------------------------------------ *)

Theorem FLAT_GENLIST_steps[local]:
  E 0 = [] ∧ (∀i. E i ≼ E (SUC i)) ⇒
  ∀n. FLAT (GENLIST (λi. DROP (LENGTH (E i)) (E (SUC i))) n) = E n
Proof
  strip_tac >> Induct >> simp[GENLIST, FLAT_SNOC] >>
  first_x_assum (qspec_then ‘n’ mp_tac) >> rw[IS_PREFIX_APPEND] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem revs_step[local]:
  run_ok lfd pol ifds m Wp ⇒
  revs lfd pol ifds m Wp 0 = [] ∧
  ∀i. revs lfd pol ifds m Wp i ≼ revs lfd pol ifds m Wp (SUC i)
Proof
  strip_tac >> drule prun_some >> strip_tac >>
  conj_tac >- (first_x_assum (qspec_then ‘0’ mp_tac) >> simp[prounds_def, revs_def]) >>
  gen_tac >> simp[revs_def] >>
  Cases_on ‘prun lfd pol ifds m Wp i’ >> PairCases_on ‘r’ >>
  Cases_on ‘prun lfd pol ifds m Wp (SUC i)’ >> PairCases_on ‘r’ >> simp[] >>
  qpat_assum ‘∀n. _’ (qspec_then ‘SUC i’ mp_tac) >>
  ONCE_REWRITE_TAC [prounds_def] >>
  qpat_assum ‘∀n. _’ (qspec_then ‘i’ (fn th => REWRITE_TAC [th])) >>
  gvs[] >>
  Cases_on ‘pround lfd pol (ifds q) (r0, r1) (new_actions (log_of m) q)’ >> simp[] >>
  PairCases_on ‘x’ >> simp[] >> rw[] >> simp[]
QED

(* MAIN: the PF model run's trace *)
Theorem pf_trace_exists:
  run_ok lfd pol ifds m Wp ⇒
  ∃io. ∀evs. LPREFIX (fromList evs) io ⇔ ppre lfd pol ifds m (Wp, pinit) evs
Proof
  strip_tac >> drule revs_step >> strip_tac >>
  qexists_tac ‘LFLATTEN (LGENLIST (λi. fromList (DROP (LENGTH (revs lfd pol ifds m Wp i))
                                                   (revs lfd pol ifds m Wp (SUC i)))) NONE)’ >>
  simp[LPREFIX_LFLATTEN] >>
  qspec_then ‘revs lfd pol ifds m Wp’ mp_tac (Q.GEN ‘E’ FLAT_GENLIST_steps) >>
  simp[] >> strip_tac >> simp[ppre_def] >>
  drule prun_some >> strip_tac >>
  gen_tac >> eq_tac >> rw[]
  >- (qexists_tac ‘n’ >>
      first_x_assum (qspec_then ‘n’ assume_tac) >>
      Cases_on ‘prun lfd pol ifds m Wp n’ >> PairCases_on ‘r’ >> gvs[revs_def])
  >> qexists_tac ‘N’ >>
  first_x_assum (qspec_then ‘N’ assume_tac) >> gvs[revs_def]
QED
