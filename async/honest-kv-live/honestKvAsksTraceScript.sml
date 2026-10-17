(*
  K-asks on the trace, the round side: a PF round that fetches on f, or
  polls f for input (asked_at), has an asks_ev f among its events; so if
  the trace stops asking on f, some round M on has neither.

  MAIN: run_fetched_asks, run_asked_asks, run_asks_tail.
*)
Theory honestKvAsksTrace
Ancestors
  honestKvAsksPF honestKvL0LiveStmts honestKvL0AsksRun honestL1PFEpisode
  honestL1PFConnTrace honestL1BRuns honestL1PFLive honestL1PFRound honestL1PFModel
  honestL1BTransfer honestL1Model ffiSpikeSocketFFI
Libs
  preamble

(* ------------------------------------------------------------------------
   A fetch on f is a recv on f
   ------------------------------------------------------------------------ *)
Theorem l0_do_ev_form[local]:
  l0_do n conf alen w = SOME (out, w', ev) ⇒ ∃bs. ev = IO_event (ExtCall n) conf bs
Proof
  rw[l0_do_def, AllCaseEqs()] >> simp[]
QED

Theorem pf_fetch_asks:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ fetched f log ⇒
    EXISTS (asks_ev f) evs
Proof
  Induct >- simp[pf_fetch_def, fetched_def] >>
  rpt gen_tac >> simp[Once pf_fetch_def] >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  IF_CASES_TAC
  >- (simp[AllCaseEqs()] >> strip_tac >> rpt (pairarg_tac >> gvs[]) >>
      qpat_x_assum ‘(case pf_fetch _ _ _ _ of NONE => _ | SOME _ => _) = _’ mp_tac >>
      CASE_TAC >> simp[] >> PairCases_on ‘x’ >> strip_tac >> gvs[] >>
      ‘fetched f x2’ by (qpat_x_assum ‘fetched _ _’ mp_tac >>
                         qpat_x_assum ‘(case l0_res_of _ of _ => _ | _ => _) = _’ mp_tac >>
                         every_case_tac >> rw[] >> fs[fetched_def]) >>
      first_x_assum drule_all >> simp[]) >>
  simp[AllCaseEqs(), sys_recv_def] >> strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum ‘(case pf_fetch _ _ _ _ of NONE => _ | SOME _ => _) = _’ mp_tac >>
  CASE_TAC >> simp[] >> PairCases_on ‘x’ >> strip_tac >> gvs[] >>
  Cases_on ‘asks_ev f ev’ >> simp[] >>
  drule l0_do_ev_form >> strip_tac >>
  ‘h ≠ f’ by (strip_tac >> qpat_x_assum ‘¬asks_ev _ _’ mp_tac >> gvs[asks_ev_def]) >>
  ‘fetched f x2’ by (qpat_x_assum ‘fetched _ _’ mp_tac >>
                     qpat_x_assum ‘(case l0_res_of _ of _ => _ | _ => _) = _’ mp_tac >>
                     every_case_tac >> rw[] >> fs[fetched_def] >> gvs[]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem bounded_max[local]:
  ∀B (g:num->num). (∀k. g k < B) ⇒ ∃M. ∀k. g k ≤ g M
Proof
  rpt strip_tac >> CCONTR_TAC >> fs[NOT_LESS_EQUAL] >>
  ‘∀n. ∃M. n ≤ g M’
    by (Induct >- simp[] >> pop_assum strip_assume_tac >>
        first_x_assum (qspec_then ‘M’ strip_assume_tac) >>
        qexists_tac ‘k’ >> decide_tac) >>
  first_x_assum (qspec_then ‘B’ strip_assume_tac) >>
  qpat_x_assum ‘∀k. g k < B’ (qspec_then ‘M’ mp_tac) >> decide_tac
QED

(* MAIN: a round that fetches on f has an asks_ev f among its events *)
Theorem pround_fetched_asks:
  pround lfd pol hs (w, ps) acts = SOME (sn, (w', ps'), log, evs) ∧ fetched f log ⇒
  EXISTS (asks_ev f) evs
Proof
  rw[pround_def, AllCaseEqs()] >> PairCases_on ‘ws1’ >> gvs[pf_tail_def, AllCaseEqs()] >>
  drule_all pf_fetch_asks >> simp[EXISTS_APPEND]
QED

Theorem run_fetched_asks:
  run_ok lfd pol ifds m w0 ∧ fetched_at lfd pol ifds m w0 k f ⇒
  EXISTS (asks_ev f) (rrev lfd pol ifds m w0 k)
Proof
  strip_tac >>
  ‘fetched f (rlog lfd pol ifds m w0 k)’
    by (qpat_x_assum ‘fetched_at _ _ _ _ _ _ _’ mp_tac >> rewrite_tac[fetched_at_def, rlog_def]) >>
  qpat_assum ‘run_ok _ _ _ _ _’ (fn th => strip_assume_tac (Q.SPEC ‘k’ (MATCH_MP prun_round' th))) >>
  irule pround_fetched_asks >> metis_tac[]
QED

Theorem run_asked_asks:
  asked_at lfd pol ifds m w0 k f ⇒ EXISTS (asks_ev f) (rrev lfd pol ifds m w0 k)
Proof
  rw[asked_at_def, EXISTS_MEM] >> first_assum (irule_at Any) >>
  rw[asks_ev_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The trace stops asking on f ⇒ the rounds stop asking on f
   ------------------------------------------------------------------------ *)
Theorem revs_len_le[local]:
  run_ok lfd pol ifds m w0 ∧ a ≤ b ⇒
  LENGTH (revs lfd pol ifds m w0 a) ≤ LENGTH (revs lfd pol ifds m w0 b)
Proof
  strip_tac >> drule revs_prefix >> disch_then (qspecl_then [‘b − a’, ‘a’] mp_tac) >>
  ‘a + (b − a) = b’ by decide_tac >> simp[IS_PREFIX_LENGTH]
QED

(* Round k's events sit in io right after revs k *)
Theorem rrev_lnth[local]:
  run_ok lfd pol ifds m w0 ∧ pftrace lfd pol ifds m w0 io ∧
  p < LENGTH (rrev lfd pol ifds m w0 k) ⇒
  LNTH (LENGTH (revs lfd pol ifds m w0 k) + p) io = SOME (EL p (rrev lfd pol ifds m w0 k))
Proof
  strip_tac >>
  qpat_assum ‘run_ok _ _ _ _ _’ (fn th => strip_assume_tac (Q.SPEC ‘k’ (MATCH_MP prun_round' th))) >>
  ‘LPREFIX (fromList (revs lfd pol ifds m w0 (SUC k))) io’ by metis_tac[pftrace_revs] >>
  pop_assum mp_tac >>
  qpat_x_assum ‘revs _ _ _ _ _ (SUC k) = _’ SUBST1_TAC >>
  rewrite_tac[LPREFIX_fromList_LNTH] >>
  disch_then (qspec_then ‘LENGTH (revs lfd pol ifds m w0 k) + p’ mp_tac) >>
  simp[EL_APPEND2]
QED

(* MAIN *)
Theorem run_asks_tail:
  run_ok lfd pol ifds m w0 ∧ pftrace lfd pol ifds m w0 io ∧ ¬asks_io_on f io ⇒
  ∃M. ∀k. M ≤ k ⇒ ¬EXISTS (asks_ev f) (rrev lfd pol ifds m w0 k)
Proof
  rw[asks_io_on_def] >>
  Cases_on ‘∃M. i ≤ LENGTH (revs lfd pol ifds m w0 M)’
  >- (pop_assum strip_assume_tac >> qexists_tac ‘M’ >> rpt strip_tac >>
      simp[EVERY_EL] >> rpt strip_tac >> rename1 ‘p < LENGTH _’ >>
      ‘LENGTH (revs lfd pol ifds m w0 M) ≤ LENGTH (revs lfd pol ifds m w0 k)’
        by metis_tac[revs_len_le] >>
      qpat_x_assum ‘∀i' ev. _’ (qspecl_then [‘LENGTH (revs lfd pol ifds m w0 k) + p’,
                                              ‘EL p (rrev lfd pol ifds m w0 k)’] mp_tac) >>
      impl_tac >- (irule rrev_lnth >> metis_tac[]) >>
      strip_tac >- decide_tac >> metis_tac[]) >>
  fs[NOT_LESS_EQUAL] >>
  qspecl_then [‘i’, ‘λk. LENGTH (revs lfd pol ifds m w0 k)’] mp_tac bounded_max >>
  simp[] >> strip_tac >> qexists_tac ‘M’ >> rpt strip_tac >>
  qpat_assum ‘run_ok _ _ _ _ _’ (fn th => strip_assume_tac (Q.SPEC ‘k’ (MATCH_MP prun_round' th))) >>
  ‘LENGTH (revs lfd pol ifds m w0 M) ≤ LENGTH (revs lfd pol ifds m w0 k)’
    by metis_tac[revs_len_le] >>
  qpat_x_assum ‘∀k. LENGTH _ ≤ LENGTH _’ (qspec_then ‘SUC k’ mp_tac) >>
  qpat_x_assum ‘revs _ _ _ _ _ (SUC k) = _’ SUBST1_TAC >>
  Cases_on ‘rrev lfd pol ifds m w0 k’ >> fs[]
QED
