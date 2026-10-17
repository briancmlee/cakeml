(*
  L3-09 (S4), step 2b: past the last arrival the PF run's listener queue
  settles, and then empties.  Its length only falls (honestL1BQueue), so it
  is eventually constant; a constant non-empty queue means every later
  accept on the listener fails, so (¬accepts_fail) accepts stop; then L1's
  accepted fds are handed out (S2), the pause runs out, the listener is
  polled every unpaused round (S1), and [F1] gives a poll that is not
  retried, hence an accept (run_lfd): a contradiction.

  MAIN: queue_empty.
*)
Theory honestL1BSettle
Ancestors
  honestL1BQueue honestL1BQuietWorld honestL1BFaith honestL1BRuns honestL1BStmts
  honestL1PFConnRun honestL1PFConn honestL1PFClient honestL1PFLive honestL1PFRound
  honestL1PFInv honestL1PFModel honestL1Steps honestL1Inv honestL1Model
  honestL0WorldInv honestL0Part honestL0WorldProps honestL0Rely honestL0World honestL0
Libs
  preamble

Theorem rworld_rely:
  run_ok lfd pol ifds m w0 ⇒ ∀n. l0_rely (rworld lfd pol ifds m w0 n)
Proof
  strip_tac >> gen_tac >>
  drule prun_some >> disch_then (qspec_then ‘n’ assume_tac) >>
  Cases_on ‘prun lfd pol ifds m w0 n’ >> rename1 ‘(hh, r)’ >> PairCases_on ‘r’ >>
  ‘l0_rely w0’ by fs[run_ok_def] >>
  drule fplays_prounds >> simp[fplays_def] >> strip_tac >> gvs[rworld_def]
QED

Theorem round_fplays:
  run_ok lfd pol ifds m w0 ⇒
  ∀k. faithful (rworld lfd pol ifds m w0 k) (rrev lfd pol ifds m w0 k) ∧
      FOLDL l0_step (SOME (rworld lfd pol ifds m w0 k)) (MAP ev_lcall (rrev lfd pol ifds m w0 k)) =
        SOME (rworld lfd pol ifds m w0 (SUC k))
Proof
  strip_tac >> gen_tac >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
  drule fplays_pround >> simp[fplays_def] >>
  ‘l0_rely (rworld lfd pol ifds m w0 k)’ by metis_tac[rworld_rely] >> simp[]
QED

(* The queue across a round past the last arrival *)
Theorem round_qof:
  run_ok lfd pol ifds m w0 ∧ quiet_after N (rworld lfd pol ifds m w0 k) ∧
  N ≤ (rworld lfd pol ifds m w0 k).clock ⇒
  ∃d. qof (rworld lfd pol ifds m w0 (SUC k)) l = DROP d (qof (rworld lfd pol ifds m w0 k) l) ∧
      ((∃e. MEM e (rrev lfd pol ifds m w0 k) ∧ ev_on «sys_accept» l e ∧ ¬failed e) ⇒
       LENGTH (qof (rworld lfd pol ifds m w0 (SUC k)) l) <
       LENGTH (qof (rworld lfd pol ifds m w0 k) l))
Proof
  strip_tac >> drule round_fplays >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  ‘l0_rely (rworld lfd pol ifds m w0 k)’ by metis_tac[rworld_rely] >>
  drule_all qof_quiet_trace >> simp[]
QED

(* A non-increasing sequence of numbers is eventually constant *)
Theorem noninc_stable:
  (∀k. K0 ≤ k ⇒ f (SUC k) ≤ (f k : num)) ⇒ ∃KK. K0 ≤ KK ∧ ∀k. KK ≤ k ⇒ f k = f KK
Proof
  strip_tac >>
  ‘∀d k. K0 ≤ k ⇒ f (k + d) ≤ f k’
    by (Induct >> rw[] >> first_x_assum (qspec_then ‘k’ mp_tac) >> simp[] >>
        first_x_assum (qspec_then ‘k + d’ mp_tac) >> simp[ADD_CLAUSES]) >>
  qabbrev_tac ‘v = LEAST v. ∃k. K0 ≤ k ∧ f k = v’ >>
  ‘∃k. K0 ≤ k ∧ f k = v’
    by (qunabbrev_tac ‘v’ >> numLib.LEAST_ELIM_TAC >> simp[] >> metis_tac[LESS_EQ_REFL]) >>
  qexists_tac ‘k’ >> rw[] >>
  ‘f k' ≤ f k’ by (first_x_assum (qspecl_then [‘k' − k’, ‘k’] mp_tac) >> simp[]) >>
  ‘f k ≤ f k'’
    by (qpat_x_assum ‘(LEAST v. _) = _’ (SUBST1_TAC o SYM) >>
        numLib.LEAST_ELIM_TAC >> conj_tac >- metis_tac[] >>
        rpt strip_tac >> spose_not_then assume_tac >>
        first_x_assum (qspec_then ‘f k'’ mp_tac) >> simp[] >>
        qexists_tac ‘k'’ >> simp[]) >>
  decide_tac
QED

(* MAIN: past the last arrival the queue is eventually constant, and no
   accept on the listener succeeds any more *)
Theorem queue_stable:
  run_ok lfd pol ifds m w0 ∧ quiet_after N w0 ⇒
  ∃KK. ∀k. KK ≤ k ⇒ qof (rworld lfd pol ifds m w0 k) l = qof (rworld lfd pol ifds m w0 KK) l ∧
                  ¬∃e. MEM e (rrev lfd pol ifds m w0 k) ∧ ev_on «sys_accept» l e ∧ ¬failed e
Proof
  strip_tac >> drule_all run_quiet >> strip_tac >>
  ‘∀k. n0 ≤ k ⇒
     ∃d. qof (rworld lfd pol ifds m w0 (SUC k)) l = DROP d (qof (rworld lfd pol ifds m w0 k) l) ∧
         ((∃e. MEM e (rrev lfd pol ifds m w0 k) ∧ ev_on «sys_accept» l e ∧ ¬failed e) ⇒
          LENGTH (qof (rworld lfd pol ifds m w0 (SUC k)) l) <
          LENGTH (qof (rworld lfd pol ifds m w0 k) l))’
    by (rpt strip_tac >> irule round_qof >> metis_tac[]) >>
  qspecl_then [‘λk. LENGTH (qof (rworld lfd pol ifds m w0 k) l)’, ‘n0’] mp_tac
    (Q.GENL [‘f’, ‘K0’] noninc_stable) >>
  impl_tac
  >- (rw[] >> first_x_assum drule >> strip_tac >> simp[LENGTH_DROP]) >>
  strip_tac >> fs[] >> qexists_tac ‘KK’ >> gen_tac >> strip_tac >>
  ‘∀j. KK ≤ j ⇒ qof (rworld lfd pol ifds m w0 (SUC j)) l = qof (rworld lfd pol ifds m w0 j) l’
    by (rpt strip_tac >> ‘n0 ≤ j’ by decide_tac >>
        qpat_assum ‘∀k. n0 ≤ k ⇒ ∃d. _’ (qspec_then ‘j’ mp_tac) >>
        (impl_tac >- decide_tac) >> strip_tac >>
        ‘LENGTH (qof (rworld lfd pol ifds m w0 (SUC j)) l) =
         LENGTH (qof (rworld lfd pol ifds m w0 j) l)’
          by (qpat_assum ‘∀k. KK ≤ k ⇒ LENGTH _ = LENGTH _’
                (fn th => metis_tac[th, LESS_EQ_SUC_REFL, LESS_EQ_TRANS])) >>
        Cases_on ‘d’ >- gvs[] >>
        Cases_on ‘qof (rworld lfd pol ifds m w0 j) l’ >- gvs[] >>
        qpat_x_assum ‘LENGTH _ = LENGTH _’ mp_tac >>
        qpat_x_assum ‘qof _ _ = DROP _ _’ SUBST1_TAC >> simp[LENGTH_DROP]) >>
  conj_tac
  >- (‘∀d. qof (rworld lfd pol ifds m w0 (KK + d)) l = qof (rworld lfd pol ifds m w0 KK) l’
        by (Induct >> simp[ADD_CLAUSES] >> first_x_assum (qspec_then ‘KK + d’ mp_tac) >>
            simp[]) >>
      first_x_assum (qspec_then ‘k − KK’ mp_tac) >> simp[])
  >> strip_tac >>
  ‘n0 ≤ k’ by decide_tac >> first_x_assum drule >> strip_tac >>
  ‘qof (rworld lfd pol ifds m w0 (SUC k)) l = qof (rworld lfd pol ifds m w0 k) l’ by simp[] >>
  metis_tac[prim_recTheory.LESS_REFL]
QED

(* ------------------------------------------------------------------------
   An accepted connection in a round's log comes from a successful accept
   ------------------------------------------------------------------------ *)

Theorem accept_ev_on[local]:
  sys_accept l w = SOME (out, w', ev) ⇒ ev_on «sys_accept» l ev
Proof
  rw[sys_accept_def] >> drule l0_do_cases >> rw[] >>
  simp[ev_on_def, call_fds_fd]
QED

Theorem fetch_conn_event:
  ∀fs w ps ws log evs.
    pf_fetch lfd pol fs (w, ps) = SOME (ws, log, evs) ∧ l0_rely w ∧ MEM (FConn g) log ⇒
    ∃e. MEM e evs ∧ ev_on «sys_accept» lfd e ∧ ¬failed e
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> IF_CASES_TAC
  >- metis_tac[]
  >> IF_CASES_TAC >> simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  imp_res_tac rplays_sys >> fs[rplays_def] >> rfs[] >>
  TRY (‘l0_rely w1’ by metis_tac[] >> first_x_assum drule_all >> metis_tac[] >> NO_TAC) >>
  qexists_tac ‘ev’ >> simp[] >> conj_tac >- metis_tac[accept_ev_on] >>
  qpat_x_assum ‘sys_accept _ _ = _’ mp_tac >> simp[sys_accept_def] >> strip_tac >>
  drule_all ev_failed >> simp[]
QED

Theorem pround_conn_event:
  pround lfd pol hs (w, ps) acts = SOME (snap, ws', log, evs) ∧ l0_rely w ∧
  MEM (FConn g) log ⇒
  ∃e. MEM e evs ∧ ev_on «sys_accept» lfd e ∧ ¬failed e
Proof
  rw[pround_def, AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  imp_res_tac rplays_pacts >>
  qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >> simp[pf_tail_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  imp_res_tac rplays_polls >> imp_res_tac rplays_flush >> fs[rplays_def] >> rfs[] >>
  drule fetch_conn_event >> simp[] >> disch_then drule >> strip_tac >>
  qexists_tac ‘e’ >> simp[]
QED

Theorem log_conns_mem[local]:
  ∀l. log_conns l ≠ [] ⇒ ∃g. MEM (FConn g) l
Proof
  Induct >> rw[log_conns_def] >> Cases_on ‘h’ >> fs[log_conns_def] >> metis_tac[]
QED

(* MAIN: a round that hands L1 an accepted connection made a successful
   accept on the listener *)
Theorem round_conn_event:
  run_ok lfd pol ifds m w0 ∧ log_conns (rlog lfd pol ifds m w0 k) ≠ [] ⇒
  ∃e. MEM e (rrev lfd pol ifds m w0 k) ∧ ev_on «sys_accept» lfd e ∧ ¬failed e
Proof
  strip_tac >> drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
  ‘∃g. MEM (FConn g) (rlog lfd pol ifds m w0 k)’
    by metis_tac[log_conns_mem] >>
  drule pround_conn_event >> disch_then irule >> simp[] >> metis_tac[rworld_rely]
QED
