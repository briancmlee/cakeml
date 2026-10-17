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

(* Past some round no accept on the listener happens at all, once the queue
   is stuck and accepts fail only finitely often *)
Theorem no_accepts_late:
  run_ok lfd pol ifds m w0 ∧ ¬accepts_fail lfd pol ifds m w0 ∧
  (∀k. KK ≤ k ⇒ ¬∃e. MEM e (rrev lfd pol ifds m w0 k) ∧ ev_on «sys_accept» lfd e ∧ ¬failed e) ⇒
  ∃K2. KK ≤ K2 ∧ ∀k. K2 ≤ k ⇒ ¬EXISTS (ev_on «sys_accept» lfd) (rrev lfd pol ifds m w0 k)
Proof
  rw[accepts_fail_def] >>
  qexists_tac ‘KK + i’ >> rw[EVERY_MEM] >> CCONTR_TAC >> fs[] >>
  rename1 ‘MEM e (rrev _ _ _ _ _ k)’ >>
  ‘KK ≤ k’ by decide_tac >>
  ‘failed e’
    by (qpat_x_assum ‘∀k. KK ≤ k ⇒ _’ (qspec_then ‘k’ mp_tac) >> simp[] >>
        disch_then (qspec_then ‘e’ mp_tac) >> simp[]) >>
  qpat_assum ‘run_ok _ _ _ _ _’ (fn ro => qpat_assum ‘MEM e _’ (fn me =>
    strip_assume_tac (MATCH_MP round_event (CONJ ro me)))) >>
  qpat_assum ‘run_ok _ _ _ _ _’ (fn ro =>
    assume_tac (Q.SPEC ‘k’ (MATCH_MP revs_grows ro))) >>
  qpat_x_assum ‘∀i' n. _’ (qspecl_then [‘i'’, ‘SUC k’] mp_tac) >> simp[]
QED

(* MAIN: past the last arrival the listener's queue empties, and L1 holds
   no accepted connection, unless accepts fail infinitely often *)
Theorem queue_empty:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ linv lfd w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ∧
  F1 lfd pol ifds m w0 ∧ S1 lfd pol ifds m w0 ∧ S2 lfd pol ifds m w0 ∧
  ¬accepts_fail lfd pol ifds m w0 ∧ quiet_after N w0 ⇒
  ∃K. ∀k. K ≤ k ⇒ qof (rworld lfd pol ifds m w0 k) lfd = [] ∧ (rstate lfd pol ifds m w0 k).acq = []
Proof
  strip_tac >> drule_all (Q.INST [‘l’ |-> ‘lfd’] queue_stable) >> strip_tac >>
  ‘∀k. KK ≤ k ⇒ log_conns (rlog lfd pol ifds m w0 k) = []’
    by metis_tac[round_conn_event] >>
  drule_all acq_empty >> strip_tac >>
  Cases_on ‘qof (rworld lfd pol ifds m w0 KK) lfd = []’
  >- (qexists_tac ‘N1’ >> rw[] >> metis_tac[LESS_EQ_TRANS])
  >> (* a stuck non-empty queue: a contradiction *)
  ‘∀k. KK ≤ k ⇒ ¬∃e. MEM e (rrev lfd pol ifds m w0 k) ∧ ev_on «sys_accept» lfd e ∧ ¬failed e’
    by metis_tac[] >>
  drule_all no_accepts_late >> strip_tac >>
  drule_all run_lfd >> strip_tac >>
  drule_all noob_run >> strip_tac >>
  ‘∀k. MEM lfd (ifds (rhist lfd pol ifds m w0 k))’ by gvs[S1_def] >>
  qabbrev_tac ‘K3 = N1 + K2’ >>
  ‘∀k. K3 ≤ k ⇒ (rstate lfd pol ifds m w0 k).acq = [] ∧
                 qof (rworld lfd pol ifds m w0 k) lfd ≠ [] ∧
                 ¬EXISTS (ev_on «sys_accept» lfd) (rrev lfd pol ifds m w0 k)’
    by (rpt gen_tac >> strip_tac >>
        ‘N1 ≤ k ∧ K2 ≤ k ∧ KK ≤ k’ by (fs[Abbr ‘K3’] >> decide_tac) >>
        rpt conj_tac
        >- (first_x_assum irule >> first_assum ACCEPT_TAC)
        >- (qpat_assum ‘∀k. KK ≤ k ⇒ qof _ _ = _ ∧ _’ (qspec_then ‘k’ mp_tac) >>
            simp[] >> strip_tac >> fs[])
        >> qpat_assum ‘∀k. K2 ≤ k ⇒ _’ irule >> first_assum ACCEPT_TAC) >>
  (* an unpaused late round polls the listener *)
  ‘∀k. K3 ≤ k ∧ (rstate lfd pol ifds m w0 k).pause = 0 ⇒
       EXISTS (ev_on «sys_poll» lfd) (rrev lfd pol ifds m w0 k)’
    by (rpt strip_tac >> first_x_assum drule >> strip_tac >>
        qpat_assum ‘∀k. (∃d. _) ∧ _’ (qspec_then ‘k’ strip_assume_tac) >>
        qpat_x_assum ‘_ ∧ _ ∧ _ ∧ _ ⇒ EXISTS _ _ ∧ _’ mp_tac >> simp[]) >>
  (* polls on the listener, infinitely often *)
  drule_all pause_zero >> strip_tac >>
  drule revs_grows >> strip_tac >>
  ‘∀i. ∃i'. i ≤ i' ∧ call_at lfd pol ifds m w0 i' «sys_poll» lfd’
    by (gen_tac >>
        qpat_assum ‘∀n. ∃n'. n ≤ n' ∧ _’ (qspec_then ‘K3 + i’ strip_assume_tac) >>
        ‘K3 ≤ n'’ by decide_tac >>
        ‘EXISTS (ev_on «sys_poll» lfd) (rrev lfd pol ifds m w0 n')’ by metis_tac[] >>
        qpat_x_assum ‘EXISTS _ (rrev _ _ _ _ _ n')’
          (strip_assume_tac o REWRITE_RULE [EXISTS_MEM]) >>
        drule_all call_at_round >> strip_tac >>
        qexists_tac ‘i'’ >> simp[] >>
        ‘LENGTH (revs lfd pol ifds m w0 (K3 + i)) ≤ LENGTH (revs lfd pol ifds m w0 n')’
          by (irule revs_len_mono >> simp[]) >>
        first_x_assum (qspec_then ‘K3 + i’ assume_tac) >> decide_tac) >>
  (* [F1]: one of them, late, is not retried *)
  ‘∃i'. LENGTH (revs lfd pol ifds m w0 K3) ≤ i' ∧ call_at lfd pol ifds m w0 i' «sys_poll» lfd ∧
        call_ok_at lfd pol ifds m w0 i'’
    by (qpat_assum ‘F1 _ _ _ _ _’ (mp_tac o REWRITE_RULE [F1_def]) >>
        disch_then (qspecl_then [‘«sys_poll»’, ‘lfd’] mp_tac) >> impl_tac >- metis_tac[] >>
        disch_then (qspec_then ‘LENGTH (revs lfd pol ifds m w0 K3)’ strip_assume_tac) >>
        metis_tac[]) >>
  drule_all call_ok_round >> strip_tac >>
  (* that round is unpaused (a paused round does not poll the listener) *)
  ‘(rstate lfd pol ifds m w0 k).pause = 0’
    by (CCONTR_TAC >>
        drule_all round_facts >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
        drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
        drule pround_paused >> simp[] >> qexistsl_tac [‘s’, ‘cm’] >> simp[EXISTS_MEM] >>
        metis_tac[]) >>
  first_x_assum (qspec_then ‘k’ mp_tac) >> simp[] >> strip_tac >>
  qpat_assum ‘∀k. (∃d. _) ∧ _’ (qspec_then ‘k’ strip_assume_tac) >>
  qpat_x_assum ‘_ ∧ _ ∧ _ ∧ _ ⇒ EXISTS _ _ ∧ _’ mp_tac >> simp[] >>
  strip_tac >> first_x_assum (qspec_then ‘ev’ mp_tac) >> simp[]
QED
