(*
  E1 per-connection liveness on the listener (task D): on the EP L1's run
  with pol_never, a connection pending on lfd is eventually accepted, or its
  channel broke, or the accepts fail for good (conn_live_l0).  The EP analogue
  of honestL1PFConnTrace.pf_conn_live; the statement is agreed with
  honest-ffi (for proxyLiveLift.conn_live_run).

  TEMPORARY: nrun, erhist, erworld, erstate, erevs and erun_ok are verbatim
  copies of honestL1EPAsksRun's (spike/proxy-asks-l0 66a541c81, file last
  changed at d7671ed17), which is not on the R3 line.  Remove them when the
  lines merge (AsksRun imports these).

  Not on e1FairRounds: its ancestor clientLiveCopy has its own F1_io,
  world_at and l0_step, which clash with honestL1BStmts' and honestL0Part's.
  crio/crbl and F1_io_rounds below are copies of its rio/rbl and
  F1_io_rfair, on honestL1BStmts' F1_io.
*)
Theory honestL1EPConnLive
Ancestors
  llist honestL1BConnLive honestL1BConn honestL1BTransfer honestL1BCorr honestL1BRuns
  honestL1BStmts e1TracePrefix honestL1EPConnNoob honestL1EPConnWorld honestL1EPConnRound
  honestL1EPOwnRun e1RoundInv honestL1EPTotal honestL1EPRefine honestL1EPModel
  honestL1PFConnRun honestL1PFConn honestL1PFInv honestL1PFRound honestL1PFModel
  honestL1Steps honestL1Inv honestL1Model honestEchoL0Spec honestL0Rely honestL0WorldInv
  honestL0WorldProps
  honestL0Part honestL0World honestL0
Libs
  preamble

(* ------------------------------------------------------------------------
   The run, with pol_never (verbatim from honestL1EPAsksRun, see above)
   ------------------------------------------------------------------------ *)

Definition nrun_def:
  nrun lfd ifds m w0 n = THE (erounds lfd pol_never ifds m (w0, einit) n)
End

Definition erhist_def:
  erhist lfd ifds m w0 n = FST (nrun lfd ifds m w0 n)
End

Definition erworld_def:
  erworld lfd ifds m w0 n = FST (FST (SND (nrun lfd ifds m w0 n)))
End

Definition erstate_def:
  erstate lfd ifds m w0 n = SND (FST (SND (nrun lfd ifds m w0 n)))
End

(* Round n's events *)
Definition erevs_def:
  erevs lfd ifds m w0 n =
    case eround lfd pol_never (ifds (erhist lfd ifds m w0 n))
           (erworld lfd ifds m w0 n, erstate lfd ifds m w0 n)
           (new_actions (log_of m) (erhist lfd ifds m w0 n)) of
    | SOME (_, _, _, evs) => evs
    | NONE => []
End

(* The run's hypotheses (those of l1ep_refines_ehl, and that it runs) *)
Definition erun_ok_def:
  erun_ok lfd ifds m w0 ⇔
    l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
    (∀n. SND (ecm lfd pol_never ifds m w0 n) + 1 < dimword (:64)) ∧
    ∀n. erounds lfd pol_never ifds m (w0, einit) n ≠ NONE
End

Theorem erun_some:
  erun_ok lfd ifds m w0 ⇒
  erounds lfd pol_never ifds m (w0, einit) n =
    SOME (erhist lfd ifds m w0 n, (erworld lfd ifds m w0 n, erstate lfd ifds m w0 n),
          FST (SND (SND (nrun lfd ifds m w0 n))), SND (SND (SND (nrun lfd ifds m w0 n))))
Proof
  rw[erun_ok_def, erhist_def, erworld_def, erstate_def, nrun_def] >>
  first_x_assum (qspec_then ‘n’ mp_tac) >>
  Cases_on ‘erounds lfd pol_never ifds m (w0, einit) n’ >> simp[] >>
  PairCases_on ‘x’ >> simp[]
QED

(* Round n, from the run's state n to its state n + 1 *)
Theorem erun_round:
  erun_ok lfd ifds m w0 ⇒
  ∃snap log.
    eround lfd pol_never (ifds (erhist lfd ifds m w0 n))
      (erworld lfd ifds m w0 n, erstate lfd ifds m w0 n)
      (new_actions (log_of m) (erhist lfd ifds m w0 n)) =
    SOME (snap, (erworld lfd ifds m w0 (SUC n), erstate lfd ifds m w0 (SUC n)), log,
          erevs lfd ifds m w0 n)
Proof
  strip_tac >>
  drule erun_some >> disch_then (qspec_then ‘SUC n’ mp_tac) >>
  drule erun_some >> disch_then (qspec_then ‘n’ mp_tac) >>
  simp[erounds_def] >> strip_tac >> simp[AllCaseEqs()] >> strip_tac >>
  simp[erevs_def]
QED

(* ------------------------------------------------------------------------
   The statement (agreed with honest-ffi)
   ------------------------------------------------------------------------ *)

Definition erun_io_def:
  erun_io lfd ifds m w0 =
    LFLATTEN (LGENLIST (λi. fromList (erevs lfd ifds m w0 i)) NONE)
End

(* E1's S1 and S2 *)
Definition eS1_def:
  eS1 lfd ifds m w0 ⇔ ∀n. MEM lfd (ifds (erhist lfd ifds m w0 n))
End

Definition eS2_def:
  eS2 lfd ifds m w0 ⇔
    ∀n. (erstate lfd ifds m w0 n).p.acq ≠ [] ⇒
        ∃n'. n ≤ n' ∧ MEM (EAccept lfd) (new_actions (log_of m) (erhist lfd ifds m w0 n'))
End

(* ------------------------------------------------------------------------
   Along the run
   ------------------------------------------------------------------------ *)

Theorem erun_0[simp]:
  erhist lfd ifds m w0 0 = [] ∧ erworld lfd ifds m w0 0 = w0 ∧ erstate lfd ifds m w0 0 = einit
Proof
  simp[erhist_def, erworld_def, erstate_def, nrun_def, erounds_def]
QED

(* Round n's fetch log *)
Definition erlog_def:
  erlog lfd ifds m w0 n =
    case eround lfd pol_never (ifds (erhist lfd ifds m w0 n))
           (erworld lfd ifds m w0 n, erstate lfd ifds m w0 n)
           (new_actions (log_of m) (erhist lfd ifds m w0 n)) of
    | SOME (_, _, log, _) => log
    | NONE => []
End

Theorem erun_step:
  erun_ok lfd ifds m w0 ⇒
  ∃snap.
    eround lfd pol_never (ifds (erhist lfd ifds m w0 n))
      (erworld lfd ifds m w0 n, erstate lfd ifds m w0 n)
      (new_actions (log_of m) (erhist lfd ifds m w0 n)) =
    SOME (snap, (erworld lfd ifds m w0 (SUC n), erstate lfd ifds m w0 (SUC n)),
          erlog lfd ifds m w0 n, erevs lfd ifds m w0 n)
Proof
  strip_tac >> drule erun_round >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  qexists_tac ‘snap’ >> simp[erlog_def]
QED

Theorem eok_einit:
  l0_rely w0 ∧ fds_lt w0 ∧ ewinv w0 ∧ MEM lfd (l0_used w0) ⇒ eok lfd w0 einit
Proof
  strip_tac >> drule eown0_einit >> strip_tac >>
  ‘small lfd’ by (drule_all fds_lt_small >> simp[fds_small_def, small_def]) >>
  ‘esmall lfd einit’
    by simp[esmall_def, einit_def, psmall_def, pinit_def, small_fds_def, l1init_def] >>
  simp[eok_def]
QED

Theorem erun_eok:
  erun_ok lfd ifds m w0 ∧ winv w0 ⇒
  ∀n. eok lfd (erworld lfd ifds m w0 n) (erstate lfd ifds m w0 n) ∧
      (erstate lfd ifds m w0 n).p.b.nxt < dimword (:64)
Proof
  strip_tac >> Induct
  >- (simp[] >> conj_tac
      >- (irule eok_einit >> fs[erun_ok_def, winv_ewinv])
      >> simp[einit_def, pinit_def, l1init_def]) >>
  pop_assum strip_assume_tac >>
  drule erun_step >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  drule_all eround_queue >> strip_tac >>
  drule_all eround_nxt_lt >> simp[]
QED

Theorem erun_linv:
  erun_ok lfd ifds m w0 ∧ winv w0 ∧ linv lfd w0 ⇒ ∀n. linv lfd (erworld lfd ifds m w0 n)
Proof
  strip_tac >> drule_all erun_eok >> strip_tac >> Induct >- simp[] >>
  drule erun_step >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  qpat_assum ‘∀n. eok _ _ _ ∧ _’ (qspec_then ‘n’ strip_assume_tac) >>
  qpat_assum ‘∀n. eok _ _ _ ∧ _’ (qspec_then ‘SUC n’ strip_assume_tac) >>
  drule_all eround_lfd >> simp[]
QED

Theorem erun_noob:
  erun_ok lfd ifds m w0 ∧ winv w0 ⇒ ∀n. noob lfd (erstate lfd ifds m w0 n).p.b
Proof
  strip_tac >> drule_all erun_eok >> strip_tac >> Induct
  >- simp[einit_def, pinit_def, l1init_def, noob_def] >>
  drule erun_step >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  qpat_assum ‘∀n. eok _ _ _ ∧ _’ (qspec_then ‘n’ strip_assume_tac) >>
  drule_all eround_noob >> simp[]
QED

(* Each round, seen from the listener (honestL1PFConnRun.run_lfd) *)
Theorem erun_lfd:
  erun_ok lfd ifds m w0 ∧ winv w0 ∧ linv lfd w0 ⇒
  ∀k. (∃d. (erstate lfd ifds m w0 (SUC k)).p.acq =
             DROP d (erstate lfd ifds m w0 k).p.acq ++ log_conns (erlog lfd ifds m w0 k) ∧
           (MEM (EAccept lfd) (new_actions (log_of m) (erhist lfd ifds m w0 k)) ∧
            (erstate lfd ifds m w0 k).p.acq ≠ [] ⇒ 0 < d)) ∧
      (0 < (erstate lfd ifds m w0 k).p.pause ⇒
       (erstate lfd ifds m w0 (SUC k)).p.pause = (erstate lfd ifds m w0 k).p.pause − 1 ∧
       ¬EXISTS (ev_on «sys_poll» lfd) (erevs lfd ifds m w0 k)) ∧
      (∀ev. MEM ev (erevs lfd ifds m w0 k) ∧ ev_on «sys_accept» lfd ev ∧ ¬failed ev ⇒
            log_conns (erlog lfd ifds m w0 k) ≠ []) ∧
      ((erstate lfd ifds m w0 k).p.pause = 0 ∧ (erstate lfd ifds m w0 k).p.acq = [] ∧
       MEM lfd (ifds (erhist lfd ifds m w0 k)) ∧ qof (erworld lfd ifds m w0 k) lfd ≠ [] ⇒
       EXISTS (ev_on «sys_poll» lfd) (erevs lfd ifds m w0 k) ∧
       ∀ev. MEM ev (erevs lfd ifds m w0 k) ∧ ev_on «sys_poll» lfd ev ∧ ¬retried ev ⇒
            EXISTS (ev_on «sys_accept» lfd) (erevs lfd ifds m w0 k))
Proof
  strip_tac >> gen_tac >>
  drule_all erun_eok >> strip_tac >> drule_all erun_linv >> strip_tac >>
  drule_all erun_noob >> strip_tac >>
  drule erun_step >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  qpat_assum ‘∀n. eok _ _ _ ∧ _’ (qspec_then ‘k’ strip_assume_tac) >>
  qpat_assum ‘∀n. eok _ _ _ ∧ _’ (qspec_then ‘SUC k’ strip_assume_tac) >>
  qpat_assum ‘∀n. linv _ _’ (qspec_then ‘k’ assume_tac) >>
  qpat_assum ‘∀n. noob _ _’ (qspec_then ‘k’ assume_tac) >>
  drule_all eround_lfd >> strip_tac >>
  rpt conj_tac
  >- (qexists_tac ‘d’ >> simp[])
  >- (strip_tac >> conj_tac >- (qpat_x_assum ‘0 < _ ⇒ _ ∧ _’ drule >> simp[]) >>
      drule_all eround_paused >> simp[])
  >- first_assum ACCEPT_TAC
  >> first_assum ACCEPT_TAC
QED

(* ------------------------------------------------------------------------
   j0's position in the queue only falls, and falls when a round accepts
   (honestL1PFConnRun's step_pos, pos_run, stuck_rounds)
   ------------------------------------------------------------------------ *)

Theorem erun_step_pos:
  erun_ok lfd ifds m w0 ∧ winv w0 ∧
  p < LENGTH (qof (erworld lfd ifds m w0 k) lfd) ∧
  EL p (qof (erworld lfd ifds m w0 k) lfd) = j0 ∧
  ¬resolved (erworld lfd ifds m w0 (SUC k)) (erlog lfd ifds m w0 k) j0 ⇒
  ∃p'. p' ≤ p ∧ p' < LENGTH (qof (erworld lfd ifds m w0 (SUC k)) lfd) ∧
       EL p' (qof (erworld lfd ifds m w0 (SUC k)) lfd) = j0 ∧
       (log_conns (erlog lfd ifds m w0 k) ≠ [] ∨
        (∃j. MEM j (qof (erworld lfd ifds m w0 k) lfd) ∧
             ¬MEM j (qof (erworld lfd ifds m w0 (SUC k)) lfd)) ⇒ p' < p)
Proof
  strip_tac >> drule_all erun_eok >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  drule erun_step >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  drule_all eround_queue >> strip_tac >>
  rename1 ‘qof _ lfd = DROP kk (qof _ lfd ++ t)’ >>
  qabbrev_tac ‘q = qof (erworld lfd ifds m w0 k) lfd’ >>
  ‘¬(p < kk)’
    by (strip_tac >>
        qpat_x_assum ‘∀j. MEM j (TAKE kk _) ⇒ _’ (qspec_then ‘j0’ mp_tac) >>
        simp[MEM_EL] >> qexists_tac ‘p’ >> simp[EL_TAKE, EL_APPEND1]) >>
  qexists_tac ‘p − kk’ >> simp[EL_DROP, EL_APPEND1] >>
  rpt strip_tac >> Cases_on ‘kk = 0’ >> gvs[] >>
  Cases_on ‘log_conns (erlog lfd ifds m w0 k)’ >> gvs[]
QED

Theorem erun_pos:
  erun_ok lfd ifds m w0 ∧ winv w0 ∧
  (∀k. n ≤ k ⇒ ¬resolved (erworld lfd ifds m w0 (SUC k)) (erlog lfd ifds m w0 k) j0) ∧
  p < LENGTH (qof (erworld lfd ifds m w0 n) lfd) ∧
  EL p (qof (erworld lfd ifds m w0 n) lfd) = j0 ⇒
  ∀d. ∃p'. p' ≤ p ∧ p' < LENGTH (qof (erworld lfd ifds m w0 (n + d)) lfd) ∧
           EL p' (qof (erworld lfd ifds m w0 (n + d)) lfd) = j0
Proof
  strip_tac >> Induct >- (qexists_tac ‘p’ >> simp[]) >>
  pop_assum strip_assume_tac >>
  ‘¬resolved (erworld lfd ifds m w0 (SUC (n + d))) (erlog lfd ifds m w0 (n + d)) j0’
    by simp[] >>
  drule_all erun_step_pos >> strip_tac >> qexists_tac ‘p''’ >> gvs[ADD_CLAUSES]
QED

Theorem erun_stuck:
  erun_ok lfd ifds m w0 ∧ winv w0 ⇒
  ∀p n. (∀k. n ≤ k ⇒ ¬resolved (erworld lfd ifds m w0 (SUC k)) (erlog lfd ifds m w0 k) j0) ∧
        p < LENGTH (qof (erworld lfd ifds m w0 n) lfd) ∧
        EL p (qof (erworld lfd ifds m w0 n) lfd) = j0 ⇒
        ∃N. n ≤ N ∧ ∀k. N ≤ k ⇒ log_conns (erlog lfd ifds m w0 k) = [] ∧
                               ∀j. MEM j (qof (erworld lfd ifds m w0 k) lfd) ⇒
                                   MEM j (qof (erworld lfd ifds m w0 (SUC k)) lfd)
Proof
  strip_tac >> completeInduct_on ‘p’ >> rpt strip_tac >>
  Cases_on ‘∀k. n ≤ k ⇒ log_conns (erlog lfd ifds m w0 k) = [] ∧
                        ∀j. MEM j (qof (erworld lfd ifds m w0 k) lfd) ⇒
                            MEM j (qof (erworld lfd ifds m w0 (SUC k)) lfd)’
  >- (qexists_tac ‘n’ >> simp[]) >>
  qpat_x_assum ‘¬∀k. _’ (strip_assume_tac o SIMP_RULE bool_ss [NOT_FORALL_THM, NOT_IMP]) >>
  rename1 ‘n ≤ k1’ >>
  drule_all erun_pos >> disch_then (qspec_then ‘k1 − n’ (qx_choose_then ‘p1’ strip_assume_tac)) >>
  ‘n + (k1 − n) = k1’ by decide_tac >> pop_assum SUBST_ALL_TAC >>
  ‘¬resolved (erworld lfd ifds m w0 (SUC k1)) (erlog lfd ifds m w0 k1) j0’
    by (qpat_assum ‘∀k. n ≤ k ⇒ ¬resolved _ _ _’ (qspec_then ‘k1’ mp_tac) >> fs[]) >>
  qspecl_then [‘lfd’, ‘ifds’, ‘m’, ‘w0’, ‘p1’, ‘k1’, ‘j0’] mp_tac
    (Q.GENL [‘lfd’, ‘ifds’, ‘m’, ‘w0’, ‘p’, ‘k’, ‘j0’] erun_step_pos) >>
  impl_tac >- fs[] >> disch_then (qx_choose_then ‘p2’ strip_assume_tac) >>
  ‘p2 < p1’ by (first_x_assum irule >> metis_tac[]) >>
  ‘p2 < p’ by metis_tac[LESS_LESS_EQ_TRANS] >>
  qpat_x_assum ‘∀m'. m' < p ⇒ _’ (qspec_then ‘p2’ mp_tac) >> impl_tac >- fs[] >>
  disch_then (qspec_then ‘SUC k1’ mp_tac) >> impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> rpt strip_tac >>
      qpat_assum ‘∀k. n ≤ k ⇒ ¬resolved _ _ _’ (qspec_then ‘k’ mp_tac) >> fs[]) >>
  strip_tac >> qexists_tac ‘N’ >> fs[]
QED

(* With no round accepting from N on, the accepted fds E1 holds are all
   handed out (eS2) *)
Theorem erun_acq_empty:
  erun_ok lfd ifds m w0 ∧ winv w0 ∧ linv lfd w0 ∧ eS2 lfd ifds m w0 ∧
  (∀k. N ≤ k ⇒ log_conns (erlog lfd ifds m w0 k) = []) ⇒
  ∃N1. N ≤ N1 ∧ ∀k. N1 ≤ k ⇒ (erstate lfd ifds m w0 k).p.acq = []
Proof
  strip_tac >> drule_all erun_lfd >> strip_tac >>
  ‘∀d n. N ≤ n ⇒ ∃e. (erstate lfd ifds m w0 (n + d)).p.acq =
                       DROP e (erstate lfd ifds m w0 n).p.acq’
    by (Induct >- (rpt strip_tac >> qexists_tac ‘0’ >> simp[]) >>
        rpt strip_tac >> first_x_assum drule >> strip_tac >>
        first_x_assum (qspec_then ‘n + d’ strip_assume_tac) >>
        ‘log_conns (erlog lfd ifds m w0 (n + d)) = []’ by simp[] >>
        qexists_tac ‘e + d'’ >> gvs[ADD_CLAUSES, DROP_DROP_T]) >>
  ‘∀l n. N ≤ n ∧ LENGTH (erstate lfd ifds m w0 n).p.acq = l ⇒
         ∃N1. n ≤ N1 ∧ (erstate lfd ifds m w0 N1).p.acq = []’
    by (completeInduct_on ‘l’ >> rpt strip_tac >>
        Cases_on ‘(erstate lfd ifds m w0 n).p.acq = []’
        >- (qexists_tac ‘n’ >> simp[]) >>
        qpat_assum ‘eS2 _ _ _ _’ (mp_tac o REWRITE_RULE [eS2_def]) >>
        disch_then drule >> disch_then (qx_choose_then ‘n1’ strip_assume_tac) >>
        first_assum (qspecl_then [‘n1 − n’, ‘n’] mp_tac) >> impl_tac >- simp[] >>
        ‘n + (n1 − n) = n1’ by simp[] >> pop_assum SUBST1_TAC >> strip_tac >>
        Cases_on ‘(erstate lfd ifds m w0 n1).p.acq = []’
        >- (qexists_tac ‘n1’ >> simp[]) >>
        qpat_assum ‘∀k. (∃d. _) ∧ _’ (qspec_then ‘n1’ strip_assume_tac) >>
        ‘0 < d’ by metis_tac[] >>
        ‘log_conns (erlog lfd ifds m w0 n1) = []’ by fs[] >>
        ‘(erstate lfd ifds m w0 (SUC n1)).p.acq =
         DROP (d + e) (erstate lfd ifds m w0 n).p.acq’
          by fs[DROP_DROP_T] >>
        ‘e < LENGTH (erstate lfd ifds m w0 n).p.acq’
          by (CCONTR_TAC >> fs[DROP_LENGTH_TOO_LONG, NOT_LESS]) >>
        first_x_assum (qspec_then ‘LENGTH (erstate lfd ifds m w0 (SUC n1)).p.acq’ mp_tac) >>
        impl_tac >- fs[LENGTH_DROP] >>
        disch_then (qspec_then ‘SUC n1’ mp_tac) >> impl_tac >- fs[] >>
        strip_tac >> qexists_tac ‘N1’ >> fs[]) >>
  first_x_assum (qspecl_then [‘LENGTH (erstate lfd ifds m w0 N).p.acq’, ‘N’] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac ‘N1’ >> simp[] >> rpt strip_tac >>
  first_x_assum (qspecl_then [‘k − N1’, ‘N1’] mp_tac) >> simp[]
QED

(* The pause runs out *)
Theorem erun_pause_zero:
  erun_ok lfd ifds m w0 ∧ winv w0 ∧ linv lfd w0 ⇒
  ∀n. ∃n'. n ≤ n' ∧ (erstate lfd ifds m w0 n').p.pause = 0
Proof
  strip_tac >> drule_all erun_lfd >> strip_tac >>
  ‘∀p n. (erstate lfd ifds m w0 n).p.pause = p ⇒
         ∃n'. n ≤ n' ∧ (erstate lfd ifds m w0 n').p.pause = 0’
    by (completeInduct_on ‘p’ >> rpt strip_tac >>
        Cases_on ‘p = 0’ >- (qexists_tac ‘n’ >> gvs[]) >>
        first_assum (qspec_then ‘n’ strip_assume_tac) >> gvs[] >>
        first_x_assum (qspec_then ‘(erstate lfd ifds m w0 n).p.pause − 1’ mp_tac) >>
        simp[] >> disch_then (qspec_then ‘SUC n’ mp_tac) >> simp[] >>
        strip_tac >> qexists_tac ‘n'’ >> simp[]) >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------
   The trace: its finite prefixes are those of the rounds' events
   ------------------------------------------------------------------------ *)

Definition erpre_def:
  erpre lfd ifds m w0 n = FLAT (GENLIST (erevs lfd ifds m w0) n)
End

Theorem erpre_SUC:
  erpre lfd ifds m w0 (SUC n) = erpre lfd ifds m w0 n ++ erevs lfd ifds m w0 n
Proof
  simp[erpre_def, GENLIST, FLAT_SNOC]
QED

Theorem erun_efplays:
  erun_ok lfd ifds m w0 ⇒ ∀n. efplays w0 (erworld lfd ifds m w0 n) (erpre lfd ifds m w0 n)
Proof
  strip_tac >> Induct >- simp[erpre_def] >>
  simp[erpre_SUC] >> irule efplays_trans >> qexists_tac ‘erworld lfd ifds m w0 n’ >> simp[] >>
  drule erun_step >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  drule efplays_eround >> simp[]
QED

Theorem erun_world_at:
  erun_ok lfd ifds m w0 ⇒
  world_at w0 (erpre lfd ifds m w0 n) = SOME (erworld lfd ifds m w0 n) ∧
  l0_rely (erworld lfd ifds m w0 n) ∧ efaithful w0 (erpre lfd ifds m w0 n)
Proof
  strip_tac >> drule erun_efplays >> disch_then (qspec_then ‘n’ mp_tac) >>
  ‘l0_rely w0’ by fs[erun_ok_def] >>
  simp[efplays_def, world_at_def, l0_replay_def]
QED

Theorem eround_evs_ne:
  eround lfd pol hs ws acts = SOME (snap, ws', log, evs) ⇒ evs ≠ []
Proof
  PairCases_on ‘ws’ >> simp[eround_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 ‘etail _ _ _ wt = _’ >> PairCases_on ‘wt’ >>
  gvs[etail_def, AllCaseEqs()] >> gvs[l1_polls_def, AllCaseEqs()]
QED

Theorem erevs_ne:
  erun_ok lfd ifds m w0 ⇒ erevs lfd ifds m w0 n ≠ []
Proof
  strip_tac >> drule erun_step >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  drule eround_evs_ne >> simp[]
QED

Theorem erpre_len:
  erun_ok lfd ifds m w0 ⇒ ∀n. n ≤ LENGTH (erpre lfd ifds m w0 n)
Proof
  strip_tac >> Induct >- simp[erpre_def] >>
  simp[erpre_SUC] >> drule erevs_ne >> disch_then (qspec_then ‘n’ mp_tac) >>
  Cases_on ‘erevs lfd ifds m w0 n’ >> simp[]
QED

Theorem erun_io_chunk:
  ∀n. erun_io lfd ifds m w0 =
      LAPPEND (fromList (erpre lfd ifds m w0 n))
              (LFLATTEN (LGENLIST (λi. fromList (erevs lfd ifds m w0 (n + i))) NONE))
Proof
  gen_tac >> REWRITE_TAC[erun_io_def, erpre_def] >> MATCH_ACCEPT_TAC LFLATTEN_LGENLIST_chunk
QED

Theorem erio_pre:
  LPREFIX (fromList (erpre lfd ifds m w0 n)) (erun_io lfd ifds m w0)
Proof
  REWRITE_TAC[Q.SPEC ‘n’ erun_io_chunk] >>
  simp[LPREFIX_fromList_LNTH, LNTH_LAPPEND, LNTH_fromList]
QED

Theorem erio_sub:
  l ≼ erpre lfd ifds m w0 N ⇒ LPREFIX (fromList l) (erun_io lfd ifds m w0)
Proof
  rw[IS_PREFIX_APPEND] >>
  qspecl_then [‘lfd’, ‘ifds’, ‘m’, ‘w0’, ‘N’] mp_tac (Q.GENL [‘lfd’, ‘ifds’, ‘m’, ‘w0’, ‘n’] erio_pre) >>
  simp[LPREFIX_fromList_LNTH] >> rpt strip_tac >>
  first_x_assum (qspec_then ‘i’ mp_tac) >> simp[EL_APPEND1]
QED

Theorem erio_prefix:
  erun_ok lfd ifds m w0 ∧ LPREFIX (fromList evs) (erun_io lfd ifds m w0) ⇒
  ∃N. evs ≼ erpre lfd ifds m w0 N
Proof
  strip_tac >> qexists_tac ‘LENGTH evs’ >>
  ‘LENGTH evs ≤ LENGTH (erpre lfd ifds m w0 (LENGTH evs))’ by (drule erpre_len >> simp[]) >>
  ‘LPREFIX (fromList (erpre lfd ifds m w0 (LENGTH evs))) (erun_io lfd ifds m w0)’
    by simp[erio_pre] >>
  fs[LPREFIX_fromList_LNTH] >>
  simp[IS_PREFIX_EQ_TAKE'] >> qexists_tac ‘LENGTH evs’ >>
  simp[LIST_EQ_REWRITE, EL_TAKE] >> rpt strip_tac >>
  ‘i < LENGTH (erpre lfd ifds m w0 (LENGTH evs))’ by decide_tac >>
  qpat_x_assum ‘∀i. i < LENGTH evs ⇒ _’ drule >>
  qpat_x_assum ‘∀i. i < LENGTH (erpre _ _ _ _ _) ⇒ _’ drule >> simp[]
QED

(* ------------------------------------------------------------------------
   [F1] at round granularity (copied from e1FairRounds, see the header)
   ------------------------------------------------------------------------ *)

val ar_tac = rpt (qpat_x_assum ‘∀x. _’ kall_tac) >> decide_tac

Definition crio_def:
  crio (pre : 'a list) r = LAPPEND (fromList pre) (LFLATTEN (LGENLIST (λi. fromList (r i)) NONE))
End

Definition crbl_def:
  crbl (pre : 'a list) (r : num -> 'a list) k = LENGTH pre + LENGTH (FLAT (GENLIST r k))
End

Theorem cFLAT_GENLIST_split:
  ∀d k. FLAT (GENLIST r (k + d)) = FLAT (GENLIST r k) ++ FLAT (GENLIST (λi. r (k + i)) d)
Proof
  Induct >> fs[GENLIST, ADD_CLAUSES, FLAT_SNOC]
QED

Theorem crbl_mono:
  k ≤ k' ⇒ crbl pre r k ≤ crbl pre r k'
Proof
  strip_tac >> ‘∃d. k' = k + d’ by (qexists_tac ‘k' − k’ >> decide_tac) >>
  pop_assum SUBST1_TAC >>
  REWRITE_TAC[crbl_def, cFLAT_GENLIST_split, LENGTH_APPEND] >> decide_tac
QED

Theorem crbl_SUC:
  crbl pre r (SUC k) = crbl pre r k + LENGTH (r k)
Proof
  simp[crbl_def, GENLIST, FLAT_SNOC]
QED

Theorem crio_chunk:
  crio pre r =
  LAPPEND (fromList (pre ++ FLAT (GENLIST r k)))
          (LFLATTEN (LGENLIST (λi. fromList (r (k + i))) NONE))
Proof
  REWRITE_TAC[crio_def, GSYM LAPPEND_fromList, LAPPEND_ASSOC] >>
  AP_TERM_TAC >> MATCH_ACCEPT_TAC LFLATTEN_LGENLIST_chunk
QED

Theorem crio_LNTH:
  p < LENGTH (r k) ⇒ LNTH (crbl pre r k + p) (crio pre r) = SOME (EL p (r k))
Proof
  strip_tac >>
  once_rewrite_tac [Q.INST [‘k’ |-> ‘SUC k’] crio_chunk] >>
  simp[LNTH_LAPPEND, LNTH_fromList, crbl_def, GENLIST, FLAT_SNOC] >>
  simp[EL_APPEND2, EL_APPEND_EQN]
QED

Theorem crio_locate:
  ∀Kb. crbl pre r j ≤ i ∧ i < crbl pre r Kb ∧ LNTH i (crio pre r) = SOME ev ⇒
      ∃k. j ≤ k ∧ MEM ev (r k)
Proof
  Induct
  >- (rpt strip_tac >> qpat_x_assum ‘i < _’ mp_tac >> qpat_x_assum ‘_ ≤ i’ mp_tac >> simp[crbl_def]) >>
  rpt strip_tac >>
  Cases_on ‘i < crbl pre r Kb’ >- (qpat_x_assum ‘_ ⇒ _’ mp_tac >> asm_rewrite_tac[]) >>
  qexists_tac ‘Kb’ >>
  ‘j ≤ Kb’
    by (CCONTR_TAC >> ‘SUC Kb ≤ j’ by decide_tac >>
        ‘crbl pre r (SUC Kb) ≤ crbl pre r j’ by simp[crbl_mono] >> decide_tac) >>
  ‘i − crbl pre r Kb < LENGTH (r Kb)’ by fs[crbl_SUC] >>
  drule crio_LNTH >> disch_then (qspec_then ‘pre’ mp_tac) >>
  ‘crbl pre r Kb + (i − crbl pre r Kb) = i’ by decide_tac >>
  simp[] >> strip_tac >> fs[] >>
  simp[MEM_EL] >> qexists_tac ‘i − crbl pre r Kb’ >> fs[]
QED

Theorem crbl_unbounded:
  (∀i. ∃k. i ≤ k ∧ r k ≠ []) ⇒ ∀m. ∃Kb. m ≤ crbl pre r Kb
Proof
  strip_tac >> Induct
  >- (qexists_tac ‘0’ >> simp[]) >>
  pop_assum strip_assume_tac >>
  first_x_assum (qspec_then ‘Kb’ strip_assume_tac) >>
  qexists_tac ‘SUC k’ >> simp[crbl_SUC] >>
  ‘crbl pre r Kb ≤ crbl pre r k’ by simp[crbl_mono] >>
  Cases_on ‘r k’ >> fs[]
QED

Theorem F1_io_rounds:
  F1_io (crio pre r) ∧ (∀i. ∃k. i ≤ k ∧ ∃ev. MEM ev (r k) ∧ ev_on nm f ev) ⇒
  ∀i. ∃k. i ≤ k ∧ ∃ev. MEM ev (r k) ∧ ev_on nm f ev ∧ ¬retried ev
Proof
  rpt strip_tac >>
  ‘∀i. ∃k. i ≤ k ∧ r k ≠ []’
    by (gen_tac >> first_x_assum (qspec_then ‘i’ strip_assume_tac) >>
        qexists_tac ‘k’ >> Cases_on ‘r k’ >> fs[]) >>
  drule crbl_unbounded >> strip_tac >>
  ‘∀i. ∃i' ev. i ≤ i' ∧ LNTH i' (crio pre r) = SOME ev ∧ ev_on nm f ev’
    by (gen_tac >> first_assum (qspecl_then [‘pre’, ‘i’] strip_assume_tac) >>
        qpat_x_assum ‘∀i. ∃k. i ≤ k ∧ ∃ev. _’ (qspec_then ‘Kb’ strip_assume_tac) >>
        fs[MEM_EL] >> rename1 ‘p < LENGTH (r k)’ >>
        qexistsl_tac [‘crbl pre r k + p’, ‘EL p (r k)’] >>
        simp[crio_LNTH] >>
        ‘crbl pre r Kb ≤ crbl pre r k’ by simp[crbl_mono] >>
        qpat_x_assum ‘ev = _’ (SUBST_ALL_TAC o SYM) >> conj_tac >- ar_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘F1_io _’ (mp_tac o REWRITE_RULE [F1_io_def]) >>
  disch_then (qspecl_then [‘nm’, ‘f’] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (qspec_then ‘crbl pre r i’ strip_assume_tac) >>
  qpat_x_assum ‘∀pre m. ∃Kb. m ≤ crbl pre r Kb’ (qspecl_then [‘pre’, ‘SUC i'’] strip_assume_tac) >>
  ‘i' < crbl pre r Kb’ by decide_tac >>
  drule_all crio_locate >> strip_tac >>
  qexists_tac ‘k’ >> simp[] >> metis_tac[]
QED

Theorem erun_io_crio:
  erun_io lfd ifds m w0 = crio [] (erevs lfd ifds m w0)
Proof
  simp[erun_io_def, crio_def]
QED

Theorem crbl_ge:
  (∀k. r k ≠ []) ⇒ ∀k. k ≤ crbl pre r k
Proof
  strip_tac >> Induct >- simp[] >>
  simp[crbl_SUC] >> first_x_assum (qspec_then ‘k’ mp_tac) >> Cases_on ‘r k’ >> simp[]
QED

(* ------------------------------------------------------------------------
   Failed accepts, in the trace
   ------------------------------------------------------------------------ *)

Theorem e_l0_accept_ok[local]:
  l0_rely w ⇒ l0_res_ok (FST (l0_accept l w))
Proof
  rw[l0_accept_def] >> every_case_tac >> simp[fail_ok, l0_res_ok_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[l0_res_ok_def, fail_ok] >>
  qspec_then ‘x’ mp_tac wordsTheory.w2n_lt >> simp[]
QED

Theorem e_accept_dec[local]:
  l0_rely w ∧ l0_ffi_fn «sys_accept» conf b w = SOME (FFIreturn out u) ⇒
  ∃r. dec_res out = SOME r
Proof
  rw[l0_ffi_fn_def, l0_call_def, AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  ‘l0_rely (l0_tick «sys_accept» w)’ by (irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  drule e_l0_accept_ok >> disch_then (qspec_then ‘bytes_fd conf’ mp_tac) >> simp[] >>
  strip_tac >> drule dec_enc_res >> disch_then (qspec_then ‘[]’ mp_tac) >> simp[]
QED

Theorem efaithful_MEM_call:
  efaithful w l ∧ l0_rely w ∧ MEM ev l ⇒
  ∃x n conf bs u. ev = IO_event (ExtCall n) conf bs ∧ l0_rely x ∧
                  l0_ffi_fn n conf (MAP FST bs) x = SOME (FFIreturn (MAP SND bs) u)
Proof
  rw[MEM_EL] >> drule_all efaithful_EL_call >> metis_tac[]
QED

Theorem erun_accepts_fail_io:
  erun_ok lfd ifds m w0 ∧
  (∀i. ∃k ev. i ≤ k ∧ MEM ev (erevs lfd ifds m w0 k) ∧ ev_on «sys_accept» lfd ev ∧ failed ev) ⇒
  accepts_fail_io (erun_io lfd ifds m w0)
Proof
  rw[accepts_fail_io_def] >>
  first_x_assum (qspec_then ‘i’ strip_assume_tac) >>
  drule erun_world_at >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  drule erun_step >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  drule efplays_eround >> simp[efplays_def] >> strip_tac >>
  drule_all efaithful_MEM_call >> strip_tac >>
  ‘∃p. p < LENGTH (erevs lfd ifds m w0 k) ∧ EL p (erevs lfd ifds m w0 k) = ev’
    by metis_tac[MEM_EL] >>
  ‘∀k. erevs lfd ifds m w0 k ≠ []’ by (gen_tac >> drule erevs_ne >> simp[]) >>
  drule crbl_ge >> disch_then (qspecl_then [‘[]’, ‘k’] assume_tac) >>
  gvs[ev_on_def, failed_def] >>
  drule_all e_accept_dec >> strip_tac >>
  qexistsl_tac [‘crbl [] (erevs lfd ifds m w0) k + p’, ‘conf’, ‘bs’, ‘e’, ‘x'’] >>
  conj_tac >- simp[] >>
  drule_then (qspec_then ‘[]’ assume_tac) crio_LNTH >>
  REWRITE_TAC[erun_io_crio] >> pop_assum (fn th => REWRITE_TAC[th]) >>
  gvs[l0_res_of_def, l0_ev_res_def]
QED

(* ------------------------------------------------------------------------
   R1-live on E1, the connection half (honestL1PFConnRun.live_conn)
   ------------------------------------------------------------------------ *)

Theorem erun_live_conn:
  erun_ok lfd ifds m w0 ∧ winv w0 ∧ linv lfd w0 ∧
  F1_io (erun_io lfd ifds m w0) ∧ eS1 lfd ifds m w0 ∧ eS2 lfd ifds m w0 ∧
  MEM j0 (qof (erworld lfd ifds m w0 n0) lfd) ⇒
  (∃k. n0 ≤ k ∧ resolved (erworld lfd ifds m w0 (SUC k)) (erlog lfd ifds m w0 k) j0) ∨
  ∀i. ∃k ev. i ≤ k ∧ MEM ev (erevs lfd ifds m w0 k) ∧ ev_on «sys_accept» lfd ev ∧ failed ev
Proof
  strip_tac >>
  Cases_on ‘∃k. n0 ≤ k ∧ resolved (erworld lfd ifds m w0 (SUC k)) (erlog lfd ifds m w0 k) j0’
  >- simp[] >>
  disj2_tac >>
  ‘∀k. n0 ≤ k ⇒ ¬resolved (erworld lfd ifds m w0 (SUC k)) (erlog lfd ifds m w0 k) j0’
    by (rpt strip_tac >> qpat_x_assum ‘¬∃k. _’ mp_tac >> simp[] >> qexists_tac ‘k’ >> simp[]) >>
  ‘∃p. p < LENGTH (qof (erworld lfd ifds m w0 n0) lfd) ∧
       EL p (qof (erworld lfd ifds m w0 n0) lfd) = j0’ by metis_tac[MEM_EL] >>
  (* j0 stays queued *)
  ‘∀n. n0 ≤ n ⇒ qof (erworld lfd ifds m w0 n) lfd ≠ []’
    by (rpt strip_tac >> drule_all erun_pos >>
        disch_then (qspec_then ‘n − n0’ strip_assume_tac) >>
        ‘n0 + (n − n0) = n’ by decide_tac >> gvs[]) >>
  (* from N on, no round accepts *)
  ‘∃N. n0 ≤ N ∧ ∀k. N ≤ k ⇒ log_conns (erlog lfd ifds m w0 k) = []’
    by (drule_all erun_stuck >> strip_tac >> qexists_tac ‘N’ >> simp[] >>
        rpt strip_tac >> first_x_assum drule >> simp[]) >>
  (* from N1 on, E1 holds no accepted fd *)
  drule_all erun_acq_empty >> strip_tac >>
  drule_all erun_lfd >> strip_tac >>
  drule_all erun_pause_zero >> strip_tac >>
  qpat_assum ‘eS1 _ _ _ _’ (strip_assume_tac o REWRITE_RULE [eS1_def]) >>
  (* polls on the listener in infinitely many rounds *)
  ‘∀i. ∃k. i ≤ k ∧ ∃ev. MEM ev (erevs lfd ifds m w0 k) ∧ ev_on «sys_poll» lfd ev’
    by (gen_tac >>
        qpat_assum ‘∀n. ∃n'. n ≤ n' ∧ _’ (qspec_then ‘N1 + i’ strip_assume_tac) >>
        qexists_tac ‘n'’ >>
        conj_tac >- (qpat_x_assum ‘N1 + i ≤ n'’ mp_tac >> simp[]) >>
        ‘N1 ≤ n'’ by (qpat_x_assum ‘N1 + i ≤ n'’ mp_tac >> simp[]) >>
        ‘n0 ≤ n'’ by metis_tac[LESS_EQ_TRANS] >>
        ‘(erstate lfd ifds m w0 n').p.acq = []’
          by (qpat_assum ‘∀k. N1 ≤ k ⇒ _’ (qspec_then ‘n'’ mp_tac) >> simp[]) >>
        ‘qof (erworld lfd ifds m w0 n') lfd ≠ []’
          by (qpat_assum ‘∀n. n0 ≤ n ⇒ qof _ _ ≠ []’ (qspec_then ‘n'’ mp_tac) >> simp[]) >>
        qpat_assum ‘∀k. (∃d. _) ∧ _’ (qspec_then ‘n'’ strip_assume_tac) >>
        qpat_x_assum ‘_ ∧ _ ∧ _ ∧ _ ⇒ EXISTS _ _ ∧ _’ mp_tac >> impl_tac >- simp[] >>
        disch_then (strip_assume_tac o REWRITE_RULE [EXISTS_MEM]) >>
        qexists_tac ‘e’ >> simp[]) >>
  (* [F1]: in infinitely many of them, a poll that is not retried *)
  ‘F1_io (crio [] (erevs lfd ifds m w0))’
    by (REWRITE_TAC[GSYM erun_io_crio] >> first_assum ACCEPT_TAC) >>
  ‘∀i. ∃k. i ≤ k ∧ ∃ev. MEM ev (erevs lfd ifds m w0 k) ∧ ev_on «sys_poll» lfd ev ∧
                        ¬retried ev’
    by (drule F1_io_rounds >> disch_then drule >> simp[]) >>
  (* each such round from N1 on has a failed accept *)
  gen_tac >>
  qpat_x_assum ‘∀i. ∃k. i ≤ k ∧ ∃ev. _ ∧ _ ∧ ¬retried ev’ (qspec_then ‘N1 + i’ strip_assume_tac) >>
  qexists_tac ‘k’ >>
  ‘N1 ≤ k ∧ i ≤ k’ by (qpat_x_assum ‘N1 + i ≤ k’ mp_tac >> simp[]) >>
  ‘n0 ≤ k’ by metis_tac[LESS_EQ_TRANS] >>
  qpat_assum ‘∀k. (∃d. _) ∧ _’ (qspec_then ‘k’ strip_assume_tac) >>
  ‘(erstate lfd ifds m w0 k).p.pause = 0’
    by (CCONTR_TAC >>
        ‘0 < (erstate lfd ifds m w0 k).p.pause’
          by (qpat_x_assum ‘(erstate _ _ _ _ _).p.pause ≠ 0’ mp_tac >> simp[]) >>
        qpat_x_assum ‘0 < _ ⇒ _ ∧ _’ drule >>
        disch_then (mp_tac o CONJUNCT2) >> REWRITE_TAC[EXISTS_MEM] >>
        qexists_tac ‘ev’ >> conj_tac >> first_assum ACCEPT_TAC) >>
  ‘(erstate lfd ifds m w0 k).p.acq = []’
    by (qpat_assum ‘∀k. N1 ≤ k ⇒ _’ (qspec_then ‘k’ mp_tac) >> simp[]) >>
  ‘qof (erworld lfd ifds m w0 k) lfd ≠ []’
    by (qpat_assum ‘∀n. n0 ≤ n ⇒ qof _ _ ≠ []’ (qspec_then ‘k’ mp_tac) >> simp[]) >>
  ‘EXISTS (ev_on «sys_accept» lfd) (erevs lfd ifds m w0 k)’
    by (qpat_x_assum ‘_ ∧ _ ∧ _ ∧ _ ⇒ EXISTS _ _ ∧ _’ mp_tac >> impl_tac >- simp[] >>
        strip_tac >> first_x_assum irule >> qexists_tac ‘ev’ >> simp[]) >>
  qpat_x_assum ‘EXISTS (ev_on «sys_accept» _) _’ (strip_assume_tac o REWRITE_RULE [EXISTS_MEM]) >>
  qexists_tac ‘e’ >> simp[] >>
  CCONTR_TAC >>
  ‘log_conns (erlog lfd ifds m w0 k) ≠ []’
    by (qpat_x_assum ‘∀ev. MEM ev _ ∧ ev_on «sys_accept» _ ev ∧ ¬failed ev ⇒ _’ irule >>
        qexists_tac ‘e’ >> simp[]) >>
  ‘N ≤ k’ by metis_tac[LESS_EQ_TRANS] >>
  qpat_x_assum ‘log_conns _ ≠ []’ mp_tac >> simp[]
QED

(* ------------------------------------------------------------------------
   New connections are accepted fds of the trace
   ------------------------------------------------------------------------ *)

Theorem e_sys_accept_accepted[local]:
  sys_accept l w = SOME (out, w', ev) ∧ l0_rely w ∧ l0_res_of out = Ok k ⇒
  l0_event_accepted ev = SOME (n2w k)
Proof
  rw[sys_accept_def, l0_do_def, AllCaseEqs()] >>
  drule_all l0_ffi_fn_length >> strip_tac >>
  gvs[l0_event_accepted_def, l0_ev_res_def, MAP_ZIP, l0_res_of_def, AllCaseEqs()]
QED

Theorem e_pf_fetch_conn[local]:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ l0_rely w ∧
    MEM (FConn g) log ⇒
    ∃ev. MEM ev evs ∧ l0_event_accepted ev = SOME g
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> rw[] >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >>
  imp_res_tac rplays_sys >> gvs[rplays_def] >>
  TRY (qexists_tac ‘ev’ >> simp[] >> metis_tac[e_sys_accept_accepted] >> NO_TAC) >>
  first_x_assum drule_all >> metis_tac[]
QED

Theorem eround_conn:
  eround lfd pol hs (w, es) acts = SOME (snap, (w', es'), log, evs) ∧ l0_rely w ∧
  MEM (FConn g) log ⇒
  ∃ev. MEM ev evs ∧ l0_event_accepted ev = SOME g
Proof
  simp[eround_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  PairCases_on ‘ws1’ >> PairCases_on ‘ws2’ >>
  drule efplays_eacts >> simp[efplays_def] >> strip_tac >>
  qpat_x_assum ‘etail _ _ _ _ = _’ mp_tac >> simp[etail_def, AllCaseEqs()] >> strip_tac >>
  gvs[] >>
  imp_res_tac rplays_polls >> imp_res_tac rplays_flush >> gvs[rplays_def] >>
  drule_all e_pf_fetch_conn >> strip_tac >> qexists_tac ‘ev’ >> simp[]
QED

Theorem erun_conn_accepted:
  erun_ok lfd ifds m w0 ∧ MEM (FConn g) (erlog lfd ifds m w0 k) ⇒
  MEM g (l0_accepted (erpre lfd ifds m w0 (SUC k)))
Proof
  strip_tac >> drule erun_world_at >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  drule erun_step >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  drule_all eround_conn >> strip_tac >>
  simp[erpre_SUC, l0_accepted_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  disj2_tac >> qexists_tac ‘ev’ >> simp[]
QED

(* ------------------------------------------------------------------------
   MAIN (agreed with honest-ffi): raw liveness for connections on E1's
   trace, for every server meeting eS1 and eS2
   ------------------------------------------------------------------------ *)

Theorem e1_conn_live:
  erun_ok lfd ifds m w0 ∧ winv w0 ∧ linv lfd w0 ∧ lone lfd w0 ∧
  F1_io (erun_io lfd ifds m w0) ∧ eS1 lfd ifds m w0 ∧ eS2 lfd ifds m w0 ⇒
  conn_live_l0 w0 (erun_io lfd ifds m w0)
Proof
  rw[conn_live_l0_def, conn_live_unless_def] >>
  drule_all erio_prefix >> strip_tac >>
  ‘∃s. erpre lfd ifds m w0 N = evs ++ s’
    by (qpat_x_assum ‘_ ≼ _’ mp_tac >> simp[IS_PREFIX_APPEND]) >>
  drule erun_world_at >> disch_then (qspec_then ‘N’ strip_assume_tac) >>
  ‘l0_rely w0 ∧ l0wf w0’ by fs[winv_def] >>
  ‘efaithful w0 (evs ++ s)’
    by (qpat_x_assum ‘efaithful w0 _’ mp_tac >>
        qpat_assum ‘erpre _ _ _ _ _ = _’ (fn th => REWRITE_TAC[th])) >>
  ‘lone lfd w ∧ l0wf w’
    by (conj_tac >> irule efaithful_world_inv >>
        (conj_tac
         >- (rpt strip_tac >>
             FIRST [drule_all lone_ffi_e >> simp[] >> NO_TAC,
                    drule_all l0wf_ffi_fn >> simp[]])) >>
        qexistsl_tac [‘evs’, ‘s’, ‘w0’] >> simp[]) >>
  drule_all lone_qof >> strip_tac >>
  qpat_x_assum ‘l = lfd’ SUBST_ALL_TAC >> qpat_x_assum ‘qof _ _ = q’ (SUBST_ALL_TAC o SYM) >>
  ‘FOLDL l0_step (SOME w) (MAP ev_lcall s) = SOME (erworld lfd ifds m w0 N)’
    by (qpat_x_assum ‘world_at w0 (erpre _ _ _ _ _) = _’ mp_tac >>
        qpat_assum ‘erpre _ _ _ _ _ = _’ (fn th => REWRITE_TAC[th]) >>
        simp[world_at_append]) >>
  ‘efaithful w s’
    by (irule efaithful_drop >> qexistsl_tac [‘evs’, ‘w0’] >>
        conj_tac >- (qpat_x_assum ‘world_at w0 evs = SOME w’ mp_tac >>
                     simp[world_at_def, l0_replay_def]) >>
        first_assum ACCEPT_TAC) >>
  Cases_on ‘MEM j0 (qof (erworld lfd ifds m w0 N) lfd)’
  >- ((* still queued at the end of round N: erun_live_conn *)
      qspecl_then [‘N’, ‘j0’] mp_tac (Q.GENL [‘n0’, ‘j0’] erun_live_conn) >>
      impl_tac >- simp[] >> strip_tac
      >- (qpat_x_assum ‘resolved _ _ _’ (strip_assume_tac o REWRITE_RULE [resolved_def])
          >- (disj2_tac >> disj1_tac >>
              qexistsl_tac [‘erpre lfd ifds m w0 (SUC k)’,
                            ‘erworld lfd ifds m w0 (SUC k)’, ‘g’] >>
              simp[erio_pre, erun_world_at] >> drule_all erun_conn_accepted >> simp[])
          >> disj2_tac >> disj2_tac >> simp[broke_def] >>
          qexistsl_tac [‘erpre lfd ifds m w0 (SUC k)’, ‘erworld lfd ifds m w0 (SUC k)’] >>
          simp[erio_pre, erun_world_at])
      >> disj1_tac >> irule erun_accepts_fail_io >> simp[]) >>
  (* it left the queue during the rounds: at an accept naming it, or broken *)
  drule_all qexit_trace_e >> strip_tac >>
  qpat_x_assum ‘s = _’ SUBST_ALL_TAC >>
  ‘world_at w0 (evs ++ a ++ [ev]) = SOME x’
    by (REWRITE_TAC[GSYM APPEND_ASSOC] >> ONCE_REWRITE_TAC[world_at_append] >>
        qpat_assum ‘world_at w0 evs = _’ (fn th => REWRITE_TAC[th]) >>
        qpat_x_assum ‘FOLDL _ _ (MAP _ (_ ++ [_])) = _’ mp_tac >> simp[]) >>
  ‘evs ++ a ++ [ev] ≼ erpre lfd ifds m w0 N’
    by (qpat_x_assum ‘erpre _ _ _ _ _ = _’ SUBST1_TAC >> simp[IS_PREFIX_APPEND]) >>
  ‘LPREFIX (fromList (evs ++ a ++ [ev])) (erun_io lfd ifds m w0)’
    by (irule erio_sub >> qexists_tac ‘N’ >> first_assum ACCEPT_TAC) >>
  TRY (disj2_tac >> disj1_tac >> qexistsl_tac [‘evs ++ a ++ [ev]’, ‘x’, ‘k’] >>
       simp[l0_accepted_def] >> NO_TAC) >>
  disj2_tac >> disj2_tac >> simp[broke_def] >>
  qexistsl_tac [‘evs ++ a ++ [ev]’, ‘x’] >> simp[]
QED
