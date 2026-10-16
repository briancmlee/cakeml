(*
  Why a server's actions stop after the last arrival, for any server
  (design/37 §5, step C1): protoMeasure's argument, with the
  protocol server replaced by what the argument uses of it.

  For a socket-level computation m on the listener lfdn:
   - uses_ok lfdn m: it uses the socket API correctly (accepts on lfdn,
     touches a connection only after accepting it);
   - acts_cause lfdn m: it does nothing at the start; it accepts only when
     the listener is readable in the new snapshot, and reads g only when g
     is readable in it and g's EOF is not read yet (skeletonActs's
     sw_new_actions, store_sv_new_actions for the store);
   - wsafe m ifds s0: in the polling run, on each fd it has written no
     more often than bytes it has read (at most one response per complete
     request).

  Then, in the polling run in a world that receives nothing more after
  round N, every action shrinks protoMeasure's measure (meas_act_gen),
  so the run reaches a round after which it performs no actions
  (acts_stop_gen).  The protocol server meets the three conditions
  (proto_stable_ok), and acts_stop_gen gives proto_acts_stop again.

  MAIN: acts_stop_gen, proto_stable_ok.
*)
Theory stableGen
Ancestors
  pair list rich_list arithmetic option pred_set llist alist words
  asyncCore asyncLevel1 asyncTranscript echoServer echoServerSafety
  socketWorld socketFair loopPollWorld loopRounds
  loopRoundsTrans loopSockInv relabel relabelDist
  echoSockModel echoRunOk loopPollDyn echoLiveSched echoLiveQueue
  echoLiveWorld echoBlockingWaits skeletonRunOk quietRounds
  echoMeasure echoStable skeleton protoInterface
  protoServer protoSafe skeletonActs protoActs
  protoMeasure QuietSpec
Libs
  preamble

(* ------------------------------------------------------------------------
   The conditions
   ------------------------------------------------------------------------ *)

Definition acts_cause_def:
  acts_cause lfdn m ⇔
    (m []).actions = [] ∧
    ∀q s a. MEM a (NA m (q ++ [s])) ⇒
      (∀l. a = Accept l ⇒ l = lfdn ∧ Readable lfdn ∈ s.ready) ∧
      ∀g. a = Read g ⇒
          Readable g ∈ s.ready ∧
          eofs g (trans m (q ++ [s])) < accs g (trans m (q ++ [s]))
End

(* On the polling run's transcripts *)
Definition wsafe_def:
  wsafe m ifds s0 ⇔
    ∀n fd. LENGTH (written fd (TSg m ifds s0 n)) ≤
           LENGTH (CONCAT (read fd (TSg m ifds s0 n)))
End

(* The hypotheses every lemma below shares *)
Overload sok = “λlfdn m s0.
  uses_ok lfdn m ∧ acts_cause lfdn m ∧ wsafe m (EI lfdn) s0 ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64)”

(* ------------------------------------------------------------------------
   The rounds
   ------------------------------------------------------------------------ *)

Theorem gen_gacts_0:
  acts_cause lfdn m ⇒ gacts ifds (srelabel m) s0 0 = []
Proof
  rw[acts_cause_def] >>
  simp[gacts_def, ghist_def, grounds_def, new_actions_relabel, new_actions_NIL,
       log_of_def]
QED

Theorem gen_gacts_SUC:
  gacts ifds (srelabel m) s0 (SUC n) =
  MAP sfa (NA m (MAP sfs (ghist ifds (srelabel m) s0 n) ++
                 [sfs (ssnap (FILTER (is_ready (gstate ifds (srelabel m) s0 (SUC n)))
                                     (ifds (ghist ifds (srelabel m) s0 n)))
                             (gres ifds (srelabel m) s0 n))]))
Proof
  simp[gacts_def, new_actions_relabel, ghist_SUC_snap]
QED

Theorem ready_sfs[local]:
  Readable g ∈ (sfs (ssnap ys rs)).ready ⇔ ∃w. g = w2n w ∧ MEM w ys
Proof
  simp[snap_map_def, ssnap_def, sfe_def] >> metis_tac[]
QED

Theorem MEM_ZIP_FST[local]:
  ∀xs ys. LENGTH xs = LENGTH ys ∧ MEM x xs ⇒ ∃y. MEM (x, y) (ZIP (xs, ys))
Proof
  Induct >> simp[] >> Cases_on ‘ys’ >> simp[] >> rw[] >> metis_tac[]
QED

Theorem read_NONE[local]:
  ∀tt. EVERY (λp. SND p = NONE) tt ⇒ read fd tt = []
Proof
  Induct >> simp[read_def] >> Cases >> rw[] >> gvs[read_def] >>
  Cases_on ‘q’ >> simp[]
QED

(* What round n's actions need, in the world: an accept, the listener
   ready; a read of c, c ready and its EOF not read in the transcript *)
Theorem gacts_cause_gen:
  acts_cause lfdn m ∧ MEM a (gacts ifds (srelabel m) s0 n) ⇒
  ∃k a0. n = SUC k ∧ a = sfa a0 ∧
    (∀l0. a0 = Accept l0 ⇒
          l0 = lfdn ∧ ∃w. lfdn = w2n w ∧ is_ready (gstate ifds (srelabel m) s0 n) w) ∧
    (∀g. a0 = Read g ⇒
         (∃w. g = w2n w ∧ is_ready (gstate ifds (srelabel m) s0 n) w) ∧
         eofs g (TSg m ifds s0 n) < accs g (TSg m ifds s0 n))
Proof
  Cases_on ‘n’ >- metis_tac[gen_gacts_0, MEM] >>
  rename1 ‘SUC k’ >> simp[] >>
  REWRITE_TAC[gen_gacts_SUC, MEM_MAP] >> strip_tac >>
  qexists_tac ‘y’ >> simp[ghist_SUC_snap] >>
  gvs[acts_cause_def] >> first_x_assum drule >> strip_tac >>
  rpt strip_tac >> gvs[ready_sfs, MEM_FILTER] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Each action shrinks the measure
   ------------------------------------------------------------------------ *)

(* An accept takes a pending connection *)
Theorem act_accept_gen:
  sok lfdn m s0 ∧ MEM (Accept l) (gacts (EI lfdn) (srelabel m) s0 n) ⇒
  0 < nacc_ok l (ZIP (gacts (EI lfdn) (srelabel m) s0 n,
                      gres (EI lfdn) (srelabel m) s0 n))
Proof
  strip_tac >>
  ‘grun_ok (EI lfdn) (srelabel m) s0’ by metis_tac[gen_grun_ok] >>
  drule_all gacts_cause_gen >> strip_tac >>
  qpat_x_assum ‘∀g. a0 = Read g ⇒ _’ kall_tac >>
  Cases_on ‘a0’ >> fs[sfa_def] >> gvs[] >>
  qspecl_then [‘interest [l]’, ‘srelabel m’, ‘s0’, ‘w2n l’] mp_tac
    (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘lfdn’] conns_no_listener_g) >>
  simp[] >> disch_then (qspec_then ‘SUC k’ assume_tac) >>
  ‘lq l (gstate (interest [l]) (srelabel m) s0 (SUC k)) ≠ []’
    by (qpat_x_assum ‘is_ready _ _’ mp_tac >> simp[is_ready_def, lq_def] >>
        every_case_tac >> simp[]) >>
  drule grun_ok_sock_acts >> disch_then (qspec_then ‘SUC k’ strip_assume_tac) >>
  drule sock_acts_accepts >> disch_then irule >> fs[]
QED

(* A read takes bytes or the EOF, of a connection whose EOF is not read *)
Theorem act_read_gen:
  sok lfdn m s0 ∧ MEM (Read c k) (gacts (EI lfdn) (srelabel m) s0 n) ⇒
  ¬weofr (EI lfdn) (srelabel m) s0 c n ∧
  (∃cn. ALOOKUP (gstate (EI lfdn) (srelabel m) s0 n).conns c = SOME cn) ∧
  (0 < rdbytes c (ZIP (gacts (EI lfdn) (srelabel m) s0 n,
                       gres (EI lfdn) (srelabel m) s0 n)) ∨
   ∃k'. MEM (Read c k', Got (SOME []))
            (ZIP (gacts (EI lfdn) (srelabel m) s0 n, gres (EI lfdn) (srelabel m) s0 n)))
Proof
  strip_tac >>
  ‘grun_ok (EI lfdn) (srelabel m) s0’ by metis_tac[gen_grun_ok] >>
  drule_all gacts_cause_gen >> strip_tac >>
  qpat_x_assum ‘∀l0. a0 = Accept l0 ⇒ _’ kall_tac >>
  Cases_on ‘a0’ >> fs[sfa_def] >> gvs[] >>
  qmatch_goalsub_rename_tac ‘gstate _ _ _ (SUC j)’ >>
  ‘accs (w2n c) (TSg m (EI lfdn) s0 (SUC j)) ≤ 1’
    by (irule accs_le_one_g >> rpt conj_tac >> TRY (qexists_tac ‘lfdn’) >> fs[]) >>
  ‘eofs (w2n c) (TSg m (EI lfdn) s0 (SUC j)) = 0’ by decide_tac >>
  conj_tac
  >- (strip_tac >>
      ‘1 ≤ eofs (w2n c) (TSg m (EI lfdn) s0 (SUC j))’
        by (irule weofr_eofs >> rpt conj_tac >> TRY (qexists_tac ‘lfdn’) >> fs[]) >>
      decide_tac) >>
  (* c is an accepted connection: not the listener *)
  ‘MEM (w2n c) (accepted (TSg m (EI lfdn) s0 (SUC j)))’
    by (CCONTR_TAC >>
        ‘FILTER ($= (w2n c)) (accepted (TSg m (EI lfdn) s0 (SUC j))) = []’
          by (simp[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
        gvs[accs_accepted]) >>
  ‘MEM c (wacc (gperf (EI lfdn) (srelabel m) s0 (SUC j)))’
    by (drule_all gen_sinv >>
        disch_then (qspecl_then [‘EI lfdn’, ‘SUC j’] strip_assume_tac) >>
        drule gen_trans_split >> strip_tac >>
        drule TREL_accepted >> drule TREL_NONE >> rpt strip_tac >>
        gvs[accepted_NONE, MEM_MAP]) >>
  ‘∃cn. ALOOKUP (gstate (EI lfdn) (srelabel m) s0 (SUC j)).conns c = SOME cn’
    by (irule accepted_conn >> rpt conj_tac >> TRY (qexists_tac ‘lfdn’) >> fs[]) >>
  ‘ALOOKUP (gstate (EI lfdn) (srelabel m) s0 (SUC j)).conns (n2w lfdn) = NONE’
    by (qspecl_then [‘EI lfdn’, ‘srelabel m’, ‘s0’, ‘lfdn’] mp_tac
          (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘lfdn’] conns_no_listener_g) >>
        impl_tac >- fs[] >> simp[]) >>
  ‘ALOOKUP (gstate (EI lfdn) (srelabel m) s0 (SUC j)).listeners c = NONE’
    by (‘c ≠ n2w lfdn’ by (strip_tac >> gvs[]) >>
        qspecl_then [‘s0’, ‘n2w lfdn’, ‘EI lfdn’, ‘srelabel m’] mp_tac
          (Q.GENL [‘s0’, ‘lfd’, ‘ifds’, ‘m’] grounds_known) >>
        simp[] >> disch_then (qspec_then ‘SUC j’ strip_assume_tac) >>
        PairCases_on ‘x0’ >> gvs[]) >>
  conj_tac >- (qexists_tac ‘cn’ >> simp[]) >>
  drule grun_ok_sock_acts >> disch_then (qspec_then ‘SUC j’ strip_assume_tac) >>
  drule sock_acts_reads >> disch_then irule >> simp[] >>
  conj_tac >- (qpat_x_assum ‘is_ready _ _’ mp_tac >> simp[is_ready_def]) >>
  qexists_tac ‘bufsz’ >> simp[]
QED

(* A write is owed: fewer writes to c than bytes read from c *)
Theorem act_write_gen:
  sok lfdn m s0 ∧ MEM (Write c bs) (gacts (EI lfdn) (srelabel m) s0 n) ⇒
  (∃cn. ALOOKUP (gstate (EI lfdn) (srelabel m) s0 n).conns c = SOME cn) ∧
  0 < nwr c (ZIP (gacts (EI lfdn) (srelabel m) s0 n, gres (EI lfdn) (srelabel m) s0 n)) ∧
  nwr c (gperf (EI lfdn) (srelabel m) s0 n) <
  rdbytes c (gperf (EI lfdn) (srelabel m) s0 n)
Proof
  strip_tac >>
  ‘grun_ok (EI lfdn) (srelabel m) s0’ by metis_tac[gen_grun_ok] >>
  drule_all gen_sinv >> disch_then (qspecl_then [‘EI lfdn’, ‘n’] strip_assume_tac) >>
  (* c is accepted *)
  ‘MEM c (wacc (gperf (EI lfdn) (srelabel m) s0 n))’
    by (drule_all gen_round_actions_ok >> simp[EVERY_MEM] >>
        disch_then drule >> simp[action_ok_def]) >>
  conj_tac >- (irule accepted_conn >> rpt conj_tac >> TRY (qexists_tac ‘lfdn’) >> fs[]) >>
  conj_tac
  >- (‘∃r. MEM (Write c bs, r)
               (ZIP (gacts (EI lfdn) (srelabel m) s0 n, gres (EI lfdn) (srelabel m) s0 n))’
        by (irule MEM_ZIP_FST >> simp[LENGTH_gres]) >>
      simp[nwr_def, LENGTH_NON_NIL, FILTER_NEQ_NIL] >>
      qexists_tac ‘(Write c bs, r)’ >> simp[]) >>
  (* safety: no more writes than bytes read *)
  ‘fresh (TSg m (EI lfdn) s0 n)’
    by (irule gen_fresh >> rpt conj_tac >> TRY (qexists_tac ‘lfdn’) >> fs[]) >>
  ‘∀fd. EXISTS (on_fd fd) (TSg m (EI lfdn) s0 n) ⇒ fd < dimword (:64)’
    by (qspecl_then [‘s0’, ‘lfdn’, ‘m’, ‘EI lfdn’, ‘n’] mp_tac
          (Q.GENL [‘s0’, ‘lfdn’, ‘m’, ‘ifds’, ‘n’] gen_fds_bounded) >>
        impl_tac >- fs[] >> simp[]) >>
  ‘LENGTH (written (w2n c) (TSg m (EI lfdn) s0 n)) ≤
   LENGTH (CONCAT (read (w2n c) (TSg m (EI lfdn) s0 n)))’
    by fs[wsafe_def] >>
  drule gen_trans_split >> strip_tac >> gvs[EXISTS_APPEND] >>
  ‘∀fd. EXISTS (on_fd fd) tt1 ⇒ fd < dimword (:64)’
    by (rpt strip_tac >> simp[] >> qpat_x_assum ‘∀fd. _ ∨ _ ⇒ _’ irule >> simp[]) >>
  ‘LENGTH (written (w2n c) tt1) = nwr c (gperf (EI lfdn) (srelabel m) s0 n)’
    by (irule TREL_written >> simp[]) >>
  ‘LENGTH (CONCAT (read (w2n c) tt1)) = rdbytes c (gperf (EI lfdn) (srelabel m) s0 n)’
    by (irule TREL_read >> simp[]) >>
  (* tt2 holds the write, unanswered *)
  drule TREL_NONE >> strip_tac >>
  ‘read (w2n c) tt2 = []’ by (irule read_NONE >> simp[]) >>
  ‘1 ≤ LENGTH (written (w2n c) tt2)’
    by (‘MEM (Write c bs) (MAP (sfa o FST) tt2)’ by simp[] >>
        pop_assum (strip_assume_tac o SIMP_RULE (srw_ss()) [MEM_MAP]) >>
        rename1 ‘MEM p tt2’ >> PairCases_on ‘p’ >>
        Cases_on ‘p0’ >> gvs[sfa_def] >> rename1 ‘MEM (Write fd s, _) tt2’ >>
        ‘fd < dimword (:64)’
          by (simp[] >> qpat_x_assum ‘∀fd. _ ∨ _ ⇒ _’ irule >> disj2_tac >> simp[EXISTS_MEM] >>
              qexists_tac ‘(Write fd s, p1)’ >> simp[]) >>
        gvs[MEM_SPLIT, written_def]) >>
  fs[] >> decide_tac
QED

(* MAIN: after the last arrival, every action shrinks the measure *)
Theorem meas_act_gen:
  sok lfdn m s0 ∧ static_g (EI lfdn) (srelabel m) s0 N ∧ N ≤ n ∧
  gacts (EI lfdn) (srelabel m) s0 n ≠ [] ⇒
  wmeas (n2w lfdn) (EI lfdn) (srelabel m) s0 (ksg (EI lfdn) (srelabel m) s0 N) (SUC n) <
  wmeas (n2w lfdn) (EI lfdn) (srelabel m) s0 (ksg (EI lfdn) (srelabel m) s0 N) n
Proof
  strip_tac >>
  ‘grun_ok (EI lfdn) (srelabel m) s0’ by metis_tac[gen_grun_ok] >>
  ‘next_step (gstate (EI lfdn) (srelabel m) s0 n) = []’ by fs[] >>
  drule_all wmeas_step >>
  disch_then (qspecl_then [‘n2w lfdn’, ‘ksg (EI lfdn) (srelabel m) s0 N’]
                (irule o CONJUNCT2)) >>
  ‘∃h. MEM h (gacts (EI lfdn) (srelabel m) s0 n)’
    by (Cases_on ‘gacts (EI lfdn) (srelabel m) s0 n’ >> fs[] >> metis_tac[MEM]) >>
  Cases_on ‘h’
  (* an accept *)
  >- (disj1_tac >> rename1 ‘Accept a’ >>
      ‘a = n2w lfdn’
        by (qpat_x_assum ‘MEM (Accept _) _’ mp_tac >> strip_tac >>
            drule_at Any gacts_cause_gen >> disch_then drule >> strip_tac >>
            qpat_x_assum ‘∀g. a0 = Read g ⇒ _’ kall_tac >>
            Cases_on ‘a0’ >> fs[sfa_def]) >>
      gvs[] >> irule act_accept_gen >> fs[])
  (* a read *)
  >- (disj2_tac >> rename1 ‘Read c k’ >> qexists_tac ‘c’ >>
      drule_at Any act_read_gen >> simp[] >> strip_tac >>
      ‘MEM c (ksg (EI lfdn) (srelabel m) s0 N)’
        by (irule conn_ks >> rpt conj_tac >> TRY (qexists_tac ‘n’) >> fs[]) >>
      simp[] >> disj1_tac >> drule_all rterm_step >>
      disch_then (qspec_then ‘c’ strip_assume_tac) >> first_x_assum irule >> fs[] >>
      metis_tac[])
  (* a write *)
  >> disj2_tac >> rename1 ‘Write c bs’ >> qexists_tac ‘c’ >>
  drule_at Any act_write_gen >> simp[] >> strip_tac >>
  conj_tac >- (irule conn_ks >> rpt conj_tac >> TRY (qexists_tac ‘n’) >> fs[]) >>
  disj2_tac >> drule_all wterm_step >>
  disch_then (qspec_then ‘c’ strip_assume_tac) >> first_x_assum irule >> simp[]
QED

(* MAIN: in a world where only finitely many things arrive, the polling run
   reaches a round after which it performs no actions *)
Theorem acts_stop_gen:
  sok lfdn m s0 ∧ arrivals_finite s0 ⇒
  ∃N n1. N ≤ n1 ∧ static_g (EI lfdn) (srelabel m) s0 N ∧
         ∀n. n1 ≤ n ⇒ gacts (EI lfdn) (srelabel m) s0 n = []
Proof
  strip_tac >>
  qspecl_then [‘s0’, ‘EI lfdn’, ‘srelabel m’] mp_tac
    (Q.GENL [‘s0’, ‘ifds’, ‘m’] static_after) >>
  simp[] >> strip_tac >>
  ‘grun_ok (EI lfdn) (srelabel m) s0’ by metis_tac[gen_grun_ok] >>
  qabbrev_tac ‘M = wmeas (n2w lfdn) (EI lfdn) (srelabel m) s0
                     (ksg (EI lfdn) (srelabel m) s0 N)’ >>
  ‘∀v n. M n = v ∧ N ≤ n ⇒
         ∃n1. n ≤ n1 ∧ ∀j. n1 ≤ j ⇒ gacts (EI lfdn) (srelabel m) s0 j = []’
    suffices_by (disch_then (qspecl_then [‘M N’, ‘N’] mp_tac) >> simp[] >>
                 strip_tac >> qexistsl [‘N’, ‘n1’] >> simp[]) >>
  completeInduct_on ‘v’ >> rpt strip_tac >>
  Cases_on ‘∀j. n ≤ j ⇒ gacts (EI lfdn) (srelabel m) s0 j = []’
  >- (qexists_tac ‘n’ >> simp[]) >>
  gvs[] >>
  ‘M (SUC j) < M j’
    by (simp[Abbr ‘M’] >> irule meas_act_gen >> fs[]) >>
  ‘M j ≤ M n’
    by (qspecl_then [‘EI lfdn’, ‘srelabel m’, ‘s0’, ‘N’, ‘n2w lfdn’,
                     ‘ksg (EI lfdn) (srelabel m) s0 N’] mp_tac
          (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘N’, ‘l’, ‘ks’] wmeas_le) >>
        impl_tac >- fs[] >>
        disch_then (qspecl_then [‘j − n’, ‘n’] mp_tac) >> simp[Abbr ‘M’]) >>
  first_x_assum (qspec_then ‘M (SUC j)’ mp_tac) >> simp[] >>
  disch_then (qspec_then ‘SUC j’ mp_tac) >> simp[] >> strip_tac >>
  qexists_tac ‘n1’ >> simp[]
QED

(* ------------------------------------------------------------------------
   The protocol server meets the conditions
   ------------------------------------------------------------------------ *)

(* MAIN: the check that the conditions are what protoMeasure used *)
Theorem proto_stable_ok:
  proto_ok P ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  uses_ok lfdn (proto_server P resp lfdn) ∧
  acts_cause lfdn (proto_server P resp lfdn) ∧
  wsafe (proto_server P resp lfdn) ifds s0
Proof
  strip_tac >>
  ‘uses_ok lfdn (proto_server P resp lfdn)’ by metis_tac[proto_uses_ok] >>
  rpt conj_tac
  >- simp[]
  >- (rw[acts_cause_def]
      >- simp[proto_server_def, sw_NIL_actions]
      >> drule proto_server_new_actions >> simp[])
  >> rw[wsafe_def] >>
  ‘fresh (TSg (proto_server P resp lfdn) ifds s0 n)’ by metis_tac[gen_fresh] >>
  drule_all proto_server_safety >> disch_then (qspec_then ‘fd’ assume_tac) >>
  drule IS_PREFIX_LENGTH >> simp[] >> strip_tac >>
  qmatch_goalsub_abbrev_tac ‘STRLEN DD’ >>
  ‘LENGTH (proto_all P DD) ≤ LENGTH DD’ by simp[proto_all_LENGTH] >>
  decide_tac
QED
