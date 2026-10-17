(*
  A pending connection is handed to the server (design/47 D, trace
  assembly, acq case): L1 has at most one pending fd (run_own); it stays
  pending until a round in which the server calls Accept (pround_keep with
  no Accept), which then puts it in L1's table (pround_take); the echo
  calls Accept while one is pending (echo_S2).

  MAIN: run_acq_taken.
*)
Theory honestEchoL0Acq
Ancestors
  honestEchoL0EofCase honestEchoL0LiveOwn honestEchoL0Inv honestEchoL0Obl honestL1PFObl
  honestL1PFConnRun honestL1PFFlush honestL1PFOutLive honestL1PFOut honestL1PFLive
  honestL1PFRound honestL1PFRefine honestL1PFInv honestL1PFModel honestL1Model
Libs
  preamble


Theorem pdo_acq_shape[local]:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ⇒
  ((∀l. a ≠ Accept l) ⇒ ps'.acq = ps.acq ∧
                        ∀g. MEM g (MAP SND ps'.b.tbl) ⇒ MEM g (MAP SND ps.b.tbl)) ∧
  (∀l g q. a = Accept l ∧ ps.acq = g :: q ⇒ ps'.acq = q ∧ MEM g (MAP SND ps'.b.tbl))
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> strip_tac >> gvs[AllCaseEqs(), set_inb_def] >>
  TRY (PairCases_on ‘z’) >> gvs[] >>
  TRY (drule l1_close_shape >> strip_tac >> gvs[forget_def, set_outbox_def]) >>
  TRY (drule l1do_write_l0 >> strip_tac >> gvs[]) >>
  gvs[MEM_MAP, ADELKEY_def, MEM_FILTER, EXISTS_PROD] >>
  TRY (metis_tac[] >> NO_TAC) >>
  qpat_x_assum ‘l1do _ _ _ = _’ mp_tac >> simp[l1do_def] >> rw[AllCaseEqs()] >>
  gvs[set_outbox_def, after_send_def] >> every_case_tac >> gvs[set_outbox_def] >>
  metis_tac[]
QED

Theorem pdo_acq_sub[local]:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ⇒ ∃t. ps.acq = t ++ ps'.acq
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> strip_tac >> gvs[AllCaseEqs(), set_inb_def] >>
  TRY (PairCases_on ‘z’) >> gvs[] >>
  TRY (drule l1_close_shape >> strip_tac >> gvs[forget_def, set_outbox_def]) >>
  TRY (drule l1do_write_l0 >> strip_tac >> gvs[]) >>
  TRY (qexists_tac ‘[h]’ >> simp[] >> NO_TAC) >>
  qexists_tac ‘[]’ >> simp[]
QED

Theorem pacts_acq_sub[local]:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ⇒ ∃t. ps.acq = t ++ ps'.acq
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  PairCases_on ‘ws1’ >> drule pdo_acq_sub >> strip_tac >>
  qpat_x_assum ‘∀w ps rs evs w' ps'. _’ drule >> strip_tac >> metis_tac[APPEND_ASSOC]
QED

Theorem pacts_noacc_tbl[local]:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ (∀l. ¬MEM (Accept l) acts) ⇒
    ps'.acq = ps.acq ∧ ∀g. MEM g (MAP SND ps'.b.tbl) ⇒ MEM g (MAP SND ps.b.tbl)
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  PairCases_on ‘ws1’ >> drule pdo_acq_shape >> strip_tac >>
  ‘∀l. h ≠ Accept l’ by metis_tac[] >> fs[] >>
  qpat_x_assum ‘∀w ps rs evs w' ps'. _’ drule >> strip_tac >> fs[]
QED

Theorem pacts_take:
  ∀acts w ps rs evs w' ps' opn.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ l0_rely w ∧
    own_ok lfd (k, opn) ps ∧ ps.b.nxt + naccepts acts < dimword (:64) ∧ keep f ps ∧
    ps.acq = [f] ∧ (∃l. MEM (Accept l) acts) ⇒
    MEM f (MAP SND ps'.b.tbl)
Proof
  Induct >- simp[] >>
  rpt gen_tac >> disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  qpat_x_assum ‘pacts _ _ _ = _’ mp_tac >>
  simp[Once pacts_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  rveq >> PairCases_on ‘ws1’ >> rename1 ‘pdo lfd (w, ps) a = SOME (r, (w1, ps1), evs1)’ >>
  ‘ps.b.nxt < dimword (:64)’ by fs[] >>
  ‘ps1.b.nxt + naccepts acts < dimword (:64)’
    by (drule pdo_nxt_acc >>
        ‘naccepts (a :: acts) = naccepts [a] + naccepts acts’ by (Cases_on ‘a’ >> simp[]) >>
        fs[wordsTheory.dimword_64]) >>
  drule_all pdo_keep >> strip_tac >>
  drule_all pdo_in >> strip_tac >>
  drule_all pdo_rely >> strip_tac >>
  drule pdo_acq_shape >> strip_tac >>
  qpat_x_assum ‘∃l. MEM (Accept l) (a :: acts)’ mp_tac >>
  Cases_on ‘l0_ep_st (k, opn) evs1’ >> fs[] >>
  reverse (Cases_on ‘∃l. a = Accept l’)
  >- (disch_then (qx_choose_then ‘l0’ assume_tac) >>
      ‘ps1.acq = [f]’ by metis_tac[] >>
      ‘∃l. MEM (Accept l) acts’ by (fs[] >> metis_tac[]) >>
      qpat_x_assum ‘∀w ps rs evs w' ps' opn. pacts _ _ _ = _ ∧ _ ⇒ _’
        (qspecl_then [‘w1’, ‘ps1’, ‘rs'’, ‘evs'’, ‘w'’, ‘ps'’, ‘r'’] mp_tac) >>
      impl_tac >- (fs[wordsTheory.dimword_64] >> metis_tac[]) >> simp[]) >>
  disch_then kall_tac >> fs[] >>
  ‘ps1.acq = [] ∧ MEM f (MAP SND ps1.b.tbl)’ by metis_tac[] >>
  drule pacts_acq_sub >> strip_tac >>
  ‘ps'.acq = []’ by (Cases_on ‘t’ >> gvs[]) >>
  drule pacts_keep >> disch_then drule >> disch_then drule >> simp[] >>
  disch_then (qspec_then ‘f’ mp_tac) >> simp[keep_def]
QED

Theorem FOLDL_drop_out_tbl[local]:
  ∀fs b. (FOLDL drop_out b fs).tbl = b.tbl
Proof
  Induct >> simp[drop_out_def, set_outbox_def]
QED

(* A round's tail leaves L1's table as it is *)
Theorem pf_tail_tbl:
  pf_tail lfd pol hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ∧ winv w ⇒ ps'.b.tbl = ps.b.tbl
Proof
  simp[pf_tail_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  ‘winv w1’ by metis_tac[l1_polls_winv] >>
  drule_all l1_flush_f >> strip_tac >> drule pf_fetch_b >> strip_tac >>
  drule l1_reap_tbl >> strip_tac >> gvs[stall_step_def, FOLDL_drop_out_tbl]
QED

Theorem pround_take:
  pround lfd pol hs (w, ps) acts = SOME (sn, (w', ps'), log, evs) ∧ l0_rely w ∧ winv w ∧
  own_ok lfd (k, opn) ps ∧ ps.b.nxt + naccepts acts < dimword (:64) ∧ keep f ps ∧
  ps.acq = [f] ∧ (∃l. MEM (Accept l) acts) ⇒
  MEM f (MAP SND ps'.b.tbl)
Proof
  simp[pround_def, AllCaseEqs()] >> disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  fs[] >> PairCases_on ‘ws1’ >> gvs[] >>
  ‘MEM f (MAP SND ws11.b.tbl)’
    by (qspecl_then [‘acts’, ‘w’, ‘ps’, ‘rs’, ‘evs'’, ‘ws10’, ‘ws11’, ‘opn’] mp_tac pacts_take >>
        simp[] >> disch_then irule >> qexists_tac ‘l’ >> simp[]) >>
  ‘winv ws10’ by metis_tac[pacts_winv] >>
  drule_all pf_tail_tbl >> simp[]
QED

Theorem pround_noacc:
  pround lfd pol hs (w, ps) acts = SOME (sn, (w', ps'), log, evs) ∧ winv w ∧
  (∀l. ¬MEM (Accept l) acts) ∧ ¬MEM f (MAP SND ps.b.tbl) ⇒
  ¬MEM f (MAP SND ps'.b.tbl)
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >> gvs[] >>
  drule_all pacts_noacc_tbl >> strip_tac >>
  ‘winv ws10’ by metis_tac[pacts_winv] >>
  drule_all pf_tail_tbl >> strip_tac >> gvs[] >>
  metis_tac[]
QED

(* MAIN: a pending fd is handed to the server, and is pending until then *)
Theorem run_acq_taken:
  echo_run lfdn pol w0 ∧ MEM f (rstate (n2w lfdn) pol EI ES w0 n).acq ⇒
  ∃n'. n < n' ∧ MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 n').b.tbl) ∧
       ∀i. n ≤ i ∧ i < n' ⇒ MEM f (rstate (n2w lfdn) pol EI ES w0 i).acq
Proof
  strip_tac >>
  ‘run_ok (n2w lfdn) pol EI ES w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0) ∧
   (∀n. SND (pcm (n2w lfdn) pol EI ES w0 n) + 1 < dimword (:64))’ by fs[echo_run_def] >>
  drule_all run_own >> strip_tac >>
  ‘∀i. pown (n2w lfdn) (rstate (n2w lfdn) pol EI ES w0 i)’
    by metis_tac[run_pown, echo_run_hyp] >>
  ‘∀i. (rstate (n2w lfdn) pol EI ES w0 i).b.nxt +
       naccepts (new_actions (log_of ES) (rhist (n2w lfdn) pol EI ES w0 i)) < dimword (:64)’
    by (gen_tac >>
        qpat_assum ‘run_ok _ _ _ _ _’ (fn th => assume_tac (MATCH_MP prun_some th)) >>
        first_x_assum (qspec_then ‘i’ assume_tac) >>
        Cases_on ‘prun (n2w lfdn) pol EI ES w0 i’ >> rename1 ‘_ = (hh, rr)’ >>
        PairCases_on ‘rr’ >>
        gvs[rstate_def, rhist_def, run_ok_def, pl2_ok_def] >>
        first_x_assum drule >> simp[]) >>
  ‘∀i. MEM f (rstate (n2w lfdn) pol EI ES w0 i).acq ⇒
       keep f (rstate (n2w lfdn) pol EI ES w0 i) ∧
       ¬MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 i).b.tbl)’
    by (rpt gen_tac >> strip_tac >>
        qpat_x_assum ‘∀i. pown _ _’ (qspec_then ‘i’ mp_tac) >>
        simp[pown_def, keep_def, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  ‘(rstate (n2w lfdn) pol EI ES w0 n).acq ≠ []’ by (strip_tac >> fs[]) >>
  drule echo_S2 >> simp[S2_def] >> disch_then drule >> strip_tac >>
  ‘∃m. (n ≤ m ∧ ∃l. MEM (Accept l)
          (new_actions (log_of ES) (rhist (n2w lfdn) pol EI ES w0 m))) ∧
       ∀m'. m' < m ⇒ ¬(n ≤ m' ∧ ∃l. MEM (Accept l)
          (new_actions (log_of ES) (rhist (n2w lfdn) pol EI ES w0 m')))’
    by (ho_match_mp_tac WOP >> metis_tac[]) >>
  ‘∀d. n + d ≤ m ⇒ MEM f (rstate (n2w lfdn) pol EI ES w0 (n + d)).acq’
    by (Induct >> simp[] >> strip_tac >>
        ‘MEM f (rstate (n2w lfdn) pol EI ES w0 (n + d)).acq’
          by (qpat_x_assum ‘n + d ≤ m ⇒ _’ irule >> simp[]) >>
        ‘keep f (rstate (n2w lfdn) pol EI ES w0 (n + d)) ∧
         ¬MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 (n + d)).b.tbl)’
          by (qpat_x_assum ‘∀i. MEM f _ ⇒ keep f _ ∧ _’ irule >> simp[]) >>
        ‘n + SUC d = SUC (n + d)’ by simp[] >> pop_assum SUBST1_TAC >>
        qpat_assum ‘run_ok _ _ _ _ _’
          (fn th => mp_tac (Q.SPEC ‘n + d’ (MATCH_MP prun_round' th))) >>
        strip_tac >>
        qpat_assum ‘∀n. wown _ _ _ ∧ _’ (qspec_then ‘n + d’ strip_assume_tac) >>
        ‘∀l. ¬MEM (Accept l) (new_actions (log_of ES) (rhist (n2w lfdn) pol EI ES w0 (n + d)))’
          by (qpat_x_assum ‘∀m'. m' < m ⇒ _’ (qspec_then ‘n + d’ mp_tac) >> simp[]) >>
        ‘winv (rworld (n2w lfdn) pol EI ES w0 (n + d))’ by metis_tac[winv_run] >>
        ‘¬MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 (SUC (n + d))).b.tbl)’
          by (drule pround_noacc >> disch_then (qspec_then ‘f’ mp_tac) >> simp[]) >>
        Cases_on ‘l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 (n + d))’ >> fs[] >>
        drule pround_keep >> disch_then drule >> disch_then drule >>
        disch_then (qspec_then ‘f’ mp_tac) >> simp[]) >>
  ‘MEM f (rstate (n2w lfdn) pol EI ES w0 m).acq’
    by (first_x_assum (qspec_then ‘m − n’ mp_tac) >> simp[]) >>
  ‘(rstate (n2w lfdn) pol EI ES w0 m).acq = [f]’
    by (qpat_assum ‘∀n. wown _ _ _ ∧ _’ (qspec_then ‘m’ strip_assume_tac) >>
        Cases_on ‘(rstate (n2w lfdn) pol EI ES w0 m).acq’ >> gvs[] >>
        Cases_on ‘t’ >> gvs[]) >>
  qexists_tac ‘SUC m’ >> simp[] >> conj_tac
  >- (qpat_assum ‘run_ok _ _ _ _ _’
        (fn th => mp_tac (Q.SPEC ‘m’ (MATCH_MP prun_round' th))) >>
      strip_tac >>
      qpat_assum ‘∀n. wown _ _ _ ∧ _’ (qspec_then ‘m’ strip_assume_tac) >>
      Cases_on ‘l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 m)’ >> fs[] >>
      ‘winv (rworld (n2w lfdn) pol EI ES w0 m)’ by metis_tac[winv_run] >>
      drule pround_take >> disch_then irule >> fs[wown_def] >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum (qspec_then ‘i − n’ mp_tac) >> simp[]
QED
