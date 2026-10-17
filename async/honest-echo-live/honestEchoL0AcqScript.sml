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
  honestL1PFRound honestL1PFRefine honestL1PFModel honestL1Model
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
