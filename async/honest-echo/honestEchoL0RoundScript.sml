(*
  Route (d), stage S3 (design/46): one round of the prefetching L1 keeps
  the ownership invariants, and moves input as the spec counts it.

  pround_in: for every episode j whose handle is in range, the input L1
  held for j before the round, then the bytes the spec says j received
  during the round, are the bytes the server read through handle j in the
  round, then the input L1 holds for j after it.  Episodes not yet opened
  are included (all four sides are empty), so that the run-level
  invariant needs no special case when an accept opens one.
*)
Theory honestEchoL0Round
Ancestors
  alist ffi honestL0 honestL0World honestL0WorldProps honestL0Rely
  asyncHLModel honestL1Model honestL1Steps honestL1PFModel
  asyncM3World honestEchoL0Spec honestEchoL0Trace honestEchoL0Events
  honestEchoL0Model honestEchoL0Inv
Libs
  preamble

(* An episode the fold has not reached gets no bytes *)
Theorem ep_fold_fresh:
  ∀evs k opn. ep_ok (k, opn) ∧ FST (l0_ep_st (k, opn) evs) ≤ j ⇒
              ep_fold pf fdf j (k, opn) evs = []
Proof
  Induct >> simp[ep_fold_def] >> rpt gen_tac >> strip_tac >>
  ‘k ≤ FST (l0_ep_step (k, opn) h)’
    by (simp[l0_ep_step_def] >> every_case_tac >> simp[]) >>
  ‘FST (l0_ep_st (l0_ep_step (k, opn) h) evs) ≤ j’ by fs[] >>
  ‘FST (l0_ep_st (l0_ep_step (k, opn) h) evs) =
   FST (l0_ep_step (k, opn) h) + LENGTH (l0_accepted evs)’
    by (Cases_on ‘l0_ep_step (k, opn) h’ >> simp[FST_l0_ep_st]) >>
  conj_tac
  >- (every_case_tac >> simp[] >> gvs[ep_ok_def, EVERY_MEM] >>
      imp_res_tac ALOOKUP_MEM >>
      ‘MEM j (MAP SND opn)’ by (simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
      res_tac >> fs[]) >>
  Cases_on ‘l0_ep_step (k, opn) h’ >> first_x_assum irule >> fs[] >>
  metis_tac[ep_ok_step]
QED

(* A handle at or past the episode count is not in the table *)
Theorem own_fresh:
  own_ok lfd (k, opn) ps ∧ k ≤ j ∧ hdln (w2n lfd) j < 18446744073709551616 ⇒
  ALOOKUP ps.b.tbl (hdl lfd j) = NONE ∧ inbp lfd ps j = []
Proof
  strip_tac >>
  ‘ALOOKUP ps.b.tbl (hdl lfd j) = NONE’
    by (Cases_on ‘ALOOKUP ps.b.tbl (hdl lfd j)’ >> simp[] >>
        ‘ALOOKUP ps.b.tbl (l1hdl lfd j) = SOME x’ by simp[] >>
        drule_all own_tbl_lookup >> strip_tac >>
        rename1 ‘l1hdl lfd j = l1hdl lfd i’ >>
        ‘i < k’ by gvs[own_ok_def] >>
        ‘hdln (w2n lfd) j < dimword (:64) ∧ hdln (w2n lfd) i < dimword (:64)’
          by (simp[] >> irule hdln_mono >> qexists_tac ‘j’ >> simp[]) >>
        ‘i = j’ by (qpat_x_assum ‘l1hdl _ _ = _’ mp_tac >> simp[hdl_eq_iff]) >>
        gvs[]) >>
  simp[inbp_def]
QED

Theorem hread_cons[local]:
  hread hd ((a, SOME r) :: tr) = hrd hd a r ++ hread hd tr
Proof
  simp[hrd_def, Once hread_def] >> simp[hread_def]
QED

(* The actions answer no read on a handle not yet handed out *)
Theorem pacts_fresh:
  ∀acts w ps rs evs w' ps' opn.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ l0_rely w ∧
    own_ok lfd (k, opn) ps ∧ l1hdln (w2n lfd) k < dimword (:64) ∧
    k ≤ j ∧ hdln (w2n lfd) j < 18446744073709551616 ⇒
    hread (l1hdl lfd j) (ZIP (acts, MAP SOME rs)) = []
Proof
  Induct >- simp[pacts_def, hread_def] >> simp[pacts_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  rename1 ‘pdo lfd (w, ps) a = SOME (r, ws1, evs1)’ >> PairCases_on ‘ws1’ >>
  ‘hrd (l1hdl lfd j) a r = []’
    by (drule_all own_fresh >> strip_tac >>
        Cases_on ‘a’ >> simp[] >>
        simp[hrd_def, hread_def] >> every_case_tac >> gvs[pdo_def, AllCaseEqs()]) >>
  fs[hread_cons] >>
  ‘l1hdln (w2n lfd) k < dimword (:64)’ by fs[] >>
  drule_all pdo_in >> strip_tac >>
  ‘l0_rely ws10’ by metis_tac[pdo_rely] >>
  Cases_on ‘l0_ep_st (k, opn) evs1’ >> gvs[] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

(* The fds polled for input: the listener and the table's fds *)
Theorem in_fds_poll_set:
  MEM f (in_fds (pf_poll_set lfd hw ps hs)) ⇒ f = lfd ∨ MEM f (MAP SND ps.b.tbl)
Proof
  simp[in_fds_def, pf_poll_set_def, MEM_MAP, MEM_FILTER, MEM_FLAT, EXISTS_PROD,
       PULL_EXISTS] >>
  rw[] >> gvs[AllCaseEqs()] >>
  every_case_tac >> gvs[] >>
  imp_res_tac ALOOKUP_MEM >> metis_tac[]
QED

(* A closing fd is out of the table and not pending *)
Theorem own_closing_free:
  own_ok lfd (k, opn) ps ∧ MEM f ps.b.closing ⇒
  ¬MEM f (MAP SND ps.b.tbl) ∧ ¬MEM f ps.acq
Proof
  strip_tac >> fs[own_ok_def] >>
  ‘∃j. j < ps.b.nxt ∧ ALOOKUP opn f = SOME j ∧ ALOOKUP ps.b.tbl (hdl lfd j) = NONE’
    by metis_tac[] >>
  conj_tac
  >- (simp[MEM_MAP, EXISTS_PROD] >> rpt strip_tac >>
      ‘∃i. i < ps.b.nxt ∧ p_1 = hdl lfd i ∧ ALOOKUP opn f = SOME i’ by metis_tac[] >>
      gvs[ALOOKUP_NONE, MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  simp[MEM_EL] >> rpt strip_tac >>
  ‘ALOOKUP opn (EL n ps.acq) = SOME (n + ps.b.nxt)’ by metis_tac[] >> gvs[]
QED

Theorem wown_hup[local]:
  wown lfd w (hup_step hfs ob log ps) ⇔ wown lfd w ps
Proof
  simp[wown_def, owned_def]
QED

Theorem pdo_nxt[local]:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ⇒ ps.b.nxt ≤ ps'.b.nxt
Proof
  Cases_on ‘a’ >>
  rw[pdo_def, l1do_def, l1_close_def, forget_def, set_outbox_def, after_send_def,
     AllCaseEqs()] >>
  gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), forget_def, set_outbox_def, set_inb_def] >>
  TRY (Cases_on ‘l0_res_of out’) >> gvs[after_send_def, set_outbox_def] >> rw[]
QED

Theorem pacts_nxt[local]:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ⇒
    ps.b.nxt ≤ ps'.b.nxt ∧ (acts = [] ⇒ ps' = ps)
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> rename1 ‘pdo lfd (w, ps) a = SOME (r, ws1, evs1)’ >>
  PairCases_on ‘ws1’ >> drule pdo_nxt >> first_x_assum drule >> simp[]
QED

(* The tail of a round (poll, flush, fetch, hung-up policy, reap): input
   arrives through the fetch only *)
Theorem pf_tail_in:
  pf_tail lfd hw hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ∧
  wown lfd w ps ∧ own_ok lfd (k, opn) ps ∧ LENGTH ps.acq ≤ 1 ∧
  l1hdln (w2n lfd) (ps.b.nxt + 1) < dimword (:64) ⇒
  wown lfd w' ps' ∧ own_ok lfd (l0_ep_st (k, opn) evs) ps' ∧ LENGTH ps'.acq ≤ 1 ∧
  ps'.b.nxt = ps.b.nxt ∧
  ∀j. hdln (w2n lfd) j < 18446744073709551616 ⇒
      inbp lfd ps' j = inbp lfd ps j ++ ep_rd j (k, opn) evs
Proof
  strip_tac >> qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >>
  simp[pf_tail_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  rename1 ‘l1_polls _ w = SOME (rv, w1, pevs)’ >>
  rename1 ‘l1_flush _ _ = SOME ((w2, b2), fevs)’ >>
  rename1 ‘pf_fetch _ _ _ _ = SOME ((w3, ps3'), log, gevs)’ >>
  rename1 ‘l1_reap _ _ = SOME ((w4, b4), cevs)’ >>
  ‘l0_rely w’ by gvs[wown_def] >>
  (* poll *)
  drule_all l1_polls_in >> disch_then (qspec_then ‘(k, opn)’ strip_assume_tac) >>
  drule_all l1_polls_wown >> strip_tac >>
  (* flush *)
  drule_all l1_flush_in >> disch_then (qspec_then ‘(k, opn)’ strip_assume_tac) >>
  ‘wown lfd w2 (ps with b := b2)’ by (irule l1_flush_wown >> metis_tac[]) >>
  ‘own_ok lfd (k, opn) (ps with b := b2) ∧ inbp lfd (ps with b := b2) = inbp lfd ps’
    by (mp_tac (Q.INST [‘ps'’ |-> ‘ps with b := b2’, ‘es’ |-> ‘(k, opn)’] own_ok_cong) >>
        simp[]) >>
  (* fetch *)
  drule pf_fetch_in >>
  disch_then (qspecl_then [‘k’, ‘opn’] mp_tac) >> simp[] >>
  impl_tac
  >- (rw[MEM_FILTER] >> TRY (drule in_fds_poll_set >> simp[] >> NO_TAC) >> fs[]) >>
  strip_tac >>
  qabbrev_tac ‘ps3 = hup_step (hup_fds rv) (outbox_of ps.b) log ps3'’ >>
  ‘wown lfd w3 ps3 ∧ own_ok lfd (l0_ep_st (k, opn) gevs) ps3 ∧ inbp lfd ps3 = inbp lfd ps3' ∧
   ps3.b.tbl = ps.b.tbl ∧ ps3.b.nxt = ps.b.nxt ∧ ps3.acq = ps3'.acq ∧
   ps3.b.closing = ps3'.b.closing’
    by simp[Abbr ‘ps3’, wown_hup, hup_step_in] >>
  (* reap *)
  Cases_on ‘l0_ep_st (k, opn) gevs’ >> rename1 ‘l0_ep_st _ gevs = (k3, opn3)’ >>
  ‘∀f. MEM f ps3.b.closing ⇒ ¬MEM f (MAP SND ps3.b.tbl) ∧ ¬MEM f ps3.acq ∧ f ≠ lfd’
    by (rpt gen_tac >> strip_tac >> drule_all own_closing_free >> strip_tac >> simp[] >>
        strip_tac >> gvs[wown_def, owned_def]) >>
  ‘l1_reap ps3.b.closing (w3, ps3.b) = SOME ((w4, b4), cevs)’ by gvs[] >>
  ‘wown lfd w4 (ps3 with b := b4)’ by (irule l1_reap_wown >> metis_tac[]) >>
  qspecl_then [‘ps3.b.closing’, ‘w3’, ‘ps3.b’, ‘w4’, ‘b4’, ‘cevs’, ‘opn3’] mp_tac
    (Q.INST [‘ps’ |-> ‘ps3’, ‘k’ |-> ‘k3’] l1_reap_in) >>
  simp[] >> impl_tac >- (gvs[wown_def] >> metis_tac[]) >> strip_tac >>
  ‘l0_ep_st (k, opn) evs = l0_ep_st (k3, opn3) cevs’
    by (qpat_x_assum ‘_ = evs’ (SUBST_ALL_TAC o SYM) >> simp[]) >>
  ‘FST (l0_ep_st (k, opn) evs) = k3’ by simp[] >>
  ‘∀j. ep_rd j (k, opn) evs = ep_rd j (k, opn) gevs’
    by (qpat_x_assum ‘_ = evs’ (SUBST_ALL_TAC o SYM) >> simp[ep_fold_APPEND]) >>
  qpat_x_assum ‘_ = ps'’ (SUBST_ALL_TAC o SYM) >>
  ‘inbp lfd (ps3 with <|b := b4; pause := ps3'.pause − 1|>) = inbp lfd ps3'’
    by (qpat_x_assum ‘inbp lfd ps3 = _’ (SUBST1_TAC o SYM) >>
        fs[inbp_def, FUN_EQ_THM, inb_of_def]) >>
  ‘ep_ok (k, opn)’ by gvs[own_ok_def] >>
  ‘k3 ≤ ps.b.nxt + 1 ∧ ps.b.nxt ≤ k’
    by (‘ps3'.b.nxt = ps.b.nxt’ by gvs[] >> gvs[own_ok_def]) >>
  rpt conj_tac
  >- (qpat_x_assum ‘wown _ w4 _’ mp_tac >> simp[wown_def, owned_def] >> metis_tac[])
  >- (qpat_x_assum ‘own_ok _ (l0_ep_st (k3, opn3) cevs) _’ mp_tac >>
      Cases_on ‘l0_ep_st (k3, opn3) cevs’ >> simp[own_ok_def, inb_of_def] >> strip_tac >> gvs[])
  >- gvs[]
  >- gvs[] >>
  rpt strip_tac >> simp[] >>
  Cases_on ‘j ≤ k’ >- simp[] >>
  ‘k3 ≤ j’ by simp[] >>
  ‘ep_rd j (k, opn) gevs = []’
    by (irule ep_fold_fresh >> simp[]) >>
  ‘inbp lfd ps j = []’ by (irule (cj 2 own_fresh) >> simp[] >> qexistsl [‘k’, ‘opn’] >> simp[]) >>
  ‘inbp lfd ps3' j = []’ by (irule (cj 2 own_fresh) >> simp[] >> qexistsl [‘k3’, ‘opn3’] >> simp[]) >>
  simp[]
QED

(* MAIN: a round, with room for its handles (as hdl_room), keeps the
   invariants; per episode in range, the input held before it and the
   bytes the spec counts during it are the bytes the server read in it,
   then the input held after it *)
Theorem pround_in:
  pround lfd hw hs (w, ps) acts = SOME (sn, (w', ps'), log, evs) ∧
  wown lfd w ps ∧ own_ok lfd (k, opn) ps ∧ LENGTH ps.acq ≤ 1 ∧
  l1hdln (w2n lfd) (ps.b.nxt + LENGTH acts + 1) < dimword (:64) ⇒
  ∃rdy rs. sn = ssnap rdy rs ∧ LENGTH rs = LENGTH acts ∧
    wown lfd w' ps' ∧ own_ok lfd (l0_ep_st (k, opn) evs) ps' ∧ LENGTH ps'.acq ≤ 1 ∧
    ∀j. hdln (w2n lfd) j < 18446744073709551616 ⇒
        inbp lfd ps j ++ ep_rd j (k, opn) evs =
        hread (l1hdl lfd j) (ZIP (acts, MAP SOME rs)) ++ inbp lfd ps' j
Proof
  strip_tac >> qpat_x_assum ‘pround _ _ _ _ _ = _’ mp_tac >>
  simp[pround_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  rename1 ‘pacts _ _ _ = SOME (rs, evs1, ws1)’ >> PairCases_on ‘ws1’ >>
  rename1 ‘pf_tail _ _ _ _ = SOME (rdy, _, log2, tevs)’ >>
  qexistsl [‘rdy’, ‘rs’] >>
  ‘l0_rely w’ by gvs[wown_def] >>
  ‘k ≤ ps.b.nxt + 1’ by gvs[own_ok_def] >>
  ‘l1hdln (w2n lfd) k < dimword (:64)’
    by (fs[] >> irule hdln_mono >> qexists_tac ‘ps.b.nxt + (LENGTH acts + 1)’ >> simp[]) >>
  drule_all pacts_in >> strip_tac >>
  drule_all pacts_wown >> strip_tac >>
  drule pacts_nxt >> strip_tac >>
  Cases_on ‘l0_ep_st (k, opn) evs1’ >> rename1 ‘l0_ep_st _ _ = (k1, opn1)’ >> gvs[] >>
  ‘LENGTH ws11.acq ≤ 1 ∧ ws11.b.nxt ≤ ps.b.nxt + LENGTH acts’
    by (Cases_on ‘acts’ >> gvs[own_ok_def]) >>
  ‘l1hdln (w2n lfd) (ws11.b.nxt + 1) < dimword (:64)’
    by (fs[] >> irule hdln_mono >> qexists_tac ‘ps.b.nxt + (LENGTH acts + 1)’ >> simp[]) >>
  drule_all pf_tail_in >> strip_tac >> simp[] >> rpt strip_tac >>
  ‘inbp lfd ps j ++ ep_rd j (k, opn) evs1 =
   hread (l1hdl lfd j) (ZIP (acts, MAP SOME rs)) ++ inbp lfd ws11 j’
    by (Cases_on ‘j < k’ >- simp[] >>
        ‘k ≤ j’ by simp[] >>
        ‘inbp lfd ps j = []’
          by (irule (cj 2 own_fresh) >> simp[] >> qexistsl [‘k’, ‘opn’] >> simp[]) >>
        ‘inbp lfd ws11 j = []’
          by (irule (cj 2 own_fresh) >> simp[] >> qexistsl [‘k’, ‘opn1’] >> simp[]) >>
        ‘ep_rd j (k, opn) evs1 = []’
          by (irule ep_fold_fresh >> gvs[own_ok_def]) >>
        ‘hread (l1hdl lfd j) (ZIP (acts, MAP SOME rs)) = []’
          by (irule pacts_fresh >> simp[] >> metis_tac[]) >>
        simp[]) >>
  first_x_assum (qspec_then ‘j’ mp_tac) >> simp[ep_fold_APPEND]
QED
