(*
  E1's round, paused (task D, r3-close): the listener never has an outbox
  (honestL1PFConnRun's noob, through edo, etail and eshuts), so a round
  with the listener paused does not poll it (pround_paused's analogue).
*)
Theory honestL1EPConnNoob
Ancestors
  honestL1EPConnRound honestL1EPOwnRun e1RoundInv e1RoundTail
  honestL1EPTotal honestL1EPModel honestL1PFConnRun honestL1PFConn honestL1PFClose
  honestL1PFInv honestL1PFRefine honestL1PFRound
  honestL1PFModel honestL1Model honestL0World
Libs
  preamble

(* ------------------------------------------------------------------------
   noob through the round
   ------------------------------------------------------------------------ *)

Theorem edo_noob:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ eown0 lfd es ∧ noob lfd es.p.b ⇒
  noob lfd es'.p.b
Proof
  strip_tac >> ‘pown lfd es.p’ by fs[eown0_def] >>
  Cases_on ‘a’ >> qpat_x_assum ‘edo _ _ _ _ = _’ mp_tac >> simp[edo_def] >>
  rw[AllCaseEqs()] >> gvs[ec_del_def] >>
  TRY (PairCases_on ‘z’ >> gvs[] >> drule_all pdo_noob >> simp[] >> NO_TAC) >>
  TRY (gvs[pf_close_def, AllCaseEqs()]) >>
  TRY (qmatch_asmsub_rename_tac ‘l1_close _ _ = SOME zz’ >> PairCases_on ‘zz’ >> gvs[] >>
       drule l1_close_noob >> disch_then (qspec_then ‘lfd’ irule) >>
       gvs[pf_release_def, set_inb_def, noob_def] >> NO_TAC) >>
  gvs[pf_release_def, set_inb_def, noob_def]
QED

Theorem eacts_noob:
  ∀acts w es rs evs w' es'.
    eacts lfd pol (w, es) acts = SOME (rs, evs, (w', es')) ∧ eok lfd w es ∧ noob lfd es.p.b ⇒
    noob lfd es'.p.b
Proof
  Induct >> simp[eacts_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  ‘eown0 lfd es’ by fs[eok_def] >>
  drule_all edo_noob >> strip_tac >>
  drule_all edo_eok >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem settle_fds_p:
  ∀fs w es w' es' evs. settle_fds fs (w, es) = SOME ((w', es'), evs) ⇒ es'.p = es.p
Proof
  Induct >> simp[settle_fds_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> first_x_assum drule >>
  rw[] >> every_case_tac >> gvs[]
QED

Theorem settle_fds_names:
  ∀fs w es w' es' evs.
    settle_fds fs (w, es) = SOME ((w', es'), evs) ⇒
    EVERY (λev. ev_name ev = ExtCall «sys_connerr») evs
Proof
  Induct >> simp[settle_fds_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> first_x_assum drule >> simp[] >>
  metis_tac[sys_ev_name]
QED

Theorem etail_noob:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, tevs) ∧ noob lfd es.p.b ⇒
  noob lfd es'.p.b
Proof
  simp[etail_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘l1_flush _ _ = SOME ((w2, b2), fevs)’ >>
  rename1 ‘pf_fetch _ _ _ _ = SOME ((w3, ps3f), log, gevs)’ >>
  rename1 ‘l1_reap _ _ = SOME ((w4, b4), cevs)’ >>
  rename1 ‘settle_fds _ _ = SOME ((w5, es5), sevs)’ >>
  drule_all l1_flush_noob >> strip_tac >>
  drule pf_fetch_b >> strip_tac >>
  qmatch_asmsub_abbrev_tac ‘l1_reap _ (_, ps3.b)’ >>
  ‘noob lfd ps3.b’
    by (simp[Abbr ‘ps3’, noob_def] >> strip_tac >>
        drule (cj 3 stall_step_outbox) >> gvs[noob_def]) >>
  drule_all l1_reap_noob >> strip_tac >>
  drule settle_fds_p >> strip_tac >>
  gvs[promote_def, apply_early_def]
QED

Theorem pf_shuts_noob:
  ∀fs w ps w' ps' kp sh evs.
    pf_shuts fs (w, ps) = SOME ((w', ps'), kp, sh, evs) ∧ noob lfd ps.b ⇒ noob lfd ps'.b
Proof
  Induct >- simp[pf_shuts_def] >>
  rpt gen_tac >> rename1 ‘kf :: fs’ >> PairCases_on ‘kf’ >>
  simp[Once pf_shuts_def] >>
  IF_CASES_TAC
  >- (strip_tac >> gvs[] >> PairCases_on ‘z’ >> gvs[] >> first_x_assum drule_all >> simp[]) >>
  IF_CASES_TAC
  >- (strip_tac >> gvs[] >> PairCases_on ‘z’ >> gvs[] >> first_x_assum drule_all >> simp[]) >>
  Cases_on ‘sys_shutdown kf1 w’ >> simp[] >>
  rename1 ‘sys_shutdown kf1 w = SOME r’ >> PairCases_on ‘r’ >> simp[] >>
  Cases_on ‘l0_res_of r0’ >> simp[]
  >- (strip_tac >> PairCases_on ‘z’ >> gvs[] >> first_x_assum drule_all >> simp[]) >>
  IF_CASES_TAC >> simp[]
  >- (strip_tac >> PairCases_on ‘z’ >> gvs[] >> first_x_assum drule_all >> simp[]) >>
  strip_tac >> PairCases_on ‘z’ >> gvs[] >> first_x_assum drule >> disch_then irule >>
  simp[drop_out_def] >> irule noob_set_outbox >> simp[]
QED

Theorem eshuts_noob:
  eshuts (w, es) = SOME ((w', es'), evs) ∧ noob lfd es.p.b ⇒ noob lfd es'.p.b
Proof
  simp[eshuts_def] >> strip_tac >> pairarg_tac >> gvs[] >>
  drule_all pf_shuts_noob >> simp[]
QED

Theorem eround_noob:
  eround lfd pol hs (w, es) acts = SOME (snap, (w', es'), log, evs) ∧ eok lfd w es ∧
  noob lfd es.p.b ⇒
  noob lfd es'.p.b
Proof
  simp[eround_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  PairCases_on ‘ws1’ >> PairCases_on ‘ws2’ >>
  drule_all eacts_noob >> strip_tac >>
  drule_all etail_noob >> strip_tac >>
  drule_all eshuts_noob >> simp[]
QED

(* ------------------------------------------------------------------------
   Paused, E1 does not poll the listener
   ------------------------------------------------------------------------ *)

Theorem etail_paused:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, tevs) ∧
  eok lfd w es ∧ noob lfd es.p.b ∧ 0 < es.p.pause ⇒
  ¬EXISTS (ev_on «sys_poll» lfd) tevs
Proof
  simp[etail_def] >> strip_tac >>
  qabbrev_tac ‘fes = pf_poll_set lfd pol es.p hs ++ MAP (λf. (f, 2n)) (pend_fds es)’ >>
  gvs[AllCaseEqs()] >>
  rename1 ‘l1_polls _ w = SOME (rv, w1, pevs)’ >>
  rename1 ‘l1_flush _ _ = SOME ((w2, b2), fevs)’ >>
  rename1 ‘pf_fetch _ _ _ _ = SOME ((w3, ps3f), log, gevs)’ >>
  rename1 ‘l1_reap _ _ = SOME ((w4, b4), cevs)’ >>
  rename1 ‘settle_fds _ _ = SOME ((w5, es5), sevs)’ >>
  drule_then strip_assume_tac eok_facts >>
  qpat_x_assum ‘eok _ _ _’ (strip_assume_tac o REWRITE_RULE [eok_def]) >>
  ‘∀h. ALOOKUP es.p.b.tbl h ≠ SOME lfd’
    by (rpt strip_tac >> imp_res_tac ALOOKUP_MEM >>
        gvs[pown_def, MEM_MAP] >> metis_tac[SND]) >>
  ‘¬MEM lfd (MAP FST (pf_poll_set lfd pol es.p hs))’ by (irule pf_poll_set_paused >> simp[]) >>
  ‘∀f. MEM f (pend_fds es) ⇒ small f ∧ f ≠ lfd’
    by (rpt gen_tac >> strip_tac >> drule pend_fds_ctbl >> strip_tac >>
        gvs[esmall_def, EVERY_MEM, eown0_def, ALL_DISTINCT_APPEND] >>
        strip_tac >> gvs[]) >>
  ‘¬MEM lfd (MAP FST fes)’
    by (simp[Abbr ‘fes’, MAP_MAP_o, combinTheory.o_DEF] >> strip_tac >>
        first_x_assum drule >> simp[]) >>
  ‘EVERY (λ(g, e). small g ∧ e < 4) (pf_poll_set lfd pol es.p hs)’
    by (irule pf_poll_set_small >> simp[]) >>
  ‘∀c. MEM c [fes] ⇒ EVERY (λ(g, e). small g ∧ e < 4) c’
    by (simp[Abbr ‘fes’, EVERY_APPEND, EVERY_MAP] >> gvs[EVERY_MEM, FORALL_PROD]) >>
  ‘∀ev. MEM ev pevs ∧ ev_on «sys_poll» lfd ev ⇒ ∃c. MEM c [fes] ∧ MEM lfd (MAP FST c)’
    by metis_tac[l1_polls_fds] >>
  drule l1_flush_names >> strip_tac >>
  drule pf_fetch_names >> strip_tac >>
  drule l1_reap_names >> strip_tac >>
  drule settle_fds_names >> strip_tac >>
  simp[EVERY_MEM] >> rpt strip_tac >> imp_res_tac ev_on_name >>
  TRY (gvs[EVERY_MEM] >> res_tac >> gvs[] >> NO_TAC) >>
  qpat_x_assum ‘∀ev. MEM ev pevs ∧ _ ⇒ _’ drule_all >> strip_tac >> gvs[]
QED

Theorem eround_paused:
  eround lfd pol hs (w, es) acts = SOME (snap, (w', es'), log, evs) ∧
  eok lfd w es ∧ linv lfd w ∧ noob lfd es.p.b ∧ 0 < es.p.pause ⇒
  ¬EXISTS (ev_on «sys_poll» lfd) evs
Proof
  simp[eround_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  PairCases_on ‘ws1’ >> PairCases_on ‘ws2’ >>
  rename1 ‘eacts _ _ _ _ = SOME (rs, aevs, (w1, es1))’ >>
  rename1 ‘etail _ _ _ _ = SOME (rdy, (w2, es2), log, tevs)’ >>
  drule_all eacts_lfd >> strip_tac >>
  drule_all eacts_eok >> strip_tac >>
  drule_all eacts_noob >> strip_tac >>
  ‘¬EXISTS (ev_on «sys_poll» lfd) tevs’ by (irule etail_paused >> simp[] >> metis_tac[]) >>
  ‘EVERY (λev. ev_name ev = ExtCall «sys_shutdown») shevs’
    by (qpat_x_assum ‘eshuts _ = _’ mp_tac >> simp[eshuts_def] >> strip_tac >>
        pairarg_tac >> gvs[] >> drule pf_shuts_world >> simp[]) >>
  qpat_x_assum ‘¬EXISTS _ tevs’ mp_tac >>
  qpat_x_assum ‘EVERY _ shevs’ mp_tac >>
  qpat_x_assum ‘EVERY _ aevs’ mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp[EVERY_MEM, EXISTS_MEM] >> rpt strip_tac >> gvs[] >>
  imp_res_tac ev_on_name >> res_tac >> gvs[]
QED
