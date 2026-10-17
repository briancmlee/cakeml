(*
  PROVISIONAL Q-17.  The proxy's buffering bound on the raw trace, with
  option (A) of Q-17: pos_excuse (hard error or timeout) in both bound
  conjuncts, for K = pf_sendwait.  Pending the user's ruling on Q-17; the
  step-9 statement file (moonshot-step9/l0/proxyL0Stmts) is NOT changed.

  The accounting (D39), per direction p → q, at a prefix between E1
  rounds n and n + 1:
    raw read on p  ≤ HL read on p's handle by round n + 1 + L1's inbox of p
    raw sent on q  = HL written to q's handle by round n − L1's outbox of q
                     (while L1 has not dropped q's fd: else the excuse)
  This file: the E1-level accounting lemmas.
*)
Theory proxyBound
Ancestors
  proxySafeRun honestL1EPRefine honestL1EPOut honestL1PFRefine e1TraceLag e1TraceChan e1TraceRead
  moonshotSentGlue moonshotClientSpec l0sysEpisodes alist
Libs
  preamble

(* L-B: what L1 holds in a fd's outbox is exactly what the program wrote on
   its handle and the raw trace has not sent, while the fd is not gone *)
Theorem e1_sent_outbox:
  e1run_ok lfd a pol ifds m w0 calls ∧
  erounds lfd pol ifds m (w0, einit) n = SOME (h, ws, evs, logs) ∧
  ALOOKUP (ehbinds lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) n) j = SOME c ∧
  ALOOKUP (SND ws).p.b.tbl c = SOME f ∧ ¬MEM f (SND ws).p.b.gone ⇒
  l0_ep_sent j evs ++ outbox_of (SND ws).p.b f =
  hl_sent c (hl_pairs m (ehhist lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) n))
Proof
  strip_tac >>
  qabbrev_tac ‘W0 = pew lfd a pol ifds m w0 calls’ >>
  qabbrev_tac ‘lv = elv lfd pol ifds m w0’ >>
  ‘W0.chans = [] ∧ W0.open_fds = [] ∧ alloc_ok W0.alloc ∧ LENGTH W0.listening ≤ 1 ∧
   EVERY (λ(l, a, q). q = []) W0.listening ∧
   ∀n. ehacts lfd lv n 0 (ehst lfd lv ifds m W0 n)
         (new_actions (log_of m) (ehhist lfd lv ifds m W0 n)) ≠ NONE’
    by (irule e1run_ok_ehrounds >> simp[Abbr ‘W0’, Abbr ‘lv’] >> metis_tac[]) >>
  drule_all ehrounds_gchinv >> disch_then (qspec_then ‘n’ assume_tac) >>
  qpat_x_assum ‘e1run_ok _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [e1run_ok_def]) >>
  ‘∀j. l0_ep_sent j evs = ersent lfd pol ifds m w0 j n’
    by (drule_all l0_ep_sent_run >> strip_tac >> first_assum ACCEPT_TAC) >>
  qspecl_then [‘w0’, ‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘n’, ‘a’, ‘calls’] mp_tac
    (Q.GENL [‘w0’, ‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘N’, ‘a’, ‘calls’] l1ep_refines_ehl_upto_sent) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  disch_then (qspecl_then [‘n’, ‘h’, ‘ws’, ‘evs’, ‘logs’] mp_tac) >>
  impl_tac >- (simp[] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘Abbrev (W0 = _)’ (fn th => REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] (GSYM th)] >> assume_tac th) >>
  qpat_x_assum ‘Abbrev (lv = _)’ (fn th => REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] (GSYM th)] >> assume_tac th) >>
  strip_tac >>
  Cases_on ‘ehst lfd lv ifds m W0 n’ >> rename1 ‘_ = (w, hs)’ >>
  qpat_x_assum ‘ehst _ _ _ _ _ _ = _’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th, FST, SND])) >>
  qabbrev_tac ‘cm = FST (ecm lfd pol ifds m w0 n)’ >>
  qabbrev_tac ‘es = SND ws’ >>
  qabbrev_tac ‘B = ehbinds lfd lv ifds m W0 n’ >>
  qabbrev_tac ‘ps = hl_pairs m (ehhist lfd lv ifds m W0 n)’ >>
  ‘ALOOKUP hs.tbl c = SOME f’
    by (qpat_x_assum ‘ehs_rel _ _’ mp_tac >> rewrite_tac[ehs_rel_def] >> strip_tac >>
        asm_rewrite_tac[] >> simp[]) >>
  drule_all ev_rel_tbl >> strip_tac >>
  ‘MEM (j, c) B ∧ j < LENGTH w.chans ∧ (EL j w.chans).sent = hl_sent c ps’
    by (qpat_x_assum ‘gchinv _ _ _ _’ mp_tac >> rewrite_tac[gchinv_def] >> strip_tac >>
        ‘MEM (j, c) B’ by (irule ALOOKUP_MEM >> first_assum ACCEPT_TAC) >>
        ‘j < LENGTH w.chans’ by (qpat_x_assum ‘∀j hd. MEM (j, hd) B ⇒ _’ drule >> simp[]) >>
        qpat_x_assum ‘∀j. j < LENGTH w.chans ⇒ _.sent = _’ (qspec_then ‘j’ mp_tac) >>
        asm_rewrite_tac[] >> simp[]) >>
  ‘j = cl cm f’
    by (qpat_x_assum ‘gchinv _ _ _ _’ mp_tac >> rewrite_tac[gchinv_def] >> strip_tac >>
        qpat_x_assum ‘∀hd f. ALOOKUP hs.tbl hd = SOME f ⇒ _’ drule >> strip_tac >>
        ‘j' = cl cm f’ by (qpat_x_assum ‘ALOOKUP w.open_fds f = SOME (cl cm f)’ mp_tac >> simp[]) >>
        qpat_x_assum ‘j' = cl cm f’ (SUBST1_TAC o SYM) >>
        qpat_x_assum ‘MEM (j', c) B’ mp_tac >> qpat_x_assum ‘MEM (j, c) B’ mp_tac >>
        qpat_x_assum ‘ALL_DISTINCT (MAP SND B)’ mp_tac >> rpt (pop_assum kall_tac) >>
        metis_tac[ALL_DISTINCT_SND_MEM]) >>
  ‘ALOOKUP cm f = SOME j’
    by (qpat_x_assum ‘j = cl cm f’ SUBST1_TAC >> qpat_x_assum ‘MEM f (MAP FST cm)’ mp_tac >>
        rewrite_tac[cl_def] >> Cases_on ‘ALOOKUP cm f’ >> simp[] >>
        pop_assum mp_tac >> simp[ALOOKUP_NONE]) >>
  qpat_x_assum ‘sent_inv _ _ _ _’ mp_tac >> rewrite_tac[sent_inv_def] >> strip_tac >>
  first_x_assum (qspec_then ‘j’ mp_tac) >> impl_tac >- first_assum ACCEPT_TAC >>
  strip_tac >> first_x_assum (qspec_then ‘f’ mp_tac) >>
  impl_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >> disj1_tac >>
      rewrite_tac[live_def, held_def, MEM_MAP] >> disj1_tac >> disj1_tac >>
      qexists_tac ‘(c, f)’ >> simp[] >> irule ALOOKUP_MEM >> first_assum ACCEPT_TAC) >>
  rewrite_tac[oacct_def] >> strip_tac >>
  qpat_x_assum ‘¬MEM f _ ⇒ _’ (fn th => qpat_x_assum ‘¬MEM f _’ (mp_tac o MATCH_MP th)) >>
  qpat_x_assum ‘w.chans❲j❳.sent = _’ SUBST1_TAC >>
  qpat_x_assum ‘ehhist _ _ _ _ _ _ = h’ (SUBST1_TAC o SYM) >>
  simp[Abbr ‘ps’]
QED

(* ------------------------------------------------------------------------
   L-A: L1's inbox of a fd never holds more than one recv, pf_chunk bytes
   (it is filled only by a fetch, one recv of at most pf_chunk, and the
   program's reads only shorten it)
   ------------------------------------------------------------------------ *)

(* The world's rely is kept by a round (on the trace: no L1 invariant) *)
Theorem pdo_rely:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ l0_rely w ⇒ l0_rely w'
Proof
  Cases_on ‘a’
  >- (simp[honestL1PFModelTheory.pdo_def, AllCaseEqs()] >> rw[] >> gvs[])
  >- (simp[honestL1PFModelTheory.pdo_def, AllCaseEqs(), PULL_EXISTS] >> rw[] >> gvs[] >>
      rename1 ‘l1_close _ _ = SOME z’ >> PairCases_on ‘z’ >> gvs[] >>
      drule_all l1_close_l0 >> simp[])
  >> metis_tac[pdo_write_ostep]
QED

Theorem edo_rely:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ l0_rely w ⇒ l0_rely w'
Proof
  Cases_on ‘a’ >> simp[honestL1EPModelTheory.edo_def, AllCaseEqs(), PULL_EXISTS] >>
  rw[] >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  FIRST [gvs[honestL1EPModelTheory.sys_connect_def] >> drule_all l0_do_rely >> simp[] >> NO_TAC,
         drule_all l1_close_l0 >> simp[] >> NO_TAC,
         drule_all pdo_rely >> simp[]]
QED

Theorem eacts_rely:
  ∀acts w es rs evs w' es'.
    eacts lfd pol (w, es) acts = SOME (rs, evs, (w', es')) ∧ l0_rely w ⇒ l0_rely w'
Proof
  Induct >> simp[honestL1EPModelTheory.eacts_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >> PairCases_on ‘ws1’ >> drule_all edo_rely >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem etail_rely:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, evs) ∧ l0_rely w ⇒ l0_rely w'
Proof
  simp[honestL1EPModelTheory.etail_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  drule_all l1_polls_l0 >> strip_tac >> drule_all l1_flush_l0 >> strip_tac >>
  drule_all pf_fetch_quiet >> strip_tac >> drule_all l1_reap_l0 >> strip_tac >>
  drule_all settle_fds_quiet >> strip_tac >> gvs[]
QED

Definition inb_ok_def:
  inb_ok (ps : l1p) ⇔ ∀f bs. MEM (f, bs) ps.inb ⇒ LENGTH bs ≤ pf_chunk
End

Theorem inb_ok_inb_of:
  inb_ok ps ⇒ LENGTH (inb_of ps f) ≤ pf_chunk
Proof
  rw[inb_ok_def, honestL1PFModelTheory.inb_of_def] >> Cases_on ‘ALOOKUP ps.inb f’ >> simp[] >>
  first_x_assum irule >> qexists_tac ‘f’ >> irule ALOOKUP_MEM >> simp[]
QED

Theorem inb_ok_set_inb:
  inb_ok ps ∧ LENGTH bs ≤ pf_chunk ⇒ inb_ok (set_inb f bs ps)
Proof
  rw[inb_ok_def, honestL1PFModelTheory.set_inb_def, ADELKEY_def, MEM_FILTER] >> metis_tac[]
QED

Theorem pdo_inb:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ inb_ok ps ⇒ inb_ok ps'
Proof
  Cases_on ‘a’ >> simp[honestL1PFModelTheory.pdo_def, AllCaseEqs(), PULL_EXISTS] >>
  rw[] >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  TRY (irule inb_ok_set_inb >> conj_tac >- first_assum ACCEPT_TAC >>
       drule inb_ok_inb_of >> disch_then (qspec_then ‘f’ mp_tac) >> simp[] >> NO_TAC) >>
  fs[inb_ok_def] >> metis_tac[]
QED

Theorem edo_inb:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ inb_ok es.p ⇒ inb_ok es'.p
Proof
  Cases_on ‘a’ >> simp[honestL1EPModelTheory.edo_def, AllCaseEqs(), PULL_EXISTS] >>
  rw[] >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  TRY (drule_all pdo_inb >> simp[] >> NO_TAC) >>
  fs[inb_ok_def, honestL1EPModelTheory.ec_del_def] >> metis_tac[]
QED

Theorem eacts_inb:
  ∀acts w es rs evs w' es'.
    eacts lfd pol (w, es) acts = SOME (rs, evs, (w', es')) ∧ inb_ok es.p ⇒ inb_ok es'.p
Proof
  Induct >> simp[honestL1EPModelTheory.eacts_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >> PairCases_on ‘ws1’ >> drule_all edo_inb >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem pf_fetch_inb:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ l0_rely w ∧ inb_ok ps ⇒ inb_ok ps'
Proof
  Induct >- simp[honestL1PFModelTheory.pf_fetch_def] >>
  rpt gen_tac >> rename1 ‘pf_fetch _ _ (g :: fs)’ >> strip_tac >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ mp_tac >>
  simp[Once honestL1PFModelTheory.pf_fetch_def] >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  IF_CASES_TAC
  >- (Cases_on ‘sys_accept lfd w’ >> simp[] >> rename1 ‘_ = SOME x’ >>
      PairCases_on ‘x’ >> rename1 ‘sys_accept _ _ = SOME (out, w1, ev)’ >> simp[] >>
      pairarg_tac >> simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >> gvs[] >>
      ‘l0_rely w1’ by (gvs[honestL1ModelTheory.sys_accept_def] >> metis_tac[l0_do_rely]) >>
      first_x_assum (drule_then irule) >> simp[] >>
      Cases_on ‘l0_res_of out’ >> gvs[] >> rw[] >> fs[inb_ok_def] >> metis_tac[]) >>
  Cases_on ‘sys_recv g pf_chunk w’ >> simp[] >> rename1 ‘_ = SOME x’ >>
  PairCases_on ‘x’ >> rename1 ‘sys_recv _ _ _ = SOME (out, w1, ev)’ >> simp[] >>
  pairarg_tac >> simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >> gvs[] >>
  ‘l0_rely w1’ by (gvs[honestL1ModelTheory.sys_recv_def] >> metis_tac[l0_do_rely]) >>
  ‘LENGTH out = pf_chunk + 13’ by (drule_all honestL1PFStreamTheory.sys_recv_len >> simp[]) >>
  first_x_assum (drule_then irule) >> simp[] >>
  Cases_on ‘l0_res_of out’ >> gvs[] >> qpat_x_assum ‘_ = (ps1, _)’ mp_tac >> rw[] >>
  TRY (fs[inb_ok_def] >> metis_tac[] >> NO_TAC) >>
  irule inb_ok_set_inb >> simp[LENGTH_TAKE_EQ]
QED

Theorem etail_inb:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, evs) ∧ l0_rely w ∧ inb_ok es.p ⇒
  inb_ok es'.p
Proof
  simp[honestL1EPModelTheory.etail_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  drule_all l1_polls_l0 >> strip_tac >> drule_all l1_flush_l0 >> strip_tac >>
  ‘inb_ok ps3'’
    by (drule pf_fetch_inb >> impl_tac >- (fs[inb_ok_def] >> metis_tac[]) >> simp[]) >>
  drule_all pf_fetch_quiet >> strip_tac >> drule_all l1_reap_l0 >> strip_tac >>
  drule_all settle_fds_quiet >> strip_tac >>
  qpat_x_assum ‘_ = es'’ (SUBST1_TAC o SYM) >>
  pop_assum mp_tac >> pop_assum mp_tac >> pop_assum mp_tac >>
  qpat_x_assum ‘inb_ok ps3'’ mp_tac >>
  simp[inb_ok_def, honestL1EPModelTheory.promote_def, honestL1PFModelTheory.stall_step_def] >>
  strip_tac >> rpt (disch_then kall_tac) >>
  qpat_x_assum ‘∀f bs. MEM (f, bs) ps3'.inb ⇒ _’ mp_tac >> rpt (pop_assum kall_tac) >> metis_tac[]
QED

Theorem eround_inb:
  eround lfd pol hs (w, es) acts = SOME (snap, (w', es'), log, evs) ∧ l0_rely w ∧ inb_ok es.p ⇒
  l0_rely w' ∧ inb_ok es'.p
Proof
  simp[honestL1EPModelTheory.eround_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  PairCases_on ‘ws1’ >>
  drule_all eacts_rely >> strip_tac >> drule_all eacts_inb >> strip_tac >>
  drule_all etail_rely >> drule_all etail_inb >> simp[]
QED

Theorem erounds_inb:
  l0_rely w0 ⇒
  ∀n h ws evs logs. erounds lfd pol ifds m (w0, einit) n = SOME (h, ws, evs, logs) ⇒
    l0_rely (FST ws) ∧ inb_ok (SND ws).p
Proof
  strip_tac >> Induct
  >- simp[honestL1EPModelTheory.erounds_def, honestL1EPModelTheory.einit_def,
          honestL1PFModelTheory.pinit_def, inb_ok_def] >>
  simp[honestL1EPModelTheory.erounds_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  rename1 ‘eround _ _ _ ws0 _ = SOME (_, ws1, _, _)’ >>
  PairCases_on ‘ws0’ >> PairCases_on ‘ws1’ >> gvs[] >>
  drule_all eround_inb >> simp[]
QED
