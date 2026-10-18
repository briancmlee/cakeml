(*
  E1's round seen from the listener (task D, r3-close): the EP analogues of
  honestL1PFConn.pround_queue / pround_lfd and honestL1PFConnRun's
  pround_paused / noob, for eround (eacts, etail, eshuts).  The world-level
  lemmas are PF's; new here are E1's own calls (sys_connect, sys_connerr,
  sys_shutdown), edo, settle_fds and pf_shuts.

  Invariants: OwnRun's eown0 / l0owne (no noclose), e1-progress's ewinv.
*)
Theory honestL1EPConnRound
Ancestors
  honestL1EPOwnRun e1RoundFlush e1RoundActs e1RoundInv e1RoundTail
  honestL1EPBund honestL1EPTotal honestL1EPRefine honestL1EPModel
  honestL1PFConnRun honestL1PFConn honestL1PFClient honestL1PFClose honestL1PFInv honestL1PFRefine
  honestL1PFRound honestL1PFModel honestL1Inv honestL1Steps honestL1Model
  honestL0WorldInv honestL0WorldProps honestL0Rely honestL0World honestL0
Libs
  preamble

(* ------------------------------------------------------------------------
   The listener's queue: E1's own calls only append to it
   ------------------------------------------------------------------------ *)

Theorem qof_connect:
  l0_connect p w = (r, v, w') ⇒ qof w' l = qof w l
Proof
  rw[l0_connect_def, AllCaseEqs()] >> simp[qof_def, upd_lchan_def]
QED

Theorem qof_do_connect:
  l0_do «sys_connect» conf alen w = SOME (out, w', ev) ⇒ ∃t. qof w' l = qof w l ++ t
Proof
  strip_tac >> drule l0_do_cases >> strip_tac >> gvs[] >>
  qspecl_then [‘w’] strip_assume_tac
    (Q.GEN ‘w’ (Q.SPECL [‘l’, ‘«sys_connect»’] (Q.GENL [‘l’, ‘nm’] qof_tick))) >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >>
  simp[l0_call_def] >> rw[AllCaseEqs()] >>
  rename1 ‘l0_connect pp tw = _’ >>
  qmatch_asmsub_abbrev_tac ‘l0_connect pp tw = (_, _, w2)’ >>
  ‘qof w2 l = qof tw l’ by metis_tac[qof_connect] >> simp[]
QED

Theorem sys_qof_e:
  (sys_connect p w = SOME (out, w', ev) ⇒ ∃t. qof w' l = qof w l ++ t) ∧
  (sys_connerr g w = SOME (out, w', ev) ⇒ ∃t. qof w' l = qof w l ++ t) ∧
  (sys_shutdown g w = SOME (out, w', ev) ⇒ ∃t. qof w' l = qof w l ++ t)
Proof
  rw[sys_connect_def, sys_connerr_def, sys_shutdown_def]
  >- (drule qof_do_connect >> simp[])
  >> drule_at (Pos last) qof_do >> simp[]
QED

Theorem edo_qof:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ eown0 lfd es ∧ l0_rely w ∧ fds_lt w ∧
  MEM lfd (l0_used w) ⇒
  ∃t. qof w' lfd = qof w lfd ++ t
Proof
  strip_tac >> ‘pown lfd es.p’ by fs[eown0_def] >>
  Cases_on ‘a’ >> qpat_x_assum ‘edo _ _ _ _ = _’ mp_tac >> simp[edo_def] >>
  rw[AllCaseEqs()] >> gvs[] >>
  TRY (qexists_tac ‘[]’ >> simp[] >> NO_TAC) >>
  TRY (PairCases_on ‘z’ >> gvs[] >> drule_all pdo_qof >> simp[] >> NO_TAC) >>
  TRY (drule (cj 1 sys_qof_e) >> simp[] >> NO_TAC) >>
  (* a connect's socket, closed at once *)
  TRY (PairCases_on ‘z’ >> gvs[] >>
       drule_all sys_connect_l0 >> strip_tac >>
       ‘n2w (res_val out) ≠ lfd’ by (strip_tac >> gvs[]) >>
       drule (cj 1 sys_qof_e) >> disch_then (qspec_then ‘lfd’ strip_assume_tac) >>
       drule_all (cj 2 sys_qof) >> strip_tac >> simp[] >> NO_TAC) >>
  (* a close of a connect handle's fd, or of a PF handle's *)
  TRY (gvs[pf_close_def, AllCaseEqs()] >> TRY (qexists_tac ‘[]’ >> simp[] >> NO_TAC)) >>
  TRY (rename1 ‘l1_close _ _ = SOME zz’ >> PairCases_on ‘zz’ >> gvs[]) >>
  rename1 ‘l1_close f _ = _’ >>
  ‘f ≠ lfd’
    by (imp_res_tac ALOOKUP_MEM >> strip_tac >> gvs[eown0_def, pown_def, MEM_MAP] >>
        metis_tac[SND]) >>
  drule_all l1_close_qof >> simp[]
QED

(* ------------------------------------------------------------------------
   The fetch and the queue, under ewinv (E1 runs have connecting channels,
   so not winv): honestL1PFConn's sys_accept_queue / pf_fetch_queue
   ------------------------------------------------------------------------ *)

Theorem sys_accept_queue_e:
  ewinv w ∧ sys_accept l w = SOME (out, w', ev) ⇒
  ∃t. (qof w' l = qof w l ++ t ∧ ∀k. l0_res_of out ≠ Ok k) ∨
      ∃j q'. qof w l ++ t = j :: q' ∧ qof w' l = q' ∧
             ((∃k. l0_res_of out = Ok k ∧ ALOOKUP w'.open_fds (n2w k) = SOME j) ∨
              ((∀k. l0_res_of out ≠ Ok k) ∧
               j < LENGTH w'.chans ∧ (EL j w'.chans).broken))
Proof
  rw[sys_accept_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  drule qof_call_accept >> simp[] >> strip_tac >> gvs[] >>
  qspecl_then [‘w’] strip_assume_tac (Q.GEN ‘w’ (Q.SPECL [‘l’, ‘«sys_accept»’] (Q.GENL [‘l’, ‘nm’] qof_tick))) >>
  ‘l0_rely (l0_tick «sys_accept» w)’
    by (gvs[ewinv_def] >> irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  drule_all l0_accept_res >> strip_tac >>
  ‘l0_res_of (enc_res r) = r’ by (irule l0_res_of_enc >> simp[]) >>
  drule accept_chans_len >> strip_tac >>
  ‘l0wf (l0_tick «sys_accept» w)’ by gvs[ewinv_def, l0wf_tick] >>
  drule accept_queue >> strip_tac >> qexists_tac ‘t’ >> gvs[] >>
  ‘j < LENGTH (l0_tick «sys_accept» w).chans’
    by (‘MEM j (qof (l0_tick «sys_accept» w) l)’
          by (qpat_x_assum ‘qof (l0_tick _ _) _ = _’ SUBST1_TAC >>
              qpat_x_assum ‘_ :: _ = _’ (SUBST1_TAC o SYM) >> simp[]) >>
        metis_tac[qof_lt]) >>
  disj2_tac >> qexists_tac ‘j’ >> gvs[] >>
  TRY (qexists_tac ‘w2n k’ >> simp[] >> NO_TAC)
QED

Theorem sys_wmono_e:
  (ewinv w ∧ sys_accept g w = SOME (out, w', ev) ⇒ wmono w w') ∧
  (sys_connerr g w = SOME (out, w', ev) ⇒ wmono w w') ∧
  (sys_shutdown g w = SOME (out, w', ev) ⇒ wmono w w')
Proof
  rpt conj_tac >> strip_tac
  >- (gvs[sys_accept_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
      gvs[l0_call_def] >> pairarg_tac >> gvs[] >>
      ‘fds_lt (l0_tick «sys_accept» w) ∧ l0_rely (l0_tick «sys_accept» w)’
        by (gvs[ewinv_def] >> irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
      drule_at (Pos last) wmono_accept >> gvs[l0_rely_def] >> strip_tac >>
      metis_tac[wmono_trans, wmono_tick])
  >- (gvs[sys_connerr_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
      gvs[l0_call_def, AllCaseEqs()] >>
      gvs[l0_connerr_def, AllCaseEqs()] >>
      TRY (irule wmono_trans >> qexists_tac ‘l0_tick «sys_connerr» w’ >>
           simp[wmono_tick] >> irule wmono_upd >> simp[] >> NO_TAC) >>
      simp[wmono_tick])
  >> gvs[sys_shutdown_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  gvs[l0_call_def] >> pairarg_tac >> gvs[] >>
  irule wmono_trans >> qexists_tac ‘l0_tick «sys_shutdown» w’ >> simp[wmono_tick] >>
  gvs[l0_shutdown_def, AllCaseEqs()] >>
  TRY (irule wmono_upd >> simp[] >> NO_TAC) >> simp[]
QED

Theorem pf_fetch_queue_e:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ ewinv w ⇒
    wmono w w' ∧
    ∃t k. k ≤ LENGTH t + LENGTH (qof w lfd) ∧ qof w' lfd = DROP k (qof w lfd ++ t) ∧
          (∀j. MEM j (TAKE k (qof w lfd ++ t)) ⇒ resolved w' log j) ∧
          LENGTH (log_conns log) ≤ k
Proof
  Induct >- (simp[pf_fetch_def] >> rpt strip_tac >> qexistsl_tac [‘[]’, ‘0’] >> simp[]) >>
  rpt gen_tac >> rename1 ‘g :: fs’ >> simp[Once pf_fetch_def] >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  IF_CASES_TAC
  >- (simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
      pairarg_tac >> gvs[] >>
      qpat_x_assum ‘option_CASE (pf_fetch _ _ _ _) _ _ = _’
        (strip_assume_tac o SIMP_RULE (srw_ss()) [AllCaseEqs()]) >> gvs[] >>
      ‘ewinv w1 ∧ wmono w w1’ by metis_tac[sys_ewinv, sys_wmono_e] >>
      first_x_assum drule_all >> strip_tac >>
      ‘wmono w w'’ by metis_tac[wmono_trans] >>
      qpat_x_assum ‘wmono w w'’ (fn th => REWRITE_TAC [th]) >>
      drule_all sys_accept_queue_e >> strip_tac
      >- (‘fl' = []’ by (Cases_on ‘l0_res_of out’ >> gvs[]) >>
          irule queue_app >> simp[] >> metis_tac[])
      >- (irule queue_pop >> gvs[] >>
          qexistsl_tac [‘j’, ‘k’, ‘t'’, ‘t’, ‘w1’] >> gvs[] >>
          simp[resolved_def] >> disj1_tac >> qexists_tac ‘n2w k'’ >> gvs[])
      >> ‘fl' = []’ by (Cases_on ‘l0_res_of out’ >> gvs[]) >>
      irule queue_pop >> gvs[] >>
      qexistsl_tac [‘j’, ‘k’, ‘t'’, ‘t’, ‘w1’] >> gvs[] >>
      simp[resolved_def])
  >> simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  pairarg_tac >> gvs[] >>
  qpat_x_assum ‘option_CASE (pf_fetch _ _ _ _) _ _ = _’
    (strip_assume_tac o SIMP_RULE (srw_ss()) [AllCaseEqs()]) >> gvs[] >>
  ‘ewinv w1 ∧ wmono w w1’ by metis_tac[sys_ewinv, sys_wmono] >>
  first_x_assum drule_all >> strip_tac >>
  ‘wmono w w'’ by metis_tac[wmono_trans] >>
  qpat_x_assum ‘wmono w w'’ (fn th => REWRITE_TAC [th]) >>
  drule (el 3 (CONJUNCTS sys_qof)) >> disch_then (qspec_then ‘lfd’ strip_assume_tac) >>
  ‘log_conns fl' = []’ by (Cases_on ‘l0_res_of out’ >> gvs[] >> every_case_tac >> gvs[]) >>
  irule queue_app >> simp[] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The run's invariants, per round
   ------------------------------------------------------------------------ *)

Definition eok_def:
  eok lfd w es ⇔ eown0 lfd es ∧ l0owne lfd w es ∧ ewinv w ∧ esmall lfd es
End

Theorem eok_facts:
  eok lfd w es ⇒ l0_rely w ∧ fds_lt w ∧ l0wf w ∧ MEM lfd (l0_used w) ∧ pown lfd es.p ∧
                 psmall lfd es.p
Proof
  simp[eok_def, ewinv_def, eown0_def, l0owne_def, l0own_def, esmall_def] >> metis_tac[]
QED

Theorem edo_ewinv:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ ewinv w ⇒ ewinv w'
Proof
  strip_tac >>
  Cases_on ‘a’ >> qpat_x_assum ‘edo _ _ _ _ = _’ mp_tac >> simp[edo_def] >>
  rw[AllCaseEqs()] >> gvs[] >>
  TRY (PairCases_on ‘z’ >> gvs[] >> drule_all pdo_ewinv >> simp[] >> NO_TAC) >>
  TRY (drule_all (cj 8 sys_ewinv) >> simp[] >> NO_TAC) >>
  TRY (PairCases_on ‘z’ >> gvs[] >> drule_all (cj 8 sys_ewinv) >> strip_tac >>
       drule_all (cj 1 sys_ewinv) >> simp[] >> NO_TAC) >>
  TRY (gvs[pf_close_def, AllCaseEqs()]) >>
  TRY (rename1 ‘l1_close _ _ = SOME zz’ >> PairCases_on ‘zz’ >> gvs[]) >>
  drule_all l1_close_ewinv >> simp[]
QED

Theorem edo_eok:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ eok lfd w es ⇒
  eok lfd w' es' ∧ ∃t. qof w' lfd = qof w lfd ++ t
Proof
  strip_tac >> drule_then strip_assume_tac eok_facts >>
  qpat_x_assum ‘eok _ _ _’ (strip_assume_tac o REWRITE_RULE [eok_def]) >>
  simp[eok_def] >> rpt conj_tac
  >- (drule_all edo_eown0 >> simp[])
  >- (drule_all edo_l0owne0 >> simp[])
  >- (drule_all edo_ewinv >> simp[])
  >- (drule_all edo_esmall >> simp[])
  >> drule_all edo_qof >> simp[]
QED

Theorem eacts_eok:
  ∀acts w es rs evs w' es'.
    eacts lfd pol (w, es) acts = SOME (rs, evs, (w', es')) ∧ eok lfd w es ⇒
    eok lfd w' es' ∧ ∃t. qof w' lfd = qof w lfd ++ t
Proof
  Induct >> simp[eacts_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  drule_all edo_eok >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> simp[]
QED

(* ------------------------------------------------------------------------
   The settling and the shutdowns: the queue only grows, the world is
   monotone
   ------------------------------------------------------------------------ *)

Theorem settle_fds_world:
  ∀fs w es w' es' evs.
    settle_fds fs (w, es) = SOME ((w', es'), evs) ⇒
    (∃t. qof w' l = qof w l ++ t) ∧ wmono w w' ∧ (ewinv w ⇒ ewinv w')
Proof
  Induct >> simp[settle_fds_def] >>
  rpt gen_tac >> simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 ‘sys_connerr _ _ = SOME (out, w1, ev)’ >>
  first_x_assum drule >> strip_tac >>
  drule (cj 2 sys_qof_e) >> disch_then (qspec_then ‘l’ strip_assume_tac) >>
  drule (cj 2 sys_wmono_e) >> strip_tac >>
  rpt conj_tac
  >- (qexists_tac ‘t' ++ t’ >> simp[])
  >- metis_tac[wmono_trans]
  >> metis_tac[sys_ewinv]
QED

Theorem pf_shuts_world:
  ∀fs w ps w' ps' kp sh evs.
    pf_shuts fs (w, ps) = SOME ((w', ps'), kp, sh, evs) ⇒
    (∃t. qof w' l = qof w l ++ t) ∧ wmono w w' ∧ (ewinv w ⇒ ewinv w') ∧
    EVERY (λev. ev_name ev = ExtCall «sys_shutdown») evs
Proof
  Induct >- (simp[pf_shuts_def] >> rpt strip_tac >> qexists_tac ‘[]’ >> simp[]) >>
  rpt gen_tac >> rename1 ‘kf :: fs’ >> PairCases_on ‘kf’ >> rename1 ‘(k, f) :: fs’ >>
  simp[Once pf_shuts_def] >>
  IF_CASES_TAC
  >- (strip_tac >> gvs[] >> PairCases_on ‘z’ >> gvs[] >> first_x_assum drule >> simp[]) >>
  IF_CASES_TAC
  >- (strip_tac >> gvs[] >> PairCases_on ‘z’ >> gvs[] >> first_x_assum drule >> simp[]) >>
  Cases_on ‘sys_shutdown f w’ >> simp[] >> rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >>
  rename1 ‘sys_shutdown _ _ = SOME (out, w1, ev)’ >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >> PairCases_on ‘z’ >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  drule (cj 3 sys_qof_e) >> disch_then (qspec_then ‘l’ strip_assume_tac) >>
  drule (cj 3 sys_wmono_e) >> strip_tac >>
  rpt conj_tac
  >- (qexists_tac ‘t' ++ t’ >> simp[])
  >- metis_tac[wmono_trans]
  >- metis_tac[sys_ewinv]
  >> gvs[sys_shutdown_def] >> drule l0_do_cases >> rw[] >> simp[ev_name_def]
QED

(* honestL1PFClient.pf_fetch_conns, under ewinv *)
Theorem pf_fetch_conns_e:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ ewinv w ∧ MEM f (l0_used w) ⇒
    ¬MEM f (log_conns log)
Proof
  Induct >- simp[pf_fetch_def] >> rpt gen_tac >>
  simp[Once pf_fetch_def] >> rw[] >> gvs[AllCaseEqs()] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘SOME (out, w1, ev)’ >>
  ‘ewinv w1’ by metis_tac[sys_ewinv] >>
  ‘MEM f (l0_used w1)’
    by (gvs[sys_accept_def, sys_recv_def] >> drule l0_do_used >> simp[]) >>
  first_x_assum drule_all >> simp[] >>
  ‘l0_rely w ∧ fds_lt w’ by fs[ewinv_def] >>
  ‘¬MEM (n2w k) (l0_used w)’ by (irule sys_accept_fresh >> metis_tac[]) >>
  strip_tac >> strip_tac >> gvs[]
QED

(* ------------------------------------------------------------------------
   The tail and the listener's queue (pround_queue's argument)
   ------------------------------------------------------------------------ *)

Theorem etail_queue:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, tevs) ∧ eok lfd w es ⇒
  ∃t k. k ≤ LENGTH t + LENGTH (qof w lfd) ∧ qof w' lfd = DROP k (qof w lfd ++ t) ∧
        (∀j. MEM j (TAKE k (qof w lfd ++ t)) ⇒ resolved w' log j) ∧
        LENGTH (log_conns log) ≤ k
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
  drule l1_polls_qof >> disch_then (qspec_then ‘lfd’ (qx_choose_then ‘t2’ assume_tac)) >>
  ‘ewinv w1’ by (drule_all l1_polls_ewinv >> simp[]) >>
  drule_all l1_polls_l0 >> strip_tac >>
  drule l1_flush_qof >> disch_then (qspec_then ‘lfd’ (qx_choose_then ‘t3’ assume_tac)) >>
  ‘ewinv w2’ by (drule_all l1_flush_ewinv >> simp[]) >>
  ‘l0_rely w1’ by gvs[ewinv_def] >>
  drule_all l1_flush_l0 >> strip_tac >>
  drule_all pf_fetch_queue_e >> strip_tac >>
  drule pf_fetch_closing >> strip_tac >>
  ‘ewinv w3’ by (drule_all pf_fetch_ewinv >> simp[]) >>
  qabbrev_tac ‘ps3 = stall_step (pf_held ps3f) (outbox_of es.p.b) log ps3f’ >>
  ‘ps3f.b.closing = ps3.b.closing’ by simp[Abbr ‘ps3’] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  ‘ps3.b.closing = es.p.b.closing’ by gvs[] >>
  ‘∀g. MEM (FConn g) log ⇒ ¬MEM g ps3.b.closing’
    by (rpt strip_tac >>
        ‘MEM g (l0_used w2)’ by gvs[l0owne_def, l0own_def] >>
        drule_all pf_fetch_conns_e >>
        simp[log_conns_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
        qexists_tac ‘FConn g’ >> simp[]) >>
  ‘¬MEM lfd ps3.b.closing’ by gvs[pown_def, ALL_DISTINCT_APPEND] >>
  drule_all l1_reap_qof >> disch_then (qx_choose_then ‘t5’ assume_tac) >>
  drule l1_reap_wkeep >> strip_tac >>
  drule settle_fds_world >> disch_then (qspec_then ‘lfd’ strip_assume_tac) >>
  rename1 ‘qof w5 lfd = qof w4 lfd ++ t6’ >>
  qexistsl_tac [‘t2 ++ t3 ++ t ++ t5 ++ t6’, ‘k’] >> gvs[] >>
  ‘k ≤ LENGTH (qof w lfd ++ t2 ++ t3 ++ t)’ by simp[] >>
  simp[DROP_APPEND1, TAKE_APPEND1] >>
  rpt strip_tac >> irule resolved_mono >> qexistsl_tac [‘log’, ‘w4’] >> simp[] >>
  irule resolved_keep >> simp[] >>
  qexistsl_tac [‘ps3.b.closing’, ‘w3’] >> simp[]
QED

Theorem etail_ewinv:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, tevs) ∧ ewinv w ⇒ ewinv w'
Proof
  simp[etail_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘l1_polls _ w = SOME (rv, w1, pevs)’ >>
  rename1 ‘l1_flush _ _ = SOME ((w2, b2), fevs)’ >>
  rename1 ‘pf_fetch _ _ _ _ = SOME ((w3, ps3f), log, gevs)’ >>
  rename1 ‘l1_reap _ _ = SOME ((w4, b4), cevs)’ >>
  ‘ewinv w1’ by (drule_all l1_polls_ewinv >> simp[]) >>
  ‘ewinv w2’ by (drule_all l1_flush_ewinv >> simp[]) >>
  ‘ewinv w3’ by (drule_all pf_fetch_ewinv >> simp[]) >>
  ‘ewinv w4’ by (drule_all l1_reap_ewinv >> simp[]) >>
  drule settle_fds_world >> simp[]
QED

Theorem etail_eok:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, tevs) ∧ eok lfd w es ⇒
  eok lfd w' es'
Proof
  strip_tac >> drule_then strip_assume_tac eok_facts >>
  qpat_x_assum ‘eok _ _ _’ (strip_assume_tac o REWRITE_RULE [eok_def]) >>
  ‘esmall lfd es'’
    by (‘∃rdy1 w1 es1 log1 evs1.
           etail lfd pol hs (w, es) = SOME (rdy1, (w1, es1), log1, evs1) ∧ esmall lfd es1’
          by metis_tac[etail_ok] >> gvs[]) >>
  drule_all etail_ewinv >> strip_tac >>
  drule_all etail_eown0 >> strip_tac >>
  simp[eok_def]
QED

Theorem eshuts_eok:
  eshuts (w, es) = SOME ((w', es'), evs) ∧ eok lfd w es ⇒
  eok lfd w' es' ∧ (∃t. qof w' l = qof w l ++ t) ∧ wmono w w'
Proof
  strip_tac >> drule_then strip_assume_tac eok_facts >>
  qpat_x_assum ‘eok _ _ _’ (strip_assume_tac o REWRITE_RULE [eok_def]) >>
  drule_all eshuts_eown0 >> strip_tac >>
  qpat_x_assum ‘eshuts _ = _’ mp_tac >> simp[eshuts_def] >> strip_tac >>
  pairarg_tac >> gvs[] >>
  rename1 ‘pf_shuts qs _ = SOME ((w', ps'), kp, sh, evs)’ >>
  drule pf_shuts_world >> disch_then (qspec_then ‘l’ strip_assume_tac) >> gvs[] >>
  qspecl_then [‘lfd’, ‘qs’, ‘w’, ‘es.p’] mp_tac (GEN_ALL pf_shuts_ok) >>
  simp[] >> strip_tac >> gvs[] >>
  gvs[eok_def, esmall_def] >> metis_tac[]
QED

Theorem eround_queue:
  eround lfd pol hs (w, es) acts = SOME (snap, (w', es'), log, evs) ∧ eok lfd w es ⇒
  eok lfd w' es' ∧
  ∃t k. k ≤ LENGTH t + LENGTH (qof w lfd) ∧ qof w' lfd = DROP k (qof w lfd ++ t) ∧
        (∀j. MEM j (TAKE k (qof w lfd ++ t)) ⇒ resolved w' log j) ∧
        LENGTH (log_conns log) ≤ k
Proof
  simp[eround_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  PairCases_on ‘ws1’ >> PairCases_on ‘ws2’ >>
  rename1 ‘eacts _ _ _ _ = SOME (rs, aevs, (w1, es1))’ >>
  rename1 ‘etail _ _ _ _ = SOME (rdy, (w2, es2), log, tevs)’ >>
  drule_all eacts_eok >> strip_tac >>
  rename1 ‘qof w1 lfd = qof w lfd ++ t1’ >>
  drule_all etail_queue >> strip_tac >>
  drule_all etail_eok >> strip_tac >>
  drule_all eshuts_eok >> disch_then (qspec_then ‘lfd’ strip_assume_tac) >>
  rename1 ‘qof w' lfd = qof w2 lfd ++ t3’ >>
  simp[] >>
  qexistsl_tac [‘t1 ++ t ++ t3’, ‘k’] >> gvs[] >>
  ‘k ≤ LENGTH (qof w lfd ++ t1 ++ t)’ by simp[] >>
  simp[DROP_APPEND1, TAKE_APPEND1] >>
  rpt strip_tac >> irule resolved_mono >> qexistsl_tac [‘log’, ‘w2’] >> simp[] >>
  first_x_assum irule >> gvs[]
QED

(* ------------------------------------------------------------------------
   The listener stays a listener (honestL1PFConn's linv lemmas, under ewinv,
   and for E1's connects)
   ------------------------------------------------------------------------ *)

Theorem linv_connect:
  linv l w ∧ fds_lt w ∧ w.fd_limit ≤ 2 ** 31 ∧ l0_connect p w = (r, n, w') ⇒ linv l w'
Proof
  strip_tac >>
  gvs[l0_connect_def, AllCaseEqs(), fail_def, linv_def, l0_alloc_def] >>
  ‘¬MEM (lowest_fd w) (l0_used w)’ by (irule lowest_fd_free_lim >> gvs[fds_lt_def]) >>
  gvs[l0_used_def, upd_lchan_def] >> rw[] >> gvs[] >> strip_tac >> gvs[]
QED

Theorem linv_call_e:
  l0_call n conf bytes w = SOME (FFIreturn bytes' w') ∧
  ¬(n = «sys_close» ∧ bytes_fd conf = l) ∧ linv l w ∧ fds_lt w ∧ w.fd_limit ≤ 2 ** 31 ⇒
  linv l w'
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> imp_res_tac linv_ops >> imp_res_tac linv_connect >> gvs[] >>
  metis_tac[linv_ticks, linv_ops, linv_connect]
QED

Theorem linv_do_e:
  l0_do n conf alen w = SOME (out, w', ev) ∧
  ¬(n = «sys_close» ∧ bytes_fd conf = l) ∧ linv l w ∧ ewinv w ⇒ linv l w'
Proof
  strip_tac >> drule l0_do_cases >> strip_tac >> gvs[] >>
  drule linv_call_e >> simp[] >> disch_then irule >>
  gvs[ewinv_def, linv_tick, l0_rely_def]
QED

Theorem linv_do_buf_e:
  l0_do_buf n conf bs w = SOME (out, w', ev) ∧
  ¬(n = «sys_close» ∧ bytes_fd conf = l) ∧ linv l w ∧ ewinv w ⇒ linv l w'
Proof
  strip_tac >> drule l0_do_buf_cases >> strip_tac >> gvs[] >>
  drule linv_call_e >> simp[] >> disch_then irule >>
  gvs[ewinv_def, linv_tick, l0_rely_def]
QED

Theorem sys_linv_e:
  (linv l w ∧ ewinv w ∧ sys_send g bs w = SOME (out, w', ev) ⇒ linv l w') ∧
  (linv l w ∧ ewinv w ∧ g ≠ l ∧ sys_close g w = SOME (out, w', ev) ⇒ linv l w') ∧
  (linv l w ∧ ewinv w ∧ sys_recv g k w = SOME (out, w', ev) ⇒ linv l w') ∧
  (linv l w ∧ ewinv w ∧ sys_accept g w = SOME (out, w', ev) ⇒ linv l w') ∧
  (linv l w ∧ ewinv w ∧ sys_poll fes w = SOME (out, w', ev) ⇒ linv l w') ∧
  (linv l w ∧ ewinv w ∧ sys_connect p w = SOME (out, w', ev) ⇒ linv l w') ∧
  (linv l w ∧ ewinv w ∧ sys_connerr g w = SOME (out, w', ev) ⇒ linv l w') ∧
  (linv l w ∧ ewinv w ∧ sys_shutdown g w = SOME (out, w', ev) ⇒ linv l w')
Proof
  rw[sys_close_def, sys_send_def, sys_recv_def, sys_accept_def, sys_poll_def,
     sys_connect_def, sys_connerr_def, sys_shutdown_def] >>
  TRY (drule_at (Pos (el 1)) linv_do_buf_e >> simp[] >> NO_TAC) >>
  drule_at (Pos (el 1)) linv_do_e >> simp[]
QED

Theorem sys_ev_name:
  (sys_close g w = SOME (out, w', ev) ⇒ ev_name ev = ExtCall «sys_close») ∧
  (sys_connect p w = SOME (out, w', ev) ⇒ ev_name ev = ExtCall «sys_connect») ∧
  (sys_connerr g w = SOME (out, w', ev) ⇒ ev_name ev = ExtCall «sys_connerr») ∧
  (sys_shutdown g w = SOME (out, w', ev) ⇒ ev_name ev = ExtCall «sys_shutdown»)
Proof
  rw[sys_close_def, sys_connect_def, sys_connerr_def, sys_shutdown_def] >>
  TRY (drule l0_do_cases >> rw[] >> simp[ev_name_def] >> NO_TAC) >>
  drule l0_do_buf_cases >> rw[] >> simp[ev_name_def]
QED

Theorem l1_close_names:
  l1_close g (w, st) = SOME ((w', st'), evs) ⇒
  EVERY (λev. ev_name ev = ExtCall «sys_close») evs
Proof
  rw[l1_close_def, AllCaseEqs()] >> gvs[] >> metis_tac[sys_ev_name]
QED

Theorem l1_close_linv_e:
  l1_close g (w, st) = SOME ((w', st'), evs) ∧ g ≠ l ∧ linv l w ∧ ewinv w ⇒ linv l w'
Proof
  rw[l1_close_def, AllCaseEqs()] >> gvs[] >> metis_tac[sys_linv_e]
QED

Theorem pdo_linv_e:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ pown lfd ps ∧ linv lfd w ∧ ewinv w ⇒
  linv lfd w'
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> rw[AllCaseEqs()] >> gvs[] >>
  PairCases_on ‘z’ >> gvs[] >>
  TRY (rename1 ‘l1_close g _ = _’ >>
       ‘g ≠ lfd’ by (imp_res_tac ALOOKUP_MEM >> gvs[pown_def, MEM_MAP] >>
                     strip_tac >> gvs[] >> metis_tac[SND]) >>
       drule_all l1_close_linv_e >> simp[] >> NO_TAC) >>
  gvs[l1do_def, AllCaseEqs()] >> metis_tac[sys_linv_e]
QED

Theorem edo_linv:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ eown0 lfd es ∧ ewinv w ∧
  MEM lfd (l0_used w) ∧ linv lfd w ⇒
  linv lfd w'
Proof
  strip_tac >> ‘pown lfd es.p’ by fs[eown0_def] >>
  ‘l0_rely w ∧ fds_lt w’ by fs[ewinv_def] >>
  Cases_on ‘a’ >> qpat_x_assum ‘edo _ _ _ _ = _’ mp_tac >> simp[edo_def] >>
  rw[AllCaseEqs()] >> gvs[] >>
  TRY (PairCases_on ‘z’ >> gvs[] >> drule_all pdo_linv_e >> simp[] >> NO_TAC) >>
  TRY (drule_all (cj 6 sys_linv_e) >> simp[] >> NO_TAC) >>
  TRY (PairCases_on ‘z’ >> gvs[] >>
       drule_all sys_connect_l0 >> strip_tac >>
       ‘n2w (res_val out) ≠ lfd’ by (strip_tac >> gvs[]) >>
       drule_all (cj 6 sys_linv_e) >> strip_tac >>
       drule_all (cj 8 sys_ewinv) >> strip_tac >>
       drule_all (cj 2 sys_linv_e) >> simp[] >> NO_TAC) >>
  TRY (gvs[pf_close_def, AllCaseEqs()]) >>
  TRY (rename1 ‘l1_close _ _ = SOME zz’ >> PairCases_on ‘zz’ >> gvs[]) >>
  rename1 ‘l1_close f _ = _’ >>
  ‘f ≠ lfd’
    by (imp_res_tac ALOOKUP_MEM >> strip_tac >> gvs[eown0_def, pown_def, MEM_MAP] >>
        metis_tac[SND]) >>
  drule_all l1_close_linv_e >> simp[]
QED

(* What an action does to the accept queue and the pause, and that it makes
   no accept *)
Theorem edo_lfd:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ⇒
  es'.p.pause = es.p.pause ∧
  (∃d. es'.p.acq = DROP d es.p.acq ∧ (a = EAccept lfd ∧ es.p.acq ≠ [] ⇒ 0 < d)) ∧
  EVERY (λev. ev_name ev ≠ ExtCall «sys_accept» ∧ ev_name ev ≠ ExtCall «sys_poll») evs
Proof
  Cases_on ‘a’ >> simp[edo_def] >> rw[AllCaseEqs()] >>
  gvs[ec_del_def, pf_close_def, AllCaseEqs()] >>
  TRY (PairCases_on ‘z’) >> gvs[] >> TRY (PairCases_on ‘z'’) >> gvs[] >>
  imp_res_tac l1_close_names >> imp_res_tac sys_ev_name >>
  TRY (qpat_x_assum ‘pdo _ _ _ = _’
         (fn th => strip_assume_tac (MATCH_MP pdo_lfd th) >>
                   strip_assume_tac (MATCH_MP pdo_names th))) >>
  gvs[pf_release_def, set_inb_def, EVERY_MEM] >>
  rpt strip_tac >>
  TRY (qexists_tac ‘d’ >> simp[] >> NO_TAC) >> TRY (qexists_tac ‘0’ >> simp[] >> NO_TAC) >>
  res_tac >> gvs[]
QED

Theorem eacts_lfd:
  ∀acts w es rs evs w' es'.
    eacts lfd pol (w, es) acts = SOME (rs, evs, (w', es')) ∧ eok lfd w es ∧ linv lfd w ⇒
    linv lfd w' ∧ es'.p.pause = es.p.pause ∧
    (∃d. es'.p.acq = DROP d es.p.acq ∧ (MEM (EAccept lfd) acts ∧ es.p.acq ≠ [] ⇒ 0 < d)) ∧
    EVERY (λev. ev_name ev ≠ ExtCall «sys_accept» ∧ ev_name ev ≠ ExtCall «sys_poll») evs
Proof
  Induct >> simp[eacts_def] >- (rpt strip_tac >> qexists_tac ‘0’ >> simp[]) >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  rename1 ‘edo _ _ _ _ = SOME (r, (w1, es1), evs1)’ >>
  drule edo_lfd >> strip_tac >>
  ‘linv lfd w1’
    by (drule_then strip_assume_tac eok_facts >>
        qpat_assum ‘eok _ _ _’ (strip_assume_tac o REWRITE_RULE [eok_def]) >>
        drule_all edo_linv >> simp[]) >>
  drule_all edo_eok >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  qexists_tac ‘d + d'’ >> simp[DROP_DROP_T] >> rw[] >> gvs[] >>
  Cases_on ‘d = 0’ >> gvs[] >>
  Cases_on ‘es.p.acq’ >> gvs[]
QED

(* The tail's steps, under ewinv (honestL1PFConn's, with winv) *)

Theorem l1_polls_linv_e:
  ∀chs w rv w' evs. l1_polls chs w = SOME (rv, w', evs) ∧ ewinv w ∧ linv l w ⇒
                    linv l w' ∧ EVERY (λev. ev_name ev = ExtCall «sys_poll») evs
Proof
  Induct >> simp[l1_polls_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  ‘ewinv w1 ∧ linv l w1’ by metis_tac[sys_ewinv, sys_linv_e] >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  gvs[sys_poll_def] >> drule l0_do_buf_cases >> rw[] >> simp[ev_name_def]
QED

Theorem l1_flush_linv_e:
  ∀fs w st w' st' evs. l1_flush fs (w, st) = SOME ((w', st'), evs) ∧ ewinv w ∧ linv l w ⇒
                       linv l w' ∧ EVERY (λev. ev_name ev = ExtCall «sys_send») evs
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (first_x_assum drule_all >> simp[]) >>
  gvs[AllCaseEqs()] >>
  ‘ewinv w'' ∧ linv l w''’ by metis_tac[sys_ewinv, sys_linv_e] >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  gvs[sys_send_def] >> drule l0_do_cases >> rw[] >> simp[ev_name_def]
QED

Theorem pf_fetch_linv_e:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ ewinv w ∧ linv l w ⇒ linv l w'
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  first_x_assum irule >> metis_tac[sys_ewinv, sys_linv_e]
QED

Theorem l1_reap_linv_e:
  ∀fs w st w' st' evs. l1_reap fs (w, st) = SOME ((w', st'), evs) ∧ ¬MEM l fs ∧
                       ewinv w ∧ linv l w ⇒ linv l w'
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (gvs[AllCaseEqs()] >> Cases_on ‘ws’ >>
      ‘h ≠ l’ by (strip_tac >> gvs[]) >>
      drule_all l1_close_linv_e >> strip_tac >>
      ‘ewinv q’ by (drule_all l1_close_ewinv >> simp[]) >>
      first_x_assum drule_all >> simp[])
  >> first_x_assum drule_all >> simp[]
QED

Theorem sys_poll_l_e:
  sys_poll fes w = SOME (out, w', ev) ∧ ewinv w ∧ linv l w ∧ qof w l ≠ [] ∧
  EVERY (λ(g, e). small g ∧ e < 4 ∧ (g = l ⇒ ODD e)) fes ⇒
  ewinv w' ∧ linv l w' ∧ qof w' l ≠ [] ∧ ev_name ev = ExtCall «sys_poll» ∧
  (MEM l (MAP FST fes) ⇒ ev_on «sys_poll» l ev) ∧
  (ev_on «sys_poll» l ev ∧ ¬retried ev ⇒ MEM l (readable_fds (poll_revents fes out)))
Proof
  strip_tac >> ‘l0_rely w’ by gvs[ewinv_def] >>
  ‘EVERY (λ(g, e). small g ∧ e < 4) fes’
    by (qpat_x_assum ‘EVERY _ fes’ mp_tac >> match_mp_tac EVERY_MONOTONIC >>
        simp[FORALL_PROD]) >>
  drule_all call_fds_poll >> strip_tac >>
  ‘ewinv w' ∧ linv l w' ∧ ∃t. qof w' l = qof w l ++ t’
    by (rpt conj_tac
        >- metis_tac[sys_ewinv]
        >- metis_tac[sys_linv_e]
        >> metis_tac[sys_qof]) >>
  qpat_x_assum ‘sys_poll _ _ = _’ mp_tac >> simp[sys_poll_def] >> strip_tac >>
  drule_all ev_do_buf >> strip_tac >>
  drule l0_do_buf_cases >> strip_tac >> gvs[ev_name_def] >>
  rw[] >> gvs[] >>
  qabbrev_tac ‘wt = l0_tick «sys_poll» w’ >>
  ‘linv l wt ∧ qof wt l ≠ [] ∧ LENGTH (wt.ch.errno_of wt.hist) = 4’
    by gvs[Abbr ‘wt’, linv_tick, qof_ne_ticks, l0_rely_def] >>
  ‘EVERY pe_ok (pollfd_entries (DROP 16 (poll_buf fes)))’
    by (simp[pollfd_entries_buf, EVERY_MAP] >> gvs[EVERY_MEM, FORALL_PROD] >>
        metis_tac[pe_pfd_bytes]) >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def] >>
  rw[AllCaseEqs()] >> gvs[] >>
  TRY (drule res_of_poll_failed >>
       disch_then (qspecl_then [‘e’, ‘poll_buf fes’] assume_tac) >> gvs[] >> NO_TAC) >>
  Cases_on ‘l0_res_of (poll_out w1 (poll_buf fes))’ >> gvs[] >>
  drule_all poll_revents_ok >> strip_tac >> simp[] >>
  gvs[MEM_MAP] >> rename1 ‘MEM y fes’ >> PairCases_on ‘y’ >> gvs[] >>
  ‘ODD y1’ by (qpat_x_assum ‘EVERY (λ(g, e). _ ∧ _ ∧ _) fes’ mp_tac >>
                simp[EVERY_MEM] >> disch_then drule >> simp[]) >>
  irule readable_zip >> qexists_tac ‘y1’ >> simp[] >>
  irule listen_revents_in >> simp[]
QED

Theorem l1_polls_l_e:
  ∀chs w rv w' evs.
    l1_polls chs w = SOME (rv, w', evs) ∧ ewinv w ∧ linv l w ∧ qof w l ≠ [] ∧
    (∀c. MEM c chs ⇒ EVERY (λ(g, e). small g ∧ e < 4 ∧ (g = l ⇒ ODD e)) c) ⇒
    ewinv w' ∧ linv l w' ∧ qof w' l ≠ [] ∧
    (∀c. MEM c chs ∧ MEM l (MAP FST c) ⇒ EXISTS (ev_on «sys_poll» l) evs) ∧
    (∀ev. MEM ev evs ∧ ev_on «sys_poll» l ev ∧ ¬retried ev ⇒ MEM l (readable_fds rv))
Proof
  Induct >> simp[l1_polls_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs(), DISJ_IMP_THM, FORALL_AND_THM] >>
  drule_all sys_poll_l_e >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  simp[readable_fds_def, FILTER_APPEND] >> gvs[readable_fds_def] >>
  rw[] >> gvs[] >> metis_tac[]
QED

Theorem pf_fetch_lfd_e:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ ewinv w ⇒
    ps'.acq = ps.acq ++ log_conns log ∧
    (0 < ps.pause ⇒ ps'.pause = ps.pause ∧ ¬EXISTS (ev_on «sys_accept» lfd) evs) ∧
    (MEM lfd fs ∧ wants_input lfd pol ps lfd ⇒ EXISTS (ev_on «sys_accept» lfd) evs) ∧
    (∀ev. MEM ev evs ∧ ev_on «sys_accept» lfd ev ∧ ¬failed ev ⇒ log_conns log ≠ [])
Proof
  Induct >- simp[pf_fetch_def, log_conns_def] >>
  rpt gen_tac >> rename1 ‘g :: fs’ >> strip_tac >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ mp_tac >> simp[Once pf_fetch_def] >>
  IF_CASES_TAC
  >- (strip_tac >> first_x_assum drule_all >> strip_tac >> simp[] >>
      rpt strip_tac >> gvs[] >> gvs[wants_input_def] >> metis_tac[]) >>
  IF_CASES_TAC
  >- (gvs[] >> simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
      pairarg_tac >> gvs[AllCaseEqs()] >>
      ‘ewinv w1’ by metis_tac[sys_ewinv] >>
      first_x_assum drule_all >> strip_tac >>
      ‘l0_rely w’ by gvs[ewinv_def] >>
      qpat_assum ‘sys_accept _ _ = _’ (strip_assume_tac o REWRITE_RULE [sys_accept_def]) >>
      drule_all ev_do >> drule_all ev_failed >> rpt strip_tac >>
      ‘ev_on «sys_accept» g ev’ by simp[call_fds_def] >>
      ‘ps.pause = 0’ by gvs[wants_input_def] >>
      Cases_on ‘l0_res_of out’ >> gvs[log_conns_def] >> rw[] >> gvs[EXISTS_MEM] >>
      metis_tac[]) >>
  simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  ‘ewinv w1’ by metis_tac[sys_ewinv] >>
  ‘l0_rely w’ by gvs[ewinv_def] >>
  qpat_assum ‘sys_recv _ _ _ = _’ (strip_assume_tac o REWRITE_RULE [sys_recv_def]) >>
  drule_all ev_do >> strip_tac >>
  ‘¬ev_on «sys_accept» lfd ev’ by simp[] >>
  first_x_assum drule_all >> strip_tac >> gvs[log_conns_def, wants_input_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem settle_fds_lfd:
  ∀fs w es w' es' evs.
    settle_fds fs (w, es) = SOME ((w', es'), evs) ∧ ewinv w ∧ linv l w ⇒
    linv l w' ∧ es'.p = es.p ∧ EVERY (λev. ev_name ev = ExtCall «sys_connerr») evs
Proof
  Induct >> simp[settle_fds_def] >>
  rpt gen_tac >> simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 ‘sys_connerr _ _ = SOME (out, w1, ev)’ >>
  ‘ewinv w1 ∧ linv l w1’ by metis_tac[sys_ewinv, sys_linv_e] >>
  first_x_assum drule_all >> strip_tac >>
  imp_res_tac sys_ev_name >> simp[] >>
  Cases_on ‘l0_res_of out’ >> gvs[] >> rw[] >> gvs[]
QED

Theorem pf_shuts_lfd:
  ∀fs w ps w' ps' kp sh evs.
    pf_shuts fs (w, ps) = SOME ((w', ps'), kp, sh, evs) ∧ ewinv w ∧ linv l w ⇒
    linv l w' ∧ ps'.pause = ps.pause ∧ ps'.acq = ps.acq
Proof
  Induct >- simp[pf_shuts_def] >>
  rpt gen_tac >> rename1 ‘kf :: fs’ >> PairCases_on ‘kf’ >> rename1 ‘(k, f) :: fs’ >>
  simp[Once pf_shuts_def] >>
  IF_CASES_TAC
  >- (strip_tac >> gvs[] >> PairCases_on ‘z’ >> gvs[] >> first_x_assum drule_all >> simp[]) >>
  IF_CASES_TAC
  >- (strip_tac >> gvs[] >> PairCases_on ‘z’ >> gvs[] >> first_x_assum drule_all >> simp[]) >>
  Cases_on ‘sys_shutdown f w’ >> simp[] >> rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >>
  rename1 ‘sys_shutdown _ _ = SOME (out, w1, ev)’ >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >> PairCases_on ‘z’ >> gvs[] >>
  ‘ewinv w1 ∧ linv l w1’ by metis_tac[sys_ewinv, sys_linv_e] >>
  ‘ps1.pause = ps.pause ∧ ps1.acq = ps.acq’
    by (Cases_on ‘l0_res_of out’ >> gvs[] >>
        qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> rw[] >>
        simp[drop_out_def, set_outbox_def]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem pend_fds_ctbl:
  MEM f (pend_fds es) ⇒ MEM f (MAP SND es.ctbl)
Proof
  simp[pend_fds_def, MEM_MAP, MEM_FILTER, EXISTS_PROD] >> metis_tac[]
QED

Theorem stall_step_lfd[simp]:
  (stall_step hfs ob log ps).acq = ps.acq ∧ (stall_step hfs ob log ps).pause = ps.pause
Proof
  simp[stall_step_def]
QED

(* The tail, seen from the listener (pround_lfd's tail argument) *)
Theorem etail_lfd:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, tevs) ∧
  eok lfd w es ∧ linv lfd w ∧ es.p.b.nxt < dimword (:64) ⇒
  linv lfd w' ∧ es'.p.acq = es.p.acq ++ log_conns log ∧
  (0 < es.p.pause ⇒ es'.p.pause = es.p.pause − 1 ∧ ¬EXISTS (ev_on «sys_accept» lfd) tevs) ∧
  (∀ev. MEM ev tevs ∧ ev_on «sys_accept» lfd ev ∧ ¬failed ev ⇒ log_conns log ≠ []) ∧
  (es.p.pause = 0 ∧ es.p.acq = [] ∧ MEM lfd hs ∧ qof w lfd ≠ [] ⇒
   EXISTS (ev_on «sys_poll» lfd) tevs ∧
   ∀ev. MEM ev tevs ∧ ev_on «sys_poll» lfd ev ∧ ¬retried ev ⇒
        EXISTS (ev_on «sys_accept» lfd) tevs)
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
  ‘ALOOKUP es.p.b.tbl lfd = NONE’ by (irule tbl_lfd >> simp[]) >>
  ‘∀h. ALOOKUP es.p.b.tbl h ≠ SOME lfd’
    by (rpt strip_tac >> imp_res_tac ALOOKUP_MEM >>
        gvs[pown_def, MEM_MAP] >> metis_tac[SND]) >>
  drule_all l1_polls_linv_e >> strip_tac >>
  ‘ewinv w1’ by (drule_all l1_polls_ewinv >> simp[]) >>
  drule_all l1_flush_linv_e >> strip_tac >>
  ‘ewinv w2’ by (drule_all l1_flush_ewinv >> simp[]) >>
  ‘l0_rely w1’ by gvs[ewinv_def] >>
  drule_all l1_flush_l0 >> strip_tac >>
  drule_all pf_fetch_lfd_e >> strip_tac >>
  drule_all pf_fetch_linv_e >> strip_tac >>
  ‘ewinv w3’ by (drule_all pf_fetch_ewinv >> simp[]) >>
  drule pf_fetch_closing >> strip_tac >>
  drule pf_fetch_names >> strip_tac >>
  qabbrev_tac ‘ps3 = stall_step (pf_held ps3f) (outbox_of es.p.b) log ps3f’ >>
  ‘ps3.b.closing = ps3f.b.closing ∧ ps3.acq = ps3f.acq ∧ ps3.pause = ps3f.pause’
    by simp[Abbr ‘ps3’, stall_step_def] >>
  drule l1_reap_names >> strip_tac >>
  ‘¬MEM lfd ps3f.b.closing’ by gvs[pown_def, ALL_DISTINCT_APPEND] >>
  drule_all l1_reap_linv_e >> strip_tac >>
  ‘ewinv w4’ by (drule_all l1_reap_ewinv >> simp[]) >>
  drule_all settle_fds_lfd >> strip_tac >>
  gvs[promote_def, apply_early_def] >>
  (* the tail's accepts are the fetch's *)
  ‘∀ev. MEM ev (pevs ++ fevs ++ cevs ++ sevs) ⇒ ¬ev_on «sys_accept» lfd ev’
    by (rpt strip_tac >> imp_res_tac ev_on_name >> gvs[EVERY_MEM] >> res_tac >> gvs[]) >>
  rpt conj_tac
  >- (strip_tac >> gvs[EVERY_MEM] >> rpt strip_tac >> gvs[] >>
      metis_tac[MEM_APPEND])
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum ‘∀ev. MEM ev (_ ++ _ ++ _ ++ _) ⇒ _’ (qspec_then ‘ev’ mp_tac) >>
      simp[] >> strip_tac >> gvs[] >>
      qpat_x_assum ‘∀ev. MEM ev gevs ∧ _ ⇒ _’ (qspec_then ‘ev’ mp_tac) >> metis_tac[])
  >> strip_tac >> gvs[] >>
  qabbrev_tac ‘pfes = pf_poll_set lfd pol es.p hs’ >>
  ‘wants_input lfd pol es.p lfd’ by gvs[wants_input_def] >>
  ‘(∃e. MEM (lfd, e) pfes) ∧ (∀e. MEM (lfd, e) pfes ⇒ ODD e) ∧ EVERY (λ(g, e). e < 4) pfes’
    by (qunabbrev_tac ‘pfes’ >> match_mp_tac pf_poll_set_lfd >> simp[]) >>
  ‘EVERY (λ(g, e). small g ∧ e < 4) pfes’
    by (qunabbrev_tac ‘pfes’ >> irule pf_poll_set_small >> simp[]) >>
  ‘∀f. MEM f (pend_fds es) ⇒ small f ∧ f ≠ lfd’
    by (rpt gen_tac >> strip_tac >> drule pend_fds_ctbl >> strip_tac >>
        gvs[esmall_def, EVERY_MEM, eown0_def, ALL_DISTINCT_APPEND] >>
        strip_tac >> gvs[]) >>
  ‘∀c. MEM c [fes] ⇒ EVERY (λ(g, e). small g ∧ e < 4 ∧ (g = lfd ⇒ ODD e)) c’
    by (simp[Abbr ‘fes’, EVERY_APPEND, EVERY_MAP] >>
        gvs[EVERY_MEM, FORALL_PROD] >> rw[] >> res_tac) >>
  drule_all l1_polls_l_e >> strip_tac >>
  ‘EXISTS (ev_on «sys_poll» lfd) pevs’
    by (first_x_assum irule >> qexists_tac ‘fes’ >>
        simp[Abbr ‘fes’, MEM_MAP] >> qexists_tac ‘(lfd, e)’ >> simp[]) >>
  ‘MEM lfd (in_fds fes)’
    by (simp[Abbr ‘fes’, in_fds_pend] >>
        simp[in_fds_def, MEM_MAP, MEM_FILTER, EXISTS_PROD] >> metis_tac[]) >>
  ‘wants_input lfd pol (es.p with b := b2) lfd’ by gvs[wants_input_def] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> gvs[] >>
  TRY (imp_res_tac ev_on_name >> gvs[EVERY_MEM] >> res_tac >> gvs[] >> NO_TAC) >>
  ‘MEM lfd (readable_fds rv)’ by metis_tac[] >>
  ‘MEM lfd (FILTER (λf. MEM f (in_fds fes)) (readable_fds rv))’ by simp[MEM_FILTER] >>
  gvs[EXISTS_MEM] >> metis_tac[]
QED

Theorem eshuts_lfd:
  eshuts (w, es) = SOME ((w', es'), evs) ∧ ewinv w ∧ linv l w ⇒
  linv l w' ∧ es'.p.pause = es.p.pause ∧ es'.p.acq = es.p.acq ∧ es'.p.b.nxt = es.p.b.nxt ∧
  EVERY (λev. ev_name ev = ExtCall «sys_shutdown») evs
Proof
  simp[eshuts_def] >> strip_tac >> pairarg_tac >> gvs[] >>
  rename1 ‘pf_shuts _ _ = SOME ((w', ps'), kp, sh, evs)’ >>
  drule_all pf_shuts_lfd >> strip_tac >>
  ‘l0_rely w’ by fs[ewinv_def] >>
  drule_all pf_shuts_fields >> strip_tac >>
  drule pf_shuts_world >> strip_tac >> simp[]
QED

Theorem eshuts_nxt:
  eshuts (w, es) = SOME ((w', es'), evs) ∧ l0_rely w ⇒ es'.p.b.nxt = es.p.b.nxt
Proof
  simp[eshuts_def] >> strip_tac >> pairarg_tac >> gvs[] >>
  drule_all pf_shuts_fields >> simp[]
QED

(* A round, seen from the listener (pround_lfd) *)
Theorem eround_lfd:
  eround lfd pol hs (w, es) acts = SOME (snap, (w', es'), log, evs) ∧
  eok lfd w es ∧ linv lfd w ∧ es'.p.b.nxt < dimword (:64) ⇒
  linv lfd w' ∧
  (∃d. es'.p.acq = DROP d es.p.acq ++ log_conns log ∧
       (MEM (EAccept lfd) acts ∧ es.p.acq ≠ [] ⇒ 0 < d)) ∧
  (0 < es.p.pause ⇒ es'.p.pause = es.p.pause − 1 ∧ ¬EXISTS (ev_on «sys_accept» lfd) evs) ∧
  (∀ev. MEM ev evs ∧ ev_on «sys_accept» lfd ev ∧ ¬failed ev ⇒ log_conns log ≠ []) ∧
  (es.p.pause = 0 ∧ es.p.acq = [] ∧ MEM lfd hs ∧ qof w lfd ≠ [] ⇒
   EXISTS (ev_on «sys_poll» lfd) evs ∧
   ∀ev. MEM ev evs ∧ ev_on «sys_poll» lfd ev ∧ ¬retried ev ⇒
        EXISTS (ev_on «sys_accept» lfd) evs)
Proof
  simp[eround_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  PairCases_on ‘ws1’ >> PairCases_on ‘ws2’ >>
  rename1 ‘eacts _ _ _ _ = SOME (rs, aevs, (w1, es1))’ >>
  rename1 ‘etail _ _ _ _ = SOME (rdy, (w2, es2), log, tevs)’ >>
  rename1 ‘eshuts _ = SOME (_, shevs)’ >>
  drule_all eacts_lfd >> strip_tac >>
  drule_all eacts_eok >> strip_tac >>
  ‘es2.p.b.nxt = es1.p.b.nxt’
    by (drule_then strip_assume_tac eok_facts >>
        qpat_assum ‘eok _ w1 _’ (strip_assume_tac o REWRITE_RULE [eok_def]) >>
        ‘∃rdy1 w3 es3 log1 evs1.
           etail lfd pol hs (w1, es1) = SOME (rdy1, (w3, es3), log1, evs1) ∧
           es3.p.b.nxt = es1.p.b.nxt’ by metis_tac[etail_ok] >>
        gvs[]) >>
  drule_all etail_eok >> strip_tac >>
  ‘ewinv w2’ by fs[eok_def] >>
  ‘l0_rely w2’ by fs[ewinv_def] >>
  drule_all eshuts_nxt >> strip_tac >>
  ‘es1.p.b.nxt < dimword (:64)’ by gvs[] >>
  drule_all etail_lfd >> strip_tac >>
  drule_all eshuts_lfd >> strip_tac >>
  ‘∀ev. MEM ev aevs ∨ MEM ev shevs ⇒ ¬ev_on «sys_accept» lfd ev ∧ ¬ev_on «sys_poll» lfd ev’
    by (rpt gen_tac >> strip_tac >> conj_tac >> strip_tac >> imp_res_tac ev_on_name >>
        gvs[EVERY_MEM] >> res_tac >> gvs[]) >>
  rpt conj_tac
  >- simp[]
  >- (qexists_tac ‘d’ >> simp[])
  >- (strip_tac >> qpat_x_assum ‘0 < es1.p.pause ⇒ _’ mp_tac >> simp[] >> strip_tac >>
      gvs[EVERY_MEM] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> gvs[] >> metis_tac[])
  >> strip_tac >>
  qpat_x_assum ‘es1.p.pause = 0 ∧ _ ⇒ _’ mp_tac >> impl_tac >- gvs[] >> strip_tac >>
  simp[] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The handle counter stays below 2^64: each increment is guarded
   ------------------------------------------------------------------------ *)

Theorem l1hdln_suc_lt:
  l1hdln (w2n (lfd:word64)) n < dimword (:64) ⇒ n + 1 < dimword (:64)
Proof
  qspec_then ‘lfd’ mp_tac wordsTheory.w2n_lt >> rw[l1hdln_def] >> fs[]
QED

Theorem edo_connect_hdln:
  edo lfd pol (w, es) (EConnect a) = SOME (EConnected (SOME h), ws, evs) ⇒
  l1hdln (w2n lfd) es.p.b.nxt < dimword (:64)
Proof
  simp[edo_def] >> strip_tac >> Cases_on ‘sys_connect a w’ >> fs[] >>
  PairCases_on ‘x’ >> fs[] >> qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >>
  IF_CASES_TAC >> simp[] >>
  IF_CASES_TAC >- (Cases_on ‘sys_close (n2w (res_val x0)) x1’ >> simp[] >>
                   rename1 ‘sys_close _ _ = SOME y’ >> PairCases_on ‘y’ >> simp[]) >>
  IF_CASES_TAC >> simp[]
QED

Theorem edo_nxt_lt:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ es.p.b.nxt < dimword (:64) ⇒
  es'.p.b.nxt < dimword (:64)
Proof
  Cases_on ‘∃l. a = EAccept l’
  >- (strip_tac >> gvs[edo_def] >> PairCases_on ‘z’ >> gvs[] >>
      gvs[pdo_def, AllCaseEqs()] >>
      ‘es.p.b.nxt + 1 < dimword (:64)’
        by FIRST [irule hdln_suc_lt >> qexists_tac ‘l’ >> simp[] >> NO_TAC,
                  irule hdln_suc_lt >> qexists_tac ‘lfd’ >> simp[] >> NO_TAC,
                  irule l1hdln_suc_lt >> qexists_tac ‘lfd’ >> simp[]] >> fs[]) >>
  strip_tac >> ‘∀l. a ≠ EAccept l’ by metis_tac[] >>
  drule_all edo_nxt >> strip_tac >>
  Cases_on ‘∃h. r = EConnected (SOME h)’
  >- (gvs[conn_hdls_def] >>
      ‘∃p. a = EConnect p’
        by (CCONTR_TAC >> qpat_x_assum ‘edo _ _ _ _ = _’ mp_tac >>
            qpat_x_assum ‘¬_’ mp_tac >> rpt (pop_assum kall_tac) >> rpt strip_tac >>
            drule edo_conn_hdls >> fs[conn_hdls_def]) >>
      gvs[] >> drule edo_connect_hdln >> strip_tac >>
      drule l1hdln_suc_lt >> simp[]) >>
  ‘conn_hdls [r] = []’ by (Cases_on ‘r’ >> gvs[conn_hdls_def] >>
                           rename1 ‘EConnected oh’ >> Cases_on ‘oh’ >> gvs[conn_hdls_def]) >>
  gvs[]
QED

Theorem eacts_nxt_lt:
  ∀acts w es rs evs w' es'.
    eacts lfd pol (w, es) acts = SOME (rs, evs, (w', es')) ∧ es.p.b.nxt < dimword (:64) ⇒
    es'.p.b.nxt < dimword (:64)
Proof
  Induct >> simp[eacts_def, AllCaseEqs()] >> rpt gen_tac >> strip_tac >> gvs[] >>
  PairCases_on ‘ws1’ >> drule edo_nxt_lt >> simp[] >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem eround_nxt_lt:
  eround lfd pol hs (w, es) acts = SOME (snap, (w', es'), log, evs) ∧ eok lfd w es ∧
  es.p.b.nxt < dimword (:64) ⇒
  es'.p.b.nxt < dimword (:64)
Proof
  simp[eround_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  PairCases_on ‘ws1’ >> PairCases_on ‘ws2’ >>
  rename1 ‘eacts _ _ _ _ = SOME (rs, aevs, (w1, es1))’ >>
  rename1 ‘etail _ _ _ _ = SOME (rdy, (w2, es2), log, tevs)’ >>
  drule eacts_nxt_lt >> simp[] >> strip_tac >>
  drule_all eacts_eok >> strip_tac >>
  ‘es2.p.b.nxt = es1.p.b.nxt’
    by (qpat_assum ‘eok _ w1 _’ (strip_assume_tac o REWRITE_RULE [eok_def]) >>
        ‘l0_rely w1’ by fs[ewinv_def] >>
        ‘∃rdy1 w3 es3 log1 evs1.
           etail lfd pol hs (w1, es1) = SOME (rdy1, (w3, es3), log1, evs1) ∧
           es3.p.b.nxt = es1.p.b.nxt’ by metis_tac[etail_ok] >>
        gvs[]) >>
  drule_all etail_eok >> strip_tac >>
  ‘l0_rely w2’ by fs[eok_def, ewinv_def] >>
  drule_all eshuts_nxt >> simp[]
QED
