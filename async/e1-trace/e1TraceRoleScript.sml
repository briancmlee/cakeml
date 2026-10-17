(*
  The shared E1 trace layer (m4-server): ROLES.  On the trace of an E1 run,
  raw episode j (l0sysEpisodes: the j-th event that got an fd) came from a
  sys_connect exactly when the handle layer's channel j, in the world built
  from the run (pew), has a peer address (made by EConnect; an Incoming
  arrival makes it NONE).

  Per round: the actions' events make only connect episodes (no
  sys_accept), one per EConnected (SOME _) result, and the actions append
  only peer-address channels, one per such result; the tail's events make
  only accept episodes (no sys_connect), and the tick appends only
  NONE channels; the counts match by l0_ep_sent_run and the refinement.

*)
Theory e1TraceRole
Ancestors
  moonshotSentGlue honestL1EPRefine honestL1EPModel honestL1PFRound honestL1PFConnRun
  honestL1PFConn endpointHLModel endpointWorld l0sysEpisodes asyncM3World
Libs
  preamble

(* ------------------------------------------------------------------------
   Raw side: the episodes' kinds (T: connect)
   ------------------------------------------------------------------------ *)

Definition ep_conn_def:
  ep_conn [] = [] ∧
  ep_conn (ev :: evs) = (case ev_new ev of SOME (_, x) => [ISL x] | NONE => []) ++ ep_conn evs
End

Theorem ep_conn_APPEND[simp]:
  ∀l1 l2. ep_conn (l1 ++ l2) = ep_conn l1 ++ ep_conn l2
Proof
  Induct >> simp[ep_conn_def]
QED

Theorem ep_next_count:
  ∀evs opn k. SND (FOLDL ep_next (opn, k) evs) = k + LENGTH (ep_conn evs)
Proof
  Induct >> simp[ep_conn_def] >> rpt gen_tac >>
  simp[moonshotSentGlueTheory.ep_next_def] >>
  Cases_on ‘ev_new h’ >> simp[] >> rename1 ‘SOME x’ >> PairCases_on ‘x’ >> simp[]
QED

Theorem name_new_INL:
  ev_name ev ≠ ExtCall «sys_accept» ∧ ev_new ev = SOME (f, x) ⇒ ISL x
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event n _ _’ >> Cases_on ‘n’ >>
  rw[ev_name_def, ev_new_def, LET_THM] >> gvs[AllCaseEqs()]
QED

Theorem name_new_INR:
  ev_name ev ≠ ExtCall «sys_connect» ∧ ev_new ev = SOME (f, x) ⇒ ISR x
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event n _ _’ >> Cases_on ‘n’ >>
  rw[ev_name_def, ev_new_def, LET_THM] >> gvs[AllCaseEqs()]
QED

Theorem noacc_conn:
  ∀evs. EVERY (λev. ev_name ev ≠ ExtCall «sys_accept») evs ⇒
        ep_conn evs = REPLICATE (LENGTH (ep_conn evs)) T
Proof
  Induct >> simp[ep_conn_def] >> rpt strip_tac >> fs[] >>
  Cases_on ‘ev_new h’ >> simp[] >> rename1 ‘SOME x’ >> PairCases_on ‘x’ >>
  drule_all name_new_INL >> simp[GSYM ADD1]
QED

Theorem noconn_acc:
  ∀evs. EVERY (λev. ev_name ev ≠ ExtCall «sys_connect») evs ⇒
        ep_conn evs = REPLICATE (LENGTH (ep_conn evs)) F
Proof
  Induct >> simp[ep_conn_def] >> rpt strip_tac >> fs[] >>
  Cases_on ‘ev_new h’ >> simp[] >> rename1 ‘SOME x’ >> PairCases_on ‘x’ >>
  drule_all name_new_INR >> Cases_on ‘x1’ >> simp[GSYM ADD1]
QED

Theorem edo_noacc:
  edo lfd pol (w, es) a = SOME (r, ws', evs) ⇒
  EVERY (λev. ev_name ev ≠ ExtCall «sys_accept») evs
Proof
  Cases_on ‘∃p. a = EConnect p’
  >- (gvs[] >> simp[edo_def, AllCaseEqs()] >> rw[] >> gvs[sys_connect_def] >>
      drule honestL1PFRoundTheory.l0_do_cases >> rw[] >> simp[ev_name_def]) >>
  strip_tac >> ‘∀p. a ≠ EConnect p’ by (rpt strip_tac >> fs[]) >>
  PairCases_on ‘ws'’ >> drule_all edo_names >>
  simp[EVERY_MEM] >> rpt strip_tac >> res_tac >> fs[]
QED

Theorem eacts_noacc:
  ∀acts ws rs evs ws'. eacts lfd pol ws acts = SOME (rs, evs, ws') ⇒
                       EVERY (λev. ev_name ev ≠ ExtCall «sys_accept») evs
Proof
  Induct >> simp[eacts_def] >> rpt gen_tac >> simp[AllCaseEqs(), PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >> gvs[] >> PairCases_on ‘ws’ >>
  drule edo_noacc >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem etail_noconn:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, tevs) ⇒
  EVERY (λev. ev_name ev ≠ ExtCall «sys_connect») tevs
Proof
  simp[etail_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  drule l1_polls_names >> strip_tac >> drule l1_flush_names >> strip_tac >>
  drule pf_fetch_names >> strip_tac >> drule l1_reap_names >> strip_tac >>
  drule settle_fds_names >> strip_tac >>
  qpat_x_assum ‘_ = tevs’ (SUBST_ALL_TAC o SYM) >>
  rpt (qpat_x_assum ‘EVERY _ _’ mp_tac) >> simp[EVERY_MEM] >>
  rpt strip_tac >> res_tac >> fs[]
QED

(* ------------------------------------------------------------------------
   Handle layer: channels' peer addresses (T: connected)
   ------------------------------------------------------------------------ *)

Definition cpa_def:
  cpa (c : chan) ⇔ IS_SOME c.peer_addr
End

Theorem upd_chan_cpa:
  (∀c. (g c).peer_addr = c.peer_addr) ⇒ MAP cpa (upd_chan j g w).chans = MAP cpa w.chans
Proof
  strip_tac >> simp[upd_chan_def, LIST_EQ_REWRITE, EL_MAP, EL_LUPDATE] >> rw[cpa_def]
QED

Theorem ep_conn_err_cpa:
  ep_conn_err f w = SOME w1 ⇒ MAP cpa w1.chans = MAP cpa w.chans
Proof
  rw[ep_conn_err_def, AllCaseEqs()] >> simp[upd_chan_cpa]
QED

Theorem ep_close_cpa:
  ep_close f w = SOME w1 ⇒ MAP cpa w1.chans = MAP cpa w.chans
Proof
  rw[ep_close_def, AllCaseEqs()] >> simp[upd_chan_cpa]
QED

Theorem ep_read_cpa:
  ep_read f n w = SOME (r, w1) ⇒ MAP cpa w1.chans = MAP cpa w.chans
Proof
  rw[ep_read_def, AllCaseEqs(), LET_THM] >> simp[upd_chan_cpa]
QED

Theorem ep_send_cpa:
  ep_send f bs w = SOME (k, w1) ⇒ MAP cpa w1.chans = MAP cpa w.chans
Proof
  rw[ep_send_def, AllCaseEqs(), LET_THM] >> simp[upd_chan_cpa]
QED

Theorem ehdo_cpa:
  ehdo lfd v (w, hs) x = SOME (r, (w', hs')) ⇒
  MAP cpa w'.chans = MAP cpa w.chans ++ REPLICATE (LENGTH (conn_hdls [r])) T
Proof
  Cases_on ‘x’ >> simp[ehdo_def]
  >- (simp[ep_accept_def, ep_alloc_def, AllCaseEqs(), LET_THM] >> rw[] >>
      gvs[conn_hdls_def])
  >- (rw[AllCaseEqs()] >> gvs[conn_hdls_def] >>
      TRY (drule_all ep_conn_err_cpa >> drule_all ep_close_cpa >> simp[conn_hdls_def] >> NO_TAC) >>
      TRY (drule_all ep_read_cpa >> drule_all ep_close_cpa >> simp[conn_hdls_def] >> NO_TAC) >>
      drule_all ep_read_cpa >> simp[conn_hdls_def])
  >- (rw[AllCaseEqs()] >> gvs[conn_hdls_def] >> pairarg_tac >> gvs[] >>
      drule_all ep_send_cpa >> simp[conn_hdls_def])
  >- (simp[ep_connect_def, ep_alloc_def, AllCaseEqs(), LET_THM] >> rw[] >>
      gvs[conn_hdls_def, cpa_def, new_chan_def] >> EVAL_TAC)
  >> rw[] >> simp[conn_hdls_def]
QED

Theorem ehacts_cpa:
  ∀acts k w hs rs w' hs'.
    ehacts lfd lv n k (w, hs) acts = SOME (rs, (w', hs')) ⇒
    MAP cpa w'.chans = MAP cpa w.chans ++ REPLICATE (LENGTH (conn_hdls rs)) T
Proof
  Induct >> simp[ehacts_def, conn_hdls_def] >>
  rpt gen_tac >> simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  rename1 ‘ehdo _ _ _ _ = SOME (r, st1)’ >> PairCases_on ‘st1’ >>
  drule ehdo_cpa >> strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
  ‘conn_hdls (r::rs') = conn_hdls [r] ++ conn_hdls rs'’ by MATCH_ACCEPT_TAC conn_hdls_cons >>
  pop_assum SUBST1_TAC >> simp[REPLICATE_APPEND]
QED

Theorem ehacts_tot_cpa:
  ehacts_tot lfd lv n st acts = (rs, (w1, hs1)) ⇒
  MAP cpa w1.chans = MAP cpa (FST st).chans ++ REPLICATE (LENGTH (conn_hdls rs)) T
Proof
  PairCases_on ‘st’ >> simp[ehacts_tot_def] >>
  Cases_on ‘ehacts lfd lv n 0 (st0, st1) acts’ >> simp[]
  >- (rw[] >> simp[conn_hdls_def]) >>
  rename1 ‘SOME x’ >> PairCases_on ‘x’ >> rw[] >> drule ehacts_cpa >> simp[]
QED

(* The tick appends unconnected channels only *)
Definition cext_def:
  cext w w' ⇔ ∃l. MAP cpa w'.chans = MAP cpa w.chans ++ l ∧ EVERY (λb. ¬b) l
End

Theorem cext_trans:
  cext w1 w2 ∧ cext w2 w3 ⇒ cext w1 w3
Proof
  rw[cext_def] >> qexists_tac ‘l ++ l'’ >> simp[]
QED

Theorem ep_deliver_cext:
  cext w (ep_deliver w x)
Proof
  Cases_on ‘x’ >> simp[ep_deliver_def] >> rw[] >> TRY every_case_tac >> simp[cext_def] >>
  FIRST [simp[cpa_def, new_chan_def] >> NO_TAC,
         qexists_tac ‘[]’ >> REWRITE_TAC [APPEND_NIL, EVERY_DEF] >> irule upd_chan_cpa >>
         simp[] >> NO_TAC,
         qexists_tac ‘[]’ >> simp[] >> NO_TAC,
         qexists_tac ‘[F]’ >> simp[cpa_def, new_chan_def] >> NO_TAC]
QED

Theorem FOLDL_deliver_cext:
  ∀as w. cext w (FOLDL ep_deliver w as)
Proof
  Induct >- simp[cext_def] >>
  rpt gen_tac >> simp[] >> irule cext_trans >>
  qexists_tac ‘ep_deliver w h’ >> simp[ep_deliver_cext]
QED

Theorem ehpoll_cext:
  ehpoll lfd hs hfds w = (rdy, w', hs') ⇒ cext w w'
Proof
  rw[ehpoll_def, LET_THM] >> simp[ep_tick_def] >> irule cext_trans >>
  qexists_tac ‘w with clock := w.clock + 1’ >> simp[FOLDL_deliver_cext] >>
  simp[cext_def]
QED

(* ------------------------------------------------------------------------
   One round, as lists
   ------------------------------------------------------------------------ *)

Theorem every_not_replicate:
  ∀l. EVERY (λb. ¬b) l ⇒ l = REPLICATE (LENGTH l) F
Proof
  Induct >> simp[]
QED

Theorem roles_step_list:
  MAP cpa c1 = e0 ++ REPLICATE x T ∧ MAP cpa c2 = MAP cpa c1 ++ l ∧ EVERY (λb. ¬b) l ∧
  ea = REPLICATE x T ∧ et = REPLICATE (LENGTH et) F ∧
  LENGTH c2 = LENGTH e0 + x + LENGTH et ⇒
  MAP cpa c2 = e0 ++ ea ++ et
Proof
  strip_tac >>
  ‘LENGTH c1 = LENGTH e0 + x’
    by (qpat_x_assum ‘MAP cpa c1 = _’ (mp_tac o AP_TERM “LENGTH : bool list -> num”) >>
        simp[]) >>
  ‘LENGTH c2 = LENGTH c1 + LENGTH l’
    by (qpat_x_assum ‘MAP cpa c2 = _’ (mp_tac o AP_TERM “LENGTH : bool list -> num”) >>
        simp[]) >>
  ‘l = REPLICATE (LENGTH l) F’ by (irule every_not_replicate >> simp[]) >>
  ‘LENGTH l = LENGTH et’ by simp[] >>
  qpat_x_assum ‘MAP cpa c2 = _’ SUBST1_TAC >> qpat_x_assum ‘MAP cpa c1 = _’ SUBST1_TAC >>
  qpat_x_assum ‘ea = _’ SUBST1_TAC >> qpat_x_assum ‘l = _’ SUBST1_TAC >>
  qpat_x_assum ‘et = _’ SUBST1_TAC >> simp[]
QED

(* ------------------------------------------------------------------------
   The run
   ------------------------------------------------------------------------ *)

Theorem e1_roles:
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧ MEM 0w (l0_used w0) ∧
  (∀n. SND (ecm lfd pol ifds m w0 n) + 1 < dimword (:64)) ⇒
  ∀n h ws evs logs.
    erounds lfd pol ifds m (w0, einit) n = SOME (h, ws, evs, logs) ⇒
    MAP cpa (FST (ehst lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) n)).chans =
    ep_conn evs
Proof
  strip_tac >> Induct
  >- (simp[erounds_def] >> rw[] >>
      simp[ehst_def, ehrounds_def, pew_def, ep_conn_def]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum ‘erounds _ _ _ _ _ (SUC _) = _’
    (strip_assume_tac o SIMP_RULE (srw_ss()) [AllCaseEqs()] o
     ONCE_REWRITE_RULE [erounds_def]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum ‘eround _ _ _ _ _ = _’ mp_tac >> simp[eround_def, AllCaseEqs()] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rename1 ‘eacts _ _ ws' _ = SOME (rs, aevs, ws1)’ >>
  PairCases_on ‘ws'’ >> PairCases_on ‘ws1’ >> PairCases_on ‘ws’ >> fs[] >>
  (* the episode counts, at rounds n and n + 1 *)
  mp_tac l0_ep_sent_run >> impl_tac >- simp[] >>
  disch_then (fn th =>
    qspecl_then [‘n’, ‘h'’, ‘(ws'0, ws'1)’, ‘evs'’, ‘logs'’] mp_tac th >>
    qspecl_then [‘SUC n’, ‘h' ++ [ssnap rdy rs]’, ‘(ws0, ws1)’, ‘evs' ++ aevs ++ tevs’,
                 ‘logs' ++ [log]’] mp_tac th) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  (* E1's invariants at rounds n and n + 1 *)
  mp_tac (Q.INST [‘N’ |-> ‘SUC n’] l1ep_refines_ehl_upto_sent) >> impl_tac >- fs[] >>
  disch_then (fn th =>
    qspecl_then [‘n’, ‘h'’, ‘(ws'0, ws'1)’, ‘evs'’, ‘logs'’] mp_tac th >>
    qspecl_then [‘SUC n’, ‘h' ++ [ssnap rdy rs]’, ‘(ws0, ws1)’, ‘evs' ++ aevs ++ tevs’,
                 ‘logs' ++ [log]’] mp_tac th) >>
  simp[] >> rpt (disch_then strip_assume_tac) >>
  (* the round's connect episodes: as l0_ep_sent_run *)
  ‘∃cm k. ecm lfd pol ifds m w0 n = (cm, k)’ by metis_tac[pairTheory.PAIR] >>
  ‘okeys ws'1.p.b’
    by (qpat_x_assum ‘sent_inv (FST (ecm _ _ _ _ _ n)) _ _ _’ mp_tac >> simp[sent_inv_def]) >>
  ‘∀i rs0 evs0 wi esi.
     i ≤ LENGTH (new_actions (log_of m) h') ∧
     eacts lfd pol (ws'0, ws'1) (TAKE i (new_actions (log_of m) h')) =
     SOME (rs0, evs0, (wi, esi)) ⇒ eown lfd esi’
    by (qpat_x_assum ‘∀n'. n' < SUC n ⇒ eround_own _ _ _ _ _ _’ (qspec_then ‘n’ mp_tac) >>
        simp[eround_own_def] >> disch_then drule >> simp[]) >>
  ‘fd0_ok ws'0 ws'1’ by (qpat_x_assum ‘fd0_ok (FST (ws'0, _)) _’ mp_tac >> simp[]) >>
  ‘FOLDL ep_next (cm, k) aevs = (cnew k (rfds ws11 rs) ++ cm, k + LENGTH (rfds ws11 rs))’
    by (qpat_x_assum ‘eacts _ _ (ws'0, ws'1) _ = _’ assume_tac >>
        drule eacts_ep >> disch_then (qspecl_then [‘0’, ‘cm’, ‘cm’, ‘k’] mp_tac) >>
        impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >> simp[]) >>
  ‘LENGTH (ep_conn aevs) = LENGTH (conn_hdls rs)’
    by (qspecl_then [‘aevs’, ‘cm’, ‘k’] mp_tac ep_next_count >>
        qpat_x_assum ‘FOLDL ep_next (cm, k) aevs = _’ (fn th => REWRITE_TAC [th]) >>
        simp[rfds_length]) >>
  ‘ep_conn aevs = REPLICATE (LENGTH (conn_hdls rs)) T’
    by (qpat_x_assum ‘eacts _ _ (ws'0, ws'1) _ = _’ assume_tac >>
        drule eacts_noacc >> strip_tac >> drule noacc_conn >>
        qpat_x_assum ‘LENGTH (ep_conn aevs) = _’ (fn th => REWRITE_TAC [th]) >> simp[]) >>
  ‘ep_conn tevs = REPLICATE (LENGTH (ep_conn tevs)) F’
    by (qpat_x_assum ‘etail _ _ _ _ = _’ assume_tac >>
        drule etail_noconn >> strip_tac >> drule noconn_acc >> simp[]) >>
  (* the handle layer's round n *)
  qabbrev_tac ‘lv = elv lfd pol ifds m w0’ >>
  qabbrev_tac ‘W0 = pew lfd a pol ifds m w0 calls’ >>
  Cases_on ‘ehacts_tot lfd lv n (ehst lfd lv ifds m W0 n)
              (new_actions (log_of m) (ehhist lfd lv ifds m W0 n))’ >>
  rename1 ‘_ = (rs1, st1)’ >> PairCases_on ‘st1’ >>
  Cases_on ‘ehpoll lfd st11 (ifds (ehhist lfd lv ifds m W0 n)) st10’ >>
  rename1 ‘_ = (rdy1, st2)’ >> PairCases_on ‘st2’ >>
  drule_all ehround_step >> strip_tac >>
  ‘rs1 = rs’
    by (qpat_x_assum ‘ehhist _ _ _ _ _ (SUC n) = ehhist _ _ _ _ _ n ++ _’ mp_tac >>
        qpat_assum ‘ehhist _ _ _ _ _ (SUC n) = h' ++ _’ (fn th => REWRITE_TAC [th]) >>
        qpat_assum ‘ehhist _ _ _ _ _ n = h'’ (fn th => REWRITE_TAC [th]) >>
        simp[ssnap_def]) >>
  qpat_x_assum ‘rs1 = rs’ SUBST_ALL_TAC >>
  qpat_x_assum ‘ehacts_tot _ _ _ _ _ = _’ (assume_tac o MATCH_MP ehacts_tot_cpa) >>
  qpat_x_assum ‘ehpoll _ _ _ _ = _’ (assume_tac o MATCH_MP ehpoll_cext) >>
  qpat_x_assum ‘cext _ _’ (strip_assume_tac o REWRITE_RULE [cext_def]) >>
  ‘LENGTH st20.chans = LENGTH (ep_conn evs') + LENGTH (conn_hdls rs) + LENGTH (ep_conn tevs)’
    by (qpat_x_assum ‘LENGTH (FST (ehst _ _ _ _ _ (SUC n))).chans = _’ mp_tac >>
        qpat_assum ‘ehst _ _ _ _ _ (SUC n) = _’ (fn th => REWRITE_TAC [th, pairTheory.FST]) >>
        disch_then SUBST1_TAC >>
        qpat_x_assum ‘FOLDL ep_next ([], 0) (evs' ++ aevs ++ tevs) = _’ (SUBST1_TAC o SYM) >>
        REWRITE_TAC [ep_next_count, ep_conn_APPEND, LENGTH_APPEND] >>
        qpat_x_assum ‘LENGTH (ep_conn aevs) = _’ (fn th => REWRITE_TAC [th]) >> simp[]) >>
  qpat_assum ‘ehst _ _ _ _ _ (SUC n) = _’ (fn th => REWRITE_TAC [th]) >>
  REWRITE_TAC [pairTheory.FST, ep_conn_APPEND] >>
  irule roles_step_list >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [‘st10.chans’, ‘l’, ‘LENGTH (conn_hdls rs)’] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘MAP cpa st10.chans = _’ (fn th => REWRITE_TAC [th]) >>
  qpat_x_assum ‘MAP cpa (FST (ehst _ _ _ _ _ n)).chans = _’ (fn th => REWRITE_TAC [th])
QED
