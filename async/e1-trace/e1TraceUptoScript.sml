(*
  The shared E1 trace layer (m4-server's part (e)): R1's client-count
  premise ∀n. SND (ecm n) + 1 < dimword (:64), from a bound on the handle
  layer's handle counter in the world built from the run.

  The E1 driver has no handle-room guard, so the premise must come from
  the program.  It cannot come from L1's own handle limit: L1 stops at
  nxt = 2^64 − 1 and holds one pre-accepted connection, so the count can
  reach 2^64.  The handle layer's counter is a program fact that holds in
  every world (for the proxy: nxt ≤ cbound), and it reaches L1 one round
  at a time:

  - ecm_count: L1's channel count is at most its handle counter plus its
    queue of pre-accepted connections, which holds at most one.
  - ehst_nxt_SUC: given the premise up to round n, the handle layer's
    counter after round n is L1's (R1 at n, then round n's actions).
  - ecm_bound: so a bound nxt + 2 < 2^64 at every round of the handle
    layer gives the premise at every round.
*)
Theory e1TraceUpto
Ancestors
  honestL1EPRefine honestL1EPModel honestL1PFRefine honestL1PFModel honestL1Model
  honestL1PFFlush honestL1PFOut endpointHLModel e1TraceRead
Libs
  preamble

(* ------------------------------------------------------------------------
   L1: the channel count against the handle counter and the queue
   ------------------------------------------------------------------------ *)

Theorem LENGTH_fconns:
  ∀l. LENGTH (fconns l) = LENGTH (FILTER (λx. ∃g. x = FConn g) l)
Proof
  Induct >> simp[fconns_def] >> Cases >> simp[fconns_def]
QED

Theorem conn_hdls_CONS:
  ∀r rs. conn_hdls (r :: rs) = conn_hdls [r] ++ conn_hdls rs
Proof
  Cases >> simp[conn_hdls_def] >> rename1 ‘EConnected x’ >> Cases_on ‘x’ >> simp[conn_hdls_def]
QED

(* A fetch queues what it accepted, at most one at a time *)
Theorem pf_fetch_acq:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ⇒
    ps'.acq = ps.acq ++ fconns log ∧ ps'.b.nxt = ps.b.nxt ∧
    (LENGTH ps.acq ≤ 1 ⇒ LENGTH ps'.acq ≤ 1)
Proof
  Induct >- simp[pf_fetch_def, fconns_def] >>
  rpt gen_tac >> rename1 ‘pf_fetch _ _ (f :: fs)’ >>
  simp[Once pf_fetch_def] >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum drule >> simp[]) >>
  IF_CASES_TAC
  >- (gvs[wants_input_def] >>
      Cases_on ‘sys_accept f w’ >> simp[] >> rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >>
      simp[] >> Cases_on ‘l0_res_of x0’ >> simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
      TRY (rename1 ‘Fail e _’ >> Cases_on ‘e = E_MFILE’) >> gvs[] >>
      first_x_assum drule >> simp[fconns_def]) >>
  Cases_on ‘sys_recv f pf_chunk w’ >> simp[] >> rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >>
  simp[] >> Cases_on ‘l0_res_of x0’ >> simp[] >>
  TRY (rename1 ‘Fail e _’ >> Cases_on ‘l1_transient e’) >>
  TRY (rename1 ‘Ok k’ >> Cases_on ‘0 < k’) >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[fconns_def, set_inb_def]
QED

Theorem l1_flush_nxt:
  ∀fs w b w' b' evs. l1_flush fs (w, b) = SOME ((w', b'), evs) ⇒ b'.nxt = b.nxt
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (first_x_assum drule >> simp[]) >>
  gvs[AllCaseEqs()] >> first_x_assum drule >> simp[after_send_def] >>
  every_case_tac >> simp[set_outbox_def]
QED

Theorem settle_fds_p:
  ∀fs w es w' es' evs. settle_fds fs (w, es) = SOME ((w', es'), evs) ⇒ es'.p = es.p
Proof
  Induct >> simp[settle_fds_def] >> rpt gen_tac >> simp[AllCaseEqs()] >> strip_tac >>
  gvs[] >> first_x_assum drule >> every_case_tac >> simp[]
QED

(* The tail keeps the counter and queues what the fetch accepted *)
Theorem etail_acq:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, tevs) ⇒
  es'.p.b.nxt = es.p.b.nxt ∧ es'.p.acq = es.p.acq ++ fconns log ∧
  (LENGTH es.p.acq ≤ 1 ⇒ LENGTH es'.p.acq ≤ 1)
Proof
  simp[etail_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule l1_flush_nxt >> strip_tac >>
  drule pf_fetch_acq >> strip_tac >>
  drule l1_reap_tbl >> strip_tac >>
  drule settle_fds_p >> strip_tac >> gvs[promote_fields, apply_early_def]
QED

Theorem l1_close_nxt:
  l1_close f (w, st) = SOME ((w', st'), evs) ⇒ st'.nxt = st.nxt
Proof
  rw[l1_close_def, AllCaseEqs()] >> simp[forget_def, set_outbox_def] >> rw[]
QED

Theorem l1do_write_nxt:
  l1do lfd (w, st) (Write h bs) = SOME (r, (w', st'), evs) ⇒ st'.nxt = st.nxt
Proof
  rw[l1do_def, AllCaseEqs()] >> gvs[set_outbox_def] >>
  Cases_on ‘l0_res_of out’ >> gvs[after_send_def, set_outbox_def] >> rw[]
QED

Theorem pdo_count:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ⇒
  ps.b.nxt + LENGTH ps.acq ≤ ps'.b.nxt + LENGTH ps'.acq ∧ LENGTH ps'.acq ≤ LENGTH ps.acq
Proof
  Cases_on ‘a’ >> simp[pdo_def, AllCaseEqs()] >> rw[] >> gvs[] >>
  TRY (PairCases_on ‘z’) >> gvs[] >>
  TRY (drule l1_close_nxt >> simp[] >> NO_TAC) >>
  TRY (drule l1do_write_nxt >> simp[] >> NO_TAC)
QED

Theorem edo_count:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ⇒
  es.p.b.nxt + LENGTH es.p.acq + LENGTH (conn_hdls [r]) ≤ es'.p.b.nxt + LENGTH es'.p.acq ∧
  LENGTH es'.p.acq ≤ LENGTH es.p.acq
Proof
  Cases_on ‘a’ >> rw[edo_def, AllCaseEqs()] >> TRY (PairCases_on ‘z’) >>
  gvs[ec_del_def, conn_hdls_def] >>
  TRY (drule_then strip_assume_tac pdo_count) >>
  TRY (drule_then strip_assume_tac l1_close_nxt) >>
  every_case_tac >> gvs[conn_hdls_def] >>
  (* R3: EClose on an L2 handle (pf_close) *)
  gvs[honestL1PFCloseTheory.pf_close_def, AllCaseEqs(), honestL1PFCloseTheory.pf_release_def] >>
  TRY (PairCases_on ‘z’) >> gvs[] >>
  TRY (drule_then strip_assume_tac l1_close_nxt) >> gvs[]
QED

Theorem eacts_count:
  ∀acts wl es rs evs wl' es'.
    eacts lfd pol (wl, es) acts = SOME (rs, evs, (wl', es')) ⇒
    es.p.b.nxt + LENGTH es.p.acq + LENGTH (conn_hdls rs) ≤ es'.p.b.nxt + LENGTH es'.p.acq ∧
    LENGTH es'.p.acq ≤ LENGTH es.p.acq
Proof
  Induct >> simp[eacts_def, conn_hdls_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> rename1 ‘edo _ _ _ _ = SOME (r, ws1, _)’ >>
  PairCases_on ‘ws1’ >> drule edo_count >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  once_rewrite_tac[conn_hdls_CONS] >> simp[]
QED

(* R3's shutdown step keeps the handle counter and the queue *)
Theorem pf_shuts_count:
  ∀fs w ps w' ps' kp sh evs.
    pf_shuts fs (w, ps) = SOME ((w', ps'), kp, sh, evs) ⇒ ps'.b.nxt = ps.b.nxt ∧ ps'.acq = ps.acq
Proof
  Induct >- simp[honestL1PFCloseTheory.pf_shuts_def] >> Cases >>
  rw[honestL1PFCloseTheory.pf_shuts_def, AllCaseEqs()] >>
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> simp[drop_out_def, set_outbox_def]
QED

Theorem eshuts_count:
  eshuts (w, es) = SOME ((w', es'), evs) ⇒ es'.p.b.nxt = es.p.b.nxt ∧ es'.p.acq = es.p.acq
Proof
  rw[eshuts_def] >> pairarg_tac >> gvs[] >> drule pf_shuts_count >> simp[]
QED

(* MAIN (U1): L1's channel count is at most its handle counter plus its
   queue, which holds at most one connection *)
Theorem ecm_count:
  ∀n h ws evs logs.
    erounds lfd pol ifds m (w0, einit) n = SOME (h, ws, evs, logs) ⇒
    SND (ecm lfd pol ifds m w0 n) ≤ (SND ws).p.b.nxt + LENGTH (SND ws).p.acq ∧
    LENGTH (SND ws).p.acq ≤ 1
Proof
  Induct >- simp[erounds_def, ecm_def, einit_def, pinit_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum ‘erounds _ _ _ _ _ (SUC _) = _’
    (strip_assume_tac o SIMP_RULE (srw_ss()) [AllCaseEqs()] o
     ONCE_REWRITE_RULE [erounds_def]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum ‘eround _ _ _ _ _ = _’ mp_tac >> simp[eround_def, AllCaseEqs()] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rename1 ‘eacts _ _ wsa _ = SOME (rs, aevs, ws1)’ >>
  rename1 ‘etail _ _ _ _ = SOME (rdy, ws2, log, tevs)’ >>
  PairCases_on ‘wsa’ >> PairCases_on ‘ws1’ >> PairCases_on ‘ws2’ >> fs[] >>
  rename1 ‘eshuts _ = SOME (ws3, _)’ >> PairCases_on ‘ws3’ >>
  qpat_x_assum ‘eshuts _ = _’ (strip_assume_tac o MATCH_MP eshuts_count) >>
  drule eacts_count >> strip_tac >>
  drule etail_acq >> strip_tac >>
  ‘eacts_of lfd pol ifds m w0 n = SOME (rs, aevs, (ws10, ws11))’ by simp[eacts_of_def] >>
  ‘econ lfd pol ifds m w0 n = rfds ws11 rs’ by simp[econ_def] >>
  ‘elog lfd pol ifds m w0 n = log’
    by (‘LENGTH logs' = n’
          by (qpat_x_assum ‘erounds _ _ _ _ _ n = _’ assume_tac >>
              drule erounds_logs >> simp[]) >>
        qpat_x_assum ‘erounds _ _ _ _ _ (SUC n) = _’ assume_tac >>
        drule elog_EL >> disch_then (qspec_then ‘n’ mp_tac) >> simp[EL_APPEND2]) >>
  Cases_on ‘ecm lfd pol ifds m w0 n’ >> rename1 ‘ecm _ _ _ _ _ n = (cm, k)’ >> fs[] >>
  ‘ecm1 lfd pol ifds m w0 n = (cnew k (rfds ws11 rs) ++ cm, k + LENGTH (rfds ws11 rs))’
    by simp[ecm1_def] >>
  Cases_on ‘arrs lfd (cnew k (rfds ws11 rs) ++ cm, k + LENGTH (rfds ws11 rs)) log’ >>
  rename1 ‘_ = (as, ck)’ >> PairCases_on ‘ck’ >>
  ‘ecm lfd pol ifds m w0 (SUC n) = (ck0, ck1)’ by simp[ecm_SUC] >>
  drule arrs_count >> strip_tac >>
  simp[] >> fs[rfds_length, GSYM LENGTH_fconns] >>
  ‘LENGTH ws11.p.acq ≤ 1’ by simp[] >> gvs[]
QED

(* ------------------------------------------------------------------------
   The handle layer's counter after round n is L1's
   ------------------------------------------------------------------------ *)

Theorem ehst_nxt_SUC:
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
  (∀hh. EVERY noclose (new_actions (log_of m) hh)) ∧
  (∀n'. n' ≤ n ⇒ SND (ecm lfd pol ifds m w0 n') + 1 < dimword (:64)) ∧
  erounds lfd pol ifds m (w0, einit) (SUC n) = SOME (hh, wss, evss, logss) ⇒
  (SND (ehst lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) (SUC n))).nxt =
  (SND wss).p.b.nxt
Proof
  strip_tac >> qabbrev_tac ‘lv = elv lfd pol ifds m w0’ >>
  qpat_assum ‘erounds _ _ _ _ _ (SUC _) = _’
    (strip_assume_tac o SIMP_RULE (srw_ss()) [AllCaseEqs()] o
     ONCE_REWRITE_RULE [erounds_def]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  mp_tac (Q.INST [‘N’ |-> ‘n’] l1ep_refines_ehl_upto_sent) >> impl_tac >- fs[] >>
  disch_then (qspecl_then [‘n’, ‘h’, ‘ws’, ‘evs’, ‘logs’] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum ‘eround _ _ _ _ _ = _’ mp_tac >> simp[eround_def, AllCaseEqs()] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rename1 ‘eacts _ _ ws _ = SOME (rs, aevs, ws1)’ >>
  PairCases_on ‘ws’ >> PairCases_on ‘ws1’ >> fs[] >>
  qabbrev_tac ‘W0 = pew lfd a pol ifds m w0 calls’ >>
  Cases_on ‘ehst lfd lv ifds m W0 n’ >> rename1 ‘_ = (w, hs)’ >> fs[] >>
  Cases_on ‘ecm lfd pol ifds m w0 n’ >> rename1 ‘ecm _ _ _ _ _ n = (cm, k)’ >> fs[] >>
  ‘eacts_of lfd pol ifds m w0 n = SOME (rs, aevs, (ws10, ws11))’ by simp[eacts_of_def] >>
  ‘econ lfd pol ifds m w0 n = rfds ws11 rs’ by simp[econ_def] >>
  ‘elog lfd pol ifds m w0 n = log’
    by (‘LENGTH logs = n’
          by (qpat_x_assum ‘erounds _ _ _ _ _ n = _’ assume_tac >>
              drule erounds_logs >> simp[]) >>
        qpat_x_assum ‘erounds _ _ _ _ _ (SUC n) = _’ assume_tac >>
        drule elog_EL >> disch_then (qspec_then ‘n’ mp_tac) >> simp[EL_APPEND2]) >>
  ‘ecm1 lfd pol ifds m w0 n = (cnew k (rfds ws11 rs) ++ cm, k + LENGTH (rfds ws11 rs))’
    by simp[ecm1_def] >>
  qabbrev_tac ‘fs = rfds ws11 rs’ >>
  Cases_on ‘arrs lfd (cnew k fs ++ cm, k + LENGTH fs) log’ >> rename1 ‘_ = (as, ck)’ >>
  PairCases_on ‘ck’ >> rename1 ‘arrs _ _ _ = (as, cm', k')’ >>
  ‘ecm lfd pol ifds m w0 (SUC n) = (cm', k')’ by simp[ecm_SUC] >>
  ‘∃new. cm' = new ++ (cnew k fs ++ cm)’ by (drule arrs_suffix >> simp[]) >>
  ‘∀f j. MEM (f, j) cm' ⇒ ∀used. ¬MEM f used ⇒ erun_alloc lfd pol ifds m w0 j used = f’
    by (rpt strip_tac >> irule erun_alloc_eq >> simp[] >> qexists_tac ‘SUC n’ >>
        qpat_x_assum ‘ecm _ _ _ _ _ (SUC n) = _’ (fn th => REWRITE_TAC [th]) >>
        REWRITE_TAC [pairTheory.FST] >> first_assum ACCEPT_TAC) >>
  ‘∀c. c < LENGTH (conn_outs rs) ⇒ (w.nosock (w.nconnects + c) ⇔ EL c (conn_outs rs))’
    by (rpt strip_tac >>
        qpat_x_assum ‘w.nosock = _’ (fn th => REWRITE_TAC [th]) >>
        qpat_x_assum ‘w.nconnects = _’ (fn th => REWRITE_TAC [th]) >>
        qpat_assum ‘erounds _ _ _ _ _ (SUC n) = _’
          (mp_tac o MATCH_MP erun_nosock_EL) >>
        disch_then (qspec_then ‘LENGTH (nosock_of (ehhist lfd lv ifds m W0 n)) + c’ mp_tac) >>
        simp[nosock_of_def, asyncM3WorldTheory.ssnap_def, EL_APPEND2]) >>
  ‘∀f j. MEM (f, j) (cnew (LENGTH w.chans) (rfds ws11 rs)) ⇒
         ∀used. ¬MEM f used ⇒ w.alloc j used = f’
    by (rpt strip_tac >>
        qpat_x_assum ‘w.alloc = _’ (fn th => REWRITE_TAC [th]) >>
        qpat_x_assum ‘∀f j. MEM (f, j) cm' ⇒ _’ irule >> simp[] >>
        qpat_x_assum ‘cm' = _’ SUBST1_TAC >> simp[MEM_APPEND] >>
        qpat_x_assum ‘MEM _ (cnew _ _)’ mp_tac >> fs[Abbr ‘fs’]) >>
  ‘∀i hd. i < LENGTH (new_actions (log_of m) (ehhist lfd lv ifds m W0 n)) ∧
          EL i (new_actions (log_of m) (ehhist lfd lv ifds m W0 n)) = ELevel hd ⇒
          EL i rs = case lv n (0 + i) of SOME l => ELvl l | NONE => EGone’
    by (rpt strip_tac >>
        qpat_assum ‘eacts _ _ _ _ = _’ assume_tac >>
        qpat_assum ‘erounds _ _ _ _ _ n = _’ assume_tac >>
        drule_all level_true >> strip_tac >> simp[Abbr ‘lv’] >> rw[]) >>
  ‘EVERY noclose (new_actions (log_of m) (ehhist lfd lv ifds m W0 n))’
    by (qpat_assum ‘∀hh. EVERY noclose _’ (qspec_then ‘ehhist lfd lv ifds m W0 n’ ACCEPT_TAC)) >>
  qpat_x_assum ‘eacts _ _ _ _ = _’ assume_tac >>
  drule_all ev_acts >> strip_tac >>
  rename1 ‘etail _ _ _ _ = SOME (rdy, wsf, log, tevs)’ >> PairCases_on ‘wsf’ >>
  rename1 ‘eshuts _ = SOME (ws3, _)’ >> PairCases_on ‘ws3’ >>
  qpat_x_assum ‘eshuts _ = _’ (strip_assume_tac o MATCH_MP eshuts_count) >>
  qpat_x_assum ‘etail _ _ _ _ = _’ (strip_assume_tac o MATCH_MP etail_acq) >>
  qpat_x_assum ‘ehs_rel hs' _’ (strip_assume_tac o REWRITE_RULE [ehs_rel_def]) >>
  ‘ehrounds lfd lv ifds m W0 n = (ehhist lfd lv ifds m W0 n, (w, hs))’
    by (qpat_x_assum ‘ehst _ _ _ _ _ n = _’ mp_tac >> simp[ehst_def, ehhist_def] >>
        Cases_on ‘ehrounds lfd lv ifds m W0 n’ >> simp[]) >>
  ‘ehacts_tot lfd lv n (w, hs) (new_actions (log_of m) (ehhist lfd lv ifds m W0 n)) =
   (rs, (w', hs'))’
    by (REWRITE_TAC [ehacts_tot_def] >>
        qpat_x_assum ‘ehacts _ _ _ _ _ _ = _’ (fn th => REWRITE_TAC [th]) >> simp[]) >>
  REWRITE_TAC [ehst_def] >> ONCE_REWRITE_TAC [ehrounds_def] >>
  qpat_x_assum ‘ehrounds _ _ _ _ _ n = _’ (fn th => REWRITE_TAC [th]) >>
  qpat_x_assum ‘ehacts_tot _ _ _ _ _ = _’ (fn th => simp[ehpoll_def, th])
QED

(* MAIN (U3): a bound on the handle layer's counter gives R1's premise *)
Theorem ecm_bound:
  (∀n. erounds lfd pol ifds m (w0, einit) n ≠ NONE) ∧
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
  (∀hh. EVERY noclose (new_actions (log_of m) hh)) ∧
  (∀n. (SND (ehst lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) n)).nxt + 2
       < dimword (:64)) ⇒
  ∀n. SND (ecm lfd pol ifds m w0 n) + 1 < dimword (:64)
Proof
  strip_tac >>
  ‘∀N n. n ≤ N ⇒ SND (ecm lfd pol ifds m w0 n) + 1 < dimword (:64)’
    suffices_by (rpt strip_tac >> first_x_assum (qspecl_then [‘n’, ‘n’] mp_tac) >> simp[]) >>
  Induct >- simp[ecm_def] >>
  rpt strip_tac >> Cases_on ‘n ≤ N’ >- (first_x_assum drule >> simp[]) >>
  ‘n = SUC N’ by simp[] >> BasicProvers.VAR_EQ_TAC >>
  Cases_on ‘erounds lfd pol ifds m (w0, einit) (SUC N)’
  >- (qpat_x_assum ‘∀n. erounds _ _ _ _ _ n ≠ NONE’ (qspec_then ‘SUC N’ mp_tac) >> simp[]) >>
  rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >>
  qpat_assum ‘erounds _ _ _ _ _ (SUC N) = _’ (strip_assume_tac o MATCH_MP ecm_count) >>
  qpat_assum ‘erounds _ _ _ _ _ (SUC N) = _’ assume_tac >>
  drule_at (Pos last) ehst_nxt_SUC >>
  disch_then (qspecl_then [‘calls’, ‘a’] mp_tac) >> impl_tac >- simp[] >>
  strip_tac >>
  qpat_x_assum ‘∀n. _ + 2 < dimword (:64)’ (qspec_then ‘SUC N’ mp_tac) >>
  qpat_x_assum ‘(SND (ehst _ _ _ _ _ _)).nxt = _’ SUBST1_TAC >>
  qpat_x_assum ‘SND (ecm _ _ _ _ _ _) ≤ _’ mp_tac >>
  qpat_x_assum ‘LENGTH _ ≤ 1’ mp_tac >>
  rpt (pop_assum kall_tac) >> simp[]
QED
