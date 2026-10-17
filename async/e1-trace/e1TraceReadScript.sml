(*
  The read side of the E1 -> raw-L0 trace layer (m4-server; the mirror of
  moonshotSentGlue's l0_ep_sent_run): on the trace of an E1 run, what
  l0sysEpisodes counts as episode j's received bytes (l0_ep_recvd) is what
  the endpoint layer's channel j received (its recv field), in the world
  built from the run (pew), at every round boundary.

  Two halves, met in the middle at the run's arrivals (earr):
   - the world: a channel's recv grows by exactly the data arrivals for
     it, since every tick's arrivals make sense (eh_round_ok, which E1's
     refinement gives), and the program's calls never touch recv;
   - the trace: each round's only receives are its fetch's, and in the
     fetch the episode map (ep_next) and the arrivals' client map (arrs)
     grow in lockstep (both number an accept that returned an fd next), so
     each received chunk is credited to the same number on both sides.
*)
Theory e1TraceRead
Ancestors
  moonshotSentGlue honestL1EPRefine honestL1EPOut honestL1EPModel honestL1PFOut
  honestL1PFModel honestL1Model honestL1PFRound honestL1PFRefine honestL1PFConnRun
  honestL1Steps honestL0WorldProps honestL0World honestL0 Marshalling ffiSpikeSocketFFI
  l0sysEpisodes endpointHLModel endpointFair endpointWorld
Libs
  preamble

(* ------------------------------------------------------------------------
   The world: recv is what arrived
   ------------------------------------------------------------------------ *)

(* The data arrivals for channel j *)
Definition pdata_def:
  pdata (j : num) [] = [] ∧
  pdata j (PData i bs :: as) = (if i = j then bs else []) ++ pdata j as ∧
  pdata j (_ :: as) = pdata j as
End

Theorem pdata_APPEND[simp]:
  ∀l l'. pdata j (l ++ l') = pdata j l ++ pdata j l'
Proof
  Induct >> simp[pdata_def] >> Cases >> simp[pdata_def]
QED

(* Channel j's received bytes; none for a channel not there yet *)
Definition chrecv_def:
  chrecv (w : eworld) j = if j < LENGTH w.chans then (EL j w.chans).recv else []
End

Theorem chrecv_upd:
  (∀c. (g c).recv = c.recv) ⇒ chrecv (upd_chan i g w) j = chrecv w j
Proof
  rw[chrecv_def, upd_chan_def, EL_LUPDATE] >> rw[]
QED

Theorem chrecv_new:
  c.recv = [] ⇒ chrecv (w with chans := w.chans ++ [c]) j = chrecv w j
Proof
  rw[chrecv_def, EL_APPEND1, EL_APPEND2] >> gvs[] >>
  ‘j = LENGTH w.chans’ by decide_tac >> simp[EL_APPEND2]
QED

Theorem chrecv_with[simp]:
  chrecv (w with open_fds := x) j = chrecv w j ∧
  chrecv (w with listening := y) j = chrecv w j ∧
  chrecv (w with nconnects := z) j = chrecv w j ∧
  chrecv (w with clock := c) j = chrecv w j
Proof
  simp[chrecv_def]
QED

Theorem chrecv_chans:
  chrecv w j = if j < LENGTH w.chans then (EL j w.chans).recv else []
Proof
  simp[chrecv_def]
QED

Theorem ep_deliver_recv:
  ep_arrival_ok w x ⇒ chrecv (ep_deliver w x) j = chrecv w j ++ pdata j [x]
Proof
  Cases_on ‘x’ >> simp[ep_arrival_ok_def, pdata_def] >> strip_tac
  >- (simp[ep_deliver_def] >> CASE_TAC >> simp[] >> rename1 ‘_ = y :: _’ >>
      PairCases_on ‘y’ >> simp[chrecv_def] >>
      Cases_on ‘j < LENGTH w.chans’ >> simp[EL_APPEND1] >>
      Cases_on ‘j = LENGTH w.chans’ >> simp[EL_APPEND2, new_chan_def])
  >- (simp[ep_deliver_def, chrecv_def, upd_chan_def, EL_LUPDATE] >>
      Cases_on ‘j = n’ >> simp[])
  >> simp[ep_deliver_def] >> irule chrecv_upd >> simp[]
QED

Theorem FOLDL_deliver_recv:
  ∀as w. ep_step_ok w as ⇒ chrecv (FOLDL ep_deliver w as) j = chrecv w j ++ pdata j as
Proof
  Induct >> simp[ep_step_ok_def, pdata_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[] >> drule ep_deliver_recv >> simp[] >>
  Cases_on ‘h’ >> simp[pdata_def]
QED

Theorem FOLDL_deliver_fields[simp]:
  ∀as w. (FOLDL ep_deliver w as).env = w.env ∧ (FOLDL ep_deliver w as).clock = w.clock ∧
         (FOLDL ep_deliver w as).hist = w.hist
Proof
  Induct >> simp[] >> rpt gen_tac >>
  ‘(ep_deliver w h).env = w.env ∧ (ep_deliver w h).clock = w.clock ∧
   (ep_deliver w h).hist = w.hist’
    by (Cases_on ‘h’ >> rw[ep_deliver_def, upd_chan_def] >> every_case_tac >> simp[] >>
        pairarg_tac >> simp[]) >>
  simp[]
QED

(* The program's calls: recv, the clock, the arrivals and the history stay *)
Theorem ehdo_recv:
  ehdo lfd v (w, hs) act = SOME (r, (w', hs')) ⇒
  (∀j. chrecv w' j = chrecv w j) ∧ w'.env = w.env ∧ w'.clock = w.clock ∧ w'.hist = w.hist
Proof
  Cases_on ‘act’ >> simp[ehdo_def, AllCaseEqs()] >> rw[] >>
  gvs[ep_accept_def, ep_connect_def, ep_read_def, ep_close_def, ep_conn_err_def,
      ep_send_def, ep_alloc_def, AllCaseEqs()] >>
  TRY (pairarg_tac >> gvs[]) >>
  simp[upd_chan_def] >>
  TRY (rw[chrecv_def, EL_LUPDATE] >> rw[] >> NO_TAC) >>
  TRY (simp[chrecv_new, new_chan_def] >> NO_TAC) >>
  rw[chrecv_def, EL_LUPDATE, EL_APPEND1, EL_APPEND2] >> rw[] >> gvs[] >>
  ‘j = LENGTH w.chans’ by decide_tac >> simp[EL_APPEND2, new_chan_def]
QED

Theorem ehacts_recv:
  ∀acts k w hs rs w' hs'.
    ehacts lfd lv n k (w, hs) acts = SOME (rs, (w', hs')) ⇒
    (∀j. chrecv w' j = chrecv w j) ∧ w'.env = w.env ∧ w'.clock = w.clock ∧ w'.hist = w.hist
Proof
  Induct >> simp[ehacts_def] >> rpt gen_tac >> simp[AllCaseEqs(), PULL_EXISTS] >>
  rpt gen_tac >> rename1 ‘ehdo _ _ _ _ = SOME (r, st1)’ >> PairCases_on ‘st1’ >>
  strip_tac >> drule ehdo_recv >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem ehacts_tot_recv:
  ehacts_tot lfd lv n (w, hs) acts = (rs, (w', hs')) ⇒
  (∀j. chrecv w' j = chrecv w j) ∧ w'.env = w.env ∧ w'.clock = w.clock ∧ w'.hist = w.hist
Proof
  simp[ehacts_tot_def] >> CASE_TAC >> strip_tac >> gvs[] >>
  drule ehacts_recv >> simp[]
QED

(* The run: channel j received what the ticks so far brought it *)
Theorem eh_recv_run:
  ∀n. (∀n'. n' < n ⇒ eh_round_ok lfd lv ifds m W0 n') ⇒
      (∀j. chrecv (FST (ehst lfd lv ifds m W0 n)) j =
           chrecv W0 j ++ FLAT (GENLIST (λi. pdata j (W0.env (W0.clock + i) W0.hist)) n)) ∧
      (FST (ehst lfd lv ifds m W0 n)).env = W0.env ∧
      (FST (ehst lfd lv ifds m W0 n)).clock = W0.clock + n ∧
      (FST (ehst lfd lv ifds m W0 n)).hist = W0.hist
Proof
  Induct >- simp[ehst_def, ehrounds_def] >>
  strip_tac >>
  ‘∀n'. n' < n ⇒ eh_round_ok lfd lv ifds m W0 n'’ by simp[] >>
  first_x_assum drule >> strip_tac >>
  ‘eh_round_ok lfd lv ifds m W0 n’ by simp[] >>
  Cases_on ‘ehst lfd lv ifds m W0 n’ >> rename1 ‘_ = (w, hs)’ >>
  Cases_on ‘ehacts_tot lfd lv n (w, hs) (new_actions (log_of m) (ehhist lfd lv ifds m W0 n))’ >>
  rename1 ‘_ = (rs, st1)’ >> PairCases_on ‘st1’ >> rename1 ‘_ = (rs, (w1, hs1))’ >>
  drule ehacts_tot_recv >> strip_tac >>
  ‘ep_step_ok (w1 with clock := w1.clock + 1) (w1.env w1.clock w1.hist)’
    by (qpat_x_assum ‘eh_round_ok _ _ _ _ _ n’ mp_tac >>
        REWRITE_TAC [eh_round_ok_def] >>
        disch_then (qspecl_then [‘rs’, ‘w1’, ‘hs1’] mp_tac) >>
        qpat_x_assum ‘ehst _ _ _ _ _ n = _’ (fn th => REWRITE_TAC [th]) >>
        qpat_x_assum ‘ehacts_tot _ _ _ _ _ = _’ (fn th => REWRITE_TAC [th]) >> simp[]) >>
  ‘ehst lfd lv ifds m W0 (SUC n) =
   (ep_tick w1, SND (SND (ehpoll lfd hs1 (ifds (ehhist lfd lv ifds m W0 n)) w1)))’
    by (qpat_x_assum ‘ehst _ _ _ _ _ n = _’ mp_tac >>
        simp[ehst_def, ehhist_def, ehrounds_def] >>
        Cases_on ‘ehrounds lfd lv ifds m W0 n’ >> simp[] >> strip_tac >> gvs[] >>
        qpat_x_assum ‘ehacts_tot _ _ _ _ _ = _’ mp_tac >> simp[ehhist_def] >> strip_tac >>
        simp[ehpoll_def]) >>
  simp[ep_tick_def] >> fs[] >>
  drule FOLDL_deliver_recv >> simp[GENLIST, SNOC_APPEND]
QED

(* ------------------------------------------------------------------------
   The trace: episode j's receives are the run's data arrivals for j
   ------------------------------------------------------------------------ *)

Theorem name_recvd:
  ev_name ev ≠ ExtCall «sys_recv» ⇒ ev_recvd ev = NONE
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event n _ _’ >> Cases_on ‘n’ >>
  simp[ev_name_def, ev_recvd_def]
QED

Theorem ep_io_norecv:
  ∀evs opn n. EVERY (λev. ev_recvd ev = NONE) evs ⇒ ep_io ev_recvd j opn n evs = []
Proof
  Induct >> simp[ep_io_def] >> rpt gen_tac >> strip_tac >> every_case_tac >> fs[]
QED

Theorem names_norecv:
  EVERY (λev. ev_name ev ≠ ExtCall «sys_recv») evs ⇒ EVERY (λev. ev_recvd ev = NONE) evs
Proof
  rw[EVERY_MEM] >> res_tac >> irule name_recvd >> simp[]
QED

Theorem bytes_fd_fd_bytes[simp]:
  bytes_fd (fd_bytes f) = f ∧ LENGTH (fd_bytes f) = 8
Proof
  simp[bytes_fd_def, fd_bytes_def, LENGTH_n2w8] >>
  ‘w82n (fd_bytes f) = w2n f’ by simp[] >> fs[fd_bytes_def]
QED

(* A receive on f: episode j gets its bytes when f is j's fd *)
Theorem sys_recv_recvd:
  sys_recv f n w = SOME (out, w1, ev) ∧ l0_rely w ⇒
  ev_new ev = NONE ∧
  ev_recvd ev = case l0_res_of out of
                | Ok k => SOME (f, TAKE k (DROP 13 out))
                | Fail _ _ => NONE
Proof
  strip_tac >>
  ‘∃bl. ev = IO_event (ExtCall «sys_recv») (fd_bytes f) bl ∧ MAP SND bl = out’
    by (gvs[sys_recv_def] >> drule_all l0_do_ev >> simp[]) >>
  simp[ev_other, ev_recvd_def, l0_res_of_def, l0_hdr_def] >>
  Cases_on ‘dec_res out’ >> simp[] >> CASE_TAC >> simp[]
QED

(* The fetch: as the log's arrivals number them, from the same map *)
Theorem pf_fetch_recvd:
  ∀fs w ps w' ps' log evs opn k.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ l0_rely w ∧ fds_lt w ∧
    MEM 0w (l0_used w) ∧ (∀f. MEM f fs ∧ f ≠ lfd ⇒ ALOOKUP opn f ≠ NONE) ⇒
    ep_io ev_recvd j opn k evs = pdata j (MAP (conv a) (FST (arrs lfd (opn, k) log)))
Proof
  Induct >- simp[pf_fetch_def, ep_io_def, arrs_def, pdata_def] >>
  rpt gen_tac >> rename1 ‘pf_fetch _ _ (f :: fs)’ >> strip_tac >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ mp_tac >> simp[Once pf_fetch_def] >>
  IF_CASES_TAC
  >- (strip_tac >> first_x_assum irule >> simp[] >> metis_tac[]) >>
  IF_CASES_TAC
  >- (qpat_x_assum ‘f = lfd’ SUBST_ALL_TAC >>
      Cases_on ‘sys_accept lfd w’ >> simp[] >> rename1 ‘_ = SOME x’ >>
      PairCases_on ‘x’ >> rename1 ‘sys_accept _ _ = SOME (out, w1, ev)’ >> simp[] >>
      pairarg_tac >> simp[] >> rename1 ‘_ = (ps1, fl1)’ >>
      Cases_on ‘pf_fetch lfd pol fs (w1, ps1)’ >> simp[] >> rename1 ‘_ = SOME y’ >>
      PairCases_on ‘y’ >> simp[] >> strip_tac >> gvs[] >>
      drule_all sys_accept_new >> strip_tac >>
      ‘ev_recvd ev = NONE’
        by (irule name_recvd >> gvs[sys_accept_def] >> drule l0_do_cases >> rw[] >>
            simp[ev_name_def]) >>
      ‘l0_rely w1’
        by (qpat_assum ‘sys_accept _ _ = _’ (assume_tac o REWRITE_RULE [sys_accept_def]) >>
            drule_all l0_do_rely >> simp[]) >>
      ‘fds_lt w1’ by (drule_all sys_accept_fds_lt >> simp[]) >>
      ‘MEM 0w (l0_used w1)’
        by (qpat_assum ‘sys_accept _ _ = _’ (assume_tac o REWRITE_RULE [sys_accept_def]) >>
            drule l0_do_used >> simp[]) >>
      Cases_on ‘l0_res_of out’ >> gvs[ep_io_def, arrs_def]
      >- (rename1 ‘l0_res_of out = Ok v’ >>
          ‘(n2w v : word64) ≠ 0w’
            by (strip_tac >> qpat_x_assum ‘v MOD _ ≠ 0’ mp_tac >>
                pop_assum (mp_tac o AP_TERM “w2n:word64->num”) >> simp[]) >> simp[] >>
          first_x_assum (drule_then (qspecl_then [‘(n2w v, k) :: opn’, ‘k + 1’] mp_tac)) >>
          impl_tac >- (simp[] >> rw[] >> fs[]) >>
          pairarg_tac >> simp[conv_def, pdata_def]) >>
      first_x_assum irule >> simp[] >> metis_tac[]) >>
  Cases_on ‘sys_recv f pf_chunk w’ >> simp[] >> rename1 ‘_ = SOME x’ >>
  PairCases_on ‘x’ >> rename1 ‘sys_recv _ _ _ = SOME (out, w1, ev)’ >> simp[] >>
  pairarg_tac >> simp[] >> rename1 ‘_ = (ps1, fl1)’ >>
  Cases_on ‘pf_fetch lfd pol fs (w1, ps1)’ >> simp[] >> rename1 ‘_ = SOME y’ >>
  PairCases_on ‘y’ >> simp[] >> strip_tac >> gvs[] >>
  drule_all sys_recv_recvd >> strip_tac >>
  ‘l0_rely w1’
    by (qpat_assum ‘sys_recv _ _ _ = _’ (assume_tac o REWRITE_RULE [sys_recv_def]) >>
        drule_all l0_do_rely >> simp[]) >>
  ‘l0_used w1 = l0_used w ∧ w1.fd_limit = w.fd_limit’
    by (qpat_assum ‘sys_recv _ _ _ = _’ (assume_tac o REWRITE_RULE [sys_recv_def]) >>
        imp_res_tac l0_do_env >> drule l0_do_used >> simp[]) >>
  ‘fds_lt w1’ by gvs[honestL0WorldPropsTheory.fds_lt_def] >>
  ‘∃i. ALOOKUP opn f = SOME i’
    by (Cases_on ‘ALOOKUP opn f’ >> simp[] >> first_x_assum (qspec_then ‘f’ mp_tac) >>
        simp[]) >>
  ‘ep_io ev_recvd j opn k y3 = pdata j (MAP (conv a) (FST (arrs lfd (opn, k) y2)))’
    by (first_x_assum (drule_then irule) >> simp[] >> metis_tac[]) >>
  ‘cl opn f = i’ by simp[cl_def] >>
  simp[ep_io_def, arrs_APPEND] >>
  Cases_on ‘arrs lfd (opn, k) y2’ >>
  Cases_on ‘l0_res_of out’ >> gvs[]
  >- (rename1 ‘l0_res_of out = Ok kk’ >> Cases_on ‘0 < kk’ >> gvs[] >>
      simp[arrs_def, conv_def, pdata_def]) >>
  Cases_on ‘l1_transient e’ >> gvs[arrs_def, conv_def, pdata_def]
QED

(* Polls, sends, closes and connerrs neither open episodes nor receive *)
Theorem names_quiet:
  EVERY (λev. ev_name ev = ExtCall n) evs ∧ n ≠ «sys_connect» ∧ n ≠ «sys_accept» ∧
  n ≠ «sys_recv» ⇒
  EVERY (λev. ev_new ev = NONE) evs ∧ EVERY (λev. ev_recvd ev = NONE) evs
Proof
  rw[EVERY_MEM] >> res_tac
  >- (irule name_new >> simp[]) >>
  irule name_recvd >> simp[]
QED

Theorem ep_io_quiet:
  EVERY (λev. ev_new ev = NONE) evs ∧ EVERY (λev. ev_recvd ev = NONE) evs ⇒
  ∀o1 n1. ep_io ev_recvd j o1 n1 evs = [] ∧ FOLDL ep_next (o1, n1) evs = (o1, n1)
Proof
  metis_tac[ep_io_norecv, ep_io_nonew]
QED

(* A round's tail: its receives are the fetch log's data arrivals *)
Theorem etail_recvd:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, tevs) ∧ l0_rely w ∧ fds_lt w ∧
  MEM 0w (l0_used w) ∧ (∀f. MEM f (MAP SND es.p.b.tbl) ⇒ ALOOKUP opn f ≠ NONE) ⇒
  ep_io ev_recvd j opn kk tevs = pdata j (MAP (conv a) (FST (arrs lfd (opn, kk) log)))
Proof
  strip_tac >>
  qpat_x_assum ‘etail _ _ _ _ = _’ mp_tac >> simp[etail_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >>
  drule l1_polls_names >> strip_tac >> drule l1_flush_names >> strip_tac >>
  drule l1_reap_names >> strip_tac >> drule settle_fds_names >> strip_tac >>
  drule_all l1_polls_l0 >> strip_tac >> drule_all l1_flush_l0 >> strip_tac >>
  ‘fds_lt w2 ∧ MEM 0w (l0_used w2)’
    by (qpat_x_assum ‘fds_lt w’ mp_tac >> qpat_x_assum ‘MEM 0w (l0_used w)’ mp_tac >>
        simp[honestL0WorldPropsTheory.fds_lt_def]) >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ assume_tac >>
  drule pf_fetch_recvd >> disch_then (qspecl_then [‘j’, ‘a’, ‘opn’, ‘kk’] mp_tac) >>
  impl_tac
  >- (simp[MEM_FILTER] >> rpt strip_tac >>
      qpat_x_assum ‘MEM f (in_fds _)’ (strip_assume_tac o REWRITE_RULE [in_fds_pend]) >>
      drule honestL1PFRefineTheory.in_fds_poll_set >> simp[] >> strip_tac >>
      qpat_x_assum ‘∀f. MEM f (MAP SND _) ⇒ _’ (qspec_then ‘f’ mp_tac) >> simp[]) >>
  strip_tac >>
  ‘∀o1 n1. ep_io ev_recvd j o1 n1 pevs = [] ∧ FOLDL ep_next (o1, n1) pevs = (o1, n1)’
    by (irule ep_io_quiet >> ONCE_REWRITE_TAC [CONJ_COMM] >> irule names_quiet >> qexists_tac ‘«sys_poll»’ >> simp[]) >>
  ‘∀o1 n1. ep_io ev_recvd j o1 n1 fevs = [] ∧ FOLDL ep_next (o1, n1) fevs = (o1, n1)’
    by (irule ep_io_quiet >> ONCE_REWRITE_TAC [CONJ_COMM] >> irule names_quiet >> qexists_tac ‘«sys_send»’ >> simp[]) >>
  ‘∀o1 n1. ep_io ev_recvd j o1 n1 cevs = [] ∧ FOLDL ep_next (o1, n1) cevs = (o1, n1)’
    by (irule ep_io_quiet >> ONCE_REWRITE_TAC [CONJ_COMM] >> irule names_quiet >> qexists_tac ‘«sys_close»’ >> simp[]) >>
  ‘∀o1 n1. ep_io ev_recvd j o1 n1 sevs = [] ∧ FOLDL ep_next (o1, n1) sevs = (o1, n1)’
    by (irule ep_io_quiet >> ONCE_REWRITE_TAC [CONJ_COMM] >> irule names_quiet >> qexists_tac ‘«sys_connerr»’ >> simp[]) >>
  qpat_x_assum ‘_ = tevs’ (SUBST_ALL_TAC o SYM) >>
  asm_rewrite_tac[ep_io_append, APPEND_NIL, APPEND, FOLDL_APPEND, pairTheory.FST, pairTheory.SND]
QED

(* After round n's actions, every table fd is in the round's client map
   (ecm1): ev_acts' ev_rel there, set up as in l1ep_refines_ehl_upto_sent *)
Theorem tbl_ecm1:
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n'. n' ≤ SUC n ⇒ SND (ecm lfd pol ifds m w0 n') + 1 < dimword (:64)) ∧
  erounds lfd pol ifds m (w0, einit) (SUC n) = SOME (hh, wss, evss, logss) ⇒
  ∃rs aevs wl1 es1.
    eacts_of lfd pol ifds m w0 n = SOME (rs, aevs, (wl1, es1)) ∧
    ∀f. MEM f (MAP SND es1.p.b.tbl) ⇒ MEM f (MAP FST (FST (ecm1 lfd pol ifds m w0 n)))
Proof
  strip_tac >> qabbrev_tac ‘lv = elv lfd pol ifds m w0’ >>
  qpat_assum ‘erounds _ _ _ _ _ (SUC _) = _’
    (strip_assume_tac o SIMP_RULE (srw_ss()) [AllCaseEqs()] o
     ONCE_REWRITE_RULE [erounds_def]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  mp_tac (Q.INST [‘N’ |-> ‘SUC n’] l1ep_refines_ehl_upto_sent) >> impl_tac >- fs[] >>
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
          EL i rs = ELvl (lv n (0 + i))’
    by (rpt strip_tac >>
        qpat_assum ‘eacts _ _ _ _ = _’ assume_tac >>
        qpat_assum ‘erounds _ _ _ _ _ n = _’ assume_tac >>
        drule_all level_true >> strip_tac >> simp[Abbr ‘lv’]) >>
  qpat_x_assum ‘eacts _ _ _ _ = _’ assume_tac >>
  drule_all ev_acts >> strip_tac >>
  ‘cnew (LENGTH w.chans) (rfds ws11 rs) = cnew k fs’ by simp[Abbr ‘fs’] >>
  qexistsl_tac [‘rs’, ‘aevs’, ‘ws10’, ‘ws11’] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum ‘ecm1 _ _ _ _ _ _ = _’ (fn th => REWRITE_TAC [th, pairTheory.FST]) >>
  rpt strip_tac >>
  ‘ALL_DISTINCT (MAP FST ws11.p.b.tbl)’
    by (qpat_x_assum ‘eown lfd ws11’ mp_tac >> simp[eown_def, pown_def]) >>
  ‘∃hd. ALOOKUP ws11.p.b.tbl hd = SOME f’
    by (qpat_x_assum ‘MEM f (MAP SND _)’ mp_tac >> simp[MEM_MAP, EXISTS_PROD] >>
        strip_tac >> qexists_tac ‘p_1’ >> irule ALOOKUP_ALL_DISTINCT_MEM >> simp[]) >>
  qpat_x_assum ‘ev_rel _ _ (cnew (LENGTH w.chans) _ ++ cm) ws11 _’
    (strip_assume_tac o REWRITE_RULE [ev_rel_def]) >>
  qpat_x_assum ‘cnew (LENGTH w.chans) _ = cnew k fs’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  first_x_assum drule >> simp[]
QED

(* A round's actions receive nothing (their reads come from the inboxes) *)
Theorem edo_norecv:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ⇒ EVERY (λev. ev_recvd ev = NONE) evs
Proof
  Cases_on ‘∃p. a = EConnect p’
  >- (gvs[] >> simp[edo_def, AllCaseEqs()] >> rw[] >> gvs[sys_connect_def] >>
      drule l0_do_cases >> rw[] >> simp[ev_recvd_def]) >>
  strip_tac >> drule edo_names >> impl_tac >- metis_tac[] >>
  simp[EVERY_MEM] >> rpt strip_tac >> res_tac >> irule name_recvd >> simp[]
QED

Theorem eacts_norecv:
  ∀acts w es rs evs w' es'.
    eacts lfd pol (w, es) acts = SOME (rs, evs, (w', es')) ⇒
    EVERY (λev. ev_recvd ev = NONE) evs
Proof
  Induct >> simp[eacts_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  rename1 ‘edo _ _ _ _ = SOME (r1, ws1, evs1)’ >> PairCases_on ‘ws1’ >> gvs[] >>
  drule edo_norecv >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem pdata_rsettles[simp]:
  pdata j (rsettles cm es es') = []
Proof
  simp[rsettles_def] >> qmatch_goalsub_abbrev_tac ‘MAP _ l’ >> pop_assum kall_tac >>
  Induct_on ‘l’ >> simp[pairTheory.FORALL_PROD, pdata_def]
QED

Theorem pdata_esett[simp]:
  pdata j (esett lfd pol ifds m w0 n) = []
Proof
  simp[esett_def] >> every_case_tac >> simp[pdata_def]
QED

(* The run: episode j's receives are the data arrivals for channel j, tick by tick *)
Theorem l0_ep_recvd_run:
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧ MEM 0w (l0_used w0) ∧
  (∀n. SND (ecm lfd pol ifds m w0 n) + 1 < dimword (:64)) ⇒
  ∀n h ws evs logs.
    erounds lfd pol ifds m (w0, einit) n = SOME (h, ws, evs, logs) ⇒
    ∀j. l0_ep_recvd j evs = FLAT (GENLIST (λi. pdata j (earr lfd a pol ifds m w0 i)) n)
Proof
  strip_tac >> Induct
  >- simp[erounds_def, l0_ep_recvd_def, ep_io_def] >>
  rpt gen_tac >> strip_tac >> gen_tac >>
  qpat_assum ‘erounds _ _ _ _ _ (SUC _) = _’
    (strip_assume_tac o SIMP_RULE (srw_ss()) [AllCaseEqs()] o
     ONCE_REWRITE_RULE [erounds_def]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  first_x_assum drule >> strip_tac >>
  mp_tac l0_ep_sent_run >> impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qpat_assum ‘erounds _ _ _ _ _ n = _’ o mp_then Any mp_tac) >> strip_tac >>
  qpat_x_assum ‘eround _ _ _ _ _ = _’ mp_tac >> simp[eround_def, AllCaseEqs()] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rename1 ‘eacts _ _ ws' _ = SOME (rs, aevs, ws1)’ >>
  PairCases_on ‘ws'’ >> PairCases_on ‘ws1’ >> PairCases_on ‘ws’ >> fs[] >>
  mp_tac (Q.INST [‘N’ |-> ‘SUC n’] l1ep_refines_ehl_upto_sent) >> impl_tac >- fs[] >>
  disch_then (fn th =>
    qspecl_then [‘n’, ‘h'’, ‘(ws'0, ws'1)’, ‘evs'’, ‘logs'’] mp_tac th >>
    qspecl_then [‘SUC n’, ‘h' ++ [ssnap rdy rs]’, ‘(ws0, ws1)’, ‘evs' ++ aevs ++ tevs’,
                 ‘logs' ++ [log]’] mp_tac th) >>
  simp[] >> rpt (disch_then strip_assume_tac) >>
  ‘∃cm k. ecm lfd pol ifds m w0 n = (cm, k)’ by metis_tac[pairTheory.PAIR] >>
  ‘okeys ws'1.p.b’
    by (qpat_x_assum ‘sent_inv (FST (ecm _ _ _ _ _ n)) _ _ _’ mp_tac >> simp[sent_inv_def]) >>
  ‘∀i rs0 evs0 wi esi.
     i ≤ LENGTH (new_actions (log_of m) h') ∧
     eacts lfd pol (ws'0, ws'1) (TAKE i (new_actions (log_of m) h')) =
     SOME (rs0, evs0, (wi, esi)) ⇒ eown lfd esi’
    by (qpat_x_assum ‘∀n'. n' < SUC n ⇒ eround_own _ _ _ _ _ _’ (qspec_then ‘n’ mp_tac) >>
        simp[eround_own_def] >> disch_then drule >> simp[]) >>
  qpat_x_assum ‘eacts _ _ _ _ = _’ assume_tac >>
  drule_all eacts_fd0 >> strip_tac >>
  ‘FOLDL ep_next (cm, k) aevs = (cnew k (rfds ws11 rs) ++ cm, k + LENGTH (rfds ws11 rs))’
    by (qpat_x_assum ‘eacts _ _ (ws'0, ws'1) _ = _’ assume_tac >>
        drule eacts_ep >> disch_then (qspecl_then [‘j’, ‘cm’, ‘cm’, ‘k’] mp_tac) >>
        impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >> simp[]) >>
  ‘∀o1 n1. ep_io ev_recvd j o1 n1 aevs = []’
    by (rpt gen_tac >> irule ep_io_norecv >>
        qpat_x_assum ‘eacts _ _ (ws'0, ws'1) _ = _’ (ACCEPT_TAC o MATCH_MP eacts_norecv)) >>
  ‘eacts_of lfd pol ifds m w0 n = SOME (rs, aevs, (ws10, ws11))’
    by (qpat_x_assum ‘erounds _ _ _ _ _ n = _’ mp_tac >> simp[eacts_of_def]) >>
  ‘econ lfd pol ifds m w0 n = rfds ws11 rs’ by simp[econ_def] >>
  ‘ecm1 lfd pol ifds m w0 n = (cnew k (rfds ws11 rs) ++ cm, k + LENGTH (rfds ws11 rs))’
    by simp[ecm1_def] >>
  ‘elog lfd pol ifds m w0 n = log’
    by (‘LENGTH logs' = n’
          by (qpat_x_assum ‘erounds _ _ _ _ _ n = _’ assume_tac >>
              drule erounds_logs >> simp[]) >>
        qpat_x_assum ‘erounds _ _ _ _ _ (SUC n) = _’ assume_tac >>
        drule elog_EL >> disch_then (qspec_then ‘n’ mp_tac) >> simp[EL_APPEND2]) >>
  ‘∀f. MEM f (MAP SND ws11.p.b.tbl) ⇒ ALOOKUP (cnew k (rfds ws11 rs) ++ cm) f ≠ NONE’
    by (qpat_x_assum ‘erounds _ _ _ _ _ (SUC n) = _’ assume_tac >>
        drule_at (Pos last) tbl_ecm1 >>
        impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
                     rpt strip_tac >>
                     qpat_x_assum ‘∀n'. SND _ + 1 < _’ (qspec_then ‘n'’ mp_tac) >> simp[]) >>
        strip_tac >> rename1 ‘eacts_of _ _ _ _ _ _ = SOME (rs1, aevs1, (wl1, es1))’ >>
        ‘es1 = ws11’
          by (qpat_x_assum ‘eacts_of _ _ _ _ _ _ = SOME (rs, _, _)’ (fn th =>
                qpat_x_assum ‘eacts_of _ _ _ _ _ _ = SOME (rs1, _, _)’
                  (mp_tac o REWRITE_RULE [th])) >> simp[]) >>
        qpat_x_assum ‘es1 = ws11’ SUBST_ALL_TAC >>
        qpat_x_assum ‘ecm1 _ _ _ _ _ _ = _’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
        rpt strip_tac >>
        qpat_x_assum ‘ALOOKUP _ f = NONE’ (mp_tac o REWRITE_RULE [ALOOKUP_NONE]) >>
        qpat_x_assum ‘∀f. MEM f (MAP SND ws11.p.b.tbl) ⇒ _’ drule >> simp[]) >>
  ‘ep_io ev_recvd j (cnew k (rfds ws11 rs) ++ cm) (k + LENGTH (rfds ws11 rs)) tevs =
   pdata j (MAP (conv a) (FST (arrs lfd (cnew k (rfds ws11 rs) ++ cm,
                                          k + LENGTH (rfds ws11 rs)) log)))’
    by (qpat_x_assum ‘etail _ _ _ _ = _’
          (fn th => irule (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] etail_recvd) th)) >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        qpat_x_assum ‘fd0_ok ws10 ws11’ mp_tac >> simp[fd0_ok_def]) >>
  ‘FOLDL ep_next ([], 0) evs' = (cm, k)’ by fs[] >>
  simp[l0_ep_recvd_def, ep_io_append, FOLDL_APPEND, GENLIST, SNOC_APPEND, FLAT_APPEND] >>
  qpat_x_assum ‘∀j. l0_ep_recvd j evs' = _’ (fn th => simp[GSYM th, l0_ep_recvd_def]) >>
  simp[earr_def]
QED

(* G2: episode j received exactly what the layer's channel j received *)
Theorem e1_l0_ep_recvd:
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧ MEM 0w (l0_used w0) ∧
  (∀n. SND (ecm lfd pol ifds m w0 n) + 1 < dimword (:64)) ⇒
  ∀n h ws evs logs j.
    erounds lfd pol ifds m (w0, einit) n = SOME (h, ws, evs, logs) ⇒
    l0_ep_recvd j evs =
    chrecv (FST (ehst lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) n)) j
Proof
  rpt strip_tac >>
  mp_tac l0_ep_recvd_run >> impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (drule_then (qspec_then ‘j’ SUBST1_TAC)) >>
  mp_tac l1ep_refines_ehl >> impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (drule_then strip_assume_tac) >>
  drule eh_recv_run >> strip_tac >>
  simp[] >> simp[chrecv_def, pew_def]
QED
