(*
  L3-09 (S4), step 3b: past the last arrival, with the listener's queue
  empty, the PF run's fetches eventually find nothing.  A fetch that
  returns data took bytes from an inbox (honestL1BInbox); a fetch that
  returns EOF or a reset marks an open connection's fd at EOF, which no
  later step undoes while the connection stays open, and no connection
  opens any more.  So the inbox total plus the number of open connections
  not at EOF never grows and falls in every round that fetches something.

  MAIN: fetch_stop.
*)
Theory honestL1BFetchStop
Ancestors
  honestL1BInbox honestL1BSettle honestL1BQueue honestL1BQuietWorld honestL1BFaith
  honestL1BRuns honestL1BStmts honestL1PFConnRun honestL1PFConn honestL1PFClient
  honestL1PFLive honestL1PFRefine honestL1PFRound honestL1PFInv honestL1PFModel
  honestL1Steps honestL1Inv honestL1Model honestL0WorldInv honestL0Part
  honestL0WorldProps honestL0Rely honestL0World honestL0
Libs
  preamble

Theorem recv_ev_data[local]:
  l0_rely w ∧ sys_recv f n w = SOME (out, w', ev) ∧ l0_res_of out = Ok k ∧ 0 < k ⇒
  recv_data ev
Proof
  rw[sys_recv_def] >> drule l0_do_cases >> rw[] >>
  ‘l0_ffi_fn «sys_recv» (fd_bytes f) (REPLICATE (13 + n) 0w) w =
     SOME (FFIreturn out (w1 with hist := w.hist ++ [(«sys_recv», fd_bytes f, REPLICATE (13 + n) 0w)]))’
    by simp[l0_ffi_fn_def] >>
  drule_all l0_ffi_fn_length >> strip_tac >>
  simp[recv_data_def, MAP_ZIP]
QED

Theorem fetch_data_event:
  ∀fs w ps ws log evs.
    pf_fetch lfd pol fs (w, ps) = SOME (ws, log, evs) ∧ l0_rely w ∧ MEM (FData g d) log ⇒
    EXISTS recv_data evs
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> IF_CASES_TAC
  >- metis_tac[]
  >> IF_CASES_TAC >> simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  imp_res_tac rplays_sys >> fs[rplays_def] >> rfs[] >>
  TRY (‘l0_rely w1’ by metis_tac[] >> first_x_assum drule_all >> simp[] >> NO_TAC) >>
  disj1_tac >> irule recv_ev_data >> metis_tac[]
QED

Theorem pround_data_event:
  pround lfd pol hs (w, ps) acts = SOME (snap, ws', log, evs) ∧ l0_rely w ∧
  MEM (FData g d) log ⇒ EXISTS recv_data evs
Proof
  rw[pround_def, AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  imp_res_tac rplays_pacts >>
  qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >> simp[pf_tail_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  imp_res_tac rplays_polls >> imp_res_tac rplays_flush >> fs[rplays_def] >> rfs[] >>
  drule fetch_data_event >> simp[] >> disch_then drule >> simp[]
QED

(* ------------------------------------------------------------------------
   Open connections not at EOF
   ------------------------------------------------------------------------ *)

Definition noeof_def:
  noeof (ps : l1p) = { f | MEM f (MAP SND ps.b.tbl) ∧ ¬MEM f ps.eof }
End

Theorem FINITE_noeof[simp]:
  FINITE (noeof ps)
Proof
  irule SUBSET_FINITE >> qexists_tac ‘set (MAP SND ps.b.tbl)’ >>
  simp[noeof_def, SUBSET_DEF]
QED

Theorem MAP_SND_ADELKEY_sub[local]:
  ∀l. MEM f (MAP SND (ADELKEY h l)) ⇒ MEM f (MAP SND l)
Proof
  Induct >> simp[ADELKEY_def, FORALL_PROD] >> rw[] >> fs[ADELKEY_def] >> metis_tac[]
QED

Theorem ALL_DISTINCT_ADELKEY[local]:
  ∀l. ALL_DISTINCT (MAP SND l) ⇒ ALL_DISTINCT (MAP SND (ADELKEY h l))
Proof
  Induct >> simp[ADELKEY_def, FORALL_PROD] >> rw[] >> fs[GSYM ADELKEY_def] >>
  metis_tac[MAP_SND_ADELKEY_sub]
QED

Theorem ALOOKUP_SND_other[local]:
  ∀l. ALL_DISTINCT (MAP SND l) ∧ ALOOKUP l h = SOME f ∧ MEM g (MAP SND (ADELKEY h l)) ⇒ g ≠ f
Proof
  Induct >> simp[ADELKEY_def, FORALL_PROD] >> rw[] >> fs[GSYM ADELKEY_def]
  >- (fs[MEM_MAP] >> strip_tac >> fs[ADELKEY_def, MEM_FILTER] >> metis_tac[])
  >> metis_tac[ALOOKUP_MEM, MEM_MAP, SND]
QED

Theorem l1do_write_tbl[local]:
  l1do lfd (w, st) (Write h bs) = SOME (r, (w', st'), evs) ⇒ st'.tbl = st.tbl
Proof
  rw[l1do_def, AllCaseEqs()] >> simp[set_outbox_def, after_send_def] >>
  every_case_tac >> simp[set_outbox_def]
QED

Theorem forget_tbl[simp]:
  (forget f st).tbl = st.tbl
Proof
  simp[forget_def, set_outbox_def]
QED

(* One action: no connection opens (nothing to accept), and an open
   connection not at EOF stays so unless it closes *)
Theorem pdo_noeof:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ ps.acq = [] ∧ ALL_DISTINCT (MAP SND ps.b.tbl) ⇒
  noeof ps' ⊆ noeof ps ∧ ps'.acq = [] ∧ ALL_DISTINCT (MAP SND ps'.b.tbl) ∧
  (∀f. MEM f (MAP SND ps'.b.tbl) ⇒ MEM f (MAP SND ps.b.tbl))
Proof
  Cases_on ‘a’ >> simp[pdo_def, AllCaseEqs()] >> rw[] >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[l1_close_def, AllCaseEqs(), set_inb_def, noeof_def, SUBSET_DEF] >>
  TRY (imp_res_tac l1do_write_tbl >> gvs[] >> NO_TAC) >>
  rw[] >> gvs[MEM_FILTER] >>
  TRY (metis_tac[ALL_DISTINCT_ADELKEY, MAP_SND_ADELKEY_sub, ALOOKUP_SND_other])
QED

Theorem pacts_noeof:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ ps.acq = [] ∧
    ALL_DISTINCT (MAP SND ps.b.tbl) ⇒
    noeof ps' ⊆ noeof ps ∧ ps'.acq = [] ∧ ALL_DISTINCT (MAP SND ps'.b.tbl) ∧
    (∀f. MEM f (MAP SND ps'.b.tbl) ⇒ MEM f (MAP SND ps.b.tbl))
Proof
  Induct >> simp[pacts_def, AllCaseEqs()] >> rpt gen_tac >> strip_tac >> gvs[] >>
  PairCases_on ‘ws1’ >>
  drule_all pdo_noeof >> strip_tac >>
  qpat_x_assum ‘∀w ps rs evs w' ps'. _’ (drule_then drule_all) >> strip_tac >>
  metis_tac[SUBSET_TRANS]
QED

(* A fetch keeps L1's tables, only adds EOFs, and an EOF or reset it
   records is new, on an fd it fetched from *)
Theorem fetch_eof:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ⇒
    ps'.b = ps.b ∧ (∀f. MEM f ps.eof ⇒ MEM f ps'.eof) ∧
    ∀f. MEM (FEof f) log ∨ MEM (FReset f) log ⇒
        MEM f ps'.eof ∧ ¬MEM f ps.eof ∧ MEM f fs ∧ f ≠ lfd
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> IF_CASES_TAC
  >- (strip_tac >> first_x_assum drule >> metis_tac[])
  >> IF_CASES_TAC >> simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >> gvs[set_inb_def] >>
  rw[] >> gvs[wants_input_def] >> metis_tac[]
QED

Theorem poll_set_tbl:
  MEM f (in_fds (pf_poll_set lfd pol ps hs)) ∧ f ≠ lfd ⇒ MEM f (MAP SND ps.b.tbl)
Proof
  simp[in_fds_def, pf_poll_set_def, MEM_MAP, MEM_FILTER, MEM_FLAT, PULL_EXISTS, EXISTS_PROD] >>
  rw[] >> gvs[] >> every_case_tac >> gvs[] >>
  metis_tac[ALOOKUP_MEM, MEM_MAP, SND]
QED

Theorem flush_tbl[local]:
  ∀fs w st w' st' evs. l1_flush fs (w, st) = SOME ((w', st'), evs) ⇒ st'.tbl = st.tbl
Proof
  Induct >> rw[l1_flush_def, AllCaseEqs()] >> res_tac >> gvs[after_send_def] >>
  every_case_tac >> gvs[set_outbox_def]
QED

Theorem reap_tbl[local]:
  ∀fs w st w' st' evs. l1_reap fs (w, st) = SOME ((w', st'), evs) ⇒ st'.tbl = st.tbl
Proof
  Induct >> rw[l1_reap_def, AllCaseEqs()] >> gvs[l1_close_def, AllCaseEqs()] >>
  TRY (PairCases_on ‘ws’) >> res_tac >> gvs[]
QED

(* The round's tail keeps L1's table, and an EOF or reset it fetches takes
   an open connection off the not-at-EOF set *)
Theorem tail_noeof:
  pf_tail lfd pol hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ⇒
  ps'.b.tbl = ps.b.tbl ∧ noeof ps' ⊆ noeof ps ∧
  ((∃f. MEM (FEof f) log ∨ MEM (FReset f) log) ⇒ noeof ps' ⊂ noeof ps)
Proof
  simp[pf_tail_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  imp_res_tac flush_tbl >> imp_res_tac reap_tbl >>
  drule fetch_eof >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac ‘l1_reap _ (_, ps3.b)’ >>
  ‘ps3.b.tbl = ps.b.tbl ∧ ps3.eof = ps3'.eof’ by simp[Abbr ‘ps3’] >>
  ‘noeof (ps3 with <| b := b4; pause := ps3.pause − 1 |>) ⊆ noeof ps’
    by (simp[noeof_def, SUBSET_DEF] >> metis_tac[]) >>
  ‘ps3.pause = ps3'.pause’ by simp[Abbr ‘ps3’] >> fs[] >>
  rpt strip_tac >> simp[PSUBSET_MEMBER] >>
  qexists_tac ‘f’ >> simp[noeof_def] >>
  ‘MEM f (MAP SND ps.b.tbl)’
    by (irule poll_set_tbl >> fs[MEM_FILTER] >> metis_tac[]) >>
  metis_tac[]
QED

Definition fmeas_def:
  fmeas (w : l0world) (ps : l1p) = tot_inbox w + CARD (noeof ps)
End

Definition log_some_def:
  log_some log ⇔ ∃f d. MEM (FData f d) log ∨ MEM (FEof f) log ∨ MEM (FReset f) log
End

Theorem pround_fmeas:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧
  ps.acq = [] ∧ ALL_DISTINCT (MAP SND ps.b.tbl) ∧
  tot_inbox w' ≤ tot_inbox w ∧ (EXISTS recv_data evs ⇒ tot_inbox w' < tot_inbox w) ∧
  l0_rely w ⇒
  fmeas w' ps' ≤ fmeas w ps ∧ (log_some log ⇒ fmeas w' ps' < fmeas w ps)
Proof
  strip_tac >>
  ‘(∃f d. MEM (FData f d) log) ⇒ EXISTS recv_data evs’
    by (strip_tac >> irule pround_data_event >> metis_tac[]) >>
  qpat_assum ‘pround _ _ _ _ _ = _’ (strip_assume_tac o SIMP_RULE (srw_ss()) [pround_def, AllCaseEqs()]) >>
  PairCases_on ‘ws1’ >> gvs[] >>
  drule_all pacts_noeof >> strip_tac >>
  drule tail_noeof >> strip_tac >>
  ‘CARD (noeof ps') ≤ CARD (noeof ps)’
    by (irule CARD_SUBSET >> simp[] >> metis_tac[SUBSET_TRANS]) >>
  simp[fmeas_def] >> rw[log_some_def]
  >- (‘tot_inbox w' < tot_inbox w’ by metis_tac[] >> decide_tac)
  >> (‘CARD (noeof ps') < CARD (noeof ps)’
        by (irule CARD_PSUBSET >> simp[] >>
            irule PSUBSET_SUBSET_TRANS >> qexists_tac ‘noeof ws11’ >> metis_tac[]) >>
      decide_tac)
QED

Theorem log_nil[local]:
  ∀l. ¬log_some l ∧ log_conns l = [] ⇒ l = []
Proof
  Induct >> simp[] >> Cases >> rw[log_some_def, log_conns_def] >> metis_tac[]
QED

(* MAIN: past the last arrival, the PF run's fetches eventually find
   nothing (unless accepts fail infinitely often) *)
Theorem fetch_stop:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ linv lfd w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ∧
  F1 lfd pol ifds m w0 ∧ S1 lfd pol ifds m w0 ∧ S2 lfd pol ifds m w0 ∧
  ¬accepts_fail lfd pol ifds m w0 ∧ quiet_after N w0 ⇒
  ∃K. ∀k. K ≤ k ⇒ rlog lfd pol ifds m w0 k = []
Proof
  strip_tac >> drule_all queue_empty >> disch_then (qx_choose_then ‘K1’ assume_tac) >>
  drule_all run_quiet >> strip_tac >>
  ‘∀k. K1 + n0 ≤ k ⇒
       fmeas (rworld lfd pol ifds m w0 (SUC k)) (rstate lfd pol ifds m w0 (SUC k)) ≤
         fmeas (rworld lfd pol ifds m w0 k) (rstate lfd pol ifds m w0 k) ∧
       (log_some (rlog lfd pol ifds m w0 k) ⇒
        fmeas (rworld lfd pol ifds m w0 (SUC k)) (rstate lfd pol ifds m w0 (SUC k)) <
          fmeas (rworld lfd pol ifds m w0 k) (rstate lfd pol ifds m w0 k))’
    by (gen_tac >> strip_tac >>
        drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
        drule_all round_facts >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
        ‘ALL_DISTINCT (MAP SND (rstate lfd pol ifds m w0 k).b.tbl)’
          by fs[pown_def, ALL_DISTINCT_APPEND] >>
        ‘(rstate lfd pol ifds m w0 k).acq = []’
          by (qpat_x_assum ‘∀k. K1 ≤ k ⇒ _’ (qspec_then ‘k’ mp_tac) >> simp[]) >>
        ‘N ≤ (rworld lfd pol ifds m w0 k).clock ∧ quiet_after N (rworld lfd pol ifds m w0 k)’
          by (qpat_x_assum ‘∀n. n0 ≤ n ⇒ _’ (qspec_then ‘k’ mp_tac) >> simp[]) >>
        drule round_fplays >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
        ‘l0_rely (rworld lfd pol ifds m w0 k)’ by metis_tac[rworld_rely] >>
        drule_all tot_quiet_trace >> strip_tac >>
        irule pround_fmeas >> metis_tac[]) >>
  qspecl_then [‘λk. fmeas (rworld lfd pol ifds m w0 k) (rstate lfd pol ifds m w0 k)’, ‘K1 + n0’]
    mp_tac (Q.GENL [‘f’, ‘K0’] noninc_stable) >>
  impl_tac >- (rw[] >> metis_tac[]) >> simp[] >> strip_tac >>
  qexists_tac ‘KK’ >> rpt strip_tac >>
  irule log_nil >> conj_tac
  >- (strip_tac >>
      ‘K1 + n0 ≤ k’ by decide_tac >>
      qpat_assum ‘∀k. KK ≤ k ⇒ _ = _’ (fn th =>
        mp_tac (Q.SPEC ‘k’ th) >> mp_tac (Q.SPEC ‘SUC k’ th)) >> simp[] >>
      qpat_x_assum ‘∀k. K1 + n0 ≤ k ⇒ _’ (qspec_then ‘k’ mp_tac) >> simp[] >>
      fs[])
  >> spose_not_then assume_tac >>
  drule_all round_conn_event >> strip_tac >>
  ‘K1 ≤ k ∧ n0 ≤ k’ by decide_tac >>
  ‘qof (rworld lfd pol ifds m w0 k) lfd = []’ by metis_tac[] >>
  ‘N ≤ (rworld lfd pol ifds m w0 k).clock ∧ quiet_after N (rworld lfd pol ifds m w0 k)’
    by metis_tac[] >>
  drule_all round_qof >> disch_then (qspec_then ‘lfd’ strip_assume_tac) >>
  ‘LENGTH (qof (rworld lfd pol ifds m w0 (SUC k)) lfd) <
   LENGTH (qof (rworld lfd pol ifds m w0 k) lfd)’ by metis_tac[] >>
  gvs[]
QED
