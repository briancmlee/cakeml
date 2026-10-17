(*
  flush_live without the bare broken and gone disjuncts (for the echo's
  main form, whose only excuses are an observed hard error and the write
  timeout).  On a broken channel L0's send never takes a byte (l0_send:
  every broken branch fails; broken_send is a world choice, possibly a
  transient error for ever), and poll may never report the fd writable.
  But the D23 write timeout does not need sends to fail hard: an outbox
  that the flush cannot shrink is a stalled round, so within pf_sendwait
  rounds L1 drops it (rdrop), unless a send failed hard first.  And gone
  is set only by a hard send failure or a drop (run_gone_cause).
*)
Theory honestL1PFBroken
Ancestors
  honestL1PFD16 honestL1PFStream honestL1PFS4w honestL1PFInput honestL1PFOutLive honestL1PFDead honestL1PFFlushLive
  honestL1PFOut honestL1PFConn honestL1PFInv honestL1PFFlush honestL1PFConnRun honestL1PFLive honestL1PFRound honestL1PFRefine
  honestL1PFModel honestL1Steps honestL1Props honestL1Model honestL0WorldInv honestL0Rely
  honestL0World honestL0
Libs
  preamble

(* ------------------------------------------------------------------------
   A broken channel stays broken, and nothing more is sent on it
   ------------------------------------------------------------------------ *)

Definition bks_def:
  bks c sb w ⇔ c < LENGTH w.chans ∧ (EL c w.chans).broken ∧ csent w c = sb
End

Theorem bks_upd:
  bks c sb w ∧ (j = c ⇒ ∀x. x.broken ⇒ (g x).broken ∧ (g x).sent = x.sent) ⇒
  bks c sb (upd_lchan j g w)
Proof
  rw[bks_def, upd_lchan_def, csent_def, EL_LUPDATE] >> rw[] >> gvs[csent_def]
QED

Theorem bks_fields[simp]:
  (bks c sb (w with listeners := x) ⇔ bks c sb w) ∧
  (bks c sb (w with open_fds := y) ⇔ bks c sb w) ∧
  (bks c sb (w with hist := h) ⇔ bks c sb w) ∧
  (bks c sb (w with clock := k) ⇔ bks c sb w) ∧
  (bks c sb (w with reserved := r) ⇔ bks c sb w)
Proof
  simp[bks_def, csent_def]
QED

Theorem bks_FOLDL_break:
  ∀q w. bks c sb w ⇒ bks c sb (FOLDL (λw j. upd_lchan j (break_lchan e F) w) w q)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  irule bks_upd >> rw[break_lchan_def]
QED

Theorem bks_deliver:
  bks c sb w ⇒ bks c sb (l0_deliver w a)
Proof
  strip_tac >> Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >> gvs[] >>
  TRY (irule bks_upd >> rw[break_lchan_def] >> gvs[bks_def] >> NO_TAC) >>
  gvs[bks_def, EL_APPEND1, csent_def]
QED

Theorem bks_tick:
  bks c sb w ⇒ bks c sb (l0_tick nm w)
Proof
  simp[l0_tick_def] >>
  ‘∀as w. bks c sb w ⇒ bks c sb (FOLDL l0_deliver w as)’
    by (Induct >> simp[] >> metis_tac[bks_deliver]) >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem bks_ticks:
  ∀k w. bks c sb w ⇒ bks c sb (l0_ticks nm k w)
Proof
  Induct >> simp[l0_ticks_def] >> metis_tac[bks_tick]
QED

Theorem bks_call:
  l0_call n conf bytes w = SOME (FFIreturn bytes' w') ∧ n ≠ «sys_connect» ∧
  bks c sb w ⇒ bks c sb w'
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  TRY (gvs[l0_listen_def, AllCaseEqs()] >> NO_TAC) >>
  TRY (irule bks_ticks >> simp[] >> NO_TAC) >>
  TRY (gvs[l0_recv_def, l0_shutdown_def, l0_connerr_def, AllCaseEqs(), fail_def] >>
       irule bks_upd >> simp[] >> NO_TAC) >>
  TRY (gvs[l0_recv_def, l0_shutdown_def, l0_connerr_def, AllCaseEqs(), fail_def] >> NO_TAC) >>
  TRY (gvs[l0_send_def, AllCaseEqs(), fail_def] >>
       irule bks_upd >> simp[] >> strip_tac >> gvs[bks_def] >> NO_TAC) >>
  TRY (gvs[l0_send_def, AllCaseEqs(), fail_def] >> NO_TAC) >>
  TRY (gvs[l0_accept_def, AllCaseEqs(), fail_def] >>
       TRY (irule bks_upd >> rw[break_lchan_def]) >> NO_TAC) >>
  gvs[l0_close_def, AllCaseEqs(), fail_def] >> simp[close_fd_def] >> every_case_tac >>
  gvs[] >>
  TRY (irule bks_FOLDL_break >> simp[] >> NO_TAC) >>
  TRY (simp[] >> NO_TAC) >>
  irule bks_upd >> simp[]
QED

Theorem wpres_bks:
  wpres (bks c sb)
Proof
  rw[wpres_def] >- (irule bks_tick >> simp[]) >>
  drule_all bks_call >> simp[]
QED

Theorem run_bks:
  oassm lfd pol ifds m w0 ∧ bks c sb (rworld lfd pol ifds m w0 k) ⇒
  ∀d. bks c sb (rworld lfd pol ifds m w0 (k + d))
Proof
  strip_tac >> ‘run_ok lfd pol ifds m w0’ by fs[oassm_def] >>
  ‘∀n. winv (rworld lfd pol ifds m w0 n)’ by metis_tac[winv_run, oassm_def] >>
  Induct >> simp[] >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k + d’] strip_assume_tac) >>
  simp[ADD_CLAUSES] >> drule_at (Pos last) pround_wpres >>
  disch_then (qspec_then ‘bks c sb’ mp_tac) >> simp[wpres_bks] >>
  ‘SUC (d + k) = SUC (k + d)’ by simp[] >> pop_assum SUBST1_TAC >> simp[]
QED

(* ------------------------------------------------------------------------
   Without an accept, f keeps its channel (or is closed)
   ------------------------------------------------------------------------ *)

Definition fat_def:
  fat f c (w : l0world) ⇔ ∀j. ALOOKUP w.open_fds f = SOME j ⇒ j = c
End

Theorem fat_tick:
  fat f c w ⇒ fat f c (l0_tick nm w)
Proof
  simp[fat_def]
QED

Theorem fat_call:
  l0_call n conf bytes w = SOME (FFIreturn bytes' w') ∧ n ≠ «sys_accept» ∧
  n ≠ «sys_connect» ∧ fat f c w ⇒ fat f c w'
Proof
  rw[fat_def] >> first_x_assum irule >>
  gvs[l0_call_def, AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  TRY (gvs[l0_listen_def, AllCaseEqs()] >> NO_TAC) >>
  TRY (‘∀k w. (l0_ticks «sys_poll» k w).open_fds = w.open_fds’
         by (Induct >> simp[l0_ticks_def]) >> gvs[] >> NO_TAC) >>
  TRY (gvs[l0_shutdown_def, AllCaseEqs(), fail_def, upd_lchan_def] >> NO_TAC) >>
  imp_res_tac ops_open_fds >> gvs[]
QED

Theorem sys_fat:
  (fat f c w ∧ sys_send g bs w = SOME (out, w', ev) ⇒ fat f c w') ∧
  (fat f c w ∧ sys_close g w = SOME (out, w', ev) ⇒ fat f c w') ∧
  (fat f c w ∧ sys_recv g k w = SOME (out, w', ev) ⇒ fat f c w') ∧
  (fat f c w ∧ sys_poll fes w = SOME (out, w', ev) ⇒ fat f c w')
Proof
  rpt conj_tac >> strip_tac >> gvs[sys_close_def, sys_send_def, sys_recv_def, sys_poll_def] >>
  TRY (drule l0_do_buf_cases >> strip_tac >> gvs[] >>
       drule fat_call >> disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >>
  impl_tac >- (simp[] >> irule fat_tick >> simp[]) >> fs[fat_def] >> NO_TAC) >>
  drule l0_do_cases >> strip_tac >> gvs[] >>
  drule fat_call >> disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >>
  impl_tac >- (simp[] >> irule fat_tick >> simp[]) >> fs[fat_def]
QED

Theorem pdo_fat:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ fat f c w ⇒ fat f c w'
Proof
  strip_tac >> Cases_on ‘a’ >> gvs[pdo_def, AllCaseEqs()] >>
  TRY (PairCases_on ‘z’) >> gvs[] >>
  rpt (qpat_x_assum ‘l1do _ _ _ = _’ mp_tac) >> rpt (qpat_x_assum ‘l1_close _ _ = _’ mp_tac) >>
  simp[l1do_def, l1_close_def, AllCaseEqs()] >> rw[] >> metis_tac[sys_fat]
QED

Theorem pacts_fat:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ fat f c w ⇒ fat f c w'
Proof
  Induct >> simp[pacts_def] >> rw[AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  metis_tac[pdo_fat]
QED

Theorem l1_polls_fat:
  ∀chs w rv w' evs. l1_polls chs w = SOME (rv, w', evs) ∧ fat f c w ⇒ fat f c w'
Proof
  Induct >> simp[l1_polls_def] >> rw[AllCaseEqs()] >> metis_tac[sys_fat]
QED

(* A send on a broken channel fails *)
Theorem sys_send_broken:
  sys_send f bs w = SOME (out, w', ev) ∧ winv w ∧ fat f c w ∧
  bks c sb w ⇒ ∃e x. l0_res_of out = Fail e x
Proof
  rw[sys_send_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  qabbrev_tac ‘wt = l0_tick «sys_send» w’ >>
  ‘l0_rely wt’
    by (gvs[Abbr ‘wt’, winv_def] >> irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  ‘bks c sb wt’ by (simp[Abbr ‘wt’] >> irule bks_tick >> simp[]) >>
  ‘fat f c wt’ by simp[Abbr ‘wt’, fat_tick] >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def, l0_hdr_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  ‘LENGTH (fd_bytes f) = 8’ by simp[] >>
  ‘bytes_fd (TAKE 8 (fd_bytes f ++ bs)) = f’ by simp[TAKE_APPEND1, TAKE_LENGTH_ID_rwt] >>
  gvs[] >>
  ‘∃e x. r = Fail e x’
    by (gvs[l0_send_def, AllCaseEqs(), fail_def, bks_def, not_chan_def] >>
        rw[] >> gvs[fat_def, l0_chan_of_def, AllCaseEqs()] >> res_tac >> gvs[]) >>
  ‘l0_res_ok r’
    by (gvs[l0_res_ok_def, l0_rely_def] >>
        qpat_x_assum ‘l0_send _ _ _ = _’ mp_tac >>
        rw[l0_send_def, AllCaseEqs(), fail_def, not_chan_def] >> simp[]) >>
  simp[l0_res_of_enc]
QED

Theorem sys_send_open_fds:
  sys_send g bs w = SOME (out, w', ev) ⇒ w'.open_fds = w.open_fds
Proof
  rw[sys_send_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def, l0_hdr_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule (cj 1 ops_open_fds) >> simp[]
QED

(* The flush on a broken channel: f's outbox is as it was, unless a send
   on f failed hard *)
Theorem l1_flush_broken:
  ∀fs w b w' b' evs.
    l1_flush fs (w, b) = SOME ((w', b'), evs) ∧ winv w ∧ fat f c w ∧
    bks c sb w ⇒
    outbox_of b' f = outbox_of b f ∨ hard_send f evs
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (first_x_assum drule_all >> simp[]) >>
  gvs[AllCaseEqs()] >>
  ‘winv w''’ by metis_tac[sys_winv] >>
  ‘bks c sb w''’
    by (mp_tac wpres_bks >> strip_tac >> drule_all sys_wpres >> strip_tac >> res_tac) >>
  ‘fat f c w''’ by metis_tac[sys_fat] >>
  Cases_on ‘h = f’
  >- (gvs[] >> drule_all sys_send_broken >> strip_tac >>
      Cases_on ‘l1_transient e’
      >- (‘after_send f (l0_res_of out) b = b’ by simp[after_send_def] >>
          first_x_assum drule_all >> rw[] >> gvs[hard_send_def] >> metis_tac[MEM])
      >> disj2_tac >>
      drule_all sys_send_hard >> simp[hard_send_def] >> metis_tac[MEM]) >>
  first_x_assum drule_all >> simp[outbox_of_after_send_other] >>
  rw[] >> gvs[hard_send_def] >> metis_tac[MEM]
QED


Theorem l1_flush_fat:
  ∀fs w b w' b' evs. l1_flush fs (w, b) = SOME ((w', b'), evs) ∧ fat f c w ⇒ fat f c w'
Proof
  Induct >> simp[l1_flush_def] >> rw[AllCaseEqs()] >> metis_tac[sys_fat]
QED

(* ------------------------------------------------------------------------
   A round on a broken channel
   ------------------------------------------------------------------------ *)

(* A round from a broken channel, with no hard send on f, that leaves f
   held with output: its stall count rises by one *)
Theorem broken_round:
  oassm lfd pol ifds m w0 ∧ fat f c (rworld lfd pol ifds m w0 k) ∧
  bks c sb (rworld lfd pol ifds m w0 k) ∧ ¬hard_send f (rrev lfd pol ifds m w0 k) ∧
  outbox_of (rstate lfd pol ifds m w0 (SUC k)).b f ≠ [] ∧
  MEM f (MAP SND (rstate lfd pol ifds m w0 (SUC k)).b.tbl ++
         (rstate lfd pol ifds m w0 (SUC k)).b.closing) ⇒
  scount (rstate lfd pol ifds m w0 (SUC k)) f = scount (rstate lfd pol ifds m w0 k) f + 1
Proof
  strip_tac >> ‘run_ok lfd pol ifds m w0’ by fs[oassm_def] >>
  ‘∀n. winv (rworld lfd pol ifds m w0 n)’ by metis_tac[winv_run, oassm_def] >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
  ‘ALL_DISTINCT (MAP FST (rstate lfd pol ifds m w0 (SUC k)).stalls)’
    by metis_tac[run_window_inv] >>
  qpat_x_assum ‘pround _ _ _ _ _ = _’ mp_tac >>
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >> gvs[] >>
  ‘scount ws11 f = scount (rstate lfd pol ifds m w0 k) f’
    by (drule pacts_stalls >> simp[scount_def]) >>
  ‘winv ws10 ∧ bks c sb ws10 ∧ fat f c ws10’
    by metis_tac[pacts_winv, pacts_wpres, wpres_bks, pacts_fat] >>
  drule tail_le >> disch_then (qspec_then ‘f’ strip_assume_tac) >>
  ‘outbox_of (rstate lfd pol ifds m w0 (SUC k)).b f = outbox_of ws11.b f’
    by (qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >> simp[pf_tail_def, AllCaseEqs()] >>
        strip_tac >>
        qpat_x_assum ‘_ = rrev _ _ _ _ _ _’ (SUBST_ALL_TAC o SYM) >>
        qpat_x_assum ‘_ = rstate _ _ _ _ _ (SUC k)’ (SUBST_ALL_TAC o SYM) >> fs[] >>
        ‘winv w1 ∧ bks c sb w1 ∧ fat f c w1’
          by metis_tac[l1_polls_winv, l1_polls_wpres, wpres_bks, l1_polls_fat] >>
        drule_all l1_flush_broken >> strip_tac >> fs[] >>
        TRY (qpat_x_assum ‘pevs ++ fevs ++ gevs ++ cevs = _’ (SUBST_ALL_TAC o SYM) >>
             fs[] >> NO_TAC) >>
        drule pf_fetch_b >> strip_tac >> fs[] >>
        drule l1_reap_le >> disch_then (qspec_then ‘f’ strip_assume_tac) >>
        fs[stall_step_drops, honestL1PFModelTheory.FOLDL_drop_out] >>
        every_case_tac >> fs[]) >>
  ‘MEM (f, scount ws11 f + 1) (rstate lfd pol ifds m w0 (SUC k)).stalls’
    by (qpat_x_assum ‘_ ∧ _ ∧ _ ⇒ MEM _ _’ irule >> fs[]) >>
  ‘ALOOKUP (rstate lfd pol ifds m w0 (SUC k)).stalls f = SOME (scount ws11 f + 1)’
    by (irule ALOOKUP_ALL_DISTINCT_MEM >> fs[]) >>
  qpat_x_assum ‘scount ws11 f = _’ (fn th => fs[th]) >>
  qabbrev_tac ‘s0 = scount (rstate lfd pol ifds m w0 k) f’ >> fs[scount_def]
QED

(* From a good round on a broken channel: within pf_sendwait rounds, a
   send on f fails hard, or the write timeout drops f, or f's outbox has
   emptied (all the server wrote is taken) *)
Theorem good_broken_window:
  oassm lfd pol ifds m w0 ∧ good lfd pol ifds m w0 f c j k ∧
  (EL c (rworld lfd pol ifds m w0 k).chans).broken ⇒
  ∀d. (∃i. k ≤ i ∧ i < k + d ∧
           (hard_send f (rrev lfd pol ifds m w0 i) ∨ rdrop lfd pol ifds m w0 i f)) ∨
      (∃i. k ≤ i ∧ i ≤ k + d ∧
           csent (rworld lfd pol ifds m w0 i) c = oout lfd pol ifds m w0 j i) ∨
      (good lfd pol ifds m w0 f c j (k + d) ∧
       bks c (csent (rworld lfd pol ifds m w0 k) c) (rworld lfd pol ifds m w0 (k + d)) ∧
       outbox_of (rstate lfd pol ifds m w0 (k + d)).b f ≠ [] ∧
       d ≤ scount (rstate lfd pol ifds m w0 (k + d)) f)
Proof
  strip_tac >>
  qabbrev_tac ‘sb = csent (rworld lfd pol ifds m w0 k) c’ >>
  ‘bks c sb (rworld lfd pol ifds m w0 k)’
    by (gvs[good_def, bks_def, Abbr ‘sb’, l0_chan_of_def, AllCaseEqs()]) >>
  ‘∀i. good lfd pol ifds m w0 f c j i ⇒ fat f c (rworld lfd pol ifds m w0 i)’
    by (rw[good_def, fat_def, l0_chan_of_def, AllCaseEqs()] >> gvs[]) >>
  ‘∀i. good lfd pol ifds m w0 f c j i ∧ outbox_of (rstate lfd pol ifds m w0 i).b f = [] ⇒
       csent (rworld lfd pol ifds m w0 i) c = oout lfd pol ifds m w0 j i’
    by (rw[good_def] >> gvs[]) >>
  Induct
  >- (Cases_on ‘outbox_of (rstate lfd pol ifds m w0 k).b f = []’
      >- (disj2_tac >> disj1_tac >> qexists_tac ‘k’ >> simp[Abbr ‘sb’])
      >> disj2_tac >> disj2_tac >> gvs[Abbr ‘sb’]) >>
  pop_assum strip_assume_tac >>
  TRY (disj1_tac >> qexists_tac ‘i’ >> simp[] >> NO_TAC) >>
  TRY (disj2_tac >> disj1_tac >> qexists_tac ‘i’ >> simp[] >> NO_TAC) >>
  drule_all good_step >> strip_tac
  >- (disj1_tac >> qexists_tac ‘k + d’ >> simp[])
  >- (disj1_tac >> qexists_tac ‘k + d’ >> simp[])
  >- (disj2_tac >> disj1_tac >> qexists_tac ‘SUC (k + d)’ >> simp[ADD_CLAUSES])
  >> ‘bks c sb (rworld lfd pol ifds m w0 (k + SUC d))’
       by (drule_all run_bks >> disch_then (qspec_then ‘1’ mp_tac) >> simp[ADD1]) >>
  Cases_on ‘hard_send f (rrev lfd pol ifds m w0 (k + d))’
  >- (disj1_tac >> qexists_tac ‘k + d’ >> simp[]) >>
  Cases_on ‘outbox_of (rstate lfd pol ifds m w0 (SUC (k + d))).b f = []’
  >- (disj2_tac >> disj1_tac >> qexists_tac ‘SUC (k + d)’ >>
      rpt conj_tac >- simp[] >- simp[] >>
      qpat_x_assum ‘∀i. good _ _ _ _ _ _ _ _ i ∧ _ ⇒ _’ irule >> simp[])
  >> disj2_tac >> disj2_tac >> gvs[ADD_CLAUSES] >>
  ‘MEM f (MAP SND (rstate lfd pol ifds m w0 (SUC (d + k))).b.tbl ++
          (rstate lfd pol ifds m w0 (SUC (d + k))).b.closing)’
    by (‘run_ok lfd pol ifds m w0’ by fs[oassm_def] >>
        drule_all run_rel >> disch_then (qspec_then ‘SUC (d + k)’ strip_assume_tac) >>
        gvs[out_rel_def, okeys_def] >> metis_tac[]) >>
  ‘scount (rstate lfd pol ifds m w0 (SUC (d + k))) f =
   scount (rstate lfd pol ifds m w0 (d + k)) f + 1’
    by (irule broken_round >> simp[] >> qexistsl [‘c’, ‘sb’] >> gvs[] >> metis_tac[]) >>
  simp[]
QED

(* ------------------------------------------------------------------------
   flush_live without the bare broken disjunct
   ------------------------------------------------------------------------ *)

Definition ofin2_def:
  ofin2 lfd pol ifds m w0 f c wr k k' ⇔
    wr ≼ csent (rworld lfd pol ifds m w0 k') c ∨
    ∃i. k ≤ i ∧ i < k' ∧
        (hard_send f (rrev lfd pol ifds m w0 i) ∨ rdrop lfd pol ifds m w0 i f)
End

Theorem ofin2_mono:
  ofin2 lfd pol ifds m w0 f c wr k k' ∧ n ≤ k ⇒ ofin2 lfd pol ifds m w0 f c wr n k'
Proof
  rw[ofin2_def] >> simp[] >> disj2_tac >> qexists_tac ‘i’ >> simp[]
QED

(* From a good round on a broken channel, whatever is owed: a later round
   has taken it, or a send on f failed hard, or the timeout dropped f *)
Theorem good_broken_fin:
  oassm lfd pol ifds m w0 ∧ good lfd pol ifds m w0 f c j k ∧
  (EL c (rworld lfd pol ifds m w0 k).chans).broken ∧ wr ≼ oout lfd pol ifds m w0 j k ⇒
  ∃k'. k ≤ k' ∧ ofin2 lfd pol ifds m w0 f c wr k k'
Proof
  strip_tac >> drule_all good_broken_window >>
  disch_then (qspec_then ‘pf_sendwait’ strip_assume_tac) >>
  TRY (qexists_tac ‘k + pf_sendwait’ >> simp[ofin2_def] >> disj2_tac >>
       qexists_tac ‘i’ >> simp[] >> NO_TAC) >>
  TRY (qexists_tac ‘i’ >> simp[ofin2_def] >> disj1_tac >>
       ‘oout lfd pol ifds m w0 j k ≼ oout lfd pol ifds m w0 j i’
         by (drule good_oout_mono >> disch_then (qspec_then ‘i’ mp_tac) >> simp[]) >>
       qpat_x_assum ‘csent _ c = _’ SUBST1_TAC >>
       irule IS_PREFIX_TRANS >> qexists_tac ‘oout lfd pol ifds m w0 j k’ >> simp[] >>
       NO_TAC) >>
  ‘run_ok lfd pol ifds m w0’ by fs[oassm_def] >>
  drule run_scount_lt >> disch_then (qspecl_then [‘f’, ‘k + pf_sendwait’] mp_tac) >>
  strip_tac >> fs[]
QED

Theorem good_progress2:
  oassm lfd pol ifds m w0 ∧ F1 lfd pol ifds m w0 ∧ F2 w0 ∧
  drains lfd pol ifds m w0 c ∧ nshut w0 ∧
  good lfd pol ifds m w0 f c j k ∧ wr ≼ oout lfd pol ifds m w0 j k ∧
  ¬(wr ≼ csent (rworld lfd pol ifds m w0 k) c) ⇒
  ∃k'. k < k' ∧
       (ofin2 lfd pol ifds m w0 f c wr k k' ∨
        (good lfd pol ifds m w0 f c j k' ∧
         LENGTH (csent (rworld lfd pol ifds m w0 k) c) <
         LENGTH (csent (rworld lfd pol ifds m w0 k') c)))
Proof
  strip_tac >>
  drule_all good_owed >> strip_tac >>
  drule_all good_olive >> strip_tac >>
  ‘l0_chan_of (rworld lfd pol ifds m w0 k) f = SOME c’ by fs[good_def] >>
  mp_tac (Q.INST [‘n’ |-> ‘k’] flush_progress_nshut) >>
  (impl_tac >- fs[oassm_def]) >>
  disch_then (qx_choose_then ‘k1’ (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  drule_all good_iter >> disch_then (qspec_then ‘k1 − k’ mp_tac) >>
  ‘k + (k1 − k) = k1’ by simp[] >> pop_assum SUBST1_TAC >>
  disch_then DISJ_CASES_TAC
  >- ((* finished in a round before k1 *)
      pop_assum (qx_choose_then ‘i’ strip_assume_tac) >>
      qexists_tac ‘SUC i’ >> simp[] >> disj1_tac >> simp[ofin2_def] >>
      TRY (disj2_tac >> qexists_tac ‘i’ >> simp[] >> NO_TAC) >>
      disj1_tac >> irule IS_PREFIX_TRANS >>
      qexists_tac ‘oout lfd pol ifds m w0 j k’ >> simp[] >>
      qpat_x_assum ‘csent _ c = _’ SUBST1_TAC >>
      irule good_oout_mono >> simp[] >> metis_tac[]) >>
  (* good at k1: its round *)
  pop_assum strip_assume_tac >>
  ‘wr ≼ oout lfd pol ifds m w0 j k1’
    by (irule IS_PREFIX_TRANS >> qexists_tac ‘oout lfd pol ifds m w0 j k’ >> simp[] >>
        irule good_oout_mono >> simp[] >> metis_tac[]) >>
  ‘wr ≼ oout lfd pol ifds m w0 j (SUC k1)’
    by (irule IS_PREFIX_TRANS >> qexists_tac ‘oout lfd pol ifds m w0 j k1’ >> simp[] >>
        irule good_oout_mono >> simp[] >> metis_tac[]) >>
  drule_all good_step >> disch_then (fn th => STRIP_ASSUME_TAC th) >>
  TRY (qexists_tac ‘SUC k1’ >> simp[] >> disj1_tac >> simp[ofin2_def] >>
       disj2_tac >> qexists_tac ‘k1’ >> simp[] >> NO_TAC) >>
  TRY (qexists_tac ‘SUC k1’ >> simp[] >> disj1_tac >> simp[ofin2_def] >> NO_TAC) >>
  qpat_x_assum ‘(∃ev. _) ∨ _’ strip_assume_tac
  >- ((* a send on f that L1 does not retry *)
      Cases_on ‘wr ≼ csent (rworld lfd pol ifds m w0 k1) c’
      >- (qexists_tac ‘k1’ >> Cases_on ‘k1 = k’ >> gvs[] >> simp[ofin2_def])
      >> ‘outbox_of (rstate lfd pol ifds m w0 k1).b f ≠ []’ by metis_tac[good_owed] >>
      drule_all good_send >> strip_tac
      >- (qexists_tac ‘SUC k1’ >> simp[] >> disj2_tac >>
          imp_res_tac IS_PREFIX_LENGTH >>
          Cases_on ‘evs_sent f (rrev lfd pol ifds m w0 k1)’ >> gvs[])
      >> qexists_tac ‘SUC k1’ >> simp[] >> disj1_tac >> simp[ofin2_def] >>
      disj2_tac >> qexists_tac ‘k1’ >> simp[])
  >- ((* f's outbox emptied: everything written is taken *)
      qexists_tac ‘SUC k1’ >> simp[] >> disj1_tac >> simp[ofin2_def] >> disj1_tac >>
      qpat_x_assum ‘good _ _ _ _ _ _ _ _ (SUC k1)’ mp_tac >> simp[good_def] >>
      strip_tac >> gvs[])
  >> (* the channel broke: the write timeout or a hard send ends it *)
  ‘wr ≼ oout lfd pol ifds m w0 j (SUC k1)’ by simp[] >>
  drule_all good_broken_fin >> strip_tac >>
  qexists_tac ‘k'’ >> simp[] >> disj1_tac >> irule ofin2_mono >> qexists_tac ‘SUC k1’ >> simp[]
QED

Theorem good_finish2:
  oassm lfd pol ifds m w0 ∧ F1 lfd pol ifds m w0 ∧ F2 w0 ∧
  drains lfd pol ifds m w0 c ∧ nshut w0 ⇒
  ∀d k. good lfd pol ifds m w0 f c j k ∧ n ≤ k ∧ wr ≼ oout lfd pol ifds m w0 j k ∧
        LENGTH wr − LENGTH (csent (rworld lfd pol ifds m w0 k) c) = d ⇒
        ∃n'. k ≤ n' ∧ ofin2 lfd pol ifds m w0 f c wr n n'
Proof
  strip_tac >> completeInduct_on ‘d’ >> rpt strip_tac >>
  Cases_on ‘wr ≼ csent (rworld lfd pol ifds m w0 k) c’
  >- (qexists_tac ‘k’ >> simp[ofin2_def]) >>
  drule_all good_progress2 >> strip_tac
  >- (qexists_tac ‘k'’ >> simp[] >> irule ofin2_mono >> metis_tac[]) >>
  ‘wr ≼ oout lfd pol ifds m w0 j k'’
    by (irule IS_PREFIX_TRANS >> qexists_tac ‘oout lfd pol ifds m w0 j k’ >> simp[] >>
        irule good_oout_mono >> simp[] >> metis_tac[]) >>
  ‘csent (rworld lfd pol ifds m w0 k') c ≼ oout lfd pol ifds m w0 j k'’
    by (qpat_x_assum ‘good _ _ _ _ _ _ _ _ k'’ mp_tac >> simp[good_def] >> strip_tac >>
        qpat_x_assum ‘_ ++ _ = oout _ _ _ _ _ _ _’ (SUBST1_TAC o SYM) >> simp[]) >>
  Cases_on ‘wr ≼ csent (rworld lfd pol ifds m w0 k') c’
  >- (qexists_tac ‘k'’ >> simp[ofin2_def]) >>
  ‘LENGTH (csent (rworld lfd pol ifds m w0 k') c) < LENGTH wr’
    by (CCONTR_TAC >>
        qspecl_then [‘oout lfd pol ifds m w0 j k'’, ‘wr’,
                     ‘csent (rworld lfd pol ifds m w0 k') c’] mp_tac prefixes_is_prefix_total >>
        simp[] >> strip_tac >> imp_res_tac IS_PREFIX_LENGTH >>
        ‘csent (rworld lfd pol ifds m w0 k') c = wr’
          by (irule (iffLR IS_PREFIX_LENGTH_ANTI) >> simp[]) >>
        gvs[]) >>
  first_x_assum (qspec_then ‘LENGTH wr − LENGTH (csent (rworld lfd pol ifds m w0 k') c)’ mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qspec_then ‘k'’ mp_tac) >> simp[] >> strip_tac >>
  qexists_tac ‘n'’ >> simp[]
QED

(* MAIN: flush_live with excuses only an observed hard send error or the
   write timeout's drop, in a window from n on; or f was already gone at n,
   where run_gone_cause gives the earlier hard send or drop *)
Theorem flush_live2:
  oassm lfd pol ifds m w0 ∧ F1 lfd pol ifds m w0 ∧ F2 w0 ∧
  drains lfd pol ifds m w0 c ∧ nshut w0 ∧
  (MEM f (MAP SND (rstate lfd pol ifds m w0 n).b.tbl) ∨
   MEM f (rstate lfd pol ifds m w0 n).b.closing) ∧
  l0_chan_of (rworld lfd pol ifds m w0 n) f = SOME c ⇒
  ∃n'. n ≤ n' ∧
       ((EL (cl (FST (pcm lfd pol ifds m w0 n)) f)
            (FST (hst lfd ifds m (psk lfd pol ifds m w0) n)).clients).outgoing ≼
          csent (rworld lfd pol ifds m w0 n') c ∨
        MEM f (rstate lfd pol ifds m w0 n).b.gone ∨
        ∃k. n ≤ k ∧ k < n' ∧
            (hard_send f (rrev lfd pol ifds m w0 k) ∨ rdrop lfd pol ifds m w0 k f))
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  Cases_on ‘MEM f (rstate lfd pol ifds m w0 n).b.gone’
  >- (qexists_tac ‘n’ >> simp[]) >>
  ‘good lfd pol ifds m w0 f c (cl (FST (pcm lfd pol ifds m w0 n)) f) n’
    by (irule good_init >> fs[]) >>
  mp_tac (Q.INST [‘j’ |-> ‘cl (FST (pcm lfd pol ifds m w0 n)) f’,
                  ‘wr’ |-> ‘oout lfd pol ifds m w0 (cl (FST (pcm lfd pol ifds m w0 n)) f) n’]
                 good_finish2) >>
  (impl_tac >- fs[]) >>
  disch_then (qspecl_then
    [‘LENGTH (oout lfd pol ifds m w0 (cl (FST (pcm lfd pol ifds m w0 n)) f) n) −
      LENGTH (csent (rworld lfd pol ifds m w0 n) c)’, ‘n’] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac ‘n'’ >> fs[ofin2_def, oout_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   gone, by cause
   ------------------------------------------------------------------------ *)

Theorem pacts_gone:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ winv w ∧ MEM f ps'.b.gone ⇒
    MEM f ps.b.gone ∨ hard_send f evs
Proof
  Induct >> simp[pacts_def] >> rw[AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  ‘winv ws10’ by metis_tac[pdo_winv] >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  drule_all pdo_gone >> strip_tac >> simp[]
QED

(* A round makes f gone only by a hard send failure on f or a timeout drop *)
Theorem pround_gone:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧ winv w ∧
  MEM f ps'.b.gone ⇒
  MEM f ps.b.gone ∨ hard_send f evs ∨ MEM f (round_drops lfd pol hs (w, ps) acts)
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >> gvs[] >>
  qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >> simp[pf_tail_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  simp[round_drops_def, tail_drops_def] >>
  ‘winv ws10’ by metis_tac[pacts_winv] >>
  ‘winv w1’ by metis_tac[l1_polls_winv] >>
  drule l1_reap_gone >> disch_then drule >> strip_tac >>
  gvs[stall_gone] >>
  drule pf_fetch_b >> strip_tac >> gvs[] >>
  drule_all l1_flush_gone >> strip_tac >> simp[] >>
  drule_all pacts_gone >> strip_tac >> simp[]
QED

(* MAIN: f gone at round n was made gone by a hard send failure on f or a
   timeout drop, at a round k < n at whose start f was not gone, and f has
   stayed gone since *)
Theorem run_gone_cause:
  oassm lfd pol ifds m w0 ⇒
  ∀n. MEM f (rstate lfd pol ifds m w0 n).b.gone ⇒
      ∃k. k < n ∧ ¬MEM f (rstate lfd pol ifds m w0 k).b.gone ∧
          (hard_send f (rrev lfd pol ifds m w0 k) ∨ rdrop lfd pol ifds m w0 k f) ∧
          ∀i. k < i ∧ i ≤ n ⇒ MEM f (rstate lfd pol ifds m w0 i).b.gone
Proof
  strip_tac >> ‘run_ok lfd pol ifds m w0’ by fs[oassm_def] >>
  ‘∀n. winv (rworld lfd pol ifds m w0 n)’ by metis_tac[winv_run, oassm_def] >>
  Induct
  >- simp[rstate_def, prun_0, pinit_def, l1init_def] >>
  strip_tac >>
  Cases_on ‘MEM f (rstate lfd pol ifds m w0 n).b.gone’
  >- (first_x_assum drule >> strip_tac >> qexists_tac ‘k’ >> simp[] >>
      rpt strip_tac >> Cases_on ‘i = SUC n’ >> gvs[]) >>
  qexists_tac ‘n’ >> simp[] >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘n’] strip_assume_tac) >>
  drule pround_gone >> simp[rdrop_def] >>
  disch_then (qspec_then ‘f’ mp_tac) >> simp[] >> strip_tac >> simp[] >>
  rpt strip_tac >> ‘i = SUC n’ by simp[] >> gvs[]
QED

(* An fd with output pending, or gone, is held (tbl or closing): okeys *)
Theorem run_okeys_held:
  oassm lfd pol ifds m w0 ∧
  (outbox_of (rstate lfd pol ifds m w0 n).b f ≠ [] ∨
   MEM f (rstate lfd pol ifds m w0 n).b.gone) ⇒
  MEM f (MAP SND (rstate lfd pol ifds m w0 n).b.tbl) ∨
  MEM f (rstate lfd pol ifds m w0 n).b.closing
Proof
  strip_tac >> drule run_rel >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  gvs[out_rel_def, okeys_def]
QED

(* ------------------------------------------------------------------------
   flush_live with its window: the least round flush_live2 names, with f
   held (and output pending, not gone) at every round before it
   ------------------------------------------------------------------------ *)

(* MAIN: as flush_live2, at the first round it names: n' = n if f was gone
   at n, and n' = SUC k for the excuse at round k; at every round of
   [n, n') f is held with output pending and not gone *)
Theorem flush_live3:
  oassm lfd pol ifds m w0 ∧ F1 lfd pol ifds m w0 ∧ F2 w0 ∧
  drains lfd pol ifds m w0 c ∧ nshut w0 ∧
  (MEM f (MAP SND (rstate lfd pol ifds m w0 n).b.tbl) ∨
   MEM f (rstate lfd pol ifds m w0 n).b.closing) ∧
  l0_chan_of (rworld lfd pol ifds m w0 n) f = SOME c ⇒
  ∃n'. n ≤ n' ∧
       (∀i. n ≤ i ∧ i < n' ⇒
            (MEM f (MAP SND (rstate lfd pol ifds m w0 i).b.tbl) ∨
             MEM f (rstate lfd pol ifds m w0 i).b.closing) ∧
            outbox_of (rstate lfd pol ifds m w0 i).b f ≠ [] ∧
            ¬MEM f (rstate lfd pol ifds m w0 i).b.gone) ∧
       ((EL (cl (FST (pcm lfd pol ifds m w0 n)) f)
            (FST (hst lfd ifds m (psk lfd pol ifds m w0) n)).clients).outgoing ≼
          csent (rworld lfd pol ifds m w0 n') c ∨
        n' = n ∧ MEM f (rstate lfd pol ifds m w0 n).b.gone ∨
        ∃k. SUC k = n' ∧
            (hard_send f (rrev lfd pol ifds m w0 k) ∨ rdrop lfd pol ifds m w0 k f))
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  qabbrev_tac ‘j = cl (FST (pcm lfd pol ifds m w0 n)) f’ >>
  qabbrev_tac ‘P = λx. n ≤ x ∧
     (oout lfd pol ifds m w0 j n ≼ csent (rworld lfd pol ifds m w0 x) c ∨
      MEM f (rstate lfd pol ifds m w0 n).b.gone ∨
      ∃k. n ≤ k ∧ k < x ∧
          (hard_send f (rrev lfd pol ifds m w0 k) ∨ rdrop lfd pol ifds m w0 k f))’ >>
  ‘∃x. P x’
    by (drule_all flush_live2 >> strip_tac >> qexists_tac ‘n'’ >>
        simp[Abbr ‘P’, oout_def, Abbr ‘j’] >> metis_tac[]) >>
  qspec_then ‘P’ mp_tac WOP >> (impl_tac >- metis_tac[]) >>
  disch_then (qx_choose_then ‘n'’ strip_assume_tac) >>
  qexists_tac ‘n'’ >>
  ‘n ≤ n'’ by fs[Abbr ‘P’] >> simp[] >>
  (* the excuses, at the least round *)
  reverse conj_tac
  >- (‘(EL j (FST (hst lfd ifds m (psk lfd pol ifds m w0) n)).clients).outgoing =
       oout lfd pol ifds m w0 j n’ by simp[oout_def] >>
      pop_assum SUBST1_TAC >>
      ‘∀y. P y ⇒ n' ≤ y’
        by (rpt strip_tac >> spose_not_then assume_tac >> ‘y < n'’ by simp[] >> res_tac) >>
      qpat_x_assum ‘P n'’ mp_tac >> simp[Abbr ‘P’] >> rpt strip_tac >> simp[]
      >- (first_x_assum (qspec_then ‘n’ mp_tac) >> simp[]) >>
      rpt disj2_tac >> qexists_tac ‘k’ >> simp[] >>
      first_x_assum (qspec_then ‘SUC k’ mp_tac) >>
      (impl_tac >- (simp[] >> rpt disj2_tac >> qexists_tac ‘k’ >> simp[])) >>
      simp[]) >>
  (* the window: no round before n' satisfies P *)
  rpt gen_tac >> strip_tac >>
  ‘¬P i’ by (first_x_assum irule >> simp[]) >>
  ‘¬MEM f (rstate lfd pol ifds m w0 n).b.gone’ by (strip_tac >> fs[Abbr ‘P’]) >>
  ‘good lfd pol ifds m w0 f c j n’ by (simp[Abbr ‘j’] >> irule good_init >> fs[]) >>
  drule_all good_iter >> disch_then (qspec_then ‘i − n’ mp_tac) >>
  ‘n + (i − n) = i’ by simp[] >> pop_assum SUBST1_TAC >> strip_tac
  >- ((* an excuse before i: P i *)
      qpat_x_assum ‘¬P i’ mp_tac >> simp[Abbr ‘P’] >> metis_tac[])
  >- (qpat_x_assum ‘¬P i’ mp_tac >> simp[Abbr ‘P’] >> metis_tac[])
  >- ((* everything written taken at SUC i' ≤ i: P (SUC i') *)
      ‘P (SUC i')’ suffices_by
        (strip_tac >> ‘SUC i' < n'’ by simp[] >> res_tac) >>
      qunabbrev_tac ‘P’ >> BETA_TAC >> (conj_tac >- simp[]) >> disj1_tac >>
      qpat_x_assum ‘csent _ c = _’ SUBST1_TAC >>
      irule good_oout_mono >> simp[] >> metis_tac[]) >>
  ‘¬MEM f (rstate lfd pol ifds m w0 i).b.gone’ by fs[good_def] >>
  ‘outbox_of (rstate lfd pol ifds m w0 i).b f ≠ []’
    by (strip_tac >> ‘P i’ suffices_by simp[] >>
        qunabbrev_tac ‘P’ >> BETA_TAC >> (conj_tac >- simp[]) >> disj1_tac >>
        ‘csent (rworld lfd pol ifds m w0 i) c = oout lfd pol ifds m w0 j i’
          by (qpat_x_assum ‘good _ _ _ _ _ _ _ _ i’ mp_tac >> simp[good_def]) >>
        pop_assum SUBST1_TAC >> irule good_oout_mono >> simp[] >> metis_tac[]) >>
  simp[] >> irule run_okeys_held >> simp[]
QED

(* ------------------------------------------------------------------------
   live_data without HD16: an orderly EOF needs no hypothesis
   (pround_feof); a hard error is kept as a disjunct, with f kept (fopen)
   through the round that observed it
   ------------------------------------------------------------------------ *)

(* MAIN: what was in front of f's inbox at n0 reaches the fetch log while
   f stays open; or f's channel really broke and was flushed; or a recv on
   f failed hard at a round k ≥ n0, f kept through rounds n0 .. k *)
Theorem live_data_hr:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ∧
  F1 lfd pol ifds m w0 ∧ S1 lfd pol ifds m w0 ∧ S3w lfd pol ifds m w0 ∧
  pol_ok hw pol ∧ S4w lfd pol hw ifds m w0 f ⇒
  ∀R n0 h. ALOOKUP (rstate lfd pol ifds m w0 n0).b.tbl h = SOME f ∧
           ¬MEM f (rstate lfd pol ifds m w0 n0).eof ∧ fl (rworld lfd pol ifds m w0 n0) f R ⇒
           (∃d. fopen lfd pol ifds m w0 h f n0 d ∧ R ≼ fdata f (rlogs lfd pol ifds m w0 n0 d)) ∨
           (∃k. n0 ≤ k ∧ flushed (rworld lfd pol ifds m w0 k) f) ∨
           ∃k. n0 ≤ k ∧ fopen lfd pol ifds m w0 h f n0 (SUC (k − n0)) ∧
               MEM (FReset f) (rlog lfd pol ifds m w0 k) ∧
               hard_recv f (rrev lfd pol ifds m w0 k)
Proof
  rpt strip_tac >>
  drule_all stream_progress >> strip_tac
  >- (CCONTR_TAC >>
      pop_assum (strip_assume_tac o SIMP_RULE bool_ss [NOT_EXISTS_THM, DE_MORGAN_THM]) >>
      ‘fds_lt w0’ by fs[winv_def] >>
      drule_all fkeep_run >> strip_tac >>
      drule_all stream_upto >> disch_then (qspec_then ‘d’ strip_assume_tac) >> gvs[] >>
      TRY (metis_tac[] >> NO_TAC) >>
      ‘winv (rworld lfd pol ifds m w0 k)’ by (drule_all winv_run >> simp[]) >>
      drule prun_round' >> disch_then (qspecl_then [‘f’, ‘k’] strip_assume_tac) >>
      ‘fopen lfd pol ifds m w0 h f n0 (SUC (k − n0))’
        by (fs[fopen_def] >> rpt strip_tac >> ‘i < d’ by decide_tac >> metis_tac[]) >>
      Cases_on ‘MEM (FReset f) (rlog lfd pol ifds m w0 k)’
      >- (drule_all pround_freset >> strip_tac >> metis_tac[]) >>
      ‘MEM (FEof f) (rlog lfd pol ifds m w0 k)’
        by (gvs[fend_def, EXISTS_MEM] >> metis_tac[]) >>
      drule_all pround_feof >> strip_tac
      >- (‘n0 + (k − n0) = k’ by decide_tac >>
          ‘fdata f (rlogs lfd pol ifds m w0 n0 (k − n0)) ++ R' ≼
           fdata f (rlogs lfd pol ifds m w0 n0 (SUC (k − n0)))’
            by (REWRITE_TAC [rlogs_SUC] >> fs[]) >>
          metis_tac[])
      >> ‘n0 ≤ SUC k’ by decide_tac >> metis_tac[])
  >> disj1_tac >> qexists_tac ‘d’ >> simp[]
QED

(* ------------------------------------------------------------------------
   Closing flushes: the round that releases f (held at k, not at SUC k)
   leaves everything the server wrote to f's client taken, unless f was
   already gone, or the round failed a send on f hard, or dropped f
   ------------------------------------------------------------------------ *)

Theorem close_flushed:
  oassm lfd pol ifds m w0 ∧
  (MEM f (MAP SND (rstate lfd pol ifds m w0 k).b.tbl) ∨
   MEM f (rstate lfd pol ifds m w0 k).b.closing) ∧
  l0_chan_of (rworld lfd pol ifds m w0 k) f = SOME c ∧
  ¬MEM f (MAP SND (rstate lfd pol ifds m w0 (SUC k)).b.tbl) ∧
  ¬MEM f (rstate lfd pol ifds m w0 (SUC k)).b.closing ⇒
  csent (rworld lfd pol ifds m w0 (SUC k)) c =
    oout lfd pol ifds m w0 (cl (FST (pcm lfd pol ifds m w0 k)) f) (SUC k) ∨
  MEM f (rstate lfd pol ifds m w0 k).b.gone ∨
  hard_send f (rrev lfd pol ifds m w0 k) ∨ rdrop lfd pol ifds m w0 k f
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  Cases_on ‘MEM f (rstate lfd pol ifds m w0 k).b.gone’ >> simp[] >>
  ‘good lfd pol ifds m w0 f c (cl (FST (pcm lfd pol ifds m w0 k)) f) k’
    by (irule good_init >> fs[]) >>
  drule_all good_step >> strip_tac >> simp[] >>
  ‘outbox_of (rstate lfd pol ifds m w0 (SUC k)).b f = []’
    by (CCONTR_TAC >> mp_tac (Q.INST [‘n’ |-> ‘SUC k’] run_okeys_held) >> simp[]) >>
  qpat_x_assum ‘good _ _ _ _ _ _ _ _ (SUC k)’ mp_tac >> simp[good_def] >> strip_tac >> gvs[]
QED

(* ------------------------------------------------------------------------
   After the release: f stays quiet until it is accepted again
   ------------------------------------------------------------------------ *)

Theorem pdo_acq:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ MEM g ps'.acq ⇒ MEM g ps.acq
Proof
  Cases_on ‘a’ >> simp[pdo_def, AllCaseEqs()] >> rw[] >> gvs[] >>
  TRY (PairCases_on ‘z’) >> gvs[] >>
  rpt (qpat_x_assum ‘l1do _ _ _ = _’ mp_tac) >> rpt (qpat_x_assum ‘l1_close _ _ = _’ mp_tac) >>
  simp[l1do_def, l1_close_def, AllCaseEqs()] >> rw[] >> gvs[]
QED

Theorem pacts_acq:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ MEM g ps'.acq ⇒ MEM g ps.acq
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  PairCases_on ‘ws1’ >> first_x_assum drule_all >> strip_tac >> drule_all pdo_acq >> simp[]
QED

Theorem pf_fetch_acq_log:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ MEM g ps'.acq ⇒
    MEM g ps.acq ∨ MEM (FConn g) log
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[AllCaseEqs()] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule_all >> strip_tac >> gvs[set_inb_def]
QED

(* A round puts g among the pre-accepted only by accepting it (FConn g) *)
Theorem pround_acq:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧ MEM g ps'.acq ⇒
  MEM g ps.acq ∨ MEM (FConn g) log
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >> gvs[] >>
  qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >> simp[pf_tail_def, AllCaseEqs()] >>
  strip_tac >> gvs[stall_step_fields] >>
  drule pf_fetch_acq_log >> disch_then drule >> strip_tac >> simp[] >>
  fs[] >> drule pacts_acq >> disch_then drule >> simp[]
QED

(* The round that releases f (held, then not, not accepted again in it)
   leaves f quiet *)
Theorem release_quiet:
  oassm lfd pol ifds m w0 ∧
  (MEM f (MAP SND (rstate lfd pol ifds m w0 k).b.tbl) ∨
   MEM f (rstate lfd pol ifds m w0 k).b.closing) ∧
  ¬MEM f (MAP SND (rstate lfd pol ifds m w0 (SUC k)).b.tbl) ∧
  ¬MEM f (rstate lfd pol ifds m w0 (SUC k)).b.closing ∧
  ¬MEM (FConn f) (rlog lfd pol ifds m w0 k) ⇒
  cquiet f (rstate lfd pol ifds m w0 (SUC k))
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  ‘run_ok lfd pol ifds m w0’ by fs[oassm_def] >>
  simp[cquiet_def] >>
  conj_tac
  >- (‘¬MEM f (rstate lfd pol ifds m w0 k).acq’
        by (drule run_rel >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
            fs[pown_def, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
      drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
      strip_tac >> drule_all pround_acq >> simp[]) >>
  CCONTR_TAC >> mp_tac (Q.INST [‘n’ |-> ‘SUC k’] run_okeys_held) >> simp[]
QED

(* tail_quiet, pround_quiet and run_closed_quiet without the channel
   invariant dinv: f stays quiet *)
Theorem tail_cquiet:
  pf_tail lfd pol hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ∧ winv w ∧
  psmall lfd ps ∧ oinv ps.b ∧ f ≠ lfd ∧ cquiet f ps ∧ ¬MEM (FConn f) log ⇒
  cquiet f ps' ∧ ev_off f evs
Proof
  simp[pf_tail_def, AllCaseEqs()] >> strip_tac >> gvs[cquiet_def] >>
  qabbrev_tac ‘fes = pf_poll_set lfd pol ps hs’ >>
  ‘EVERY (λ(g, e). small g ∧ e < 4) fes’
    by (simp[Abbr ‘fes’] >> irule pf_poll_set_small >> simp[]) >>
  ‘l0_rely w’ by fs[winv_def] >>
  ‘ev_off f pevs’
    by (simp[ev_off_def] >> rpt strip_tac >>
        ‘ev_name ev = ExtCall «sys_poll»’
          by (drule l1_polls_names >> simp[EVERY_MEM]) >>
        ‘nm = «sys_poll»’ by (Cases_on ‘ev’ >> gvs[ev_on_def, ev_name_def]) >> gvs[] >>
        ‘MEM f (MAP FST fes)’
          by (qspecl_then [‘[fes]’, ‘w’, ‘rv’, ‘w1’, ‘pevs’] mp_tac l1_polls_fds >>
              simp[] >> metis_tac[]) >>
        gvs[MEM_MAP] >> rename1 ‘MEM y fes’ >> PairCases_on ‘y’ >> gvs[Abbr ‘fes’] >>
        drule pf_poll_set_keys >> strip_tac >> gvs[oinv_def, MEM_MAP] >>
        metis_tac[]) >>
  ‘winv w1’ by metis_tac[l1_polls_winv] >>
  drule_all l1_flush_off >> strip_tac >>
  drule l1_flush_fields >> strip_tac >>
  ‘winv w2’ by metis_tac[l1_flush_winv] >>
  ‘¬MEM f (FILTER (λf. MEM f (in_fds fes)) (readable_fds rv))’
    by (simp[MEM_FILTER] >> disj1_tac >> strip_tac >> gvs[Abbr ‘fes’] >>
        drule in_fds_poll_set >> simp[]) >>
  drule_all pf_fetch_off >> strip_tac >>
  drule pf_fetch_b >> strip_tac >>
  drule_all pf_fetch_lfd >> strip_tac >>
  ‘winv w3’ by metis_tac[pf_fetch_winv] >>
  qabbrev_tac ‘ps3 = stall_step (pf_held ps3') (outbox_of ps.b) log ps3'’ >>
  ‘ps3.b.tbl = b2.tbl ∧ ps3.b.closing = b2.closing ∧ ps3.acq = ps3'.acq ∧
   outbox_of ps3.b f = []’
    by (simp[Abbr ‘ps3’, stall_step_drops, FOLDL_drop_out] >>
        simp[stall_step_def] >> rw[]) >>
  ‘¬MEM f ps3.b.closing ∧ ¬MEM f ps3'.b.closing’ by gvs[] >>
  drule_all l1_reap_off >> strip_tac >>
  drule_all l1_reap_quiet >> strip_tac >>
  drule l1_reap_tbl >> strip_tac >>
  gvs[log_conns_FConn]
QED

Theorem pround_cquiet:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧ winv w ∧
  psmall lfd ps ∧ oinv ps.b ∧ f ≠ lfd ∧ cquiet f ps ∧ ¬MEM (FConn f) log ⇒
  cquiet f ps' ∧ ev_off f evs
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >> gvs[] >>
  ‘¬MEM f (MAP SND ps.b.tbl) ∧ ¬MEM f ps.acq’ by fs[cquiet_def] >>
  drule_all pacts_off >> strip_tac >>
  ‘winv ws10 ∧ psmall lfd ws11 ∧ oinv ws11.b’
    by metis_tac[pacts_winv, pacts_psmall, pacts_oinv] >>
  ‘cquiet f ws11’ by gvs[cquiet_def] >>
  drule_all tail_cquiet >> simp[]
QED

(* MAIN (for async-spike): from a quiet f, until it is accepted again, f
   stays quiet and no event mentions it *)
Theorem run_quiet:
  oassm lfd pol ifds m w0 ∧ f ≠ lfd ∧ cquiet f (rstate lfd pol ifds m w0 k0) ⇒
  ∀k. k0 ≤ k ∧ (∀i. k0 ≤ i ∧ i < k ⇒ ¬MEM (FConn f) (rlog lfd pol ifds m w0 i)) ⇒
      cquiet f (rstate lfd pol ifds m w0 k) ∧
      ∀i nm ev. k0 ≤ i ∧ i < k ∧ MEM ev (rrev lfd pol ifds m w0 i) ⇒ ¬ev_on nm f ev
Proof
  strip_tac >> fs[oassm_def] >> Induct
  >- (rpt strip_tac >> gvs[]) >>
  strip_tac >> Cases_on ‘k0 = SUC k’ >- (gvs[] >> rpt strip_tac >> gvs[]) >>
  ‘k0 ≤ k’ by simp[] >>
  ‘cquiet f (rstate lfd pol ifds m w0 k) ∧
   ∀i nm ev. k0 ≤ i ∧ i < k ∧ MEM ev (rrev lfd pol ifds m w0 i) ⇒ ¬ev_on nm f ev’
    by (first_x_assum irule >> simp[]) >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
  drule pround_cquiet >> disch_then (qspec_then ‘f’ mp_tac) >>
  impl_tac
  >- (simp[] >> metis_tac[winv_run, psmall_run, run_oinv, LESS_EQ_REFL]) >>
  strip_tac >> simp[] >> rpt strip_tac >>
  Cases_on ‘i = k’ >- gvs[ev_off_def] >>
  first_x_assum (qspecl_then [‘i’, ‘nm’, ‘ev’] mp_tac) >> simp[]
QED

(* ------------------------------------------------------------------------
   A held fd keeps its channel while it stays held
   ------------------------------------------------------------------------ *)

Theorem held_chan_keep:
  oassm lfd pol ifds m w0 ∧
  (MEM f (MAP SND (rstate lfd pol ifds m w0 k).b.tbl) ∨
   MEM f (rstate lfd pol ifds m w0 k).b.closing) ∧
  (MEM f (MAP SND (rstate lfd pol ifds m w0 (SUC k)).b.tbl) ∨
   MEM f (rstate lfd pol ifds m w0 (SUC k)).b.closing) ∧
  l0_chan_of (rworld lfd pol ifds m w0 k) f = SOME c ⇒
  l0_chan_of (rworld lfd pol ifds m w0 (SUC k)) f = SOME c
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  mp_tac run_round_x >> (impl_tac >- fs[]) >> strip_tac >>
  Cases_on ‘live’ >> fs[tkx_def, tk_def, acct_def]
QED

Theorem held_chan_stretch:
  oassm lfd pol ifds m w0 ∧ l0_chan_of (rworld lfd pol ifds m w0 k) f = SOME c ⇒
  ∀d. (∀i. k ≤ i ∧ i ≤ k + d ⇒
           MEM f (MAP SND (rstate lfd pol ifds m w0 i).b.tbl) ∨
           MEM f (rstate lfd pol ifds m w0 i).b.closing) ⇒
      l0_chan_of (rworld lfd pol ifds m w0 (k + d)) f = SOME c
Proof
  strip_tac >> Induct >> simp[] >> strip_tac >>
  ‘l0_chan_of (rworld lfd pol ifds m w0 (k + d)) f = SOME c’
    by (first_x_assum irule >> simp[]) >>
  ‘k + SUC d = SUC (k + d)’ by simp[] >> pop_assum SUBST1_TAC >>
  irule held_chan_keep >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  first_x_assum irule >> simp[]
QED
