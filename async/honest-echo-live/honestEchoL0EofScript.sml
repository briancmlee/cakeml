(*
  The peer's data is final once L1 fetches f's end-of-file (design/47 D,
  trace assembly, EOF case): a recv that returns 0 leaves f's channel with
  an empty inbox and the peer's end-of-file (or broken, i.e. flushed), and
  the rest of the round keeps it so (deof: LData is dropped after the
  peer's end-of-file or a break).

  MAIN: pround_deof, run_deof.
*)
Theory honestEchoL0Eof
Ancestors
  honestL1PFD16 honestL1PFStream honestL1PFFlushLive honestL1PFFlush honestL1PFRound
  honestL1PFOut honestL1PFLive honestL1PFModel honestL1Steps honestL1Model
  honestL1PFOutLive honestL1PFInput honestL0WorldInv honestL0Rely honestL0World
Libs
  preamble


Definition deof_def:
  deof c (w : l0world) ⇔
    c < LENGTH w.chans ∧ (EL c w.chans).inbox = [] ∧
    ((EL c w.chans).peer_eof ∨ (EL c w.chans).broken)
End

Theorem deliver_deof[local]:
  deof c w ⇒ deof c (l0_deliver w a)
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def, deof_def, upd_lchan_def, EL_LUPDATE] >>
  every_case_tac >> gvs[EL_APPEND1, EL_LUPDATE] >> rw[] >> gvs[break_lchan_def] >> rw[]
QED

Theorem FOLDL_deliver_deof[local]:
  ∀as w. deof c w ⇒ deof c (FOLDL l0_deliver w as)
Proof
  Induct >> simp[] >> metis_tac[deliver_deof]
QED

Theorem tick_deof[local]:
  deof c w ⇒ deof c (l0_tick nm w)
Proof
  rw[l0_tick_def] >> irule FOLDL_deliver_deof >> fs[deof_def]
QED

Theorem ticks_deof[local]:
  ∀k w. deof c w ⇒ deof c (l0_ticks nm k w)
Proof
  Induct >> simp[l0_ticks_def] >> metis_tac[tick_deof]
QED

Theorem FOLDL_deof[local]:
  ∀q w1. (∀w' j. deof c w' ⇒ deof c (f w' j)) ∧ deof c w1 ⇒ deof c (FOLDL f w1 q)
Proof
  Induct >> rw[]
QED

Theorem l0_call_deof[local]:
  l0_call n conf bytes w = SOME (FFIreturn out w') ∧ deof c w ⇒ deof c w'
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  TRY (simp[ticks_deof] >> NO_TAC) >>
  TRY (fs[deof_def] >> NO_TAC) >>
  gvs[l0_listen_def, l0_accept_def, l0_recv_def, l0_send_def, l0_shutdown_def,
      l0_connect_def, l0_connerr_def, l0_close_def, close_fd_def, l0_alloc_def,
      AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[AllCaseEqs()]) >>
  TRY (irule FOLDL_deof >> conj_tac
       >- (rpt gen_tac >> rw[deof_def, EL_LUPDATE, upd_lchan_def, break_lchan_def] >>
           rw[] >> gvs[])
       >> fs[deof_def] >> NO_TAC) >>
  fs[deof_def, upd_lchan_def, EL_LUPDATE, break_lchan_def, EL_APPEND1] >> rw[] >> gvs[] >>
  TRY (metis_tac[] >> NO_TAC)
QED

(* MAIN: deof is kept by every world step L1 takes *)
Theorem wpres_deof:
  wpres (deof c)
Proof
  rw[wpres_def]
  >- (irule tick_deof >> simp[])
  >- fs[deof_def]
  >- (drule_all l0_call_deof >> simp[])
QED

(* A recv that returns 0 leaves f's channel drained at end-of-file (or
   broken) *)
Theorem recv_zero_deof:
  l0_recv f n w = (Ok 0, d, w') ∧ 0 < n ∧ l0_rely w ∧ noconn w ∧
  l0_chan_of w f = SOME j ⇒
  w' = w ∧ deof j w
Proof
  strip_tac >> ‘j < LENGTH w.chans’ by metis_tac[chan_lt] >>
  ‘fl w f (EL j w.chans).inbox’ by (simp[fl_def, front_def]) >>
  drule_all recv_zero >> strip_tac
  >- (qpat_x_assum ‘l0_recv _ _ _ = _’ mp_tac >>
      simp[l0_recv_def, AllCaseEqs(), fail_def, not_chan_def] >> rw[] >> gvs[deof_def]) >>
  gvs[flushed_def, deof_def]
QED

Theorem sys_recv_deof:
  winv w ∧ 0 < k ∧ k < 256 ** 8 ∧ sys_recv f k w = SOME (out, w', ev) ∧
  l0_res_of out = Ok 0 ⇒
  ∃j. l0_chan_of w' f = SOME j ∧ deof j w'
Proof
  rw[sys_recv_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  qabbrev_tac ‘wt = l0_tick «sys_recv» w’ >>
  ‘noconn wt ∧ l0_rely wt’
    by (gvs[Abbr ‘wt’, winv_def, noconn_tick] >>
        irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def, l0_hdr_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  ‘l0_res_ok r’
    by (qspecl_then [‘wt’, ‘f’, ‘k’, ‘r’, ‘d’, ‘w'’] mp_tac
          (Q.GENL [‘w’, ‘f’, ‘n’, ‘r’, ‘d’, ‘w'’] recv_res_ok) >> simp[]) >>
  ‘l0_res_of (enc_res r ++ d ++ REPLICATE (k − LENGTH d) 0w) = r’
    by (REWRITE_TAC [GSYM APPEND_ASSOC] >> irule l0_res_of_enc_app >> simp[]) >>
  gvs[] >>
  ‘∃j. l0_chan_of wt f = SOME j’
    by (Cases_on ‘l0_chan_of wt f’ >> simp[] >>
        qpat_x_assum ‘l0_recv _ _ _ = _’ mp_tac >>
        simp[l0_recv_def, not_chan_def, fail_def] >> rw[] >> gvs[AllCaseEqs()]) >>
  drule_all recv_zero_deof >> strip_tac >> gvs[] >>
  TRY (qexists_tac ‘j’) >> fs[deof_def, l0_chan_of_def]
QED

(* An end-of-file fetched on f leaves f's channel drained at end-of-file
   (or broken) at the end of the fetch *)
Theorem pf_fetch_deof:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ winv w ∧ qfresh w ∧
    MEM (FEof f) log ⇒
    ∃j. l0_chan_of w' f = SOME j ∧ deof j w'
Proof
  Induct >- simp[pf_fetch_def] >>
  rpt gen_tac >> rename1 ‘g :: fs’ >> strip_tac >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ mp_tac >> simp[Once pf_fetch_def] >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  IF_CASES_TAC
  >- (simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
      pairarg_tac >> fs[AllCaseEqs()] >> rveq >>
      ‘winv w1 ∧ qfresh w1’ by metis_tac[sys_winv, sys_qfresh] >>
      gvs[AllCaseEqs()] >> first_x_assum drule_all >> simp[]) >>
  simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  pairarg_tac >> fs[CaseEq "option", CaseEq "prod"] >> rveq >>
  ‘winv w1 ∧ qfresh w1’ by metis_tac[sys_winv, sys_qfresh] >>
  Cases_on ‘MEM (FEof f) log'’ >- (first_x_assum drule_all >> simp[]) >>
  (* the EOF is this recv's: g = f, and it returned 0 *)
  ‘g = f ∧ l0_res_of out = Ok 0’
    by (Cases_on ‘l0_res_of out’ >> fs[] >> gvs[AllCaseEqs()] >>
        every_case_tac >> gvs[]) >>
  rveq >>
  ‘0 < pf_chunk ∧ pf_chunk < 256 ** 8’ by EVAL_TAC >>
  drule_all sys_recv_deof >> strip_tac >>
  drule_all pf_fetch_out >> strip_tac >>
  qexists_tac ‘j’ >> simp[] >>
  irule pf_fetch_wpres >> simp[wpres_deof] >> metis_tac[]
QED

Theorem FOLDL_drop_out_closing[local]:
  ∀fs b. (FOLDL drop_out b fs).closing = b.closing
Proof
  Induct >> simp[drop_out_def, set_outbox_def]
QED

Theorem l1do_write_closing[local]:
  l1do lfd (w, b) (Write h bs) = SOME (r, (w', b'), evs) ⇒ b'.closing = b.closing
Proof
  rw[l1do_def, AllCaseEqs()] >>
  gvs[set_outbox_def, after_send_def, AllCaseEqs()] >> rw[set_outbox_def]
QED

Theorem pdo_eof_closing[local]:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧
  ¬MEM f ps.eof ∧ ¬MEM f ps.b.closing ⇒
  ¬MEM f ps'.eof ∧ ¬MEM f ps'.b.closing
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> strip_tac >>
  gvs[AllCaseEqs(), set_inb_def, MEM_FILTER] >>
  TRY (pairarg_tac >> gvs[]) >>
  gvs[l1_close_def, AllCaseEqs(), forget_def, set_outbox_def, MEM_FILTER] >>
  TRY (rw[] >> gvs[] >> NO_TAC) >>
  TRY (drule l1do_write_closing >> simp[] >> NO_TAC) >>
  metis_tac[]
QED

Theorem pacts_eof_closing[local]:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧
    ¬MEM f ps.eof ∧ ¬MEM f ps.b.closing ⇒
    ¬MEM f ps'.eof ∧ ¬MEM f ps'.b.closing
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  drule_all pdo_eof_closing >> strip_tac >> first_x_assum drule_all >> simp[]
QED

(* MAIN: a round in which L1, keeping f at its start, fetches f's
   end-of-file ends with f's channel drained at end-of-file (or broken) *)
Theorem pround_deof:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧
  winv w ∧ qfresh w ∧ ¬MEM f ps.eof ∧ ¬MEM f ps.b.closing ∧ MEM (FEof f) log ⇒
  ∃j. l0_chan_of w' f = SOME j ∧ deof j w'
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >> gvs[] >>
  rename1 ‘pacts _ _ _ = SOME (rs1, aevs, (w1, ps1))’ >>
  drule_all pacts_eof_closing >> strip_tac >>
  ‘winv w1’ by metis_tac[pacts_winv] >>
  ‘qfresh w1’ by metis_tac[pacts_qfresh] >>
  qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >>
  simp[pf_tail_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  ‘winv w1' ∧ qfresh w1'’ by metis_tac[l1_polls_winv, l1_polls_qfresh] >>
  ‘winv w2 ∧ qfresh w2’ by metis_tac[l1_flush_winv, l1_flush_qfresh] >>
  drule_all pf_fetch_deof >> strip_tac >>
  ‘winv w3’ by metis_tac[pf_fetch_winv] >>
  ‘b2.closing = ps1.b.closing’ by (drule l1_flush_f >> simp[]) >>
  ‘ps3'.b = b2’ by (drule_all pf_fetch_out >> simp[]) >>
  qexists_tac ‘j’ >> conj_tac
  >- (drule l1_reap_cflow >> disch_then drule >> disch_then drule >>
      impl_tac >- simp[stall_step_def, FOLDL_drop_out_closing] >> simp[]) >>
  irule l1_reap_wpres >> simp[wpres_deof] >> metis_tac[]
QED

Theorem run_qfresh:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ qfresh w0 ⇒
  ∀n. qfresh (rworld lfd pol ifds m w0 n)
Proof
  strip_tac >> Induct >- simp[rworld_def, prun_0] >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘n’] strip_assume_tac) >>
  drule pround_qfresh >> disch_then irule >> simp[] >>
  drule_all winv_run >> simp[]
QED

Theorem run_deof:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ qfresh w0 ∧
  ¬MEM f (rstate lfd pol ifds m w0 k).eof ∧ ¬MEM f (rstate lfd pol ifds m w0 k).b.closing ∧
  MEM (FEof f) (rlog lfd pol ifds m w0 k) ⇒
  ∃j. l0_chan_of (rworld lfd pol ifds m w0 (SUC k)) f = SOME j ∧
      deof j (rworld lfd pol ifds m w0 (SUC k))
Proof
  strip_tac >>
  drule prun_round' >> disch_then (qspecl_then [‘f’, ‘k’] strip_assume_tac) >>
  drule pround_deof >> disch_then irule >> simp[] >>
  metis_tac[winv_run, run_qfresh]
QED

(* MAIN: once L1 has fetched f's end-of-file in round k (f connected in
   round a, kept since), the peer's data on f's channel is final, and is
   exactly what L1 fetched on f since a -- or the channel is flushed *)
Theorem eof_final:
  oassm lfd pol ifds m w0 ∧ qinb w0 ∧
  MEM (FConn f) (rlog lfd pol ifds m w0 a) ∧
  (∀i. a < i ∧ i ≤ k ⇒ ¬MEM (FConn f) (rlog lfd pol ifds m w0 i)) ∧ a ≤ k ∧
  ¬MEM f (rstate lfd pol ifds m w0 k).eof ∧ ¬MEM f (rstate lfd pol ifds m w0 k).b.closing ∧
  MEM (FEof f) (rlog lfd pol ifds m w0 k) ⇒
  ∃j. l0_chan_of (rworld lfd pol ifds m w0 (SUC k)) f = SOME j ∧
      ((EL j (rworld lfd pol ifds m w0 (SUC k)).chans).peer_eof ∧
       (EL j (rworld lfd pol ifds m w0 (SUC k)).chans).peer_sent =
         fdata f (rlogs lfd pol ifds m w0 a (SUC k − a)) ∨
       flushed (rworld lfd pol ifds m w0 (SUC k)) f)
Proof
  strip_tac >>
  ‘run_ok lfd pol ifds m w0 ∧ winv w0 ∧ qfresh w0’ by fs[oassm_def] >>
  drule_all run_deof >> strip_tac >> qexists_tac ‘j’ >> simp[] >>
  Cases_on ‘(EL j (rworld lfd pol ifds m w0 (SUC k)).chans).broken’
  >- (disj2_tac >> fs[flushed_def, deof_def]) >>
  ‘(EL j (rworld lfd pol ifds m w0 (SUC k)).chans).peer_eof ∧
   (EL j (rworld lfd pol ifds m w0 (SUC k)).chans).inbox = []’ by fs[deof_def] >>
  simp[] >>
  ‘(EL j (rworld lfd pol ifds m w0 (SUC k)).chans).peer_sent =
     fdata f (rlogs lfd pol ifds m w0 a (SUC k − a)) ++
     (EL j (rworld lfd pol ifds m w0 (SUC k)).chans).inbox ∨
   flushed (rworld lfd pol ifds m w0 (SUC k)) f’
    by (irule run_peer_sent >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        TRY decide_tac >> rpt strip_tac >>
        qpat_x_assum ‘∀i. a < i ∧ i ≤ k ⇒ _’ (qspec_then ‘k'’ mp_tac) >> simp[]) >>
  fs[]
QED
