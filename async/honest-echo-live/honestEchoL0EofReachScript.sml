(*
  The peer's end-of-file reaches L1 (design/47 D, D27 (a)): if L1 keeps f
  (fkeep: f in the table under h, no EOF, not closing) while f's channel
  has the peer's end-of-file, then L1 stops keeping f in some later round.
  At that round f has an EOF in the table, or it has left the table.

  The argument, by contradiction (L1 keeps f in every round from n0):
   - no round fetches f's end (FEof or FReset sets f's EOF: fetch_eof),
     and f's channel stays the same (no close call on f: pround_keep_chan);
   - phase 1: stream_progress with R the inbox at n0 gives d with R ≼ the
     data fetched in [n0, n0+d).  The peer sent nothing after its
     end-of-file (psmono), so run_peer_sent gives an empty inbox at n0+d:
     the channel is drained at EOF (deof);
   - phase 2: deof is pending, so fetch_progress gives a later round that
     fetches on f: an end (excluded above) or data, but a recv on a
     drained channel returns no data (pround_nodata).

  MAIN: eof_reaches.
*)
Theory honestEchoL0EofReach
Ancestors
  honestEchoL0Eof honestEchoL0Peer honestEchoL0OutAny honestL1PFConnTrace
  honestL1PFDropBroken honestEchoL0Inv honestEchoL0LiveOwn
  honestL1PFInput honestL1PFD16 honestL1PFStream honestL1PFFlushLive honestL1PFFlush
  honestL1PFRound honestL1PFOut honestL1PFOutLive honestL1PFLive honestL1PFModel
  honestL1Steps honestL1Model honestL0WorldInv honestL0Rely honestL0World
Libs
  preamble

(* ------------------------------------------------------------------------
   A drained channel gives no data
   ------------------------------------------------------------------------ *)

Theorem recv_deof_nodata[local]:
  l0_recv f n w = (Ok k, d, w') ∧ l0_chan_of w f = SOME c ∧ deof c w ⇒ k = 0
Proof
  rw[l0_recv_def, deof_def] >> gvs[AllCaseEqs(), fail_def]
QED

Theorem sys_recv_nodata[local]:
  winv w ∧ k < 256 ** 8 ∧ sys_recv f k w = SOME (out, w', ev) ∧
  l0_chan_of w f = SOME c ∧ deof c w ∧ l0_res_of out = Ok n ⇒ n = 0
Proof
  rw[sys_recv_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  qabbrev_tac ‘wt = l0_tick «sys_recv» w’ >>
  ‘l0_rely wt’
    by (gvs[Abbr ‘wt’, winv_def] >> irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  ‘deof c wt’ by (simp[Abbr ‘wt’] >> metis_tac[wpres_deof, wpres_def]) >>
  ‘l0_chan_of wt f = SOME c’
    by (qpat_x_assum ‘l0_chan_of w f = _’ mp_tac >> qpat_x_assum ‘deof c wt’ mp_tac >>
        simp[l0_chan_of_def, deof_def, Abbr ‘wt’, AllCaseEqs()]) >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def, l0_hdr_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  ‘l0_res_ok r’
    by (qspecl_then [‘wt’, ‘f’, ‘k’, ‘r’, ‘d’, ‘w'’] mp_tac
          (Q.GENL [‘w’, ‘f’, ‘n’, ‘r’, ‘d’, ‘w'’] recv_res_ok) >> simp[]) >>
  ‘l0_res_of (enc_res r ++ d ++ REPLICATE (k − LENGTH d) 0w) = r’
    by (REWRITE_TAC [GSYM APPEND_ASSOC] >> irule l0_res_of_enc_app >> simp[]) >>
  gvs[] >> drule_all recv_deof_nodata >> simp[]
QED

Theorem pf_fetch_nodata[local]:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ winv w ∧
    l0_chan_of w f = SOME c ∧ deof c w ⇒
    ∀bs. ¬MEM (FData f bs) log
Proof
  Induct >- simp[pf_fetch_def] >>
  rpt gen_tac >> rename1 ‘g :: fs’ >> strip_tac >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ mp_tac >> simp[Once pf_fetch_def] >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  IF_CASES_TAC
  >- (simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
      pairarg_tac >> fs[AllCaseEqs()] >> rveq >>
      ‘winv w1’ by metis_tac[sys_winv] >>
      ‘l0_chan_of w1 f = SOME c’ by metis_tac[sys_csent] >>
      ‘deof c w1’ by metis_tac[sys_wpres, wpres_deof] >>
      gvs[AllCaseEqs()] >> first_x_assum drule_all >> simp[]) >>
  simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  pairarg_tac >> fs[CaseEq "option", CaseEq "prod"] >> rveq >>
  ‘winv w1’ by metis_tac[sys_winv] >>
  ‘l0_chan_of w1 f = SOME c’ by metis_tac[sys_csent] >>
  ‘deof c w1’ by metis_tac[sys_wpres, wpres_deof] >>
  first_x_assum drule_all >> strip_tac >> gen_tac >> simp[] >>
  (* this recv's data is not on f, or it is empty *)
  strip_tac >>
  ‘g = f ∧ ∃k. l0_res_of out = Ok k ∧ 0 < k’
    by (Cases_on ‘l0_res_of out’ >> fs[] >> gvs[AllCaseEqs()] >>
        every_case_tac >> gvs[]) >>
  rveq >>
  ‘pf_chunk < 256 ** 8’ by EVAL_TAC >>
  drule_all sys_recv_nodata >> simp[]
QED

(* ------------------------------------------------------------------------
   A kept fd: no close call, the same channel, no end fetched
   ------------------------------------------------------------------------ *)

Theorem sys_close_call[local]:
  sys_close g w = SOME (out, w', ev) ⇒ (closes_call f ev ⇔ g = f)
Proof
  rw[sys_close_def] >> drule l0_do_cases >> rw[] >> simp[closes_call_def] >>
  ‘LENGTH (fd_bytes g) = 8’ by simp[] >> simp[] >> metis_tac[]
QED

Theorem sys_send_nocall[local]:
  sys_send g bs w = SOME (out, w', ev) ⇒ ¬closes_call f ev
Proof
  rw[sys_send_def] >> drule l0_do_cases >> rw[] >> simp[closes_call_def]
QED

(* An action makes no close call on a kept fd: the auto-close at EOF is
   on an fd with an EOF *)
Theorem pdo_keep_noclose[local]:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ fkeep lfd h f ps ⇒
  ¬EXISTS (closes_call f) evs
Proof
  strip_tac >> Cases_on ‘a’
  >- gvs[pdo_def, AllCaseEqs()]
  >- (qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def] >>
      rw[AllCaseEqs()] >> gvs[] >>
      PairCases_on ‘z’ >> gvs[] >>
      drule l1_close_shape >> strip_tac >> gvs[] >>
      drule sys_close_call >> disch_then (qspec_then ‘f’ assume_tac) >> gvs[] >>
      strip_tac >> gvs[fkeep_def]) >>
  qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def, PULL_EXISTS] >> rpt gen_tac >>
  PairCases_on ‘z’ >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum ‘l1do _ _ _ = _’ mp_tac >> simp[l1do_def] >>
  rw[AllCaseEqs()] >> gvs[] >> metis_tac[sys_send_nocall]
QED

Theorem pacts_keep_noclose[local]:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ winv w ∧ fkeep lfd h f ps ⇒
    ¬EXISTS (closes_call f) evs
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  PairCases_on ‘ws1’ >> rename1 ‘pdo lfd (w, ps) a = SOME (r, (w1, ps1), evs1)’ >>
  conj_tac >- (drule_all pdo_keep_noclose >> simp[]) >>
  drule_all pdo_f >> strip_tac >>
  first_x_assum irule >> metis_tac[]
QED

(* A local copy of honestL1BFetchStop's fetch_eof (that theory's
   ancestors are heavy): a fetched end sets f's EOF *)
Theorem fetch_eof[local]:
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

Theorem pround_fend_eof:
  pround lfd pol hs (w, ps) acts = SOME (snp, (w', ps'), log, evs) ∧ fend f log ⇒
  MEM f ps'.eof
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >> gvs[] >>
  qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >>
  simp[pf_tail_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule fetch_eof >> strip_tac >>
  qpat_x_assum ‘∀f. MEM (FEof f) log ∨ _ ⇒ _’ (qspec_then ‘f’ mp_tac) >>
  impl_tac >- (fs[fend_def, EXISTS_MEM] >> metis_tac[]) >>
  simp[stall_step_def]
QED

(* MAIN: a round that starts keeping f keeps f's channel *)
Theorem pround_keep_chan:
  pround lfd pol hs (w, ps) acts = SOME (snp, (w', ps'), log, evs) ∧
  winv w ∧ qfresh w ∧ fkeep lfd h f ps ∧ l0_chan_of w f = SOME c ⇒
  l0_chan_of w' f = SOME c
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >> gvs[] >>
  rename1 ‘pacts _ _ _ = SOME (rs1, aevs, (w1, ps1))’ >>
  drule_all pacts_f >> strip_tac >>
  drule_all pacts_keep_noclose >> strip_tac >>
  ‘l0_chan_of w1 f = SOME c’ by (drule_all pacts_chan_noclose >> simp[]) >>
  ‘qfresh w1’ by metis_tac[pacts_qfresh] >>
  qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >>
  simp[pf_tail_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all l1_polls_csent >> strip_tac >>
  ‘winv w1' ∧ qfresh w1'’ by metis_tac[l1_polls_winv, l1_polls_qfresh] >>
  drule_all l1_flush_cflow >> strip_tac >>
  ‘winv w2 ∧ qfresh w2’ by metis_tac[l1_flush_winv, l1_flush_qfresh] >>
  drule_all pf_fetch_out >> strip_tac >>
  ‘winv w3’ by metis_tac[pf_fetch_winv] >>
  ‘l0_chan_of w3 f = SOME c’ by metis_tac[] >>
  ‘b2.closing = ps1.b.closing’ by (drule l1_flush_f >> simp[]) >>
  ‘¬MEM f ps1.b.closing’ by fs[fkeep_def] >>
  drule l1_reap_cflow >> disch_then drule >> disch_then drule >>
  impl_tac >- simp[stall_step_def, FOLDL_drop_out] >> simp[]
QED

(* MAIN: a round that starts keeping f, with f's channel drained at EOF,
   fetches no data on f *)
Theorem pround_nodata:
  pround lfd pol hs (w, ps) acts = SOME (snp, (w', ps'), log, evs) ∧
  winv w ∧ fkeep lfd h f ps ∧ l0_chan_of w f = SOME c ∧ deof c w ⇒
  ∀bs. ¬MEM (FData f bs) log
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >> gvs[] >>
  rename1 ‘pacts _ _ _ = SOME (rs1, aevs, (w1, ps1))’ >>
  drule_all pacts_f >> strip_tac >>
  drule_all pacts_keep_noclose >> strip_tac >>
  ‘l0_chan_of w1 f = SOME c’ by (drule_all pacts_chan_noclose >> simp[]) >>
  ‘deof c w1’ by metis_tac[pacts_wpres, wpres_deof] >>
  qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >>
  simp[pf_tail_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all l1_polls_csent >> strip_tac >>
  ‘winv w1'’ by metis_tac[l1_polls_winv] >>
  ‘deof c w1'’ by metis_tac[l1_polls_wpres, wpres_deof] >>
  drule_all l1_flush_cflow >> strip_tac >>
  ‘winv w2’ by metis_tac[l1_flush_winv] >>
  ‘deof c w2’ by metis_tac[l1_flush_wpres, wpres_deof] >>
  drule_all pf_fetch_nodata >> simp[]
QED

(* ------------------------------------------------------------------------
   The run, while L1 keeps f
   ------------------------------------------------------------------------ *)

Theorem run_wpres_from[local]:
  wpres P ∧ run_ok lfd pol ifds m w0 ∧ winv w0 ∧ P (rworld lfd pol ifds m w0 a) ⇒
  ∀d. P (rworld lfd pol ifds m w0 (a + d))
Proof
  strip_tac >> Induct >- simp[] >>
  ‘a + SUC d = SUC (a + d)’ by decide_tac >> pop_assum SUBST1_TAC >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘a + d’] strip_assume_tac) >>
  drule_at (Pos last) pround_wpres >> disch_then irule >> simp[] >>
  drule_all winv_run >> simp[]
QED

(* A local copy of honestEchoL0EofCase's run_psmono (local there) *)
Theorem run_psmono[local]:
  run_ok lfd pol ifds m w0 ∧ a ≤ b ⇒
  psmono c (rworld lfd pol ifds m w0 a) (rworld lfd pol ifds m w0 b)
Proof
  strip_tac >>
  ‘revs lfd pol ifds m w0 a ≼ revs lfd pol ifds m w0 (a + (b − a))’
    by (drule revs_prefix >> disch_then (qspecl_then [‘b − a’, ‘a’] ACCEPT_TAC)) >>
  ‘a + (b − a) = b’ by decide_tac >> fs[IS_PREFIX_APPEND] >>
  irule world_at_psmono >> qexistsl_tac [‘revs lfd pol ifds m w0 a’, ‘l’, ‘w0’] >>
  metis_tac[run_world_at]
QED

Theorem run_keep_chan[local]:
  oassm lfd pol ifds m w0 ∧ (∀k. n0 ≤ k ⇒ fkeep lfd h f (rstate lfd pol ifds m w0 k)) ∧
  l0_chan_of (rworld lfd pol ifds m w0 n0) f = SOME c ⇒
  ∀d. l0_chan_of (rworld lfd pol ifds m w0 (n0 + d)) f = SOME c
Proof
  strip_tac >> ‘run_ok lfd pol ifds m w0 ∧ winv w0 ∧ qfresh w0’ by fs[oassm_def] >>
  Induct >- simp[] >>
  ‘n0 + SUC d = SUC (n0 + d)’ by decide_tac >> pop_assum SUBST1_TAC >>
  drule prun_round' >> disch_then (qspecl_then [‘f’, ‘n0 + d’] strip_assume_tac) >>
  ‘fkeep lfd h f (rstate lfd pol ifds m w0 (n0 + d))’ by (first_assum irule >> simp[]) >>
  ‘qfresh (rworld lfd pol ifds m w0 (n0 + d))’ by (irule run_qfresh >> simp[]) >>
  ‘winv (rworld lfd pol ifds m w0 (n0 + d))’ by (drule_all winv_run >> simp[]) >>
  drule pround_keep_chan >> disch_then irule >> rpt conj_tac >> TRY (qexists_tac ‘h’) >>
  first_assum ACCEPT_TAC
QED

Theorem run_keep_nofend[local]:
  run_ok lfd pol ifds m w0 ∧ (∀k. n0 ≤ k ⇒ fkeep lfd h f (rstate lfd pol ifds m w0 k)) ⇒
  ∀k. n0 ≤ k ⇒ ¬fend f (rlog lfd pol ifds m w0 k)
Proof
  rpt strip_tac >>
  drule prun_round' >> disch_then (qspecl_then [‘f’, ‘k’] strip_assume_tac) >>
  drule_all pround_fend_eof >> strip_tac >>
  qpat_x_assum ‘∀k. n0 ≤ k ⇒ _’ (qspec_then ‘SUC k’ mp_tac) >> simp[fkeep_def]
QED

Theorem rlogs_nofend[local]:
  (∀k. n0 ≤ k ⇒ ¬fend f (rlog lfd pol ifds m w0 k)) ⇒
  ∀d. ¬fend f (rlogs lfd pol ifds m w0 n0 d)
Proof
  strip_tac >> Induct >- simp[rlogs_def, fend_def] >>
  simp[rlogs_SUC]
QED

Theorem pfx_app_nil[local]:
  r ≼ y ∧ x ++ r = x ++ y ++ z ⇒ z = []
Proof
  rw[] >> fs[] >> rveq >> fs[IS_PREFIX_APPEND] >>
  ‘LENGTH (y ++ z ++ l) = LENGTH y’ by metis_tac[] >> fs[] >>
  Cases_on ‘z’ >> fs[]
QED

Theorem flushed_deof[local]:
  flushed w f ∧ l0_chan_of w f = SOME c ⇒ deof c w
Proof
  rw[flushed_def, deof_def] >> gvs[l0_chan_of_def, AllCaseEqs()]
QED

Theorem peer_deof[local]:
  l0_chan_of w f = SOME c ∧ (EL c w.chans).inbox = [] ∧ (EL c w.chans).peer_eof ⇒ deof c w
Proof
  rw[deof_def] >> gvs[l0_chan_of_def, AllCaseEqs()]
QED

(* Phase 1: f's channel gets drained at EOF *)
Theorem keep_deof[local]:
  oassm lfd pol ifds m w0 ∧ qinb w0 ∧
  F1 lfd pol ifds m w0 ∧ S1 lfd pol ifds m w0 ∧ S3w lfd pol ifds m w0 ∧
  pol_ok hw pol ∧ S4w lfd pol hw ifds m w0 f ∧
  (∀k. n0 ≤ k ⇒ fkeep lfd h f (rstate lfd pol ifds m w0 k)) ∧
  l0_chan_of (rworld lfd pol ifds m w0 n0) f = SOME c ∧
  (EL c (rworld lfd pol ifds m w0 n0).chans).peer_eof ⇒
  ∃k1. n0 ≤ k1 ∧ deof c (rworld lfd pol ifds m w0 k1)
Proof
  strip_tac >>
  ‘run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
   (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64))’ by fs[oassm_def] >>
  ‘∀d. l0_chan_of (rworld lfd pol ifds m w0 (n0 + d)) f = SOME c’
    by (drule_all run_keep_chan >> simp[]) >>
  ‘∀d. ¬fend f (rlogs lfd pol ifds m w0 n0 d)’
    by (irule rlogs_nofend >>
        qpat_assum ‘∀k. n0 ≤ k ⇒ fkeep _ _ _ _’ (fn th => qpat_assum ‘run_ok _ _ _ _ _’
          (fn r => ACCEPT_TAC (MATCH_MP run_keep_nofend (CONJ r th))))) >>
  ‘fkeep lfd h f (rstate lfd pol ifds m w0 n0)’ by (first_x_assum irule >> simp[]) >>
  (* f's last connection a < n0 *)
  ‘∃a. a < n0 ∧ MEM (FConn f) (rlog lfd pol ifds m w0 a) ∧
       ∀k. a < k ∧ k < n0 ⇒ ¬MEM (FConn f) (rlog lfd pol ifds m w0 k)’
    by (qpat_assum ‘run_ok _ _ _ _ _’ (fn th => irule (MATCH_MP last_conn th)) >>
        drule run_rel >> disch_then (qspec_then ‘n0’ strip_assume_tac) >>
        drule held_acct >> disch_then drule >> disch_then drule >>
        disch_then (qspec_then ‘f’ mp_tac) >> impl_tac >> simp[] >>
        disj1_tac >> fs[fkeep_def] >> drule ALOOKUP_MEM >>
        simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  ‘∀k. a < k ⇒ ¬MEM (FConn f) (rlog lfd pol ifds m w0 k)’
    by (rpt strip_tac >> Cases_on ‘k < n0’ >- metis_tac[] >>
        ‘k = n0 + (k − n0) ∧ SUC k = n0 + SUC (k − n0)’ by decide_tac >>
        qspecl_then [‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘k’, ‘f’, ‘c’] mp_tac
          (Q.GENL [‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘k’, ‘f’, ‘c’] run_noconn) >>
        impl_tac >> simp[] >> rpt conj_tac
        >- (disj1_tac >>
            qpat_x_assum ‘∀k. n0 ≤ k ⇒ fkeep _ _ _ _’ (qspec_then ‘k’ mp_tac) >>
            simp[fkeep_def] >> strip_tac >> drule ALOOKUP_MEM >>
            simp[MEM_MAP, EXISTS_PROD] >> metis_tac[])
        >- metis_tac[]
        >> metis_tac[]) >>
  ‘c < LENGTH (rworld lfd pol ifds m w0 n0).chans’
    by (qpat_x_assum ‘l0_chan_of _ f = SOME c’ mp_tac >> simp[l0_chan_of_def, AllCaseEqs()]) >>
  (* the peer's data at n0 *)
  qspecl_then [‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘f’, ‘a’, ‘n0’, ‘c’] mp_tac
    (Q.GENL [‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘f’, ‘a’, ‘n’, ‘c’] run_peer_sent) >>
  impl_tac >- simp[] >>
  reverse strip_tac
  >- (qexists_tac ‘n0’ >> simp[] >> drule_all flushed_deof >> simp[]) >>
  (* stream_progress with R the inbox at n0 *)
  ‘fl (rworld lfd pol ifds m w0 n0) f (EL c (rworld lfd pol ifds m w0 n0).chans).inbox’
    by (rewrite_tac[fl_def, front_def] >> disj1_tac >> qexists_tac ‘c’ >>
        conj_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  mp_tac stream_progress >> impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [‘(EL c (rworld lfd pol ifds m w0 n0).chans).inbox’, ‘n0’, ‘h’] mp_tac) >>
  impl_tac
  >- (qpat_x_assum ‘fkeep _ _ _ (rstate _ _ _ _ _ n0)’ mp_tac >> rewrite_tac[fkeep_def] >>
      strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then ‘d’ strip_assume_tac)
  >- (qpat_x_assum ‘∀d. ¬fend _ _’ (qspec_then ‘d’ mp_tac) >> simp[]) >>
  (* the peer's data at k1 = n0 + d *)
  qabbrev_tac ‘k1 = n0 + d’ >>
  ‘n0 ≤ k1 ∧ a < k1’ by simp[Abbr ‘k1’] >>
  ‘l0_chan_of (rworld lfd pol ifds m w0 k1) f = SOME c’
    by (qunabbrev_tac ‘k1’ >> first_assum (qspec_then ‘d’ ACCEPT_TAC)) >>
  qspecl_then [‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘f’, ‘a’, ‘k1’, ‘c’] mp_tac
    (Q.GENL [‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘f’, ‘a’, ‘n’, ‘c’] run_peer_sent) >>
  impl_tac >- simp[] >>
  reverse strip_tac
  >- (qexists_tac ‘k1’ >> simp[] >> drule_all flushed_deof >> simp[]) >>
  qspecl_then [‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘n0’, ‘k1’, ‘c’] mp_tac
    (Q.GENL [‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘a’, ‘b’, ‘c’] run_psmono) >>
  impl_tac >- simp[] >>
  rewrite_tac[psmono_def] >> disch_then drule >> strip_tac >>
  ‘rlogs lfd pol ifds m w0 a (k1 − a) =
   rlogs lfd pol ifds m w0 a (n0 − a) ++ rlogs lfd pol ifds m w0 n0 d’
    by (‘k1 − a = (n0 − a) + d’ by simp[Abbr ‘k1’] >> pop_assum SUBST1_TAC >>
        rewrite_tac[rlogs_add] >>
        ‘a + (n0 − a) = n0’ by decide_tac >> pop_assum SUBST1_TAC >> rewrite_tac[]) >>
  qpat_x_assum ‘_ ⇒ _ ∧ _’ (fn th =>
    qpat_assum ‘(EL c (rworld _ _ _ _ _ n0).chans).peer_eof’ (strip_assume_tac o MATCH_MP th)) >>
  ‘(EL c (rworld lfd pol ifds m w0 k1).chans).inbox = []’
    by (irule pfx_app_nil >>
        qexistsl_tac [‘(EL c (rworld lfd pol ifds m w0 n0).chans).inbox’,
                      ‘fdata f (rlogs lfd pol ifds m w0 a (n0 − a))’,
                      ‘fdata f (rlogs lfd pol ifds m w0 n0 d)’] >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
        qpat_x_assum ‘_ = fdata f (rlogs _ _ _ _ _ a (n0 − a)) ++ _’
          (fn th => rewrite_tac[GSYM th]) >>
        qpat_x_assum ‘_ = (EL c (rworld _ _ _ _ _ n0).chans).peer_sent’
          (fn th => rewrite_tac[GSYM th]) >>
        qpat_x_assum ‘_ = fdata f (rlogs _ _ _ _ _ a (k1 − a)) ++ _’
          (fn th => rewrite_tac[th]) >>
        qpat_x_assum ‘rlogs _ _ _ _ _ a (k1 − a) = _’ (fn th => rewrite_tac[th]) >>
        rewrite_tac[fdata_app, APPEND_ASSOC]) >>
  qexists_tac ‘k1’ >> conj_tac >- first_assum ACCEPT_TAC >>
  irule peer_deof >> rpt conj_tac >> TRY (qexists_tac ‘f’) >> first_assum ACCEPT_TAC
QED

Theorem deof_pend[local]:
  l0_chan_of w f = SOME c ∧ deof c w ⇒ pend w f
Proof
  rw[deof_def, pend_def]
QED

(* Phase 2: L1 does not keep f forever *)
Theorem keep_forever_F[local]:
  oassm lfd pol ifds m w0 ∧ qinb w0 ∧
  F1 lfd pol ifds m w0 ∧ S1 lfd pol ifds m w0 ∧ S3w lfd pol ifds m w0 ∧
  pol_ok hw pol ∧ S4w lfd pol hw ifds m w0 f ∧
  (∀k. n0 ≤ k ⇒ fkeep lfd h f (rstate lfd pol ifds m w0 k)) ∧
  l0_chan_of (rworld lfd pol ifds m w0 n0) f = SOME c ∧
  (EL c (rworld lfd pol ifds m w0 n0).chans).peer_eof ⇒
  F
Proof
  strip_tac >>
  ‘run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
   (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64))’ by fs[oassm_def] >>
  mp_tac keep_deof >> impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  ‘∀d. l0_chan_of (rworld lfd pol ifds m w0 (n0 + d)) f = SOME c’
    by (mp_tac run_keep_chan >> impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
        simp[]) >>
  ‘∀k. n0 ≤ k ⇒ ¬fend f (rlog lfd pol ifds m w0 k)’
    by (mp_tac run_keep_nofend >> impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
        simp[]) >>
  ‘l0_chan_of (rworld lfd pol ifds m w0 k1) f = SOME c’
    by (qpat_x_assum ‘∀d. l0_chan_of _ _ = _’ (qspec_then ‘k1 − n0’ mp_tac) >> simp[]) >>
  ‘fkeep lfd h f (rstate lfd pol ifds m w0 k1)’ by (first_assum irule >> simp[]) >>
  (* a later round fetches on f *)
  mp_tac fetch_progress >> impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [‘k1’, ‘h’] mp_tac) >>
  impl_tac
  >- (qpat_x_assum ‘fkeep _ _ _ (rstate _ _ _ _ _ k1)’ mp_tac >> rewrite_tac[fkeep_def] >>
      strip_tac >> rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
      irule deof_pend >> qexists_tac ‘c’ >> conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then ‘k’ strip_assume_tac) >>
  drule prun_round' >> disch_then (qspecl_then [‘f’, ‘k’] strip_assume_tac) >>
  ‘fetched f (rlog lfd pol ifds m w0 k)’ by metis_tac[] >>
  pop_assum (strip_assume_tac o REWRITE_RULE [fetched_fend])
  >- (qpat_x_assum ‘∀k. n0 ≤ k ⇒ ¬fend _ _’ (qspec_then ‘k’ mp_tac) >> simp[]) >>
  (* but f's channel is still drained at EOF, so the fetch got no data *)
  ‘deof c (rworld lfd pol ifds m w0 k)’
    by (qspecl_then [‘deof c’, ‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘k1’] mp_tac
          (Q.GENL [‘P’, ‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘a’] run_wpres_from) >>
        impl_tac >- simp[wpres_deof] >>
        disch_then (qspec_then ‘k − k1’ mp_tac) >> simp[]) >>
  ‘l0_chan_of (rworld lfd pol ifds m w0 k) f = SOME c’
    by (qpat_x_assum ‘∀d. l0_chan_of _ _ = _’ (qspec_then ‘k − n0’ mp_tac) >> simp[]) >>
  ‘fkeep lfd h f (rstate lfd pol ifds m w0 k)’ by (first_assum irule >> simp[]) >>
  ‘winv (rworld lfd pol ifds m w0 k)’ by (drule_all winv_run >> simp[]) >>
  drule pround_nodata >> disch_then (qspecl_then [‘h’, ‘f’, ‘c’] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qspec_then ‘bs’ mp_tac) >> simp[]
QED

(* MAIN (D27 (a)): if L1 keeps f at round n0 while f's channel has the
   peer's end-of-file, then L1 stops keeping f at some round k ≥ n0, and
   keeps it until then *)
Theorem eof_reaches:
  oassm lfd pol ifds m w0 ∧ qinb w0 ∧
  F1 lfd pol ifds m w0 ∧ S1 lfd pol ifds m w0 ∧ S3w lfd pol ifds m w0 ∧
  pol_ok hw pol ∧ S4w lfd pol hw ifds m w0 f ∧
  fkeep lfd h f (rstate lfd pol ifds m w0 n0) ∧
  l0_chan_of (rworld lfd pol ifds m w0 n0) f = SOME c ∧
  (EL c (rworld lfd pol ifds m w0 n0).chans).peer_eof ⇒
  ∃k. n0 ≤ k ∧ (∀i. n0 ≤ i ∧ i < k ⇒ fkeep lfd h f (rstate lfd pol ifds m w0 i)) ∧
      ¬fkeep lfd h f (rstate lfd pol ifds m w0 k)
Proof
  strip_tac >>
  ‘∃k. n0 ≤ k ∧ ¬fkeep lfd h f (rstate lfd pol ifds m w0 k)’
    by (CCONTR_TAC >>
        ‘∀k. n0 ≤ k ⇒ fkeep lfd h f (rstate lfd pol ifds m w0 k)’
          by (rpt strip_tac >> CCONTR_TAC >> qpat_x_assum ‘¬∃k. _’ mp_tac >> simp[] >>
              qexists_tac ‘k’ >> simp[]) >>
        mp_tac keep_forever_F >> impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
        simp[]) >>
  (* the least such k *)
  qspec_then ‘λk. n0 ≤ k ∧ ¬fkeep lfd h f (rstate lfd pol ifds m w0 k)’ mp_tac WOP >>
  impl_tac >- (qexists_tac ‘k’ >> simp[]) >>
  BETA_TAC >> disch_then (qx_choose_then ‘k0’ strip_assume_tac) >>
  qexists_tac ‘k0’ >> simp[] >> rpt strip_tac >>
  qpat_x_assum ‘∀m. m < k0 ⇒ _’ (qspec_then ‘i’ mp_tac) >> simp[]
QED
