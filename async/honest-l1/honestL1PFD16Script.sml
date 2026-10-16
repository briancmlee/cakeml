(*
  R1-live, the D16 corollary (design/36 §6, §9 D16): if a hard error on an
  fd f is reported only when f's connection really broke and nothing is
  left to read (HD16, on the observed fetch log and the channel at round
  boundaries), then every byte that was in f's kernel inbox reaches L1's
  fetch log (and so psk, by live_data's part (B)), unless the connection
  really broke and the kernel discarded unread data (flushed).

  The main live-data theorem allows the episode to end early (Eof2) on a
  spurious hard error; this corollary excludes exactly that. An orderly
  EOF needs no hypothesis: L0's recv returns 0 only with an empty inbox,
  after the peer's EOF or a real break.
*)
Theory honestL1PFD16
Ancestors
  honestL1PFConnRun honestL1PFConn honestL1PFClient honestL1PFStream honestL1PFLive honestL1PFRound honestL1PFRefine
  honestL1PFModel honestL1Steps honestL1Props honestL1Inv honestL1Model
  honestL0WorldInv honestL0WorldProps honestL0Rely honestL0World honestL0 asyncCore
Libs
  preamble

(* Flushed: every R is (vacuously) still to come *)
Theorem flushed_all:
  flushed w f ⇔ ∀R. fl w f R
Proof
  eq_tac >- simp[fl_def] >>
  rw[fl_def] >>
  first_assum (qspec_then ‘[]’ assume_tac) >>
  ‘∃j. l0_chan_of w f = SOME j’ by gvs[front_def, flushed_def] >>
  first_x_assum (qspec_then ‘REPLICATE (SUC (LENGTH (EL j w.chans).inbox)) 0w’ mp_tac) >>
  REWRITE_TAC [front_def] >> strip_tac >> TRY (first_assum ACCEPT_TAC) >>
  imp_res_tac IS_PREFIX_LENGTH >> gvs[]
QED

(* recv returning 0: the inbox was empty (so R = []), or the channel is
   flushed *)
Theorem recv_zero:
  l0_recv f n w = (Ok 0, d, w') ∧ 0 < n ∧ l0_rely w ∧ noconn w ∧ fl w f R ⇒
  R = [] ∨ (w' = w ∧ flushed w f)
Proof
  rw[l0_recv_def, AllCaseEqs(), fail_def] >> gvs[] >>
  TRY (gvs[l0_rely_def] >> NO_TAC) >>
  gvs[fl_def, front_def, flushed_def] >>
  TRY (‘0 < w.ch.short j w.hist (LENGTH (EL j w.chans).inbox)’
         by gvs[l0_rely_def, LENGTH_NIL] >> gvs[MIN_DEF] >> NO_TAC) >>
  gvs[] >> rw[] >> gvs[] >>
  ‘0 < LENGTH (EL j w.chans).inbox’ by (Cases_on ‘(EL j w.chans).inbox’ >> fs[]) >>
  fs[l0_rely_def] >> res_tac >> metis_tac[prim_recTheory.LESS_REFL]
QED

Theorem flushed_hist[simp]:
  flushed (w with hist := h) f ⇔ flushed w f
Proof
  simp[flushed_def, l0_chan_of_def]
QED

Theorem sys_recv_zero:
  winv w ∧ fl w f R ∧ 0 < k ∧ k < 256 ** 8 ∧ sys_recv f k w = SOME (out, w', ev) ∧
  l0_res_of out = Ok 0 ⇒
  R = [] ∨ flushed w' f
Proof
  rw[sys_recv_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  qabbrev_tac ‘wt = l0_tick «sys_recv» w’ >>
  ‘fl wt f R ∧ noconn wt ∧ l0_rely wt’
    by (gvs[Abbr ‘wt’, winv_def, fl_tick, noconn_tick] >>
        irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def, l0_hdr_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  ‘l0_res_ok r’
    by (qspecl_then [‘wt’, ‘f’, ‘k’, ‘r’, ‘d’, ‘w'’] mp_tac
          (Q.GENL [‘w’, ‘f’, ‘n’, ‘r’, ‘d’, ‘w'’] recv_res_ok) >> simp[]) >>
  ‘l0_res_of (enc_res r ++ d ++ REPLICATE (k − LENGTH d) 0w) = r’
    by (REWRITE_TAC [GSYM APPEND_ASSOC] >> irule l0_res_of_enc_app >> simp[]) >>
  gvs[] >> drule recv_zero >> simp[] >> disch_then drule >> rw[] >> simp[]
QED

(* Once f's input has ended in L1, the rest of the fetch neither reads f
   nor disturbs its kernel input *)
Theorem pf_fetch_ended:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ∧ winv w ∧ fl w f R ∧
    MEM f ps.eof ∧ f ≠ lfd ⇒
    fl w' f R ∧ ¬fetched f log
Proof
  Induct >- simp[pf_fetch_def, fetched_def] >>
  rpt gen_tac >> rename1 ‘g :: fs’ >> strip_tac >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ mp_tac >> simp[Once pf_fetch_def] >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  ‘g ≠ f’ by (strip_tac >> gvs[wants_input_def]) >>
  IF_CASES_TAC
  >- (simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
      pairarg_tac >> fs[AllCaseEqs()] >> rveq >>
      ‘winv w1 ∧ fl w1 f R’ by metis_tac[sys_fl, sys_winv] >>
      gvs[AllCaseEqs()] >> first_x_assum drule >> simp[] >>
      gvs[fetched_def])
  >> simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  pairarg_tac >> fs[AllCaseEqs()] >> rveq >>
  ‘winv w1 ∧ fl w1 f R’ by metis_tac[sys_fl, sys_winv] >>
  gvs[AllCaseEqs()] >> first_x_assum drule >> simp[set_inb_def] >>
  gvs[fetched_def]
QED

(* An orderly EOF on f in the fetch: what was at the front of f's kernel
   inbox was fetched, or f's channel is flushed *)
Theorem pf_fetch_feof:
  ∀fs w ps w' ps' log evs R.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ∧ winv w ∧ fl w f R ∧
    fkeep lfd h f ps ∧ MEM (FEof f) log ⇒
    R ≼ fdata f log ∨ flushed w' f
Proof
  Induct >- simp[pf_fetch_def] >>
  rpt gen_tac >> rename1 ‘g :: fs’ >> strip_tac >>
  ‘¬MEM f ps.eof ∧ f ≠ lfd ∧ ¬MEM f ps.acq’
    by (qpat_x_assum ‘fkeep _ _ _ _’ mp_tac >> simp[fkeep_def]) >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ mp_tac >> simp[Once pf_fetch_def] >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  IF_CASES_TAC
  >- ((* accept on the listener *)
      ‘g ≠ f’ by (strip_tac >> fs[]) >>
      simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
      pairarg_tac >> fs[AllCaseEqs()] >> rveq >>
      ‘winv w1 ∧ fl w1 f R’ by metis_tac[sys_fl, sys_winv] >>
      gvs[AllCaseEqs()] >>
      first_x_assum drule >> disch_then (qspec_then ‘R’ mp_tac) >> impl_tac >>
      TRY (simp[] >> NO_TAC) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (‘¬MEM (n2w k) (l0_used w)’
             by (irule sys_accept_fresh >> gvs[winv_def] >> metis_tac[]) >>
           ‘n2w k ≠ f’ by metis_tac[fl_used]) >>
      qpat_x_assum ‘fkeep _ _ _ _’ mp_tac >> simp[fkeep_def])
  >> Cases_on ‘g = f’
  >- ((* recv on f *)
      gvs[] >> simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
      pairarg_tac >> fs[CaseEq "option", CaseEq "prod"] >>
      ‘0 < pf_chunk ∧ pf_chunk < 256 ** 8’ by EVAL_TAC >>
      ‘winv w1’ by metis_tac[sys_winv] >>
      qspecl_then [‘w’, ‘f’, ‘R’, ‘pf_chunk’, ‘out’, ‘w1’, ‘ev’] mp_tac
        (Q.GENL [‘w’, ‘f’, ‘R’, ‘k’, ‘out’, ‘w'’, ‘ev’] sys_recv_fl) >>
      impl_tac >- fs[] >> strip_tac >>
      Cases_on ‘l0_res_of out’ >> fs[] >>
      TRY (rename1 ‘Ok n’ >> Cases_on ‘0 < n’) >>
      TRY (rename1 ‘Fail e _’ >> Cases_on ‘l1_transient e’) >>
      fs[] >> rveq >> fs[] >>
      (* EOF *)
      TRY (TRY (‘n = 0’ by decide_tac >> fs[]) >>
           ‘l0_res_of out = Ok 0’ by fs[] >>
           qspecl_then [‘w’, ‘f’, ‘R’, ‘pf_chunk’, ‘out’, ‘w1’, ‘ev’] mp_tac
             (Q.GENL [‘w’, ‘f’, ‘R’, ‘k’, ‘out’, ‘w'’, ‘ev’] sys_recv_zero) >>
           impl_tac >- fs[] >> strip_tac >> simp[] >>
           disj2_tac >> simp[flushed_all] >> gen_tac >>
           qpat_x_assum ‘flushed w1 f’ (mp_tac o REWRITE_RULE [flushed_all]) >>
           disch_then (qspec_then ‘R'’ assume_tac) >>
           drule pf_fetch_ended >> simp[] >> disch_then drule >> simp[] >> NO_TAC) >>
      (* an error: f's input has ended in L1, so no EOF follows *)
      TRY (drule pf_fetch_ended >> simp[] >> disch_then drule >>
           simp[fetched_def, EXISTS_MEM] >> metis_tac[] >> NO_TAC) >>
      (* a retried failure *)
      TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
      (* data *)
      TRY (simp[prefix_app] >> NO_TAC) >>
      qpat_x_assum ‘∀w ps w' ps' log evs R. _’
        (qspecl_then [‘w1’, ‘set_inb f (TAKE m (DROP 13 out)) ps’, ‘w'’, ‘ps'’, ‘log'’,
                      ‘evs'’, ‘R'’] mp_tac) >>
      impl_tac >- (fs[] >> qpat_x_assum ‘fkeep _ _ _ ps’ mp_tac >> simp[fkeep_def]) >>
      strip_tac >> simp[])
  >> (* recv on another fd *)
  simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  pairarg_tac >> fs[AllCaseEqs()] >> rveq >>
  ‘winv w1 ∧ fl w1 f R’ by metis_tac[sys_fl, sys_winv] >>
  gvs[AllCaseEqs()] >>
  first_x_assum drule >> disch_then (qspec_then ‘R’ mp_tac) >> impl_tac >>
  TRY (simp[] >> NO_TAC) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘fkeep _ _ _ _’ mp_tac >> simp[fkeep_def]
QED

Theorem pround_feof:
  pround lfd hw hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧
  winv w ∧ fl w f R ∧ fkeep lfd h f ps ∧ MEM (FEof f) log ⇒
  R ≼ fdata f log ∨ flushed w' f
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >>
  gvs[pf_tail_def, AllCaseEqs()] >>
  rename1 ‘pacts _ _ _ = SOME (rs, aevs, wa, pa)’ >>
  drule_all pacts_fl >> strip_tac >>
  drule_all pacts_f >> strip_tac >>
  drule_all pacts_winv >> strip_tac >>
  drule_all l1_polls_fl >> strip_tac >>
  drule_all l1_polls_winv >> strip_tac >>
  drule_all l1_flush_fl >> strip_tac >>
  drule_all l1_flush_f >> strip_tac >>
  drule_all l1_flush_winv >> strip_tac >>
  ‘fkeep lfd h f (pa with b := b2)’ by (irule fkeep_b_same >> fs[]) >>
  drule_all pf_fetch_winv >> strip_tac >>
  drule_all pf_fetch_feof >> strip_tac >> simp[] >>
  drule pf_fetch_b >> strip_tac >>
  ‘¬MEM f ps3.b.closing’ by (gvs[] >> qpat_x_assum ‘fkeep _ _ _ (pa with b := b2)’ mp_tac >>
                             simp[fkeep_def]) >>
  disj2_tac >> gvs[flushed_all] >> gen_tac >>
  first_x_assum (qspec_then ‘R'’ assume_tac) >>
  drule_all l1_reap_fl >> simp[]
QED

(* ------------------------------------------------------------------------
   Along the run
   ------------------------------------------------------------------------ *)

Theorem rlogs_SUC:
  rlogs lfd hw ifds m w0 n0 (SUC d) =
  rlogs lfd hw ifds m w0 n0 d ++ rlog lfd hw ifds m w0 (n0 + d)
Proof
  ‘SUC d = d + 1’ by simp[] >> pop_assum SUBST1_TAC >>
  simp[rlogs_add] >> simp[rlogs_def]
QED

Theorem fdata_app[simp]:
  fdata f (l1 ++ l2) = fdata f l1 ++ fdata f l2 ∧ (fend f (l1 ++ l2) ⇔ fend f l1 ∨ fend f l2)
Proof
  simp[fdata_def, fend_def]
QED

(* f's stream round by round, up to the first round that ends it *)
Theorem stream_upto:
  run_ok lfd hw ifds m w0 ∧ winv w0 ⇒
  ∀d R. fl (rworld lfd hw ifds m w0 n0) f R ∧ fkeep lfd h f (rstate lfd hw ifds m w0 n0) ⇒
    R ≼ fdata f (rlogs lfd hw ifds m w0 n0 d) ∨
    (∃k R'. n0 ≤ k ∧ k < n0 + d ∧ fend f (rlog lfd hw ifds m w0 k) ∧
            fl (rworld lfd hw ifds m w0 k) f R' ∧ fkeep lfd h f (rstate lfd hw ifds m w0 k) ∧
            R = fdata f (rlogs lfd hw ifds m w0 n0 (k − n0)) ++ R') ∨
    (¬fend f (rlogs lfd hw ifds m w0 n0 d) ∧
     ∃R'. R = fdata f (rlogs lfd hw ifds m w0 n0 d) ++ R' ∧
          fl (rworld lfd hw ifds m w0 (n0 + d)) f R' ∧
          fkeep lfd h f (rstate lfd hw ifds m w0 (n0 + d)))
Proof
  strip_tac >> Induct >- (rpt strip_tac >> simp[rlogs_def]) >>
  rpt strip_tac >> first_x_assum drule_all >> strip_tac
  >- (disj1_tac >> simp[rlogs_SUC, prefix_app])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [‘k’, ‘R'’] >> simp[]) >>
  Cases_on ‘fend f (rlog lfd hw ifds m w0 (n0 + d))’
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [‘n0 + d’, ‘R'’] >> simp[]) >>
  drule_all stream_step >> strip_tac >> gvs[]
  >- (disj1_tac >> simp[rlogs_SUC]) >>
  disj2_tac >> disj2_tac >> simp[rlogs_SUC, ADD_CLAUSES] >>
  qexists_tac ‘R''’ >> simp[]
QED

(* ------------------------------------------------------------------------
   The corollary
   ------------------------------------------------------------------------ *)

(* HD16 (an explicit hypothesis, on the fetch log and f's channel at round
   boundaries): a hard error on f is reported only when f's connection
   really broke and nothing is left to read *)
Definition HD16_def:
  HD16 lfd hw ifds m w0 f ⇔
    ∀k. MEM (FReset f) (rlog lfd hw ifds m w0 k) ⇒
        flushed (rworld lfd hw ifds m w0 (SUC k)) f
End

Theorem live_data_d16:
  run_ok lfd hw ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd hw ifds m w0 n) + 1 < dimword (:64)) ∧
  F1 lfd hw ifds m w0 ∧ S1 lfd hw ifds m w0 ∧ S3 lfd hw ifds m w0 ∧
  S4 lfd hw ifds m w0 f ∧ HD16 lfd hw ifds m w0 f ⇒
  ∀R n0 h. ALOOKUP (rstate lfd hw ifds m w0 n0).b.tbl h = SOME f ∧
           ¬MEM f (rstate lfd hw ifds m w0 n0).eof ∧ fl (rworld lfd hw ifds m w0 n0) f R ⇒
           (∃d. fopen lfd hw ifds m w0 h f n0 d ∧ R ≼ fdata f (rlogs lfd hw ifds m w0 n0 d)) ∨
           ∃k. n0 ≤ k ∧ flushed (rworld lfd hw ifds m w0 k) f
Proof
  rpt strip_tac >>
  drule_all stream_progress >> strip_tac
  >- (CCONTR_TAC >>
      pop_assum (strip_assume_tac o SIMP_RULE bool_ss [NOT_EXISTS_THM, DE_MORGAN_THM]) >>
      ‘fds_lt w0’ by fs[winv_def] >>
      drule_all fkeep_run >> strip_tac >>
      drule_all stream_upto >> disch_then (qspec_then ‘d’ strip_assume_tac) >> gvs[] >>
      TRY (metis_tac[] >> NO_TAC) >>
      ‘winv (rworld lfd hw ifds m w0 k)’ by (drule_all winv_run >> simp[]) >>
      drule prun_round' >> disch_then (qspecl_then [‘f’, ‘k’] strip_assume_tac) >>
      Cases_on ‘MEM (FReset f) (rlog lfd hw ifds m w0 k)’
      >- (qpat_x_assum ‘HD16 _ _ _ _ _ _’ (mp_tac o REWRITE_RULE [HD16_def]) >>
          disch_then drule >> strip_tac >>
          ‘n0 ≤ SUC k’ by decide_tac >> metis_tac[]) >>
      ‘MEM (FEof f) (rlog lfd hw ifds m w0 k)’
        by (gvs[fend_def, EXISTS_MEM] >> metis_tac[]) >>
      drule_all pround_feof >> strip_tac
      >- (‘n0 + (k − n0) = k’ by decide_tac >>
          ‘fdata f (rlogs lfd hw ifds m w0 n0 (k − n0)) ++ R' ≼
           fdata f (rlogs lfd hw ifds m w0 n0 (SUC (k − n0)))’
            by (REWRITE_TAC [rlogs_SUC] >> fs[]) >>
          ‘fopen lfd hw ifds m w0 h f n0 (SUC (k − n0))’
            by (fs[fopen_def] >> rpt strip_tac >> ‘i < d’ by decide_tac >> metis_tac[]) >>
          metis_tac[])
      >> ‘n0 ≤ SUC k’ by decide_tac >> metis_tac[])
  >> disj1_tac >> qexists_tac ‘d’ >> simp[]
QED

(* In the version-2 world: what was in f's kernel inbox at round n0 is
   eventually client j's data in psk, unless f's connection really broke
   and the kernel discarded unread data *)
Theorem live_data_psk_d16:
  run_ok lfd hw ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd hw ifds m w0 n) + 1 < dimword (:64)) ∧
  F1 lfd hw ifds m w0 ∧ S1 lfd hw ifds m w0 ∧ S3 lfd hw ifds m w0 ∧
  S4 lfd hw ifds m w0 f ∧ HD16 lfd hw ifds m w0 f ⇒
  ∀n0 h c.
    ALOOKUP (rstate lfd hw ifds m w0 n0).b.tbl h = SOME f ∧
    ¬MEM f (rstate lfd hw ifds m w0 n0).eof ∧
    l0_chan_of (rworld lfd hw ifds m w0 n0) f = SOME c ⇒
    (∃d. (EL c (rworld lfd hw ifds m w0 n0).chans).inbox ≼
         cdata (cl (FST (pcm lfd hw ifds m w0 n0)) f) (pars lfd hw ifds m w0 n0 d)) ∨
    ∃k. n0 ≤ k ∧ flushed (rworld lfd hw ifds m w0 k) f
Proof
  strip_tac >> rpt strip_tac >>
  mp_tac live_data_d16 >> impl_tac >- simp[] >>
  disch_then (qspecl_then [‘(EL c (rworld lfd hw ifds m w0 n0).chans).inbox’, ‘n0’, ‘h’]
                          mp_tac) >>
  impl_tac >- simp[fl_def, front_def] >> strip_tac
  >- (disj1_tac >>
  ‘fds_lt w0’ by fs[winv_def] >>
  ‘∃s. pv_rel lfd (FST (pcm lfd hw ifds m w0 n0)) (rstate lfd hw ifds m w0 n0) s’
    by (drule_all refine_at >> metis_tac[]) >>
  ‘∃j. ALOOKUP (FST (pcm lfd hw ifds m w0 n0)) f = SOME j’
    by (fs[pv_rel_def] >> res_tac >> Cases_on ‘ALOOKUP (FST (pcm lfd hw ifds m w0 n0)) f’ >>
        gvs[ALOOKUP_NONE]) >>
  ‘cl (FST (pcm lfd hw ifds m w0 n0)) f = j’ by simp[cl_def] >>
  drule_all client_rounds >> strip_tac >>
  qexists_tac ‘d’ >> gvs[])
  >> disj2_tac >> metis_tac[]
QED
