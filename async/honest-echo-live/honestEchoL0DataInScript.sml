(*
  The data chain of echo_live_l0 at round level (design/47 D, assembly):
  from a round n at which f (connected in round a, not re-connected
  since) is in L1's table on channel c with no EOF seen, everything the
  peer has sent on c by round n eventually reaches the kernel's sent on c,
  unless c is flushed (broken, inbox empty) or episode j0 shows a hard
  error or a D23 timeout.

  Input: in_chain (honest-ffi's run_peer_sent, live_data_hr); no
  re-connect inside the fetch window: fkeep_noconn (from pround_client).
  Server and output: fetched_out.

  MAIN: conn_data_out.
*)
Theory honestEchoL0DataIn
Ancestors
  honestEchoL0DataOut honestEchoL0OutAny honestEchoL0Chain honestEchoL0Excuse
  honestEchoL0Stop honestEchoL0Obl honestL1PFObl
  honestL1PFBroken honestL1PFInput honestL1PFStream honestL1PFClient honestL1PFLive
  honestL1PFRound honestL1PFFlush honestL1PFOutLive honestL1PFOut honestL1PFRefine
Libs
  preamble


Theorem MEM_FConn_log_conns[local]:
  ∀l. MEM (FConn f) l ⇔ MEM f (log_conns l)
Proof
  Induct >> simp[log_conns_def] >> Cases >> simp[]
QED

Theorem fkeep_held[local]:
  fkeep lfd h f ps ⇒ MEM f (MAP SND ps.b.tbl)
Proof
  rw[fkeep_def] >> imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

(* An fd kept by L1 (in its table under h, no EOF, not closing) with its
   channel at the start of round k is not re-connected in round k *)
Theorem fkeep_noconn:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ∧
  fl (rworld lfd pol ifds m w0 k) f R ∧ fkeep lfd h f (rstate lfd pol ifds m w0 k) ⇒
  ¬MEM (FConn f) (rlog lfd pol ifds m w0 k)
Proof
  strip_tac >> ‘fds_lt w0’ by gvs[winv_def] >>
  drule_all refine_at >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  drule prun_round' >> disch_then (qspecl_then [‘f’, ‘k’] strip_assume_tac) >>
  ‘winv (rworld lfd pol ifds m w0 k)’ by (drule_all winv_run >> simp[]) >>
  drule_all pround_client >> strip_tac >>
  simp[MEM_FConn_log_conns]
QED

(* MAIN: the round-level data chain *)
Theorem conn_data_out:
  echo_run lfdn pol w0 ∧ qfresh w0 ∧ qinb w0 ∧ pol_ok hw pol ∧ F1 (n2w lfdn) pol EI ES w0 ∧
  honestL1PFFlush$F2 w0 ∧ honestL1PFFlush$drains (n2w lfdn) pol EI ES w0 c ∧ nshut w0 ∧
  pftrace (n2w lfdn) pol EI ES w0 io ∧
  MEM (FConn f) (rlog (n2w lfdn) pol EI ES w0 a) ∧
  (∀k. a < k ∧ k < n ⇒ ¬MEM (FConn f) (rlog (n2w lfdn) pol EI ES w0 k)) ∧ a < n ∧
  ALOOKUP (rstate (n2w lfdn) pol EI ES w0 n).b.tbl h = SOME f ∧
  ¬MEM f (rstate (n2w lfdn) pol EI ES w0 n).eof ∧
  l0_chan_of (rworld (n2w lfdn) pol EI ES w0 n) f = SOME c ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 n))) f = SOME j0 ⇒
  (∃n'. (EL c (rworld (n2w lfdn) pol EI ES w0 n).chans).peer_sent ≼
        csent (rworld (n2w lfdn) pol EI ES w0 n') c) ∨
  (∃k. n ≤ k ∧ fl_at (n2w lfdn) pol EI ES w0 f j0 k) ∨
  ep_hard_err j0 io ∨ ep_timed_out pf_sendwait j0 io
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  ‘oassm (n2w lfdn) pol EI ES w0’ by fs[oassm_def, echo_run_def] >>
  ‘run_ok (n2w lfdn) pol EI ES w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0) ∧
   (∀n. SND (pcm (n2w lfdn) pol EI ES w0 n) + 1 < dimword (:64)) ∧ fds_lt w0’
    by fs[echo_run_def, winv_def] >>
  ‘fkeep (n2w lfdn) h f (rstate (n2w lfdn) pol EI ES w0 n)’
    by (drule_all fkeep_run >> simp[]) >>
  ‘f ≠ n2w lfdn’ by fs[fkeep_def] >>
  ‘S1 (n2w lfdn) pol EI ES w0’ by (irule S1_interest >> simp[]) >>
  ‘S3w (n2w lfdn) pol EI ES w0’ by metis_tac[echo_S3w] >>
  ‘S4w (n2w lfdn) pol hw EI ES w0 f’ by metis_tac[echo_S4w] >>
  ‘(∃d. fopen (n2w lfdn) pol EI ES w0 h f n d ∧
        (EL c (rworld (n2w lfdn) pol EI ES w0 n).chans).peer_sent ≼
        fdata f (rlogs (n2w lfdn) pol EI ES w0 a (n − a + d))) ∨
   (∃k. n ≤ k ∧ fl_at (n2w lfdn) pol EI ES w0 f j0 k) ∨
   ∃k. n ≤ k ∧ fopen (n2w lfdn) pol EI ES w0 h f n (SUC (k − n)) ∧
       hard_recv f (rrev (n2w lfdn) pol EI ES w0 k)’
    by (irule in_chain >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        TRY (qexists_tac ‘hw’) >> fs[]) >>
  pop_assum strip_assume_tac
  >- ((* fetched within the window: fetched_out *)
      ‘∀k. a < k ∧ k < a + (n − a + d) ⇒ ¬MEM (FConn f) (rlog (n2w lfdn) pol EI ES w0 k)’
        by (rpt gen_tac >> strip_tac >>
            Cases_on ‘k < n’ >- (qpat_x_assum ‘∀k. a < k ∧ k < n ⇒ _’ irule >> fs[]) >>
            qpat_x_assum ‘fopen _ _ _ _ _ _ _ _ _’
              (qspec_then ‘k − n’ mp_tac o REWRITE_RULE [fopen_def]) >>
            impl_tac >- decide_tac >> strip_tac >>
            ‘n + (k − n) = k’ by simp[] >> fs[] >>
            irule fkeep_noconn >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
            TRY (qexists_tac ‘R’ >> first_assum ACCEPT_TAC >> NO_TAC) >>
            TRY (qexists_tac ‘h’ >> first_assum ACCEPT_TAC >> NO_TAC) >>
            fs[echo_run_def]) >>
      ‘∃n'. (EL c (rworld (n2w lfdn) pol EI ES w0 n).chans).peer_sent ≼
              csent (rworld (n2w lfdn) pol EI ES w0 n') c ∨
            ep_hard_err j0 io ∨ ep_timed_out pf_sendwait j0 io’
        by (irule fetched_out >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
            qexistsl_tac [‘n − a + d’, ‘a’, ‘f’, ‘n’] >> simp[] >>
            drule fkeep_held >> simp[]) >>
      TRY (disj1_tac >> qexists_tac ‘n'’ >> first_assum ACCEPT_TAC >> NO_TAC) >>
      fs[])
  >- (disj2_tac >> disj1_tac >> metis_tac[]) >>
  (* a hard recv error, f kept from n to k *)
  disj2_tac >> disj2_tac >> disj1_tac >>
  drule recv_excuse_j0 >> disch_then drule >> disch_then drule >>
  disch_then (qspec_then ‘k’ mp_tac) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> rpt strip_tac >>
      qpat_x_assum ‘fopen _ _ _ _ _ _ _ _ _’
        (qspec_then ‘i − n’ mp_tac o REWRITE_RULE [fopen_def]) >>
      impl_tac >- decide_tac >> strip_tac >>
      ‘n + (i − n) = i’ by decide_tac >> fs[] >>
      drule fkeep_held >> simp[]) >>
  simp[]
QED
