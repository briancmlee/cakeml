(*
  From L1's fetches to the kernel's sent (design/47 D, assembly): bytes
  L1 has fetched on f since f's connect round a (no re-connect of f in
  the window) are client j's data in the server's run, which the echo
  writes back to client j (echo_out_live), which reaches the kernel on f's
  channel c (out_chain_any) -- or episode j0 shows a hard error or a D23
  timeout.

  MAIN: fetched_out.
*)
Theory honestEchoL0DataOut
Ancestors
  honestEchoL0OutAny honestEchoL0OutAll honestEchoL0Frozen honestEchoL0SrvOut
  honestEchoL0Excuse honestEchoL0Obl
  honestL1PFBroken honestL1PFInput honestL1PFStream honestL1PFClient
  honestL1PFFlushLive honestL1PFFlush honestL1PFOutLive honestL1PFOut honestL1PFLive
  honestL1PFRefine
Libs
  preamble


Theorem pfx_trans[local]:
  x ≼ y ∧ y ≼ z ⇒ x ≼ z
Proof
  rw[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]
QED

(* MAIN: what L1 fetched on f since its connect reaches the kernel *)
Theorem fetched_out:
  echo_run lfdn pol w0 ∧ qfresh w0 ∧ F1 (n2w lfdn) pol EI ES w0 ∧
  honestL1PFFlush$F2 w0 ∧ honestL1PFFlush$drains (n2w lfdn) pol EI ES w0 c ∧ nshut w0 ∧
  pftrace (n2w lfdn) pol EI ES w0 io ∧ f ≠ n2w lfdn ∧
  MEM (FConn f) (rlog (n2w lfdn) pol EI ES w0 a) ∧
  (∀k. a < k ∧ k < a + M ⇒ ¬MEM (FConn f) (rlog (n2w lfdn) pol EI ES w0 k)) ∧
  D ≼ fdata f (rlogs (n2w lfdn) pol EI ES w0 a M) ∧ a < n ∧ n ≤ a + M ∧
  held f (rstate (n2w lfdn) pol EI ES w0 n) ∧
  l0_chan_of (rworld (n2w lfdn) pol EI ES w0 n) f = SOME c ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 n))) f = SOME j0 ⇒
  ∃n'. D ≼ csent (rworld (n2w lfdn) pol EI ES w0 n') c ∨
       ep_hard_err j0 io ∨ ep_timed_out pf_sendwait j0 io
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS (BETA_RULE th))) >>
  ‘oassm (n2w lfdn) pol EI ES w0’ by fs[oassm_def, echo_run_def] >>
  ‘cdata (cl (FST (pcm (n2w lfdn) pol EI ES w0 (SUC a))) f)
         (pars (n2w lfdn) pol EI ES w0 0 (a + M)) =
   fdata f (rlogs (n2w lfdn) pol EI ES w0 a M)’
    by (drule client_since >> disch_then drule >> disch_then (qspec_then ‘M’ mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  ‘ALOOKUP (FST (pcm (n2w lfdn) pol EI ES w0 n)) f =
   SOME (cl (FST (pcm (n2w lfdn) pol EI ES w0 (SUC a))) f)’
    by (drule client_stable >> disch_then drule >> disch_then drule >>
        disch_then (qspec_then ‘n’ mp_tac) >> simp[]) >>
  qabbrev_tac ‘j = cl (FST (pcm (n2w lfdn) pol EI ES w0 (SUC a))) f’ >>
  ‘D ≼ cdata j (pars (n2w lfdn) pol EI ES w0 0 (a + M))’ by fs[] >>
  drule echo_out_live >> disch_then (qspecl_then [‘j’, ‘a + M’] strip_assume_tac)
  >- (‘D = []’ by (Cases_on ‘D’ >> fs[]) >> qexists_tac ‘n’ >> simp[]) >>
  ‘(EL j (FST (hst (n2w lfdn) EI ES PSK N)).clients).outgoing ≼
   (EL j (FST (hst (n2w lfdn) EI ES PSK (N + n))).clients).outgoing’
    by (qpat_x_assum ‘j < LENGTH (FST (hst _ _ _ _ N)).clients’ assume_tac >>
        drule hst_out_mono >> disch_then (qspec_then ‘n’ mp_tac) >> simp[]) >>
  ‘∃n'. (EL j (FST (hst (n2w lfdn) EI ES PSK (N + n))).clients).outgoing ≼
          csent (rworld (n2w lfdn) pol EI ES w0 n') c ∨
        ep_hard_err j0 io ∨ ep_timed_out pf_sendwait j0 io’
    by (irule out_chain_any >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        TRY (qexistsl_tac [‘f’, ‘n’]) >> fs[]) >>
  qexists_tac ‘n'’ >>
  TRY (disj2_tac >> asm_rewrite_tac [] >> NO_TAC) >>
  disj1_tac >>
  irule pfx_trans >>
  qexists_tac ‘(EL j (FST (hst (n2w lfdn) EI ES PSK (N + n))).clients).outgoing’ >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  irule pfx_trans >>
  qexists_tac ‘(EL j (FST (hst (n2w lfdn) EI ES PSK N)).clients).outgoing’ >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  irule pfx_trans >>
  qexists_tac ‘cdata j (pars (n2w lfdn) pol EI ES w0 0 (a + M))’ >>
  conj_tac >> first_assum ACCEPT_TAC
QED
