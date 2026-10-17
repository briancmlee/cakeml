(*
  The output chain for any later outgoing stream (design/47 D, assembly):
  for the PF echo, from a round n at which L1 holds f (channel c, episode
  j0), and any later round N up to which f is not re-connected, client j's
  outgoing stream at N eventually reaches the kernel, or episode j0 shows
  a hard error or a D23 timeout on the trace.

  If f stays held to N: out_chain at N (held_chan_stretch, keep_to_round).
  Else at the first release, honest-ffi's close_flushed: the kernel has
  taken all of client j's outgoing stream (and it is frozen from then on:
  release_quiet, run_quiet, outgoing_frozen), or an output excuse.

  MAIN: out_chain_all.
*)
Theory honestEchoL0OutAll
Ancestors
  honestEchoL0Chain honestEchoL0SrvOut honestEchoL0Excuse honestL1PFBroken
  honestEchoL0Obl honestL1PFRefine honestL1PFFlushLive honestL1PFFlush honestL1PFOutLive
  honestL1PFLive honestL1PFOut
Libs
  preamble


Theorem out_chain_all:
  echo_run lfdn pol w0 ∧ qfresh w0 ∧ F1 (n2w lfdn) pol EI ES w0 ∧
  honestL1PFFlush$F2 w0 ∧ honestL1PFFlush$drains (n2w lfdn) pol EI ES w0 c ∧ nshut w0 ∧
  pftrace (n2w lfdn) pol EI ES w0 io ∧ f ≠ n2w lfdn ∧
  held f (rstate (n2w lfdn) pol EI ES w0 n) ∧
  l0_chan_of (rworld (n2w lfdn) pol EI ES w0 n) f = SOME c ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 n))) f = SOME j0 ∧ n ≤ N ∧
  (∀k. n ≤ k ∧ k ≤ N ⇒ ALOOKUP (FST (pcm (n2w lfdn) pol EI ES w0 k)) f = SOME j) ∧
  (∀k. n ≤ k ∧ k < N ⇒ ¬MEM (FConn f) (rlog (n2w lfdn) pol EI ES w0 k)) ∧
  j < LENGTH (FST (hst (n2w lfdn) EI ES PSK n)).clients ⇒
  ∃n'. (EL j (FST (hst (n2w lfdn) EI ES PSK N)).clients).outgoing ≼
         csent (rworld (n2w lfdn) pol EI ES w0 n') c ∨
       ep_hard_err j0 io ∨ ep_timed_out pf_sendwait j0 io
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS (BETA_RULE th))) >>
  ‘oassm (n2w lfdn) pol EI ES w0’ by fs[oassm_def, echo_run_def] >>
  ‘run_ok (n2w lfdn) pol EI ES w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0)’
    by fs[oassm_def] >>
  Cases_on ‘∀k. n ≤ k ∧ k ≤ N ⇒ held f (rstate (n2w lfdn) pol EI ES w0 k)’
  >- ((* f held to N *)
      ‘l0_chan_of (rworld (n2w lfdn) pol EI ES w0 N) f = SOME c’
        by (drule held_chan_stretch >> disch_then drule >> disch_then (qspec_then ‘N − n’ mp_tac) >>
            impl_tac
            >- (rpt strip_tac >> qpat_x_assum ‘∀k. n ≤ k ∧ k ≤ N ⇒ _’ irule >> fs[]) >>
            ‘n + (N − n) = N’ by fs[] >> simp[]) >>
      ‘ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 N))) f = SOME j0’
        by (irule keep_to_round >> simp[] >> qexists_tac ‘n’ >> simp[] >>
            rpt strip_tac >> first_x_assum irule >> simp[]) >>
      ‘held f (rstate (n2w lfdn) pol EI ES w0 N)’ by (first_x_assum irule >> simp[]) >>
      ‘cl (FST (pcm (n2w lfdn) pol EI ES w0 N)) f = j’
        by (qpat_x_assum ‘∀k. n ≤ k ∧ k ≤ N ⇒ ALOOKUP _ _ = _’ (qspec_then ‘N’ mp_tac) >>
            simp[cl_def]) >>
      ‘∃n'. N ≤ n' ∧
            ((EL (cl (FST (pcm (n2w lfdn) pol EI ES w0 N)) f)
                 (FST (hst (n2w lfdn) EI ES PSK N)).clients).outgoing ≼
               csent (rworld (n2w lfdn) pol EI ES w0 n') c ∨
             ep_hard_err j0 io ∨ ep_timed_out pf_sendwait j0 io)’
        by (irule out_chain >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[]) >>
      qexists_tac ‘n'’ >> gvs[]) >>
  (* the first release *)
  fs[] >> rename1 ‘¬MEM f (MAP SND (rstate _ _ _ _ _ kc).b.tbl)’ >>
  ‘∃t. (n ≤ t ∧ t ≤ N ∧ ¬held f (rstate (n2w lfdn) pol EI ES w0 t)) ∧
       ∀t'. t' < t ⇒ ¬(n ≤ t' ∧ t' ≤ N ∧ ¬held f (rstate (n2w lfdn) pol EI ES w0 t'))’
    by (ho_match_mp_tac WOP >> metis_tac[]) >>
  ‘n < t’ by (CCONTR_TAC >> ‘t = n’ by simp[] >> fs[]) >>
  ‘∃k. t = SUC k’ by (qexists_tac ‘t − 1’ >> simp[]) >> rveq >>
  ‘∀i. n ≤ i ∧ i ≤ k ⇒ held f (rstate (n2w lfdn) pol EI ES w0 i)’
    by (rpt strip_tac >> first_x_assum (qspec_then ‘i’ mp_tac) >> simp[]) >>
  ‘l0_chan_of (rworld (n2w lfdn) pol EI ES w0 k) f = SOME c’
    by (qpat_assum ‘l0_chan_of (rworld _ _ _ _ _ n) f = SOME c’ assume_tac >>
        drule held_chan_stretch >> disch_then drule >> disch_then (qspec_then ‘k − n’ mp_tac) >>
        impl_tac
        >- (rpt strip_tac >> qpat_x_assum ‘∀i. n ≤ i ∧ i ≤ k ⇒ _’ (qspec_then ‘i’ mp_tac) >> fs[]) >>
        ‘n + (k − n) = k’ by fs[] >> simp[]) >>
  ‘held f (rstate (n2w lfdn) pol EI ES w0 k)’ by (first_x_assum irule >> simp[]) >>
  ‘csent (rworld (n2w lfdn) pol EI ES w0 (SUC k)) c =
     (EL (cl (FST (pcm (n2w lfdn) pol EI ES w0 k)) f)
         (FST (hst (n2w lfdn) EI ES PSK (SUC k))).clients).outgoing ∨
   MEM f (rstate (n2w lfdn) pol EI ES w0 k).b.gone ∨
   hard_send f (rrev (n2w lfdn) pol EI ES w0 k) ∨ rdrop (n2w lfdn) pol EI ES w0 k f’
    by (REWRITE_TAC [GSYM oout_def] >> irule close_flushed >> fs[]) >>
  pop_assum strip_assume_tac >>
  TRY ((* the kernel took it all; client j's outgoing frozen from SUC k *)
      qpat_x_assum ‘csent _ c = _’ assume_tac >>
      qexists_tac ‘SUC k’ >> disj1_tac >>
      ‘cl (FST (pcm (n2w lfdn) pol EI ES w0 k)) f = j’
        by (qpat_x_assum ‘∀k'. n ≤ k' ∧ k' ≤ N ⇒ _’ (qspec_then ‘k’ mp_tac) >>
            simp[cl_def]) >>
      ‘cquiet f (rstate (n2w lfdn) pol EI ES w0 (SUC k))’
        by (irule release_quiet >> fs[] >> first_x_assum irule >> simp[]) >>
      ‘∀i. SUC k ≤ i ∧ i ≤ N ⇒ cquiet f (rstate (n2w lfdn) pol EI ES w0 i)’
        by (rpt strip_tac >> drule run_quiet >> disch_then drule >> disch_then drule >>
            disch_then (qspec_then ‘i’ mp_tac) >>
            impl_tac >- (rpt strip_tac >> fs[] >> qpat_x_assum ‘∀k. n ≤ k ∧ k < N ⇒ ¬MEM (FConn f) _’ (qspec_then ‘i'’ mp_tac) >> simp[]) >> simp[]) >>
      ‘j < LENGTH (FST (hst (n2w lfdn) EI ES PSK (SUC k))).clients’
        by (‘n + (SUC k − n) = SUC k’ by decide_tac >>
            qpat_x_assum ‘j < LENGTH (FST (hst _ _ _ _ n)).clients’ assume_tac >>
            drule hst_out_mono >> disch_then (qspec_then ‘SUC k − n’ mp_tac) >> fs[]) >>
      ‘(EL j (FST (hst (n2w lfdn) EI ES PSK (SUC k + (N − SUC k)))).clients).outgoing =
       (EL j (FST (hst (n2w lfdn) EI ES PSK (SUC k))).clients).outgoing’
        by (irule outgoing_frozen >> simp[] >> qexists_tac ‘f’ >> rpt strip_tac
            >- (qpat_x_assum ‘∀k'. n ≤ k' ∧ k' ≤ N ⇒ _’ irule >> fs[]) >>
            ‘cquiet f (rstate (n2w lfdn) pol EI ES w0 k')’
              by (qpat_x_assum ‘∀i. SUC k ≤ i ∧ i ≤ N ⇒ _’ irule >> fs[]) >>
            fs[cquiet_def]) >>
      ‘SUC k + (N − SUC k) = N’ by decide_tac >> fs[] >> NO_TAC) >>
  (* an output excuse *)
  qexists_tac ‘SUC k’ >> disj2_tac >>
  TRY (qpat_x_assum ‘MEM f (rstate _ _ _ _ _ k).b.gone’ assume_tac >>
       drule run_gone_cause >> disch_then drule >>
       disch_then (qx_choose_then ‘k1’ (fn th => MAP_EVERY assume_tac (CONJUNCTS th))) >>
       Cases_on ‘n ≤ k1’
       >- (drule excuse_j0 >> disch_then drule >> disch_then drule >> disch_then drule >>
           disch_then (qspec_then ‘k1’ mp_tac) >> impl_tac >> simp[] >> rpt conj_tac >>
           TRY (first_assum ACCEPT_TAC) >> TRY decide_tac >>
           rpt strip_tac >> qpat_x_assum ‘∀i. n ≤ i ∧ i ≤ k ⇒ _’ (qspec_then ‘i’ mp_tac) >> fs[]) >>
       drule excuse_back >> disch_then drule >> disch_then drule >> disch_then drule >>
       disch_then (qspec_then ‘k1’ mp_tac) >> impl_tac >> simp[] >> rpt conj_tac >>
       TRY (first_assum ACCEPT_TAC) >> TRY decide_tac >>
       rpt strip_tac >> irule run_okeys_held >> fs[] >> NO_TAC) >>
  (* hard_send or rdrop in round k *)
  drule excuse_j0 >> disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (qspec_then ‘k’ mp_tac) >> impl_tac >> simp[] >> rpt conj_tac >>
  TRY (asm_rewrite_tac [] >> NO_TAC) >>
  rpt strip_tac >> qpat_x_assum ‘∀i. n ≤ i ∧ i ≤ k ⇒ _’ (qspec_then ‘i’ mp_tac) >> fs[]
QED
