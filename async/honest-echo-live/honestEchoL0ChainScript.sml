(*
  The output chain of echo_live_l0 (design/47 D, assembly step 2): from a
  round boundary n at which L1 holds f on channel c, in episode j0, the
  bytes the server has written to client j (its outgoing stream in psk)
  eventually reach the kernel, or episode j0 shows a hard error or a D23
  timeout on the trace.

  From honest-ffi's flush_live3 (the least such round), run_gone_cause and
  run_okeys_held (a gone fd is held), with excuse_j0 (excuse after n) and
  excuse_back (excuse before n, f held since).

  MAIN: out_chain.
*)
Theory honestEchoL0Chain
Ancestors
  honestEchoL0Excuse honestL1PFBroken honestL1PFFlushLive honestL1PFFlush honestL1PFOutLive honestL1PFDead honestL1PFLive
  honestL1PFOut honestEchoL0LiveOwn honestEchoL0Trace honestL1BStmts
Libs
  preamble

(* An output-side excuse in round k < n, with f held from round k + 1 to
   n, is the trace excuse of the episode f has at round n *)
Theorem excuse_back:
  oassm lfd pol ifds m w0 ∧ pftrace lfd pol ifds m w0 io ∧ f ≠ lfd ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 n))) f = SOME j0 ∧ k < n ∧
  (∀i. k < i ∧ i ≤ n ⇒ held f (rstate lfd pol ifds m w0 i)) ∧
  (hard_send f (rrev lfd pol ifds m w0 k) ∨ rdrop lfd pol ifds m w0 k f) ⇒
  ep_hard_err j0 io ∨ ep_timed_out pf_sendwait j0 io
Proof
  strip_tac >>
  ‘run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0)’ by fs[oassm_def]
  >- (fs[hard_send_def] >>
      qpat_x_assum ‘MEM _ (rrev _ _ _ _ _ _)’
        (qx_choosel_then [‘l1’, ‘l2’] strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
      ‘rrev lfd pol ifds m w0 k = l1 ++ [ev] ++ l2’ by simp[] >>
      ‘∃j. ep_hard_err j io ∧ ep_open j (revs lfd pol ifds m w0 k ++ l1) ∧
           EL j (l0_accepted (revs lfd pol ifds m w0 k ++ l1)) = f’
        by metis_tac[run_ep_hard_err] >>
      ‘ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 k ++ l1))) f = SOME j’
        by metis_tac[ep_open_state] >>
      ‘ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 n))) f = SOME j’
        by (irule keep_backward >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
            qexistsl_tac [‘k’, ‘[ev] ++ l2’, ‘l1’] >> fs[]) >>
      gvs[]) >>
  drule_all rdrop_excuse >> strip_tac >>
  ‘ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 i ++ pre))) f = SOME j’
    by metis_tac[ep_open_state] >>
  ‘ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 n))) f = SOME j’
    by (irule keep_backward >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        qexistsl_tac [‘i’, ‘post’, ‘pre’] >> fs[] >> rpt strip_tac >>
        Cases_on ‘i' ≤ k’ >> fs[]) >>
  gvs[]
QED

(* MAIN: the output chain *)
Theorem out_chain:
  oassm lfd pol ifds m w0 ∧ F1 lfd pol ifds m w0 ∧ honestL1PFFlush$F2 w0 ∧
  honestL1PFFlush$drains lfd pol ifds m w0 c ∧ nshut w0 ∧ pftrace lfd pol ifds m w0 io ∧
  f ≠ lfd ∧
  held f (rstate lfd pol ifds m w0 n) ∧
  l0_chan_of (rworld lfd pol ifds m w0 n) f = SOME c ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 n))) f = SOME j0 ⇒
  ∃n'. n ≤ n' ∧
       ((EL (cl (FST (pcm lfd pol ifds m w0 n)) f)
            (FST (hst lfd ifds m (psk lfd pol ifds m w0) n)).clients).outgoing ≼
          csent (rworld lfd pol ifds m w0 n') c ∨
        ep_hard_err j0 io ∨ ep_timed_out pf_sendwait j0 io)
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS (BETA_RULE th))) >>
  drule_all flush_live3 >> strip_tac
  >- (qexists_tac ‘n'’ >> simp[])
  >- ((* gone at n: its cause came before, f held since *)
      qexists_tac ‘n’ >> simp[] >> rveq >>
      drule run_gone_cause >> disch_then drule >> strip_tac >>
      disj2_tac >> irule excuse_back >> simp[] >>
      qexistsl_tac [‘f’, ‘ifds’, ‘k’, ‘lfd’, ‘m’, ‘n’, ‘pol’, ‘w0’] >> simp[] >>
      rpt strip_tac >> irule run_okeys_held >> fs[]) >>
  (* an excuse at k = n' − 1, f held from n to k *)
  qexists_tac ‘n'’ >> simp[] >> disj2_tac >>
  Cases_on ‘n ≤ k’ >>
  TRY (irule excuse_j0 >> simp[] >>
       qexistsl_tac [‘n’, ‘f’, ‘ifds’, ‘k’, ‘lfd’, ‘m’, ‘pol’, ‘w0’] >> simp[] >>
       rpt strip_tac >> qpat_x_assum ‘∀i. n ≤ i ∧ _ ⇒ _’ (qspec_then ‘i’ mp_tac) >>
       simp[] >> NO_TAC) >>
  (* n' = n: the excuse is in round n − 1 *)
  irule excuse_back >> simp[] >>
  qexistsl_tac [‘f’, ‘ifds’, ‘k’, ‘lfd’, ‘m’, ‘n’, ‘pol’, ‘w0’] >> fs[] >>
  rpt strip_tac >> ‘i = n’ by decide_tac >> fs[]
QED

