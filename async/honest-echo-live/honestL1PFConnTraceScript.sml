(*
  The PF run's trace, read as L3-00's statements read it (design/47 A), and
  raw liveness for connections on it (C).

  The trace io of the PF run of m from w0 is cf-actions' ptrace (its finite
  prefixes are exactly the prefixes of the run's events, ppre).  On it:
   - an fd L1 fetched as a new connection (FConn g in a round's fetch log)
     is an accepted fd of the trace (l0_accepted);
   - [F1] on the trace gives honest-ffi's F1 on the run;
   - honest-ffi's accepts_fail on the run is accepts_fail_io on the trace;
  and conn_live_l0 follows from honestL1PFConnRun.live_conn_psk, for every
  server meeting S1 and S2 (the PF echo: honestEchoL0Obl).
*)
Theory honestL1PFConnTrace
Ancestors
  honestL1PFObl honestL1BConnLive honestL1BConn honestL1BFaith honestL1BTransfer
  honestL1BCorr honestL1BRuns honestL1BStmts
  honestL1PFConnRun honestL1PFConn honestL1PFLive honestL1PFRound honestL1PFRefine
  honestL1PFModel honestL1Steps honestL1Model honestEchoL0Spec honestL0WorldProps honestL0Rely
  honestL0World honestL0 llist
Libs
  preamble

(* ------------------------------------------------------------------------
   New connections are accepted fds of the trace
   ------------------------------------------------------------------------ *)

Theorem sys_accept_accepted:
  sys_accept l w = SOME (out, w', ev) ∧ l0_rely w ∧ l0_res_of out = Ok k ⇒
  l0_event_accepted ev = SOME (n2w k)
Proof
  rw[sys_accept_def, l0_do_def, AllCaseEqs()] >>
  drule_all l0_ffi_fn_length >> strip_tac >>
  gvs[l0_event_accepted_def, l0_ev_res_def, MAP_ZIP, l0_res_of_def, AllCaseEqs()]
QED

Theorem pf_fetch_conn:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ l0_rely w ∧
    MEM (FConn g) log ⇒
    ∃ev. MEM ev evs ∧ l0_event_accepted ev = SOME g
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> rw[] >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >>
  imp_res_tac rplays_sys >> gvs[rplays_def] >>
  TRY (qexists_tac ‘ev’ >> simp[] >> metis_tac[sys_accept_accepted] >> NO_TAC) >>
  first_x_assum drule_all >> metis_tac[]
QED

(* A round's new connections are accepted fds of its events *)
Theorem pround_conn:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧ l0_rely w ∧
  MEM (FConn g) log ⇒
  ∃ev. MEM ev evs ∧ l0_event_accepted ev = SOME g
Proof
  rw[pround_def, AllCaseEqs()] >> PairCases_on ‘ws1’ >> gvs[pf_tail_def, AllCaseEqs()] >>
  imp_res_tac rplays_pacts >> imp_res_tac rplays_polls >> imp_res_tac rplays_flush >>
  gvs[rplays_def] >> drule_all pf_fetch_conn >> strip_tac >>
  qexists_tac ‘ev’ >> simp[]
QED

(* ------------------------------------------------------------------------
   An accept's result is well encoded
   ------------------------------------------------------------------------ *)

Theorem l0_accept_ok:
  l0_rely w ⇒ l0_res_ok (FST (l0_accept l w))
Proof
  rw[l0_accept_def] >> every_case_tac >> simp[fail_ok, l0_res_ok_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[l0_res_ok_def, fail_ok] >>
  qspec_then ‘x’ mp_tac wordsTheory.w2n_lt >> simp[]
QED

Theorem accept_dec:
  l0_rely w ∧ l0_ffi_fn «sys_accept» conf b w = SOME (FFIreturn out u) ⇒
  ∃r. dec_res out = SOME r
Proof
  rw[l0_ffi_fn_def, l0_call_def, AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  ‘l0_rely (l0_tick «sys_accept» w)’ by (irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  drule l0_accept_ok >> disch_then (qspec_then ‘bytes_fd conf’ mp_tac) >> simp[] >>
  strip_tac >> drule dec_enc_res >> disch_then (qspec_then ‘[]’ mp_tac) >> simp[]
QED
