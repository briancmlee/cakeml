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
  honestL0Part honestL0World honestL0 llist
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

(* ------------------------------------------------------------------------
   The trace
   ------------------------------------------------------------------------ *)

(* io is the PF run's trace from w0 (cf-actions' ptrace, for any start
   world): its finite prefixes are the prefixes of the run's events *)
Definition pftrace_def:
  pftrace lfd pol ifds m w0 (io : io_event llist) ⇔
    ∀evs. LPREFIX (fromList evs) io ⇔ ppre lfd pol ifds m (w0, pinit) evs
End

Theorem pftrace_revs:
  run_ok lfd pol ifds m w0 ∧ pftrace lfd pol ifds m w0 io ⇒
  LPREFIX (fromList (revs lfd pol ifds m w0 n)) io
Proof
  rw[pftrace_def, ppre_def] >> drule_then (qspec_then ‘n’ assume_tac) prun_some >>
  Cases_on ‘prun lfd pol ifds m w0 n’ >> PairCases_on ‘r’ >>
  qexistsl_tac [‘n’, ‘q’, ‘(r0, r1)’, ‘r2’, ‘r3’] >> gvs[revs_def]
QED

Theorem pftrace_prefix:
  run_ok lfd pol ifds m w0 ∧ pftrace lfd pol ifds m w0 io ∧ LPREFIX (fromList evs) io ⇒
  ∃N. evs ≼ revs lfd pol ifds m w0 N
Proof
  rw[pftrace_def] >> ‘ppre lfd pol ifds m (w0, pinit) evs’ by metis_tac[] >>
  fs[ppre_def] >> qexists_tac ‘N’ >> drule_then (qspec_then ‘N’ assume_tac) prun_some >>
  gvs[revs_def]
QED

Theorem run_world_at:
  run_ok lfd pol ifds m w0 ⇒
  world_at w0 (revs lfd pol ifds m w0 n) = SOME (rworld lfd pol ifds m w0 n) ∧
  faithful w0 (revs lfd pol ifds m w0 n)
Proof
  strip_tac >> ‘l0_rely w0’ by fs[run_ok_def] >>
  drule_then (qspec_then ‘n’ assume_tac) prun_some >>
  Cases_on ‘prun lfd pol ifds m w0 n’ >> PairCases_on ‘r’ >>
  drule fplays_prounds >> simp[fplays_def, world_at_def, l0_replay_def] >>
  gvs[revs_def, rworld_def]
QED

(* The trace's elements are the run's events *)
Theorem pftrace_LNTH:
  run_ok lfd pol ifds m w0 ∧ pftrace lfd pol ifds m w0 io ⇒
  (LNTH i io = SOME ev ⇔
   ∃n. i < LENGTH (revs lfd pol ifds m w0 n) ∧ EL i (revs lfd pol ifds m w0 n) = ev)
Proof
  strip_tac >> eq_tac >> strip_tac
  >- (drule LNTH_prefix_exists >> strip_tac >>
      drule_all pftrace_prefix >> strip_tac >> qexists_tac ‘N’ >>
      fs[IS_PREFIX_APPEND] >> gvs[] >> simp[EL_APPEND1])
  >> drule_all pftrace_revs >> disch_then (qspec_then ‘n’ mp_tac) >>
  simp[LPREFIX_fromList_LNTH]
QED

(* MAIN: [F1] on the trace is honest-ffi's F1 on the run *)
Theorem F1_io_F1:
  run_ok lfd pol ifds m w0 ∧ pftrace lfd pol ifds m w0 io ∧ F1_io io ⇒
  F1 lfd pol ifds m w0
Proof
  rw[F1_def, F1_io_def, call_at_def, call_ok_at_def] >>
  ‘∀i. ∃i' ev. i ≤ i' ∧ LNTH i' io = SOME ev ∧ ev_on nm f ev’
    by (gen_tac >> first_x_assum (qspec_then ‘i’ strip_assume_tac) >>
        qexistsl_tac [‘i'’, ‘EL i' (revs lfd pol ifds m w0 n)’] >>
        simp[] >> drule_all pftrace_LNTH >> simp[] >> metis_tac[]) >>
  first_x_assum drule >> disch_then (qspec_then ‘i’ strip_assume_tac) >>
  drule_all pftrace_LNTH >> strip_tac >> gvs[] >>
  qexists_tac ‘i'’ >> simp[] >> metis_tac[]
QED

(* The world before the run's i-th event keeps the rely, and the event is
   that world's answer to its call *)
Theorem faithful_EL_call:
  ∀l w0 i. faithful w0 l ∧ l0_rely w0 ∧ i < LENGTH l ⇒
           ∃x n' conf bs u.
             EL i l = IO_event (ExtCall n') conf bs ∧ l0_rely x ∧
             l0_ffi_fn n' conf (MAP FST bs) x = SOME (FFIreturn (MAP SND bs) u)
Proof
  Induct >> simp[faithful_def] >> rpt gen_tac >> strip_tac >> Cases_on ‘i’ >> gvs[]
  >- metis_tac[]
  >> drule_all l0_ffi_fn_length >> strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem run_event_call:
  run_ok lfd pol ifds m w0 ∧ i < LENGTH (revs lfd pol ifds m w0 n) ⇒
  ∃x n' conf bs u.
    EL i (revs lfd pol ifds m w0 n) = IO_event (ExtCall n') conf bs ∧ l0_rely x ∧
    l0_ffi_fn n' conf (MAP FST bs) x = SOME (FFIreturn (MAP SND bs) u)
Proof
  strip_tac >> drule_then (qspec_then ‘n’ strip_assume_tac) run_world_at >>
  ‘l0_rely w0’ by fs[run_ok_def] >> drule_all faithful_EL_call >> simp[]
QED

(* MAIN: honest-ffi's accepts_fail on the run is accepts_fail_io on the
   trace (an accept's result always decodes) *)
Theorem accepts_fail_io_run:
  run_ok lfd pol ifds m w0 ∧ pftrace lfd pol ifds m w0 io ∧
  accepts_fail lfd pol ifds m w0 ⇒ accepts_fail_io io
Proof
  rw[accepts_fail_def, accepts_fail_io_def] >>
  first_x_assum (qspec_then ‘i’ strip_assume_tac) >>
  drule_all run_event_call >> strip_tac >>
  qexists_tac ‘i'’ >> simp[] >>
  ‘LNTH i' io = SOME (EL i' (revs lfd pol ifds m w0 n))’
    by (drule_all pftrace_LNTH >> simp[] >> metis_tac[]) >>
  gvs[ev_on_def, failed_def] >>
  drule_all accept_dec >> strip_tac >>
  gvs[l0_res_of_def, l0_ev_res_def]
QED
