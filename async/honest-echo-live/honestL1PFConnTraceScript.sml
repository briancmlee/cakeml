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
  honestL1PFConnRun honestL1PFClient honestL1PFConn honestL1PFLive honestL1PFRound honestL1PFRefine
  honestL1PFModel honestL1Steps honestL1Model honestEchoL0Spec honestL0WorldInv honestL0WorldProps
  honestL0Rely
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

(* ------------------------------------------------------------------------
   Raw liveness for connections
   ------------------------------------------------------------------------ *)

Theorem pftrace_sub:
  run_ok lfd pol ifds m w0 ∧ pftrace lfd pol ifds m w0 io ∧
  evs ≼ revs lfd pol ifds m w0 N ⇒ LPREFIX (fromList evs) io
Proof
  rw[pftrace_def, ppre_def] >> drule_then (qspec_then ‘N’ assume_tac) prun_some >>
  Cases_on ‘prun lfd pol ifds m w0 N’ >> PairCases_on ‘r’ >>
  qexistsl_tac [‘N’, ‘q’, ‘(r0, r1)’, ‘r2’, ‘r3’] >> gvs[revs_def]
QED

(* A new connection of round k is an accepted fd of the run's events *)
Theorem run_conn_accepted:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM (FConn g) (rlog lfd pol ifds m w0 k) ⇒
  MEM g (l0_accepted (revs lfd pol ifds m w0 (SUC k)))
Proof
  strip_tac >> drule_all winv_run >> disch_then (qspec_then ‘k’ assume_tac) >>
  ‘l0_rely (rworld lfd pol ifds m w0 k)’ by fs[winv_def] >>
  drule_then (qspec_then ‘k’ strip_assume_tac) prun_round >>
  ‘rlog lfd pol ifds m w0 k = log’ by simp[rlog_def] >> gvs[] >>
  drule_all pround_conn >> strip_tac >>
  simp[l0_accepted_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  disj2_tac >> qexists_tac ‘ev’ >> simp[]
QED

(* MAIN (C): raw liveness for connections on the PF trace, for every server
   meeting S1 and S2 *)
Theorem pf_conn_live:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ linv lfd w0 ∧ lone lfd w0 ∧
  MEM lfd (l0_used w0) ∧ (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ∧
  F1 lfd pol ifds m w0 ∧ S1 lfd pol ifds m w0 ∧ S2 lfd pol ifds m w0 ∧
  pftrace lfd pol ifds m w0 io ⇒
  conn_live_l0 w0 io
Proof
  rw[conn_live_l0_def, conn_live_unless_def] >>
  drule_all pftrace_prefix >> strip_tac >>
  ‘∃s. revs lfd pol ifds m w0 N = evs ++ s’ by fs[IS_PREFIX_APPEND] >>
  drule_then (qspec_then ‘N’ strip_assume_tac) run_world_at >>
  ‘l0_rely w0 ∧ l0wf w0’ by fs[run_ok_def, winv_def] >>
  ‘faithful w0 (evs ++ s)’ by metis_tac[] >>
  ‘lone lfd w ∧ l0wf w’
    by (conj_tac >> irule faithful_world_inv >>
        (conj_tac >- metis_tac[lone_ffi, l0wf_ffi_fn]) >>
        qexistsl_tac [‘evs’, ‘s’, ‘w0’] >> simp[]) >>
  drule_all lone_qof >> strip_tac >>
  qpat_x_assum ‘l = lfd’ SUBST_ALL_TAC >> qpat_x_assum ‘qof _ _ = q’ (SUBST_ALL_TAC o SYM) >>
  ‘FOLDL l0_step (SOME w) (MAP ev_lcall s) = SOME (rworld lfd pol ifds m w0 N)’
    by (qpat_x_assum ‘world_at w0 (revs _ _ _ _ _ _) = _’ mp_tac >>
        qpat_assum ‘revs _ _ _ _ _ _ = _’ (fn th => REWRITE_TAC[th]) >>
        simp[world_at_append]) >>
  ‘faithful w s’
    by (irule faithful_drop >> qexistsl_tac [‘evs’, ‘w0’] >>
        fs[world_at_def, l0_replay_def]) >>
  Cases_on ‘MEM j0 (qof (rworld lfd pol ifds m w0 N) lfd)’
  >- ((* still queued at the end of the round: live_conn_psk *)
      qspecl_then [‘N’, ‘j0’] mp_tac (Q.GENL [‘n0’, ‘j0’] live_conn_psk) >>
      impl_tac >- simp[] >> strip_tac
      >- (disj2_tac >> disj1_tac >>
          qexistsl_tac [‘revs lfd pol ifds m w0 (SUC k)’,
                        ‘rworld lfd pol ifds m w0 (SUC k)’, ‘g’] >>
          simp[run_world_at] >> metis_tac[pftrace_revs, run_conn_accepted])
      >- (disj2_tac >> disj2_tac >> simp[broke_def] >>
          qexistsl_tac [‘revs lfd pol ifds m w0 (SUC k)’,
                        ‘rworld lfd pol ifds m w0 (SUC k)’] >>
          simp[run_world_at] >> metis_tac[pftrace_revs])
      >> disj1_tac >> metis_tac[accepts_fail_io_run]) >>
  (* it left the queue during the round: at an accept naming it, or broken *)
  drule_all qexit_trace >> strip_tac >>
  qpat_x_assum ‘s = _’ SUBST_ALL_TAC >>
  ‘world_at w0 (evs ++ a ++ [ev]) = SOME x’
    by (REWRITE_TAC[GSYM APPEND_ASSOC] >> ONCE_REWRITE_TAC[world_at_append] >>
        qpat_assum ‘world_at w0 evs = _’ (fn th => REWRITE_TAC[th]) >>
        qpat_x_assum ‘FOLDL _ _ (MAP _ (_ ++ [_])) = _’ mp_tac >> simp[]) >>
  ‘evs ++ a ++ [ev] ≼ revs lfd pol ifds m w0 N’
    by (qpat_x_assum ‘revs _ _ _ _ _ _ = _’ SUBST1_TAC >> simp[IS_PREFIX_APPEND]) >>
  ‘LPREFIX (fromList (evs ++ a ++ [ev])) io’ by metis_tac[pftrace_sub] >>
  TRY (disj2_tac >> disj1_tac >> qexistsl_tac [‘evs ++ a ++ [ev]’, ‘x’, ‘k’] >>
       simp[l0_accepted_def] >> NO_TAC) >>
  disj2_tac >> disj2_tac >> simp[broke_def] >>
  qexistsl_tac [‘evs ++ a ++ [ev]’, ‘x’] >> simp[]
QED

(* ------------------------------------------------------------------------
   The number of clients: at most the accepted fds of the trace
   ------------------------------------------------------------------------ *)

Theorem arrs_nconns:
  ∀l cm k. SND (SND (arrs lfd (cm, k) l)) = k + LENGTH (log_conns l)
Proof
  Induct >- simp[arrs_def, log_conns_def] >>
  Cases >> rpt gen_tac >> simp[arrs_def] >> rpt (pairarg_tac >> gvs[]) >>
  TRY (first_x_assum (qspecl_then [‘(c, k) :: cm’, ‘k + 1’] mp_tac) >>
       gvs[log_conns_def] >> NO_TAC) >>
  first_x_assum (qspecl_then [‘cm’, ‘k’] mp_tac) >> gvs[log_conns_def]
QED

Theorem pf_fetch_conns:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ l0_rely w ⇒
    LENGTH (log_conns log) ≤ LENGTH (l0_accepted evs)
Proof
  Induct >- simp[pf_fetch_def, log_conns_def, l0_accepted_def] >>
  simp[pf_fetch_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> rw[] >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >>
  imp_res_tac rplays_sys >> gvs[rplays_def] >>
  first_x_assum drule_all >> strip_tac >>
  fs[log_conns_def, l0_accepted_def] >>
  TRY (drule_all sys_accept_accepted >> simp[] >> NO_TAC) >>
  CASE_TAC >> simp[]
QED

Theorem pround_conns:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧ l0_rely w ⇒
  LENGTH (log_conns log) ≤ LENGTH (l0_accepted evs)
Proof
  rw[pround_def, AllCaseEqs()] >> PairCases_on ‘ws1’ >> gvs[pf_tail_def, AllCaseEqs()] >>
  imp_res_tac rplays_pacts >> imp_res_tac rplays_polls >> imp_res_tac rplays_flush >>
  gvs[rplays_def] >> drule_all pf_fetch_conns >>
  simp[l0_accepted_def, FLAT_APPEND, MAP_APPEND]
QED

Theorem plog_rlog:
  run_ok lfd pol ifds m w0 ⇒ plog lfd pol ifds m w0 n = rlog lfd pol ifds m w0 n
Proof
  strip_tac >> drule_then (qspec_then ‘SUC n’ assume_tac) prun_some >>
  simp[plog_def, rlog_def] >> Cases_on ‘prun lfd pol ifds m w0 (SUC n)’ >>
  PairCases_on ‘r’ >> gvs[]
QED

Theorem run_pcm_le:
  run_ok lfd pol ifds m w0 ∧ winv w0 ⇒
  ∀n. SND (pcm lfd pol ifds m w0 n) ≤ LENGTH (l0_accepted (revs lfd pol ifds m w0 n))
Proof
  strip_tac >> drule_all winv_run >> strip_tac >>
  Induct >- simp[pcm_def, revs_def, prun_0, l0_accepted_def] >>
  ‘SND (pcm lfd pol ifds m w0 (SUC n)) =
   SND (pcm lfd pol ifds m w0 n) + LENGTH (log_conns (rlog lfd pol ifds m w0 n))’
    by (simp[pcm_def] >> Cases_on ‘pcm lfd pol ifds m w0 n’ >>
        simp[arrs_nconns] >> metis_tac[plog_rlog]) >>
  drule_then (qspec_then ‘n’ strip_assume_tac) prun_round >>
  ‘rlog lfd pol ifds m w0 n = log’ by simp[rlog_def] >>
  ‘l0_rely (rworld lfd pol ifds m w0 n)’ by fs[winv_def] >>
  drule_all pround_conns >> strip_tac >> gvs[] >>
  simp[l0_accepted_def, FLAT_APPEND, MAP_APPEND] >> fs[l0_accepted_def]
QED

(* The client count bound from the trace's accepts_below *)
Theorem pcm_bound_accepts_below:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ pftrace lfd pol ifds m w0 io ∧ accepts_below io ⇒
  ∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)
Proof
  rpt strip_tac >> drule_all run_pcm_le >> disch_then (qspec_then ‘n’ assume_tac) >>
  drule_all pftrace_revs >> disch_then (qspec_then ‘n’ assume_tac) >>
  fs[accepts_below_def] >> first_x_assum drule >> simp[]
QED
