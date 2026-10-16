(*
  L3-09 (S3): a run's events replay to its world.  The raw-trace
  statements read the world after a prefix of the trace as the replay of
  the prefix's calls from the initial world (world_at, l0_replay).  Every
  L1 step, and every blocking round, makes its calls through l0_do, so
  replaying its events from where it started gives where it ended (the
  rely gives the buffers' lengths, so an event's call is the call made).

  MAIN: rplays_bround, rplays_pround.
*)
Theory honestL1BRuns
Ancestors
  honestL1BStmts honestL1BSim honestL1BRefine honestL1BModel honestL1BHist honestL0Part
  honestL1PFRound honestL1PFModel honestL1Model honestL0WorldProps honestL0Rely
  honestL0World honestL0
Libs
  preamble

Definition rplays_def:
  rplays w w' (evs : io_event list) ⇔
    l0_rely w ⇒ FOLDL l0_step (SOME w) (MAP ev_lcall evs) = SOME w' ∧ l0_rely w'
End

Theorem FOLDL_step_NONE[local,simp]:
  ∀cs. FOLDL l0_step NONE cs = NONE
Proof
  Induct >> simp[l0_step_def]
QED

Theorem rplays_nil[simp]:
  rplays w w []
Proof
  simp[rplays_def]
QED

Theorem rplays_trans:
  rplays w1 w2 a ∧ rplays w2 w3 b ⇒ rplays w1 w3 (a ++ b)
Proof
  rw[rplays_def] >> fs[FOLDL_APPEND]
QED

Theorem rplays_cons:
  rplays w1 w2 [e] ∧ rplays w2 w3 b ⇒ rplays w1 w3 (e :: b)
Proof
  metis_tac[rplays_trans, APPEND]
QED

Theorem rplays_do:
  l0_do n conf alen w = SOME (out, w', ev) ⇒ rplays w w' [ev]
Proof
  rw[rplays_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  ‘l0_ffi_fn n conf (REPLICATE alen 0w) w =
     SOME (FFIreturn out (w1 with hist := w.hist ++ [(n, conf, REPLICATE alen 0w)]))’
    by simp[l0_ffi_fn_def] >>
  drule_all l0_ffi_fn_length >> strip_tac >>
  simp[ev_lcall_def, l0_step_def, MAP_ZIP]
QED

Theorem rplays_sys:
  (sys_accept l w = SOME (out, w', ev) ⇒ rplays w w' [ev]) ∧
  (sys_recv f k w = SOME (out, w', ev) ⇒ rplays w w' [ev]) ∧
  (sys_send f bs w = SOME (out, w', ev) ⇒ rplays w w' [ev]) ∧
  (sys_close f w = SOME (out, w', ev) ⇒ rplays w w' [ev]) ∧
  (sys_poll fes w = SOME (out, w', ev) ⇒ rplays w w' [ev])
Proof
  rw[sys_accept_def, sys_recv_def, sys_send_def, sys_close_def, sys_poll_def] >>
  metis_tac[rplays_do]
QED

Theorem rplays_close:
  l1_close f (w, st) = SOME ((w', st'), evs) ⇒ rplays w w' evs
Proof
  rw[l1_close_def, AllCaseEqs()] >> TRY (PairCases_on ‘v’) >> gvs[] >>
  metis_tac[rplays_sys]
QED

Theorem rplays_l1do:
  l1do lfd (w, st) a = SOME (r, (w', st'), evs) ⇒ rplays w w' evs
Proof
  Cases_on ‘a’ >> rw[l1do_def, AllCaseEqs()] >> gvs[] >>
  TRY (PairCases_on ‘v’) >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac rplays_sys >> imp_res_tac rplays_close >> gvs[] >>
  TRY (irule rplays_cons >> goal_assum drule >> first_assum ACCEPT_TAC)
QED

Theorem rplays_pdo:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ⇒ rplays w w' evs
Proof
  Cases_on ‘a’ >> rw[pdo_def, AllCaseEqs()] >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac rplays_close >> imp_res_tac rplays_l1do >> gvs[]
QED

Theorem rplays_pacts:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ⇒ rplays w w' evs
Proof
  Induct >> rw[pacts_def, AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  res_tac >> imp_res_tac rplays_pdo >> irule rplays_trans >> metis_tac[]
QED

Theorem rplays_polls:
  ∀chs w rv w' evs. l1_polls chs w = SOME (rv, w', evs) ⇒ rplays w w' evs
Proof
  Induct >> rw[l1_polls_def, AllCaseEqs()] >>
  res_tac >> imp_res_tac rplays_sys >> irule rplays_cons >> metis_tac[]
QED

Theorem rplays_flush:
  ∀fs w st w' st' evs. l1_flush fs (w, st) = SOME ((w', st'), evs) ⇒ rplays w w' evs
Proof
  Induct >> rw[l1_flush_def, AllCaseEqs()] >> res_tac >> imp_res_tac rplays_sys >>
  TRY (irule rplays_cons >> metis_tac[]) >> metis_tac[]
QED

Theorem rplays_fetch:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ⇒ rplays w w' evs
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> pairarg_tac >> gvs[] >>
  qpat_x_assum ‘_ = (ps1, _)’ (fn th => fs[th]) >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> imp_res_tac rplays_sys >> strip_tac >>
  irule rplays_cons >> goal_assum drule >> first_assum ACCEPT_TAC
QED

Theorem rplays_reap:
  ∀fs w st w' st' evs. l1_reap fs (w, st) = SOME ((w', st'), evs) ⇒ rplays w w' evs
Proof
  Induct >> rw[l1_reap_def, AllCaseEqs()] >> TRY (PairCases_on ‘ws’) >>
  res_tac >> imp_res_tac rplays_close >> gvs[] >>
  irule rplays_trans >> metis_tac[]
QED

Theorem rplays_after:
  pf_after lfd hw hs ps fes (rv, w1, []) = SOME (rdy, (w', ps'), log, evs) ⇒
  rplays w1 w' evs
Proof
  rw[pf_after_def, AllCaseEqs()] >> gvs[] >>
  imp_res_tac rplays_flush >> imp_res_tac rplays_fetch >> imp_res_tac rplays_reap >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >>
  irule rplays_trans >> qexists_tac ‘w2’ >> conj_tac >- first_assum ACCEPT_TAC >>
  irule rplays_trans >> qexists_tac ‘w3’ >> conj_tac >> first_assum ACCEPT_TAC
QED

Theorem rplays_tail:
  pf_tail lfd hw hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ⇒ rplays w w' evs
Proof
  simp[pf_tail_after, AllCaseEqs()] >> strip_tac >> PairCases_on ‘v’ >> gvs[] >>
  qpat_x_assum ‘pf_after _ _ _ _ _ _ = _’ (assume_tac o ONCE_REWRITE_RULE[pf_after_pevs]) >>
  gvs[] >> rename1 ‘pf_after _ _ _ _ _ _ = SOME z’ >> PairCases_on ‘z’ >> gvs[] >>
  imp_res_tac rplays_polls >> imp_res_tac rplays_after >>
  irule rplays_trans >> metis_tac[]
QED

(* MAIN: a PF round replays *)
Theorem rplays_pround:
  pround lfd hw hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ⇒ rplays w w' evs
Proof
  rw[pround_def, AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  imp_res_tac rplays_pacts >> imp_res_tac rplays_tail >>
  irule rplays_trans >> metis_tac[]
QED

Theorem rplays_pollb:
  sys_pollb fes w = SOME (INL (out, w', ev)) ⇒ rplays w w' [ev]
Proof
  rw[sys_pollb_def, AllCaseEqs(), rplays_def] >>
  drule_all l0_ffi_fn_length >> strip_tac >>
  simp[ev_lcall_def, l0_step_def, MAP_ZIP]
QED

(* MAIN: a blocking round replays *)
Theorem rplays_bround:
  bround lfd hw idle hs (w, ps) acts = SOME (BRound snap (w', ps') log evs) ⇒
  rplays w w' evs
Proof
  rw[bround_def, AllCaseEqs()] >> gvs[] >>
  imp_res_tac rplays_pacts >> imp_res_tac rplays_tail
  >- (qpat_x_assum ‘pf_after _ _ _ _ _ _ = _’ (assume_tac o ONCE_REWRITE_RULE[pf_after_pevs]) >>
      gvs[] >> rename1 ‘pf_after _ _ _ _ _ _ = SOME z’ >> PairCases_on ‘z’ >> gvs[] >>
      imp_res_tac rplays_after >> imp_res_tac rplays_pollb >> gvs[] >>
      irule rplays_cons >> qexists_tac ‘w2’ >> conj_tac >> first_assum ACCEPT_TAC)
  >> irule rplays_trans >> metis_tac[]
QED

(* MAIN: the runs replay *)
Theorem rplays_brounds:
  ∀n h w ps evs logs.
    brounds lfd hw ifds bz m (w0, ps0) n = SOME (BRun h (w, ps) evs logs) ⇒
    rplays w0 w evs
Proof
  Induct >- rw[brounds_def] >>
  rpt strip_tac >> drule brounds_SUC_BRun >> strip_tac >> PairCases_on ‘ws’ >>
  first_x_assum drule >> strip_tac >> imp_res_tac rplays_bround >>
  gvs[] >> irule rplays_trans >> metis_tac[]
QED

Theorem rplays_prounds:
  ∀n h w ps evs logs.
    prounds lfd hw ifds m (w0, ps0) n = SOME (h, (w, ps), evs, logs) ⇒
    rplays w0 w evs
Proof
  Induct >- rw[prounds_def] >>
  rw[prounds_def, AllCaseEqs()] >> PairCases_on ‘ws’ >>
  first_x_assum drule >> strip_tac >> imp_res_tac rplays_pround >>
  irule rplays_trans >> metis_tac[]
QED
