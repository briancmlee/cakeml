(*
  L3-09 (S3): a run's events are the calls it made, with their results.
  As honestL1BRuns (rplays), and also: every event is a call L1 makes
  (accept, recv, send, close or poll) whose recorded result is what the L0
  world returned (faithful), so a trace's results can be read as the
  world's.

  MAIN: fplays_brounds.
*)
Theory honestL1BFaith
Ancestors
  honestL1BRuns honestL1BStmts honestL1BSim honestL1BRefine honestL1BModel honestL1BHist
  honestL0Part honestL1PFRound honestL1PFModel honestL1Model honestL0WorldProps
  honestL0Rely honestL0World honestL0
Libs
  preamble

Definition l1_names_def:
  l1_names = [«sys_accept»; «sys_recv»; «sys_send»; «sys_close»; «sys_poll»]
End

(* Each event is a call L1 makes, from the world before it, returning its
   recorded result *)
Definition faithful_def:
  faithful w [] = T ∧
  faithful w (ev :: evs) =
    ∃n conf bs u. ev = IO_event (ExtCall n) conf bs ∧ MEM n l1_names ∧
                  l0_ffi_fn n conf (MAP FST bs) w = SOME (FFIreturn (MAP SND bs) u) ∧
                  faithful u evs
End

Definition fplays_def:
  fplays w w' (evs : io_event list) ⇔
    l0_rely w ⇒ FOLDL l0_step (SOME w) (MAP ev_lcall evs) = SOME w' ∧ l0_rely w' ∧
                faithful w evs
End

Theorem FOLDL_step_NONE[local,simp]:
  ∀cs. FOLDL l0_step NONE cs = NONE
Proof
  Induct >> simp[l0_step_def]
QED

Theorem faithful_append:
  ∀a w w2. faithful w a ∧ FOLDL l0_step (SOME w) (MAP ev_lcall a) = SOME w2 ∧
           faithful w2 b ⇒ faithful w (a ++ b)
Proof
  Induct >> rw[faithful_def] >> gvs[ev_lcall_def, l0_step_def] >> metis_tac[]
QED

Theorem fplays_nil[simp]:
  fplays w w []
Proof
  simp[fplays_def, faithful_def]
QED

Theorem fplays_trans:
  fplays w1 w2 a ∧ fplays w2 w3 b ⇒ fplays w1 w3 (a ++ b)
Proof
  rw[fplays_def] >> fs[FOLDL_APPEND] >> metis_tac[faithful_append]
QED

Theorem fplays_cons:
  fplays w1 w2 [e] ∧ fplays w2 w3 b ⇒ fplays w1 w3 (e :: b)
Proof
  metis_tac[fplays_trans, APPEND]
QED

Theorem fplays_do:
  l0_do n conf alen w = SOME (out, w', ev) ∧ MEM n l1_names ⇒ fplays w w' [ev]
Proof
  rw[fplays_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  ‘l0_ffi_fn n conf (REPLICATE alen 0w) w =
     SOME (FFIreturn out (w1 with hist := w.hist ++ [(n, conf, REPLICATE alen 0w)]))’
    by simp[l0_ffi_fn_def] >>
  drule_all l0_ffi_fn_length >> strip_tac >>
  simp[ev_lcall_def, l0_step_def, MAP_ZIP, faithful_def]
QED

Theorem fplays_do_buf:
  l0_do_buf n conf bs w = SOME (out, w', ev) ∧ MEM n l1_names ⇒ fplays w w' [ev]
Proof
  rw[fplays_def] >> drule l0_do_buf_cases >> strip_tac >> gvs[] >>
  ‘l0_ffi_fn n conf bs w = SOME (FFIreturn out (w1 with hist := w.hist ++ [(n, conf, bs)]))’
    by simp[l0_ffi_fn_def] >>
  drule_all l0_ffi_fn_length >> strip_tac >>
  simp[ev_lcall_def, l0_step_def, MAP_ZIP, faithful_def]
QED

Theorem fplays_sys:
  (sys_accept l w = SOME (out, w', ev) ⇒ fplays w w' [ev]) ∧
  (sys_recv f k w = SOME (out, w', ev) ⇒ fplays w w' [ev]) ∧
  (sys_send f bs w = SOME (out, w', ev) ⇒ fplays w w' [ev]) ∧
  (sys_close f w = SOME (out, w', ev) ⇒ fplays w w' [ev]) ∧
  (sys_poll fes w = SOME (out, w', ev) ⇒ fplays w w' [ev])
Proof
  rw[sys_accept_def, sys_recv_def, sys_send_def, sys_close_def, sys_poll_def] >>
  TRY (irule fplays_do_buf >> simp[l1_names_def] >> metis_tac[] >> NO_TAC) >>
  irule fplays_do >> simp[l1_names_def] >> metis_tac[]
QED

Theorem fplays_close:
  l1_close f (w, st) = SOME ((w', st'), evs) ⇒ fplays w w' evs
Proof
  rw[l1_close_def, AllCaseEqs()] >> TRY (PairCases_on ‘v’) >> gvs[] >>
  metis_tac[fplays_sys]
QED

Theorem fplays_l1do:
  l1do lfd (w, st) a = SOME (r, (w', st'), evs) ⇒ fplays w w' evs
Proof
  Cases_on ‘a’ >> rw[l1do_def, AllCaseEqs()] >> gvs[] >>
  TRY (PairCases_on ‘v’) >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac fplays_sys >> imp_res_tac fplays_close >> gvs[] >>
  TRY (irule fplays_cons >> goal_assum drule >> first_assum ACCEPT_TAC)
QED

Theorem fplays_pdo:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ⇒ fplays w w' evs
Proof
  Cases_on ‘a’ >> rw[pdo_def, AllCaseEqs()] >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac fplays_close >> imp_res_tac fplays_l1do >> gvs[]
QED

Theorem fplays_pacts:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ⇒ fplays w w' evs
Proof
  Induct >> rw[pacts_def, AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  res_tac >> imp_res_tac fplays_pdo >> irule fplays_trans >> metis_tac[]
QED

Theorem fplays_polls:
  ∀chs w rv w' evs. l1_polls chs w = SOME (rv, w', evs) ⇒ fplays w w' evs
Proof
  Induct >> rw[l1_polls_def, AllCaseEqs()] >>
  res_tac >> imp_res_tac fplays_sys >> irule fplays_cons >> metis_tac[]
QED

Theorem fplays_flush:
  ∀fs w st w' st' evs. l1_flush fs (w, st) = SOME ((w', st'), evs) ⇒ fplays w w' evs
Proof
  Induct >> rw[l1_flush_def, AllCaseEqs()] >> res_tac >> imp_res_tac fplays_sys >>
  TRY (irule fplays_cons >> metis_tac[]) >> metis_tac[]
QED

Theorem fplays_fetch:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ⇒ fplays w w' evs
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> pairarg_tac >> gvs[] >>
  qpat_x_assum ‘_ = (ps1, _)’ (fn th => fs[th]) >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> imp_res_tac fplays_sys >> strip_tac >>
  irule fplays_cons >> goal_assum drule >> first_assum ACCEPT_TAC
QED

Theorem fplays_reap:
  ∀fs w st w' st' evs. l1_reap fs (w, st) = SOME ((w', st'), evs) ⇒ fplays w w' evs
Proof
  Induct >> rw[l1_reap_def, AllCaseEqs()] >> TRY (PairCases_on ‘ws’) >>
  res_tac >> imp_res_tac fplays_close >> gvs[] >>
  irule fplays_trans >> metis_tac[]
QED

Theorem fplays_after:
  pf_after lfd hw hs ps fes (rv, w1, []) = SOME (rdy, (w', ps'), log, evs) ⇒
  fplays w1 w' evs
Proof
  rw[pf_after_def, AllCaseEqs()] >> gvs[] >>
  imp_res_tac fplays_flush >> imp_res_tac fplays_fetch >> imp_res_tac fplays_reap >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >>
  irule fplays_trans >> qexists_tac ‘w2’ >> conj_tac >- first_assum ACCEPT_TAC >>
  irule fplays_trans >> qexists_tac ‘w3’ >> conj_tac >> first_assum ACCEPT_TAC
QED

Theorem fplays_tail:
  pf_tail lfd hw hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ⇒ fplays w w' evs
Proof
  simp[pf_tail_after, AllCaseEqs()] >> strip_tac >> PairCases_on ‘v’ >> gvs[] >>
  qpat_x_assum ‘pf_after _ _ _ _ _ _ = _’ (assume_tac o ONCE_REWRITE_RULE[pf_after_pevs]) >>
  gvs[] >> rename1 ‘pf_after _ _ _ _ _ _ = SOME z’ >> PairCases_on ‘z’ >> gvs[] >>
  imp_res_tac fplays_polls >> imp_res_tac fplays_after >>
  irule fplays_trans >> metis_tac[]
QED

(* MAIN: a PF round replays *)
Theorem fplays_pround:
  pround lfd hw hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ⇒ fplays w w' evs
Proof
  rw[pround_def, AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  imp_res_tac fplays_pacts >> imp_res_tac fplays_tail >>
  irule fplays_trans >> metis_tac[]
QED

Theorem fplays_pollb:
  sys_pollb fes w = SOME (INL (out, w', ev)) ⇒ fplays w w' [ev]
Proof
  rw[sys_pollb_def, AllCaseEqs(), fplays_def] >>
  drule_all l0_ffi_fn_length >> strip_tac >>
  simp[ev_lcall_def, l0_step_def, MAP_ZIP, faithful_def, l1_names_def]
QED

(* MAIN: a blocking round replays *)
Theorem fplays_bround:
  bround lfd hw idle hs (w, ps) acts = SOME (BRound snap (w', ps') log evs) ⇒
  fplays w w' evs
Proof
  rw[bround_def, AllCaseEqs()] >> gvs[] >>
  imp_res_tac fplays_pacts >> imp_res_tac fplays_tail
  >- (qpat_x_assum ‘pf_after _ _ _ _ _ _ = _’ (assume_tac o ONCE_REWRITE_RULE[pf_after_pevs]) >>
      gvs[] >> rename1 ‘pf_after _ _ _ _ _ _ = SOME z’ >> PairCases_on ‘z’ >> gvs[] >>
      imp_res_tac fplays_after >> imp_res_tac fplays_pollb >> gvs[] >>
      irule fplays_cons >> qexists_tac ‘w2’ >> conj_tac >> first_assum ACCEPT_TAC)
  >> irule fplays_trans >> metis_tac[]
QED

(* MAIN: the runs' events are faithful *)
Theorem fplays_brounds:
  ∀n h w ps evs logs.
    brounds lfd hw ifds bz m (w0, ps0) n = SOME (BRun h (w, ps) evs logs) ⇒
    fplays w0 w evs
Proof
  Induct >- rw[brounds_def] >>
  rpt strip_tac >> drule brounds_SUC_BRun >> strip_tac >> PairCases_on ‘ws’ >>
  first_x_assum drule >> strip_tac >> imp_res_tac fplays_bround >>
  gvs[] >> irule fplays_trans >> metis_tac[]
QED

Theorem fplays_prounds:
  ∀n h w ps evs logs.
    prounds lfd hw ifds m (w0, ps0) n = SOME (h, (w, ps), evs, logs) ⇒
    fplays w0 w evs
Proof
  Induct >- rw[prounds_def] >>
  rw[prounds_def, AllCaseEqs()] >> PairCases_on ‘ws’ >>
  first_x_assum drule >> strip_tac >> imp_res_tac fplays_pround >>
  irule fplays_trans >> metis_tac[]
QED
