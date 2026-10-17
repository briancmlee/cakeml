(*
  L3-09 (S3), D32 step 3b: L1 never calls connect.  Every L1 step and every
  blocking round makes its calls through sys_accept / sys_recv / sys_send /
  sys_close / sys_poll (and the blocking poll), so no event of a blocking
  run is a connect.  Hence winv (honestL1PFRound, kept by every call but
  connect) holds at every prefix of a blocking run.

  The lemmas follow honestL1BRuns' rplays_* one for one.

  MAIN: bpre_nc.
*)
Theory honestL1BNoConn
Ancestors
  honestL1BCorr honestL1BRuns honestL1BStmts honestL1BSim honestL1BRefine honestL1BModel
  honestL0Part honestL1PFRound honestL1PFModel honestL1Model honestL0World honestL0
Libs
  preamble

(* No event is a connect *)
Definition nc_def:
  nc (evs : io_event list) ⇔ EVERY (λev. FST (ev_lcall ev) ≠ «sys_connect») evs
End

Theorem nc_simps[simp]:
  nc [] ∧ (nc (a ++ b) ⇔ nc a ∧ nc b) ∧
  (nc (e :: b) ⇔ FST (ev_lcall e) ≠ «sys_connect» ∧ nc b)
Proof
  simp[nc_def]
QED

Theorem nc_do[local]:
  l0_do n conf alen w = SOME (out, w', ev) ∧ n ≠ «sys_connect» ⇒ nc [ev]
Proof
  rw[] >> drule l0_do_cases >> strip_tac >> gvs[nc_def, ev_lcall_def]
QED

Theorem nc_do_buf[local]:
  l0_do_buf n conf bs w = SOME (out, w', ev) ∧ n ≠ «sys_connect» ⇒ nc [ev]
Proof
  rw[] >> drule l0_do_buf_cases >> strip_tac >> gvs[nc_def, ev_lcall_def]
QED

Theorem nc_sys:
  (sys_accept l w = SOME (out, w', ev) ⇒ FST (ev_lcall ev) ≠ «sys_connect») ∧
  (sys_recv f k w = SOME (out, w', ev) ⇒ FST (ev_lcall ev) ≠ «sys_connect») ∧
  (sys_send f bs w = SOME (out, w', ev) ⇒ FST (ev_lcall ev) ≠ «sys_connect») ∧
  (sys_close f w = SOME (out, w', ev) ⇒ FST (ev_lcall ev) ≠ «sys_connect») ∧
  (sys_poll fes w = SOME (out, w', ev) ⇒ FST (ev_lcall ev) ≠ «sys_connect»)
Proof
  rw[sys_accept_def, sys_recv_def, sys_send_def, sys_close_def, sys_poll_def] >>
  FIRST [drule nc_do >> simp[] >> NO_TAC, drule nc_do_buf >> simp[]]
QED

Theorem nc_close:
  l1_close f (w, st) = SOME ((w', st'), evs) ⇒ nc evs
Proof
  rw[l1_close_def, AllCaseEqs()] >> TRY (PairCases_on ‘v’) >> gvs[] >>
  metis_tac[nc_sys]
QED

Theorem nc_l1do:
  l1do lfd (w, st) a = SOME (r, (w', st'), evs) ⇒ nc evs
Proof
  Cases_on ‘a’ >> rw[l1do_def, AllCaseEqs()] >> gvs[] >>
  TRY (PairCases_on ‘v’) >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac nc_sys >> imp_res_tac nc_close >> gvs[]
QED

Theorem nc_pdo:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ⇒ nc evs
Proof
  Cases_on ‘a’ >> rw[pdo_def, AllCaseEqs()] >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac nc_close >> imp_res_tac nc_l1do >> gvs[]
QED

Theorem nc_pacts:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ⇒ nc evs
Proof
  Induct >> rw[pacts_def, AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  res_tac >> imp_res_tac nc_pdo >> simp[]
QED

Theorem nc_polls:
  ∀chs w rv w' evs. l1_polls chs w = SOME (rv, w', evs) ⇒ nc evs
Proof
  Induct >> rw[l1_polls_def, AllCaseEqs()] >>
  res_tac >> imp_res_tac nc_sys >> simp[]
QED

Theorem nc_flush:
  ∀fs w st w' st' evs. l1_flush fs (w, st) = SOME ((w', st'), evs) ⇒ nc evs
Proof
  Induct >> rw[l1_flush_def, AllCaseEqs()] >> res_tac >> imp_res_tac nc_sys >> simp[]
QED

Theorem nc_fetch:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ⇒ nc evs
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> pairarg_tac >> gvs[] >>
  qpat_x_assum ‘_ = (ps1, _)’ (fn th => fs[th]) >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> imp_res_tac nc_sys >> simp[]
QED

Theorem nc_reap:
  ∀fs w st w' st' evs. l1_reap fs (w, st) = SOME ((w', st'), evs) ⇒ nc evs
Proof
  Induct >> rw[l1_reap_def, AllCaseEqs()] >> TRY (PairCases_on ‘ws’) >>
  res_tac >> imp_res_tac nc_close >> gvs[]
QED

Theorem nc_after:
  pf_after lfd hw hs ps fes (rv, w1, []) = SOME (rdy, (w', ps'), log, evs) ⇒ nc evs
Proof
  rw[pf_after_def, AllCaseEqs()] >> gvs[] >>
  imp_res_tac nc_flush >> imp_res_tac nc_fetch >> imp_res_tac nc_reap >> simp[]
QED

Theorem nc_tail:
  pf_tail lfd hw hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ⇒ nc evs
Proof
  simp[pf_tail_after, AllCaseEqs()] >> strip_tac >> PairCases_on ‘v’ >> gvs[] >>
  qpat_x_assum ‘pf_after _ _ _ _ _ _ = _’ (assume_tac o ONCE_REWRITE_RULE[pf_after_pevs]) >>
  gvs[] >> rename1 ‘pf_after _ _ _ _ _ _ = SOME z’ >> PairCases_on ‘z’ >> gvs[] >>
  imp_res_tac nc_polls >> imp_res_tac nc_after >> simp[]
QED

Theorem nc_pollb:
  sys_pollb fes w = SOME (INL (out, w', ev)) ⇒ FST (ev_lcall ev) ≠ «sys_connect»
Proof
  rw[sys_pollb_def, AllCaseEqs()] >> simp[ev_lcall_def]
QED

Theorem nc_bround:
  bround lfd hw idle hs (w, ps) acts = SOME (BRound snap (w', ps') log evs) ⇒ nc evs
Proof
  rw[bround_def, AllCaseEqs()] >> gvs[] >>
  imp_res_tac nc_pacts >> imp_res_tac nc_tail >> simp[] >>
  qpat_x_assum ‘pf_after _ _ _ _ _ _ = _’ (assume_tac o ONCE_REWRITE_RULE[pf_after_pevs]) >>
  gvs[] >> rename1 ‘pf_after _ _ _ _ _ _ = SOME z’ >> PairCases_on ‘z’ >> gvs[] >>
  imp_res_tac nc_after >> imp_res_tac nc_pollb >> simp[]
QED

Theorem nc_brounds:
  ∀n h w ps evs logs.
    brounds lfd hw ifds bz m (w0, ps0) n = SOME (BRun h (w, ps) evs logs) ⇒ nc evs
Proof
  Induct >- rw[brounds_def] >>
  rpt strip_tac >> drule brounds_SUC_BRun >> strip_tac >> PairCases_on ‘ws’ >>
  first_x_assum drule >> strip_tac >> imp_res_tac nc_bround >> gvs[]
QED

Theorem nc_brounds_slept:
  ∀n h evs cb.
    brounds lfd hw ifds bz m (w0, ps0) n = SOME (BSlept h evs cb) ⇒ nc evs
Proof
  Induct >- rw[brounds_def] >>
  simp[brounds_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
  >> TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  PairCases_on ‘ws’ >> imp_res_tac nc_brounds >> simp[] >>
  gvs[bround_def, AllCaseEqs()] >> imp_res_tac nc_pacts >> simp[]
QED

Theorem nc_prefix:
  nc b ∧ a ≼ b ⇒ nc a
Proof
  rw[nc_def, IS_PREFIX_APPEND] >> fs[]
QED

(* MAIN *)
Theorem bpre_nc:
  bpre lfd hw ifds bz m (w0, ps0) bp ⇒ nc bp
Proof
  rw[bpre_def] >> irule nc_prefix >> qexists_tac ‘evs’ >> simp[]
  >- (PairCases_on ‘ws’ >> drule nc_brounds >> simp[]) >>
  drule nc_brounds_slept >> simp[]
QED
