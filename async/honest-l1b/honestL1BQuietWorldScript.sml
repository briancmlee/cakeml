(*
  L3-09 (S4), step 1: after the last arrival the world only changes by
  L1's calls.  Every call ticks the clock (and no call lowers it), so the
  PF run's clock passes the last arrival time; from then on a step of time
  only advances the clock.

  MAIN: quiet_tick, quiet_ticks, run_quiet.
*)
Theory honestL1BQuietWorld
Ancestors
  honestL1BFaith honestL1PFConnRun honestL1BStmts honestL1PFLive honestL1PFRound honestL1PFModel honestL1Steps
  honestL1Model honestL0Part honestL0WorldProps honestL0World honestL0
Libs
  preamble

Theorem deliver_clock[simp]:
  (l0_deliver w a).clock = w.clock
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >> simp[upd_lchan_def]
QED

Theorem FOLDL_deliver_clock[simp]:
  ∀as w. (FOLDL l0_deliver w as).clock = w.clock
Proof
  Induct >> simp[]
QED

Theorem tick_clock[simp]:
  (l0_tick nm w).clock = w.clock + 1
Proof
  simp[l0_tick_def]
QED

Theorem ticks_clock[simp]:
  ∀k w. (l0_ticks nm k w).clock = w.clock + k
Proof
  Induct >> simp[l0_ticks_def]
QED

Theorem FOLDL_upd_clock[simp]:
  ∀q w. (FOLDL (λw j. upd_lchan j g w) w q).clock = w.clock
Proof
  Induct >> rw[] >> first_x_assum (qspec_then ‘upd_lchan h g w’ SUBST1_TAC) >>
  simp[upd_lchan_def]
QED

Theorem ops_clock:
  (l0_listen p w = (x, w') ⇒ w'.clock = w.clock) ∧
  (l0_accept l w = (r, w') ⇒ w'.clock = w.clock) ∧
  (l0_recv f n w = (r, d, w') ⇒ w'.clock = w.clock) ∧
  (l0_send f bs w = (r, w') ⇒ w'.clock = w.clock) ∧
  (l0_shutdown f w = (r, w') ⇒ w'.clock = w.clock) ∧
  (l0_close f w = (r, w') ⇒ w'.clock = w.clock) ∧
  (l0_connect p w = (r, v, w') ⇒ w'.clock = w.clock) ∧
  (l0_connerr f w = (y, w') ⇒ w'.clock = w.clock)
Proof
  rpt conj_tac >> rw[l0_listen_def, l0_accept_def, l0_recv_def, l0_send_def,
                     l0_shutdown_def, l0_close_def, l0_connect_def, l0_connerr_def,
                     AllCaseEqs()] >> gvs[] >>
  rw[close_fd_def] >> every_case_tac >> simp[upd_lchan_def, FOLDL_upd_clock]
QED

Theorem l0_call_clock:
  l0_call n conf bytes w = SOME (FFIreturn bytes' w') ⇒ w.clock ≤ w'.clock
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> imp_res_tac ops_clock >> simp[]
QED

(* Every call moves the clock on *)
Theorem l0_ffi_fn_clock:
  l0_ffi_fn n conf bytes w = SOME (FFIreturn bytes' w') ⇒ w.clock < w'.clock
Proof
  rw[l0_ffi_fn_def, AllCaseEqs()] >> drule l0_call_clock >> simp[]
QED

(* ------------------------------------------------------------------------
   After the last arrival
   ------------------------------------------------------------------------ *)

Definition quiet_after_def:
  quiet_after N (w : l0world) ⇔ ∀n h nm. N ≤ n ⇒ w.env n h nm = []
End

Theorem quiet_tick:
  quiet_after N w ∧ N ≤ w.clock ⇒ l0_tick nm w = w with clock := w.clock + 1
Proof
  rw[quiet_after_def, l0_tick_def]
QED

Theorem quiet_ticks:
  ∀k w. quiet_after N w ∧ N ≤ w.clock ⇒ l0_ticks nm k w = w with clock := w.clock + k
Proof
  Induct >> simp[l0_ticks_def] >> rpt strip_tac >>
  drule_all quiet_tick >> disch_then (qspec_then ‘nm’ SUBST1_TAC) >>
  first_x_assum (qspec_then ‘w with clock := w.clock + 1’ mp_tac) >>
  impl_tac >- fs[quiet_after_def] >> simp[] >> strip_tac >>
  simp[honestL0WorldTheory.l0world_component_equality]
QED

(* ------------------------------------------------------------------------
   The PF run's clock passes any bound
   ------------------------------------------------------------------------ *)

Theorem l0_ffi_fn_env:
  l0_ffi_fn n conf bytes w = SOME (FFIreturn bytes' w') ⇒ w'.env = w.env
Proof
  rw[l0_ffi_fn_def, AllCaseEqs()] >> drule l0_call_env >> simp[]
QED

Theorem faithful_clock:
  ∀evs u u'. faithful u evs ∧ FOLDL l0_step (SOME u) (MAP ev_lcall evs) = SOME u' ⇒
             u.clock + LENGTH evs ≤ u'.clock ∧ u'.env = u.env
Proof
  Induct >> rw[faithful_def] >> gvs[ev_lcall_def, l0_step_def] >>
  first_x_assum drule_all >> strip_tac >>
  imp_res_tac l0_ffi_fn_clock >> imp_res_tac l0_ffi_fn_env >> simp[]
QED

Theorem run_clock:
  run_ok lfd pol ifds m w0 ⇒
  ∀n. w0.clock + n ≤ (rworld lfd pol ifds m w0 n).clock ∧
      (rworld lfd pol ifds m w0 n).env = w0.env
Proof
  strip_tac >> gen_tac >>
  drule prun_some >> disch_then (qspec_then ‘n’ assume_tac) >>
  Cases_on ‘prun lfd pol ifds m w0 n’ >> rename1 ‘(hh, r)’ >> PairCases_on ‘r’ >>
  ‘l0_rely w0’ by fs[run_ok_def] >>
  drule fplays_prounds >> simp[fplays_def] >> strip_tac >>
  drule_all faithful_clock >> strip_tac >>
  drule revs_grows >> disch_then (qspec_then ‘n’ mp_tac) >>
  gvs[rworld_def, revs_def]
QED

(* MAIN: from some round on, the PF run's worlds are past the last arrival *)
Theorem run_quiet:
  run_ok lfd pol ifds m w0 ∧ quiet_after N w0 ⇒
  ∃n0. ∀n. n0 ≤ n ⇒ N ≤ (rworld lfd pol ifds m w0 n).clock ∧
                    quiet_after N (rworld lfd pol ifds m w0 n)
Proof
  strip_tac >> drule run_clock >> strip_tac >> qexists_tac ‘N’ >> rw[]
  >- (first_x_assum (qspec_then ‘n’ strip_assume_tac) >> decide_tac)
  >> fs[quiet_after_def]
QED
