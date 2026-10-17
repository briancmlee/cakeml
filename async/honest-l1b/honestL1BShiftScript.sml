(*
  The echo's guarantee across the program's leading listen.  The L1
  loops' guarantees (the PF run's, async-spike's; the blocking run's,
  honestL1BQuiet) are on the loop's trace from the world after the listen;
  the program's (l0_echo2_claim, quiet_on_kernel_claim) is on the whole
  trace from the start world.  A listen event is no accept, close, send,
  recv or poll, and replaying it from the start world gives the world
  after it, so the guarantee moves across it:

     echo2_guar_l0 KK w1 io  ⇒  echo2_guar_l0 KK W0 (LCONS ev io)

  for the listen ev from W0 to w1 (W0 with no listeners yet).  One copy,
  for both programs.

  MAIN: echo2_guar_shift, sys_listen_echo_shift.
*)
Theory honestL1BShift
Ancestors
  llist honestL0 honestL0World honestL0WorldProps honestL0Part honestL1Model
  honestEchoL0Spec honestEchoL0Prog honestL1BStmts
Libs
  preamble

(* A listen event *)
Definition listen_ev_def:
  listen_ev ev ⇔ ∃conf bs. ev = IO_event (ExtCall «sys_listen») conf bs
End

(* ------------------------------------------------------------------------
   A listen event is none of the events the guarantee reads
   ------------------------------------------------------------------------ *)

Theorem listen_ev_not[simp]:
  listen_ev ev ⇒
  l0_event_accepted ev = NONE ∧ l0_event_closed ev = NONE ∧
  (∀f. l0_event_sent f ev = []) ∧ (∀f. l0_event_recv f ev = []) ∧
  (∀f. ¬hard_err_on f ev) ∧ (∀f. ¬ep_ends f ev)
Proof
  rw[listen_ev_def] >>
  simp[l0_event_accepted_def, l0_event_closed_def, l0_event_sent_def, l0_event_recv_def,
       hard_err_on_def, ep_ends_def]
QED

Theorem l0_accepted_listen:
  listen_ev ev ⇒ l0_accepted (ev :: evs) = l0_accepted evs
Proof
  rw[l0_accepted_def]
QED

Theorem l0_ep_events_listen:
  listen_ev ev ⇒ l0_ep_events j 0 [] (ev :: evs) = l0_ep_events j 0 [] evs
Proof
  rw[l0_ep_events_def]
QED

Theorem l0_sent_listen:
  listen_ev ev ⇒ l0_sent j (ev :: evs) = l0_sent j evs
Proof
  rw[l0_sent_def, l0_accepted_listen, l0_ep_events_listen]
QED

Theorem l0_read_listen:
  listen_ev ev ⇒ l0_read j (ev :: evs) = l0_read j evs
Proof
  rw[l0_read_def, l0_accepted_listen, l0_ep_events_listen]
QED

Theorem ep_open_listen:
  listen_ev ev ⇒ (ep_open j (ev :: evs) ⇔ ep_open j evs)
Proof
  rw[ep_open_def] >> eq_tac >> rw[]
  >- (Cases_on ‘pre’ >> gvs[] >>
      qexistsl [‘t’, ‘ev'’, ‘post’, ‘f’] >> gvs[l0_accepted_listen])
  >> qexistsl [‘ev :: pre’, ‘ev'’, ‘post’, ‘f’] >> simp[l0_accepted_listen]
QED

Theorem ep_closed_listen:
  listen_ev ev ⇒ (ep_closed j (ev :: evs) ⇔ ep_closed j evs)
Proof
  rw[ep_closed_def] >> eq_tac >> rw[]
  >- (Cases_on ‘pre’ >> gvs[] >>
      qexistsl [‘t’, ‘ev'’, ‘post’, ‘f’] >> gvs[l0_accepted_listen])
  >> qexistsl [‘ev :: pre’, ‘ev'’, ‘post’, ‘f’] >> simp[l0_accepted_listen]
QED

(* ------------------------------------------------------------------------
   Prefixes, and the world after them
   ------------------------------------------------------------------------ *)

Theorem LPREFIX_fromList_LCONS:
  LPREFIX (fromList evs) (LCONS ev io) ⇔
    evs = [] ∨ ∃evs'. evs = ev :: evs' ∧ LPREFIX (fromList evs') io
Proof
  Cases_on ‘evs’ >> simp[LPREFIX_LCONS] >> metis_tac[]
QED

Theorem LPREFIX_cons:
  LPREFIX (fromList (ev :: evs)) (LCONS ev io) ⇔ LPREFIX (fromList evs) io
Proof
  simp[LPREFIX_LCONS]
QED

Theorem world_at_cons:
  l0_step (SOME W0) (ev_lcall ev) = SOME w1 ⇒ world_at W0 (ev :: evs) = world_at w1 evs
Proof
  simp[world_at_def, l0_replay_def]
QED

Theorem world_at_nil[simp]:
  world_at w0 [] = SOME w0
Proof
  simp[world_at_def, l0_replay_def]
QED

Theorem ffi_fn_ch[local]:
  l0_ffi_fn n conf b w = SOME (FFIreturn out w') ⇒ w'.ch = w.ch
Proof
  rw[l0_ffi_fn_def, AllCaseEqs()] >> drule l0_call_ch >> simp[]
QED

Theorem l0_step_ch:
  l0_step (SOME W0) c = SOME w1 ⇒ w1.ch = W0.ch
Proof
  PairCases_on ‘c’ >> rw[l0_step_def, AllCaseEqs()] >> metis_tac[ffi_fn_ch]
QED

(* ------------------------------------------------------------------------
   The guarantee's parts
   ------------------------------------------------------------------------ *)

Theorem LNTH_LCONS_SUC[local]:
  LNTH (SUC n) (LCONS h t) = LNTH n t
Proof
  simp[]
QED

Theorem echo_safe_shift:
  listen_ev ev ∧ echo_safe_l0 io ⇒ echo_safe_l0 (LCONS ev io)
Proof
  rw[echo_safe_l0_def, LPREFIX_fromList_LCONS]
  >- simp[l0_sent_def, l0_accepted_def]
  >> gvs[l0_sent_listen, l0_read_listen, l0_accepted_listen]
QED

Theorem F1_shift:
  F1_io (LCONS ev io) ⇒ F1_io io
Proof
  rw[F1_io_def] >>
  first_x_assum (qspecl_then [‘nm’, ‘f’] mp_tac) >> impl_tac
  >- (rpt strip_tac >> first_x_assum (qspec_then ‘i’ strip_assume_tac) >>
      qexistsl [‘SUC i'’, ‘ev'’] >> simp[]) >>
  disch_then (qspec_then ‘SUC i’ strip_assume_tac) >>
  Cases_on ‘i'’ >> gvs[] >> qexistsl [‘n’, ‘ev'’] >> simp[]
QED

Theorem accepts_below_shift:
  listen_ev ev ∧ accepts_below (LCONS ev io) ⇒ accepts_below io
Proof
  rw[accepts_below_def] >>
  first_x_assum (qspec_then ‘ev :: evs’ mp_tac) >> fs[LPREFIX_LCONS, l0_accepted_listen]
QED

Theorem accepts_fail_shift:
  accepts_fail_io io ⇒ accepts_fail_io (LCONS ev io)
Proof
  rw[accepts_fail_io_def] >> first_x_assum (qspec_then ‘i’ strip_assume_tac) >>
  qexistsl [‘SUC i'’, ‘conf’, ‘bs’, ‘e’, ‘x’] >> simp[]
QED

Theorem F2_shift:
  l0_step (SOME W0) c = SOME w1 ∧ F2 W0 ⇒ F2 w1
Proof
  rw[F2_def] >> drule l0_step_ch >> simp[]
QED

Theorem drains_shift:
  l0_step (SOME W0) (ev_lcall ev) = SOME w1 ∧ drains W0 (LCONS ev io) c ⇒ drains w1 io c
Proof
  rw[drains_def] >> drule world_at_cons >> strip_tac >>
  qpat_x_assum ‘∀evs w. LPREFIX (fromList evs) (LCONS ev io) ∧ _ ⇒ _’
    (qspecl_then [‘ev :: evs’, ‘w’] mp_tac) >>
  gvs[LPREFIX_LCONS] >> impl_tac
  >- (rpt strip_tac >> gvs[LPREFIX_LCONS] >> metis_tac[]) >>
  rw[] >> qexistsl [‘evs'’, ‘w'’] >> gvs[LPREFIX_LCONS]
QED

Theorem broke_shift:
  l0_step (SOME W0) (ev_lcall ev) = SOME w1 ∧ broke w1 io c ⇒ broke W0 (LCONS ev io) c
Proof
  rw[broke_def] >> drule world_at_cons >> strip_tac >>
  qexistsl [‘ev :: evs’, ‘w’] >> fs[LPREFIX_LCONS]
QED

(* For ruling #4 (echo_live_l0's excuse gains flushed_ch) *)
Theorem flushed_ch_shift:
  l0_step (SOME W0) (ev_lcall ev) = SOME w1 ∧ flushed_ch w1 io c ⇒
  flushed_ch W0 (LCONS ev io) c
Proof
  rw[flushed_ch_def] >> drule world_at_cons >> strip_tac >>
  qexistsl [‘ev :: evs’, ‘w’] >> fs[LPREFIX_LCONS]
QED

Theorem ep_hard_err_shift:
  listen_ev ev ∧ ep_hard_err j io ⇒ ep_hard_err j (LCONS ev io)
Proof
  rw[ep_hard_err_def] >> qexistsl [‘ev :: evs’, ‘ev'’] >>
  fs[LPREFIX_LCONS, ep_open_listen, l0_accepted_listen]
QED

Theorem ep_timed_out_shift:
  listen_ev ev ∧ ep_timed_out KK j io ⇒ ep_timed_out KK j (LCONS ev io)
Proof
  rw[ep_timed_out_def] >> qexistsl [‘ev :: evs’, ‘span’] >>
  fs[LPREFIX_LCONS, ep_open_listen, l0_accepted_listen]
QED

Theorem echo_live_shift:
  listen_ev ev ∧ l0_step (SOME W0) (ev_lcall ev) = SOME w1 ∧ echo_live_l0 KK w1 io ⇒
  echo_live_l0 KK W0 (LCONS ev io)
Proof
  rw[echo_live_l0_def, echo_live_unless_def] >>
  gvs[LPREFIX_fromList_LCONS]
  >- fs[ep_open_def] >>
  drule world_at_cons >> strip_tac >> gvs[] >>
  gvs[ep_open_listen, l0_accepted_listen] >>
  first_x_assum (qspecl_then [‘evs'’, ‘j’, ‘c’, ‘w’] mp_tac) >>
  impl_tac >- (simp[] >> irule drains_shift >> metis_tac[]) >>
  rw[]
  >- (disj1_tac >> disj1_tac >> irule ep_hard_err_shift >> simp[])
  >- (disj1_tac >> disj2_tac >> irule ep_timed_out_shift >> simp[])
  >> disj2_tac >> conj_tac
  >- (qexists_tac ‘ev :: evs''’ >> fs[LPREFIX_LCONS, l0_sent_listen])
  >> strip_tac >> gvs[] >>
  qexists_tac ‘ev :: evs'³'’ >> fs[LPREFIX_LCONS, ep_closed_listen]
QED

Theorem conn_live_shift:
  listen_ev ev ∧ l0_step (SOME W0) (ev_lcall ev) = SOME w1 ∧ W0.listeners = [] ∧
  conn_live_l0 w1 io ⇒
  conn_live_l0 W0 (LCONS ev io)
Proof
  rw[conn_live_l0_def, conn_live_unless_def] >>
  gvs[LPREFIX_fromList_LCONS] >>
  drule world_at_cons >> strip_tac >> gvs[] >>
  first_x_assum (qspecl_then [‘evs'’, ‘w’, ‘l’, ‘p’, ‘q’, ‘j0’] mp_tac) >> simp[] >>
  rw[]
  >- (disj1_tac >> irule accepts_fail_shift >> simp[])
  >- (disj2_tac >> disj1_tac >> qexistsl [‘ev :: evs''’, ‘w'’, ‘f’] >>
      fs[LPREFIX_LCONS, l0_accepted_listen])
  >> disj2_tac >> disj2_tac >> irule broke_shift >> metis_tac[]
QED

(* MAIN: the guarantee across the listen *)
Theorem echo2_guar_shift:
  listen_ev ev ∧ l0_step (SOME W0) (ev_lcall ev) = SOME w1 ∧ W0.listeners = [] ∧
  echo2_guar_l0 KK w1 io ⇒
  echo2_guar_l0 KK W0 (LCONS ev io)
Proof
  rw[echo2_guar_l0_def]
  >- (irule echo_safe_shift >> simp[]) >>
  ‘F1_io io ∧ F2 w1 ∧ accepts_below io’
    by metis_tac[F1_shift, F2_shift, accepts_below_shift] >>
  gvs[] >> metis_tac[echo_live_shift, conn_live_shift]
QED

(* The echo programs' listen is such an event *)
Theorem sys_listen_echo_shift:
  l0_rely W0 ∧ sys_listen_echo W0 = SOME (out, w1, ev) ⇒
  listen_ev ev ∧ l0_step (SOME W0) (ev_lcall ev) = SOME w1
Proof
  rw[sys_listen_echo_def, l0_do_def, AllCaseEqs()] >> simp[listen_ev_def] >>
  drule_all l0_ffi_fn_length >> strip_tac >>
  simp[ev_lcall_def, l0_step_def, MAP_ZIP]
QED
