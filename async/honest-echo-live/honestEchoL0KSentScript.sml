(*
  Episode j's sent bytes in the kernel (design/47 D, step i, the kernel
  side): replaying a faithful trace, the channel an accept gave f starts
  with nothing sent, and while no close is called on f it grows by exactly
  what the trace's sends on f took (l0_event_sent).  Read on the trace
  through world_at, so it holds of any faithful L1 trace, not only the
  PF run's.

  MAIN: faithful_csent, faithful_accept_csent.
*)
Theory honestEchoL0KSent
Ancestors
  honestEchoL0Sent honestEchoL0Spec honestL1BFaith honestL1BStmts honestL0Part
  honestL1PFOut honestL1PFRound honestL1Steps honestL1Inv honestL1Model honestL0WorldProps
  honestL0WorldInv honestL0Rely honestL0World
Libs
  preamble

(* honest-ffi's per-event account is the trace's *)
Theorem ev_sent_l0:
  ev_sent f ev = l0_event_sent f ev
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bs’ >> Cases_on ‘nm’ >>
  rw[ev_sent_def, l0_event_sent_def, taken_def, l0_res_of_def, l0_ev_res_def] >>
  every_case_tac >> fs[DROP_LENGTH_TOO_LONG]
QED

(* A call on f's fd that is a close: what ends f's channel *)
Definition closes_fd_def:
  closes_fd f (IO_event nm conf bs) ⇔ nm = ExtCall «sys_close» ∧ bytes_fd conf = f
End

Theorem faithful_CONS_buf:
  faithful w (ev :: evs) ⇒
  ∃n conf bs u. ev = IO_event (ExtCall n) conf bs ∧ MEM n l1_names ∧
                l0_do_buf n conf (MAP FST bs) w = SOME (MAP SND bs, u, ev) ∧
                l0_step (SOME w) (ev_lcall ev) = SOME u ∧ faithful u evs
Proof
  rw[faithful_def] >> simp[l0_do_buf_def, l0_step_def, ev_lcall_def, ZIP_MAP_FST_SND_EQ]
QED

(* One faithful event keeps winv and f's channel, and adds its sent bytes *)
Theorem faithful_step_csent:
  winv w ∧ l0_chan_of w f = SOME c ∧ ¬closes_fd f ev ∧ faithful w (ev :: evs) ⇒
  ∃u. l0_step (SOME w) (ev_lcall ev) = SOME u ∧ faithful u evs ∧ winv u ∧
      l0_chan_of u f = SOME c ∧ csent u c = csent w c ++ l0_event_sent f ev
Proof
  strip_tac >> drule faithful_CONS_buf >> strip_tac >> gvs[] >>
  ‘n ≠ «sys_connect»’ by (strip_tac >> gvs[l1_names_def]) >>
  conj_tac >- metis_tac[winv_do_buf] >>
  drule_at (Pos last) csent_do_buf >> simp[GSYM ev_sent_l0] >>
  disch_then irule >> fs[closes_fd_def]
QED

(* MAIN: while f is not closed, its channel takes exactly f's sends *)
Theorem faithful_csent:
  ∀evs w. faithful w evs ∧ winv w ∧ l0_chan_of w f = SOME c ∧
          EVERY (λe. ¬closes_fd f e) evs ⇒
          ∃u. FOLDL l0_step (SOME w) (MAP ev_lcall evs) = SOME u ∧ winv u ∧
              l0_chan_of u f = SOME c ∧
              csent u c = csent w c ++ FLAT (MAP (l0_event_sent f) evs)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  drule_all faithful_step_csent >> strip_tac >> simp[] >>
  first_x_assum drule_all >> strip_tac >> simp[]
QED

(* MAIN: an accept that returned f gives f a channel with nothing sent *)
Theorem faithful_accept_csent:
  faithful w (ev :: evs) ∧ winv w ∧ qfresh w ∧ l0_event_accepted ev = SOME f ⇒
  ∃u c. l0_step (SOME w) (ev_lcall ev) = SOME u ∧ faithful u evs ∧ winv u ∧ qfresh u ∧
        l0_chan_of u f = SOME c ∧ csent u c = []
Proof
  strip_tac >> drule faithful_CONS_buf >> strip_tac >> gvs[] >>
  ‘n ≠ «sys_connect»’ by (strip_tac >> gvs[l1_names_def]) >>
  ‘winv u ∧ qfresh u’ by metis_tac[winv_do_buf, qfresh_do_buf] >> simp[] >>
  gvs[l0_event_accepted_def, AllCaseEqs(), l0_ev_res_def, l0_do_buf_def, l0_ffi_fn_def,
      l0_call_def] >>
  pairarg_tac >> gvs[] >>
  ‘l0_rely (l0_tick «sys_accept» w)’
    by (irule l0_rely_ch >> qexists_tac ‘w’ >> gvs[winv_def]) >>
  ‘qfresh (l0_tick «sys_accept» w)’ by simp[qfresh_tick] >>
  drule_all l0_accept_res >> strip_tac >>
  ‘r = Ok k’ by (drule l0_res_of_enc >> simp[l0_res_of_def]) >> gvs[] >>
  drule_all l0_accept_chan >> strip_tac >> qexists_tac ‘c’ >>
  gvs[l0_chan_of_def, csent_def]
QED
