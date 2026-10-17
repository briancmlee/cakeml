(*
  L3-09 (S3), for D32's excuse flushed_open: a channel that has broken
  with its unread input discarded stays so.  Data never arrives at a
  broken channel (l0_deliver), a break of a broken channel changes
  nothing (break_lchan), and the program's calls only take from an inbox.

  MAIN: replay_fl, world_at_fl.
*)
Theory honestL1BFlush
Ancestors
  honestL1BChan honestL1BStmts honestL1BPoll honestL0Part honestL0World honestL0
Libs
  preamble

(* Channel c is broken with an empty inbox *)
Definition fl_def:
  fl c (w : l0world) ⇔
    c < LENGTH w.chans ∧ (EL c w.chans).broken ∧ (EL c w.chans).inbox = []
End

Theorem deliver_fl:
  fl c w ⇒ fl c (l0_deliver w a)
Proof
  Cases_on ‘a’ >>
  rw[fl_def, l0_deliver_def, upd_lchan_def, EL_LUPDATE, break_lchan_def] >>
  every_case_tac >> gvs[EL_LUPDATE, EL_APPEND1] >> rw[] >> gvs[]
QED

Theorem FOLDL_deliver_fl:
  ∀q w. fl c w ⇒ fl c (FOLDL l0_deliver w q)
Proof
  Induct >> rw[] >> first_x_assum irule >> irule deliver_fl >> simp[]
QED

Theorem tick_fl:
  fl c w ⇒ fl c (l0_tick nm w)
Proof
  rw[l0_tick_def] >> irule FOLDL_deliver_fl >> fs[fl_def]
QED

Theorem ticks_fl:
  ∀n w. fl c w ⇒ fl c (l0_ticks nm n w)
Proof
  Induct >> rw[l0_ticks_def] >> first_x_assum irule >> irule tick_fl >> simp[]
QED

Theorem FOLDL_fl:
  ∀q w. (∀w' j. fl c w' ⇒ fl c (g w' j)) ∧ fl c w ⇒ fl c (FOLDL g w q)
Proof
  Induct >> rw[] >> first_x_assum irule >> simp[]
QED

Theorem l0_call_fl:
  l0_call n conf bytes w = SOME (FFIreturn out w') ∧ fl cc w ⇒ fl cc w'
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  TRY (irule ticks_fl >> simp[] >> NO_TAC) >>
  TRY (fs[fl_def] >> NO_TAC) >>
  gvs[l0_listen_def, l0_accept_def, l0_recv_def, l0_send_def, l0_shutdown_def,
      l0_connect_def, l0_connerr_def, l0_close_def, close_fd_def, l0_alloc_def,
      AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[AllCaseEqs()]) >>
  TRY (irule FOLDL_deliver_fl >> fs[fl_def] >> NO_TAC) >>
  TRY (irule FOLDL_fl >> conj_tac
       >- (rw[fl_def, upd_lchan_def, break_lchan_def, EL_LUPDATE] >> rw[]) >>
       fs[fl_def] >> NO_TAC) >>
  fs[fl_def, upd_lchan_def, EL_LUPDATE, break_lchan_def, EL_APPEND1] >> rw[] >> gvs[]
QED

Theorem step_fl:
  l0_step (SOME w) lc = SOME w' ∧ fl c w ⇒ fl c w'
Proof
  PairCases_on ‘lc’ >> rw[l0_step_def, l0_ffi_fn_def, AllCaseEqs()] >>
  ‘fl c (l0_tick lc0 w)’ by simp[tick_fl] >>
  drule_all l0_call_fl >> simp[fl_def]
QED

Theorem FOLDL_step_NONE[local]:
  ∀cs. FOLDL l0_step NONE cs = NONE
Proof
  Induct >> simp[l0_step_def]
QED

(* MAIN *)
Theorem replay_fl:
  ∀cs w w'. FOLDL l0_step (SOME w) cs = SOME w' ∧ fl c w ⇒ fl c w'
Proof
  Induct >- simp[] >> rpt gen_tac >> simp[] >>
  Cases_on ‘l0_step (SOME w) h’ >> simp[FOLDL_step_NONE] >> strip_tac >>
  first_x_assum irule >> qexists_tac ‘x’ >> simp[] >> metis_tac[step_fl]
QED

(* MAIN: along a trace *)
Theorem world_at_fl:
  world_at w0 a = SOME x ∧ world_at w0 (a ++ b) = SOME y ∧ fl c x ⇒ fl c y
Proof
  rw[world_at_def, l0_replay_def, FOLDL_APPEND] >> gvs[] >> metis_tac[replay_fl]
QED
