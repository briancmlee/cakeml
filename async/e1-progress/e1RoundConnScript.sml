(*
  One channel not connecting (close-v2, shared E1 progress layer,
  post-R3): honestL0WorldInv's noconn for a single channel c.  E1 runs
  have connecting channels (their pending connects), so noconn fails, but
  a channel that is up stays so: no delivery and no call makes an existing
  channel connecting (a connect's new channel is a new one).

  MAIN: nc_do, nc_do_buf.
*)
Theory e1RoundConn
Ancestors
  honestL1PFRound honestL0WorldInv honestL0WorldProps honestL0World
Libs
  preamble

Definition nc_def:
  nc c w ⇔ c < LENGTH w.chans ∧ ¬(EL c w.chans).connecting
End

Theorem nc_deliver:
  nc c w ⇒ nc c (l0_deliver w a)
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >>
  gvs[nc_def, upd_lchan_def, EL_LUPDATE] >> rw[] >>
  gvs[EL_APPEND_EQN, fresh_lchan_def] >> rw[] >> gvs[break_lchan_def] >> rw[]
QED

Theorem nc_tick:
  nc c w ⇒ nc c (l0_tick n w)
Proof
  simp[l0_tick_def] >>
  ‘∀as w. nc c w ⇒ nc c (FOLDL l0_deliver w as)’
    by (Induct >> simp[] >> metis_tac[nc_deliver]) >>
  rw[] >> first_x_assum irule >> gvs[nc_def]
QED

Theorem nc_ticks:
  ∀k w. nc c w ⇒ nc c (l0_ticks n k w)
Proof
  Induct >> simp[l0_ticks_def] >> metis_tac[nc_tick]
QED

Theorem nc_FOLDL_break:
  ∀q w. nc c w ⇒ nc c (FOLDL (λw j. upd_lchan j (break_lchan e F) w) w q)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  gvs[nc_def, upd_lchan_def, EL_LUPDATE] >> rw[] >> rw[break_lchan_def]
QED

Theorem nc_close_fd:
  nc c w ⇒ nc c (close_fd f w)
Proof
  rw[close_fd_def] >> every_case_tac >> gvs[] >>
  TRY (irule nc_FOLDL_break >> gvs[nc_def] >> NO_TAC) >>
  gvs[nc_def, upd_lchan_def, EL_LUPDATE] >> rw[] >> gvs[]
QED

Theorem nc_ops:
  (nc c w ∧ l0_listen p w = (x, w') ⇒ nc c w') ∧
  (nc c w ∧ l0_accept l w = (r, w') ⇒ nc c w') ∧
  (nc c w ∧ l0_recv f n w = (r, d, w') ⇒ nc c w') ∧
  (nc c w ∧ l0_send f bs w = (r, w') ⇒ nc c w') ∧
  (nc c w ∧ l0_shutdown f w = (r, w') ⇒ nc c w') ∧
  (nc c w ∧ l0_close f w = (r, w') ⇒ nc c w') ∧
  (nc c w ∧ l0_connerr f w = (y, w') ⇒ nc c w') ∧
  (nc c w ∧ l0_connect p w = (r, v, w') ⇒ nc c w')
Proof
  rpt conj_tac >>
  rw[l0_listen_def, l0_accept_def, l0_recv_def, l0_send_def, l0_shutdown_def,
     l0_close_def, l0_connerr_def, l0_connect_def, AllCaseEqs()] >> gvs[] >>
  TRY (simp[close_fd_def] >> every_case_tac >> simp[] >>
       TRY (irule nc_FOLDL_break) >> gvs[nc_def] >> NO_TAC) >>
  TRY (irule nc_close_fd >> simp[] >> NO_TAC) >>
  gvs[nc_def, upd_lchan_def, EL_LUPDATE, EL_APPEND1] >> rw[] >> rw[break_lchan_def] >>
  gvs[EL_APPEND1]
QED

Theorem nc_call:
  nc c w ∧ l0_call n conf bytes w = SOME (FFIreturn bytes' w') ⇒ nc c w'
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> imp_res_tac nc_ops >>
  TRY (drule_then irule nc_ticks) >> gvs[]
QED

Theorem nc_do:
  nc c w ∧ l0_do n conf alen w = SOME (out, w', ev) ⇒ nc c w'
Proof
  strip_tac >> drule l0_do_cases >> strip_tac >> gvs[] >>
  ‘nc c (l0_tick n w)’ by simp[nc_tick] >>
  drule_all nc_call >> simp[nc_def]
QED

Theorem nc_do_buf:
  nc c w ∧ l0_do_buf n conf bs w = SOME (out, w', ev) ⇒ nc c w'
Proof
  strip_tac >> drule l0_do_buf_cases >> strip_tac >> gvs[] >>
  ‘nc c (l0_tick n w)’ by simp[nc_tick] >>
  drule_all nc_call >> simp[nc_def]
QED
