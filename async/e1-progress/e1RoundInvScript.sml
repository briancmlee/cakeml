(*
  The world invariant of E1's rounds (close-v2, shared E1 progress layer,
  post-R3): the PF lemmas' winv without noconn, which fails on E1 once a
  connect is pending.  Kept by every L0 call (connects: ewinv_connect).

  MAIN: sys_ewinv.
*)
Theory e1RoundInv
Ancestors
  honestL1EPRefine honestL1EPModel honestL1PFClose honestL1PFRefine honestL1PFRound honestL1Model honestL0WorldInv honestL0WorldProps honestL0Rely honestL0World
Libs
  preamble

Definition ewinv_def:
  ewinv w ⇔ l0_rely w ∧ l0wf w ∧ fds_lt w ∧ errb w
End

Theorem winv_ewinv:
  winv w ⇒ ewinv w
Proof
  simp[winv_def, ewinv_def]
QED

Theorem ewinv_do:
  ewinv w ∧ n ≠ «sys_connect» ∧ l0_do n conf alen w = SOME (out, w', ev) ⇒ ewinv w'
Proof
  strip_tac >>
  ‘l0_rely w'’ by (irule l0_do_rely >> gvs[ewinv_def] >> metis_tac[]) >>
  gvs[ewinv_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  ‘l0wf (l0_tick n w) ∧ fds_lt (l0_tick n w) ∧ errb (l0_tick n w)’
    by simp[l0wf_tick, errb_tick] >>
  rpt conj_tac
  >- (drule_all l0wf_call >> simp[])
  >- (drule_all fds_lt_call >> simp[fds_lt_def, l0_used_def])
  >> qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >>
  rw[l0_call_def] >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> imp_res_tac errb_ops >>
  TRY (drule_then irule errb_ticks) >> gvs[]
QED

Theorem ewinv_do_buf:
  ewinv w ∧ n ≠ «sys_connect» ∧ l0_do_buf n conf bs w = SOME (out, w', ev) ⇒ ewinv w'
Proof
  strip_tac >>
  ‘l0_rely w'’ by (irule l0_do_buf_rely >> gvs[ewinv_def] >> metis_tac[]) >>
  gvs[ewinv_def] >> drule l0_do_buf_cases >> strip_tac >> gvs[] >>
  ‘l0wf (l0_tick n w) ∧ fds_lt (l0_tick n w) ∧ errb (l0_tick n w)’
    by simp[l0wf_tick, errb_tick] >>
  rpt conj_tac
  >- (drule_all l0wf_call >> simp[])
  >- (drule_all fds_lt_call >> simp[fds_lt_def, l0_used_def])
  >> qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >>
  rw[l0_call_def] >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> imp_res_tac errb_ops >>
  TRY (drule_then irule errb_ticks) >> gvs[]
QED

Theorem errb_connect:
  errb w ∧ l0_connect p w = (r, v, w') ⇒ errb w'
Proof
  rw[l0_connect_def, AllCaseEqs()] >> gvs[errb_def] >>
  rw[upd_lchan_def, EL_LUPDATE, EL_APPEND_EQN] >> gvs[fresh_lchan_def] >>
  ‘j − LENGTH w.chans = 0’ by decide_tac >> gvs[]
QED

Theorem ewinv_connect:
  ewinv w ∧ sys_connect p w = SOME (out, w', ev) ⇒ ewinv w'
Proof
  strip_tac >>
  ‘l0_rely w' ∧ fds_lt w'’ by (drule_at (Pos last) sys_connect_l0 >> gvs[ewinv_def]) >>
  qpat_x_assum ‘sys_connect _ _ = _’ (strip_assume_tac o REWRITE_RULE [sys_connect_def]) >>
  gvs[ewinv_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  ‘l0wf (l0_tick «sys_connect» w) ∧ errb (l0_tick «sys_connect» w)’
    by simp[l0wf_tick, errb_tick] >>
  conj_tac
  >- (drule_all l0wf_call >> simp[]) >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >>
  rw[l0_call_def] >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> imp_res_tac errb_ops >>
  drule_all errb_connect >> simp[]
QED

(* L1's calls, connects and shutdowns included *)
Theorem sys_ewinv:
  (ewinv w ∧ sys_close g w = SOME (out, w', ev) ⇒ ewinv w') ∧
  (ewinv w ∧ sys_send g bs w = SOME (out, w', ev) ⇒ ewinv w') ∧
  (ewinv w ∧ sys_recv g k w = SOME (out, w', ev) ⇒ ewinv w') ∧
  (ewinv w ∧ sys_accept g w = SOME (out, w', ev) ⇒ ewinv w') ∧
  (ewinv w ∧ sys_poll fes w = SOME (out, w', ev) ⇒ ewinv w') ∧
  (ewinv w ∧ sys_connerr g w = SOME (out, w', ev) ⇒ ewinv w') ∧
  (ewinv w ∧ sys_shutdown g w = SOME (out, w', ev) ⇒ ewinv w') ∧
  (ewinv w ∧ sys_connect p w = SOME (out, w', ev) ⇒ ewinv w')
Proof
  rpt conj_tac >> strip_tac
  >- (gvs[sys_close_def] >> drule_at (Pos last) ewinv_do >> simp[])
  >- (gvs[sys_send_def] >> drule_at (Pos last) ewinv_do >> simp[])
  >- (gvs[sys_recv_def] >> drule_at (Pos last) ewinv_do >> simp[])
  >- (gvs[sys_accept_def] >> drule_at (Pos last) ewinv_do >> simp[])
  >- (gvs[sys_poll_def] >> drule_at (Pos last) ewinv_do_buf >> simp[])
  >- (gvs[sys_connerr_def] >> drule_at (Pos last) ewinv_do >> simp[])
  >- (gvs[sys_shutdown_def] >> drule_at (Pos last) ewinv_do >> simp[])
  >> drule_all ewinv_connect >> simp[]
QED
