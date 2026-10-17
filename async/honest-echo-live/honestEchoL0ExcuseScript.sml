(*
  The excuses of echo_live_l0 read off the PF run's events (design/47 D,
  the excuse mapping): honest-ffi's hard_send / hard_recv on a round's
  events are L3-00's hard_err_on (a send's or recv's result always
  decodes).

  MAIN: run_hard_err_on.
*)
Theory honestEchoL0Excuse
Ancestors
  honestL1PFConnTrace honestL1BStmts honestEchoL0Spec honestL1PFOutLive honestL1PFDead
  honestL1PFRound honestL1Steps honestL1Model honestL0Rely honestL0World honestL0 Marshalling
Libs
  preamble

(* Every result of a send or recv is a value or a fail of the world *)
Theorem l0_send_res:
  ∀f bs w. ∃e. FST (l0_send f bs w) = fail w e ∨ ∃v. FST (l0_send f bs w) = Ok v
Proof
  rw[l0_send_def, not_chan_def] >> every_case_tac >> simp[] >> metis_tac[]
QED

Theorem l0_recv_res:
  ∀f n w. ∃e. FST (l0_recv f n w) = fail w e ∨ ∃v. FST (l0_recv f n w) = Ok v
Proof
  rw[l0_recv_def, not_chan_def] >> every_case_tac >> simp[] >> metis_tac[]
QED

(* Such a result decodes, whatever follows it *)
Theorem dec_res_shape:
  l0_rely w ∧ (r = fail w e ∨ ∃v. r = Ok v) ⇒ dec_res (enc_res r ++ rest) = SOME r ∨
  ∃v. r = Ok v ∧ ∃r'. dec_res (enc_res r ++ rest) = SOME r'
Proof
  rw[]
  >- (disj1_tac >> irule dec_enc_res >> simp[fail_ok]) >>
  disj2_tac >> simp[enc_res_def, dec_res_def, LENGTH_n2w8]
QED

(* A run event that is a send or recv: its conf holds an fd, and its
   result decodes; a failed one decodes to its failure *)
Theorem sendrecv_dec:
  l0_rely x ∧ l0_ffi_fn n conf b x = SOME (FFIreturn out u) ∧
  (n = «sys_send» ∨ n = «sys_recv») ⇒
  8 ≤ LENGTH conf ∧ ∀e raw. l0_res_of out = Fail e raw ⇒ dec_res out = SOME (Fail e raw)
Proof
  strip_tac >>
  ‘∀nm. l0_rely (l0_tick nm x)’ by (rw[] >> irule l0_rely_ch >> qexists_tac ‘x’ >> simp[]) >>
  qpat_x_assum ‘l0_ffi_fn _ _ _ _ = _’ mp_tac >>
  simp[l0_ffi_fn_def, l0_call_def, AllCaseEqs()] >> rw[] >>
  rpt (pairarg_tac >> gvs[])
  >- (qspecl_then [‘bytes_fd (TAKE 8 conf)’, ‘DROP 8 conf’, ‘l0_tick «sys_send» x’]
        strip_assume_tac l0_send_res >> gvs[] >>
      TRY (gvs[l0_res_of_def, enc_res_def, dec_res_def, LENGTH_n2w8] >> NO_TAC) >>
      ‘l0_res_ok (fail (l0_tick «sys_send» x) e')’ by simp[fail_ok] >>
      drule dec_enc_res >> disch_then (qspec_then ‘[]’ mp_tac) >>
      qpat_x_assum ‘l0_res_of _ = _’ mp_tac >> rw[] >> gvs[l0_res_of_def]) >>
  qspecl_then [‘bytes_fd conf’, ‘LENGTH b − l0_hdr’, ‘l0_tick «sys_recv» x’]
    strip_assume_tac l0_recv_res >> gvs[] >>
  TRY (gvs[l0_res_of_def, enc_res_def, dec_res_def, LENGTH_n2w8] >> NO_TAC) >>
  ‘l0_res_ok (fail (l0_tick «sys_recv» x) e')’ by simp[fail_ok] >>
  drule dec_enc_res >> disch_then (qspec_then ‘d ++ DROP (l0_hdr + LENGTH d) b’ mp_tac) >>
  qpat_x_assum ‘l0_res_of _ = _’ mp_tac >> rw[] >> gvs[l0_res_of_def]
QED

(* MAIN: a hard send or recv failure on a run event is hard_err_on *)
Theorem run_hard_err_on:
  run_ok lfd pol ifds m w0 ∧ i < LENGTH (revs lfd pol ifds m w0 n) ∧
  EL i (revs lfd pol ifds m w0 n) = ev ∧
  (ev_on «sys_send» f ev ∨ ev_on «sys_recv» f ev) ∧ ¬retried ev ∧ ev_failed ev ⇒
  hard_err_on f ev
Proof
  strip_tac >> drule_all run_event_call >> strip_tac >> gvs[] >>
  gvs[ev_on_def, call_fds_def, ev_failed_def, retried_def] >>
  ‘8 ≤ LENGTH conf ∧ dec_res (MAP SND bs) = SOME (Fail e x')’
    by (qmatch_asmsub_abbrev_tac ‘l0_ffi_fn nm conf _ x’ >>
        ‘nm = «sys_send» ∨ nm = «sys_recv»’ by simp[Abbr ‘nm’] >>
        qpat_x_assum ‘Abbrev _’ kall_tac >> metis_tac[sendrecv_dec]) >>
  simp[hard_err_on_def, l0_ev_res_def]
QED
