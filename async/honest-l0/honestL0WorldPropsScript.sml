(*
  Basic facts about the L0 world (not trusted: proved).
   - l0_ffi_fn_length: every call returns a buffer of the length it was
     given, as CakeML's FFI semantics requires of an oracle;
   - time, arrivals and calls never change the world's choices or fd limit,
     so the rely holds all along a run (l0_ffi_fn_rely).
*)
Theory honestL0WorldProps
Ancestors
  honestL0World honestL0Rely honestL0 Marshalling
Libs
  preamble

Theorem LENGTH_enc_ok[simp]:
  LENGTH (enc_res (Ok v)) = 13
Proof
  simp[enc_res_def, LENGTH_n2w8]
QED

Theorem LENGTH_enc_fail:
  l0_rely w ⇒ LENGTH (enc_res (fail w e)) = 13
Proof
  rw[fail_def, enc_res_def, l0_rely_def, LENGTH_n2w8]
QED

Theorem LENGTH_enc_not_chan:
  l0_rely w ⇒ LENGTH (enc_res (not_chan w f)) = 13
Proof
  rw[not_chan_def] >> simp[LENGTH_enc_fail]
QED

Theorem deliver_ch[simp]:
  (l0_deliver w a).ch = w.ch ∧ (l0_deliver w a).fd_limit = w.fd_limit
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def, upd_lchan_def] >> every_case_tac >> simp[]
QED

Theorem FOLDL_deliver_ch[simp]:
  ∀as w. (FOLDL l0_deliver w as).ch = w.ch ∧ (FOLDL l0_deliver w as).fd_limit = w.fd_limit
Proof
  Induct >> simp[]
QED

Theorem tick_ch[simp]:
  (l0_tick nm w).ch = w.ch ∧ (l0_tick nm w).fd_limit = w.fd_limit
Proof
  simp[l0_tick_def]
QED

Theorem ticks_ch[simp]:
  ∀k w. (l0_ticks nm k w).ch = w.ch ∧ (l0_ticks nm k w).fd_limit = w.fd_limit
Proof
  Induct >> simp[l0_ticks_def]
QED

Theorem recv_LENGTH:
  l0_recv f n w = (r, d, w') ⇒ LENGTH d ≤ n
Proof
  rw[l0_recv_def, AllCaseEqs()] >> gvs[LENGTH_TAKE_EQ] >> rw[MIN_DEF]
QED

Theorem upd_lchan_ch[simp]:
  (upd_lchan j g w).ch = w.ch ∧ (upd_lchan j g w).fd_limit = w.fd_limit
Proof
  simp[upd_lchan_def]
QED

Theorem FOLDL_upd_ch[simp]:
  ∀q w. (FOLDL (λw j. upd_lchan j (g j) w) w q).ch = w.ch ∧
        (FOLDL (λw j. upd_lchan j (g j) w) w q).fd_limit = w.fd_limit
Proof
  Induct >> simp[]
QED

Theorem close_fd_ch[simp]:
  (close_fd f w).ch = w.ch ∧ (close_fd f w).fd_limit = w.fd_limit
Proof
  rw[close_fd_def] >> every_case_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac ‘FOLDL _ w0 q’ >>
  ‘∀q w0. (FOLDL (λw j. upd_lchan j (break_lchan E_CONNRESET F) w) w0 q).ch = w0.ch ∧
          (FOLDL (λw j. upd_lchan j (break_lchan E_CONNRESET F) w) w0 q).fd_limit = w0.fd_limit’
    by (Induct >> simp[]) >>
  simp[Abbr ‘w0’]
QED

Theorem ops_ch:
  (l0_listen p w = (x, w') ⇒ w'.ch = w.ch ∧ w'.fd_limit = w.fd_limit) ∧
  (l0_accept l w = (r, w') ⇒ w'.ch = w.ch ∧ w'.fd_limit = w.fd_limit) ∧
  (l0_recv f n w = (r, d, w') ⇒ w'.ch = w.ch ∧ w'.fd_limit = w.fd_limit) ∧
  (l0_send f bs w = (r, w') ⇒ w'.ch = w.ch ∧ w'.fd_limit = w.fd_limit) ∧
  (l0_shutdown f w = (r, w') ⇒ w'.ch = w.ch ∧ w'.fd_limit = w.fd_limit) ∧
  (l0_close f w = (r, w') ⇒ w'.ch = w.ch ∧ w'.fd_limit = w.fd_limit)
Proof
  rpt conj_tac >> rw[l0_listen_def, l0_accept_def, l0_recv_def, l0_send_def,
                     l0_shutdown_def, l0_close_def, AllCaseEqs()] >> gvs[]
QED

Theorem LENGTH_poll_out:
  LENGTH (poll_out w fes) = 13 + LENGTH fes
Proof
  simp[poll_out_def]
QED

(* MAIN: buffers keep their length *)
Theorem l0_call_length:
  l0_rely w ∧ l0_call n conf bytes w = SOME (FFIreturn bytes' w') ⇒
  LENGTH bytes' = LENGTH bytes
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs(), l0_hdr_def, LENGTH_poll_out, LENGTH_enc_fail]
  >- (Cases_on ‘ke’ >> gvs[enc_listen_fail_def, LENGTH_n2w8, l0_rely_def])
  >- (pairarg_tac >> gvs[] >>
      ‘∃e. r = Ok (w2n e) ∨ ∃e'. r = fail w e' ∨ r = not_chan w e’ by
        (gvs[l0_accept_def, AllCaseEqs()] >> metis_tac[]) >>
      gvs[LENGTH_enc_fail, LENGTH_enc_not_chan] >>
      gvs[l0_accept_def, AllCaseEqs(), LENGTH_enc_fail])
  >- (pairarg_tac >> gvs[] >> imp_res_tac recv_LENGTH >>
      ‘LENGTH (enc_res r) = 13’ by
        (gvs[l0_recv_def, AllCaseEqs(), LENGTH_enc_fail, LENGTH_enc_not_chan]) >>
      simp[])
  >> pairarg_tac >> gvs[] >>
  gvs[l0_send_def, l0_shutdown_def, l0_close_def, AllCaseEqs(),
      LENGTH_enc_fail, LENGTH_enc_not_chan]
QED

Theorem l0_call_ch:
  l0_call n conf bytes w = SOME (FFIreturn bytes' w') ⇒
  w'.ch = w.ch ∧ w'.fd_limit = w.fd_limit
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> imp_res_tac ops_ch >> simp[]
QED

(* MAIN: a call, with the step of time before it, returns a buffer of the
   length it was given, and the rely holds afterwards *)
Theorem l0_ffi_fn_length:
  l0_rely w ∧ l0_ffi_fn n conf bytes w = SOME (FFIreturn bytes' w') ⇒
  LENGTH bytes' = LENGTH bytes ∧ l0_rely w'
Proof
  simp[l0_ffi_fn_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  ‘l0_rely (l0_tick n w)’ by (irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  drule_all l0_call_length >> simp[] >> strip_tac >>
  imp_res_tac l0_call_ch >> irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]
QED
