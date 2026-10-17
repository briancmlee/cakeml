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

Theorem LENGTH_enc_err_val:
  l0_rely w ⇒ LENGTH (enc_err_val w e v) = 13
Proof
  rw[enc_err_val_def, l0_rely_def, LENGTH_n2w8]
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
  (l0_close f w = (r, w') ⇒ w'.ch = w.ch ∧ w'.fd_limit = w.fd_limit) ∧
  (l0_connect p w = (r, v, w') ⇒ w'.ch = w.ch ∧ w'.fd_limit = w.fd_limit) ∧
  (l0_connerr f w = (y, w') ⇒ w'.ch = w.ch ∧ w'.fd_limit = w.fd_limit)
Proof
  rpt conj_tac >> rw[l0_listen_def, l0_accept_def, l0_recv_def, l0_send_def,
                     l0_shutdown_def, l0_close_def, l0_connect_def, l0_connerr_def,
                     AllCaseEqs()] >> gvs[]
QED

Theorem LENGTH_FLAT_entries:
  ∀bs g. LENGTH bs MOD 8 = 0 ∧ (∀i e. LENGTH (g i e) = 2) ⇒
         LENGTH (FLAT (MAPi (λi e. TAKE 6 e ++ g i e) (pollfd_entries bs))) = LENGTH bs
Proof
  recInduct pollfd_entries_ind >> rw[] >>
  ONCE_REWRITE_TAC [pollfd_entries_def] >> rw[]
  >- (‘LENGTH bs MOD 8 = LENGTH bs’ by (irule LESS_MOD >> simp[]) >> fs[])
  >> simp[o_DEF] >>
  first_x_assum (drule_then (qspec_then ‘λi. g (SUC i)’ mp_tac)) >> impl_tac
  >- (simp[] >> qpat_x_assum ‘LENGTH bs MOD 8 = 0’ mp_tac >>
          ‘LENGTH bs = (LENGTH bs − 8) + 8’ by simp[] >>
          pop_assum (fn th => ONCE_REWRITE_TAC [th]) >> simp[ADD_MODULUS]) >>
  simp[]
QED

Theorem LENGTH_FLAT_entries_MAP:
  ∀bs. LENGTH bs MOD 8 = 0 ∧ (∀e. LENGTH (g e) = 2) ⇒
       LENGTH (FLAT (MAP (λe. TAKE 6 e ++ g e) (pollfd_entries bs))) = LENGTH bs
Proof
  recInduct pollfd_entries_ind >> rw[] >>
  ONCE_REWRITE_TAC [pollfd_entries_def] >> rw[]
  >- (‘LENGTH bs MOD 8 = LENGTH bs’ by (irule LESS_MOD >> simp[]) >> fs[])
  >> first_x_assum drule >> impl_tac
  >- (simp[] >> qpat_x_assum ‘LENGTH bs MOD 8 = 0’ mp_tac >>
          ‘LENGTH bs = (LENGTH bs − 8) + 8’ by simp[] >>
          pop_assum (fn th => ONCE_REWRITE_TAC [th]) >> simp[ADD_MODULUS]) >>
  simp[]
QED

Theorem LENGTH_poll_out:
  l0_rely w ∧ 16 ≤ LENGTH bytes ∧ (LENGTH bytes − 16) MOD 8 = 0 ⇒
  LENGTH (poll_out w bytes) = LENGTH bytes ∧ LENGTH (poll_failed w e bytes) = LENGTH bytes
Proof
  strip_tac >> drule LENGTH_enc_fail >> strip_tac >>
  ‘LENGTH (DROP 16 bytes) MOD 8 = 0’ by simp[] >>
  simp[poll_out_def, poll_failed_def, LENGTH_enc_fail] >> conj_tac
  >- (qspecl_then [‘λe. abi_rev (pfd_revents w (pe_fe e))’, ‘DROP 16 bytes’] mp_tac
        (Q.GEN ‘g’ LENGTH_FLAT_entries_MAP) >> simp[abi_rev_def])
  >> qspecl_then [‘DROP 16 bytes’, ‘λi e. [w.ch.poll_junk w.hist (2 * i);
                                         w.ch.poll_junk w.hist (2 * i + 1)]’] mp_tac
       LENGTH_FLAT_entries >> simp[]
QED

(* MAIN: buffers keep their length *)
Theorem l0_call_length:
  l0_rely w ∧ l0_call n conf bytes w = SOME (FFIreturn bytes' w') ⇒
  LENGTH bytes' = LENGTH bytes
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs(), l0_hdr_def, LENGTH_enc_fail] >>
  TRY (irule (cj 1 LENGTH_poll_out) >> simp[] >> NO_TAC) >>
  TRY (irule (cj 2 LENGTH_poll_out) >> simp[] >> NO_TAC) >>
  TRY (irule (cj 1 LENGTH_poll_out) >> simp[] >> irule l0_rely_ch >>
       qexists_tac ‘w’ >> simp[ticks_ch] >> NO_TAC)
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
  >> TRY (pairarg_tac >> gvs[]) >>
  gvs[l0_send_def, l0_shutdown_def, l0_close_def, l0_connect_def, l0_connerr_def,
      AllCaseEqs(), LENGTH_enc_fail, LENGTH_enc_not_chan, LENGTH_enc_err_val]
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

(* ------------------------------------------------------------------------
   Every fd in use stays below the limit (moved from honestL1Steps)
   ------------------------------------------------------------------------ *)

Definition fds_lt_def:
  fds_lt (w : l0world) ⇔ ∀x. MEM x (l0_used w) ⇒ w2n x < w.fd_limit
End

Theorem used_deliver[simp]:
  l0_used (l0_deliver w a) = l0_used w ∧ (l0_deliver w a).fd_limit = w.fd_limit
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def, l0_used_def, upd_lchan_def] >>
  every_case_tac >> gvs[] >>
  simp[AFUPDKEY_def] >> rpt (pop_assum mp_tac) >>
  qid_spec_tac ‘w.listeners’ >> Induct >> simp[AFUPDKEY_def, FORALL_PROD] >> rw[]
QED

Theorem used_FOLDL_deliver[simp]:
  ∀as w. l0_used (FOLDL l0_deliver w as) = l0_used w
Proof
  Induct >> simp[]
QED

Theorem fds_lt_tick[simp]:
  fds_lt (l0_tick nm w) ⇔ fds_lt w
Proof
  simp[fds_lt_def, l0_tick_def] >>
  ‘l0_used (w with clock := w.clock + 1) = l0_used w’ by simp[l0_used_def] >>
  simp[]
QED
