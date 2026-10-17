(*
  L3-09 (S4), step 3a: past the last arrival the bytes waiting in the
  kernel's inboxes only fall.  Only arrivals add to an inbox; a recv takes
  bytes, a reset discards them, and nothing else touches them.  A recv
  that returns data takes at least one byte.

  MAIN: inbox_quiet_ffi, recv_data_inbox.
*)
Theory honestL1BInbox
Ancestors
  honestL1BQueue honestL1BQuietWorld honestL1BFaith honestL1BStmts honestL1PFConn
  honestL1PFRound honestL1Steps honestL1Inv honestL1Model honestEchoL0Spec
  honestL0WorldInv honestL0Part honestL0WorldProps honestL0Rely honestL0World honestL0
Libs
  preamble

Definition tot_inbox_def:
  tot_inbox (w : l0world) = SUM (MAP (λc. LENGTH c.inbox) w.chans)
End

Theorem tot_inbox_simple[simp]:
  tot_inbox (w with clock := c) = tot_inbox w ∧ tot_inbox (w with hist := h) = tot_inbox w ∧
  tot_inbox (w with listeners := ls) = tot_inbox w ∧
  tot_inbox (w with open_fds := ofs) = tot_inbox w ∧
  tot_inbox (w with reserved := rs) = tot_inbox w
Proof
  simp[tot_inbox_def]
QED

Theorem SUM_MAP_LUPDATE_le[local]:
  ∀l j x. j < LENGTH l ∧ f x ≤ f (EL j l) ⇒ SUM (MAP f (LUPDATE x j l)) ≤ SUM (MAP f l)
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on ‘j’ >> simp[LUPDATE_def] >> rw[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem SUM_MAP_LUPDATE_lt[local]:
  ∀l j x. j < LENGTH l ∧ f x < f (EL j l) ⇒ SUM (MAP f (LUPDATE x j l)) < SUM (MAP f l)
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on ‘j’ >> simp[LUPDATE_def] >> rw[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem tot_upd_le:
  (j < LENGTH w.chans ⇒ LENGTH (g (EL j w.chans)).inbox ≤ LENGTH (EL j w.chans).inbox) ⇒
  tot_inbox (upd_lchan j g w) ≤ tot_inbox w
Proof
  rw[tot_inbox_def, upd_lchan_def] >> Cases_on ‘j < LENGTH w.chans’
  >- (irule SUM_MAP_LUPDATE_le >> simp[])
  >> simp[LUPDATE_SEM, LIST_EQ_REWRITE] >>
  ‘LUPDATE (g (EL j w.chans)) j w.chans = w.chans’ by simp[LUPDATE_SEM, LIST_EQ_REWRITE] >>
  simp[]
QED

Theorem tot_FOLDL_break_le:
  ∀q w. tot_inbox (FOLDL (λw j. upd_lchan j (break_lchan e kp) w) w q) ≤ tot_inbox w
Proof
  Induct >> simp[] >> rpt gen_tac >>
  irule LESS_EQ_TRANS >> qexists_tac ‘tot_inbox (upd_lchan h (break_lchan e kp) w)’ >>
  simp[] >> irule tot_upd_le >> rw[break_lchan_def]
QED

val tot_tac =
  TRY (irule LESS_EQ_TRANS >> irule_at (Pos hd) tot_upd_le >> rw[break_lchan_def] >> NO_TAC) >>
  TRY (irule LESS_EQ_TRANS >> irule_at (Pos hd) tot_FOLDL_break_le >> simp[] >> NO_TAC) >>
  TRY (irule tot_upd_le >> rw[break_lchan_def] >> NO_TAC) >>
  simp[];

Theorem tot_close_fd_le:
  tot_inbox (close_fd f w) ≤ tot_inbox w
Proof
  rw[close_fd_def] >> every_case_tac >> tot_tac
QED

Theorem tot_ops:
  (l0_accept l w = (r, w') ⇒ tot_inbox w' ≤ tot_inbox w) ∧
  (l0_recv f n w = (r, d, w') ⇒ tot_inbox w' ≤ tot_inbox w) ∧
  (l0_send f bs w = (r, w') ⇒ tot_inbox w' ≤ tot_inbox w) ∧
  (l0_close f w = (r, w') ⇒ tot_inbox w' ≤ tot_inbox w)
Proof
  rpt conj_tac >> strip_tac
  >- (gvs[l0_accept_def, AllCaseEqs(), fail_def, l0_alloc_def] >> tot_tac)
  >- (gvs[l0_recv_def, AllCaseEqs(), fail_def] >> tot_tac)
  >- (gvs[l0_send_def, AllCaseEqs(), fail_def] >> tot_tac)
  >> gvs[l0_close_def, AllCaseEqs(), fail_def] >> simp[tot_close_fd_le]
QED

Theorem recv_ok_lt:
  l0_rely w ∧ l0_recv f n w = (Ok k, d, w') ∧ 0 < k ⇒ tot_inbox w' < tot_inbox w
Proof
  rw[l0_recv_def, AllCaseEqs(), fail_def, not_chan_def] >> gvs[] >>
  simp[tot_inbox_def, upd_lchan_def] >>
  irule (BETA_RULE (Q.ISPEC ‘λc:lchan. LENGTH c.inbox’ (Q.GEN ‘f’ SUM_MAP_LUPDATE_lt))) >>
  fs[l0_chan_of_def, AllCaseEqs()] >> Cases_on ‘(EL j w.chans).inbox’ >> gvs[] >>
  simp[LENGTH_DROP, MIN_DEF] >> rw[]
QED

Theorem tot_call_quiet:
  l0_call n conf bytes w = SOME (FFIreturn out w') ∧ MEM n l1_names ∧
  quiet_after N w ∧ N ≤ w.clock ⇒
  tot_inbox w' ≤ tot_inbox w
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs(), l1_names_def] >>
  rpt (pairarg_tac >> gvs[]) >> imp_res_tac tot_ops >> simp[] >>
  drule_all quiet_ticks >> disch_then (fn th => simp[th])
QED

(* One call, past the last arrival *)
Theorem tot_ffi_quiet:
  l0_ffi_fn n conf bytes u = SOME (FFIreturn out u') ∧ MEM n l1_names ∧
  quiet_after N u ∧ N ≤ u.clock ⇒
  tot_inbox u' ≤ tot_inbox u
Proof
  rw[l0_ffi_fn_def, AllCaseEqs()] >>
  ‘l0_tick n u = u with clock := u.clock + 1’ by metis_tac[quiet_tick] >> fs[] >>
  drule tot_call_quiet >> simp[] >> disch_then (qspec_then ‘N’ mp_tac) >>
  simp[quiet_after_mono]
QED

Theorem recv_fail_ok[local]:
  l0_rely w ∧ l0_recv f n w = (Fail e x, d, w') ⇒ l0_res_ok (Fail e x)
Proof
  rw[l0_recv_def, AllCaseEqs()] >> gvs[not_chan_def] >> metis_tac[fail_ok]
QED

(* A recv that returns data takes bytes from an inbox *)
Theorem recv_data_ffi:
  l0_ffi_fn «sys_recv» conf bytes u = SOME (FFIreturn out u') ∧ l0_rely u ∧
  quiet_after N u ∧ N ≤ u.clock ∧ l0_res_of out = Ok k ∧ 0 < k ⇒
  tot_inbox u' < tot_inbox u
Proof
  rw[l0_ffi_fn_def, AllCaseEqs()] >>
  ‘l0_tick «sys_recv» u = u with clock := u.clock + 1’ by metis_tac[quiet_tick] >> fs[] >>
  gvs[l0_call_def, AllCaseEqs()] >> pairarg_tac >> gvs[] >>
  ‘l0_rely (u with clock := u.clock + 1)’ by simp[rely_clock] >>
  Cases_on ‘r’
  >- (rename1 ‘Ok v’ >> Cases_on ‘v = 0’
      >- (gvs[] >>
          ‘l0_res_of (enc_res (Ok 0) ++ d ++ DROP (l0_hdr + LENGTH d) bytes) = Ok 0’
            by (REWRITE_TAC[GSYM APPEND_ASSOC] >> irule l0_res_of_enc_app >>
                simp[l0_res_ok_def]) >> gvs[])
      >> ‘0 < v’ by decide_tac >> drule_all recv_ok_lt >> simp[])
  >> drule_all recv_fail_ok >> strip_tac >>
  ‘l0_res_of (enc_res (Fail e l) ++ d ++ DROP (l0_hdr + LENGTH d) bytes) = Fail e l’
    by (REWRITE_TAC[GSYM APPEND_ASSOC] >> irule l0_res_of_enc_app >> simp[]) >>
  gvs[]
QED

Definition recv_data_def:
  recv_data (IO_event nm conf bs) ⇔
    nm = ExtCall «sys_recv» ∧ ∃k. l0_res_of (MAP SND bs) = Ok k ∧ 0 < k
End

(* MAIN: along a faithful trace past the last arrival the inbox total does
   not grow, and falls after a recv that returned data *)
Theorem tot_quiet_trace:
  ∀evs u u'. faithful u evs ∧ FOLDL l0_step (SOME u) (MAP ev_lcall evs) = SOME u' ∧
             quiet_after N u ∧ N ≤ u.clock ∧ l0_rely u ⇒
             tot_inbox u' ≤ tot_inbox u ∧
             (EXISTS recv_data evs ⇒ tot_inbox u' < tot_inbox u)
Proof
  Induct >- simp[] >>
  rpt gen_tac >> strip_tac >> qpat_x_assum ‘faithful _ _’ mp_tac >>
  simp[faithful_def] >> strip_tac >>
  rename1 ‘l0_ffi_fn n conf (MAP FST bs) u = SOME (FFIreturn (MAP SND bs) v)’ >>
  ‘l0_step (SOME u) (ev_lcall h) = SOME v’ by gvs[ev_lcall_def, l0_step_def] >>
  ‘FOLDL l0_step (SOME v) (MAP ev_lcall evs) = SOME u'’
    by (qpat_x_assum ‘FOLDL _ _ (MAP _ (h::evs)) = _’ mp_tac >> REWRITE_TAC[MAP, FOLDL] >>
        qpat_assum ‘l0_step _ _ = _’ (fn th => REWRITE_TAC[th])) >>
  ‘l0_rely v ∧ u.clock < v.clock ∧ v.env = u.env’
    by metis_tac[l0_ffi_fn_length, l0_ffi_fn_clock, l0_ffi_fn_env] >>
  ‘quiet_after N v ∧ N ≤ v.clock’ by fs[quiet_after_def] >>
  ‘tot_inbox v ≤ tot_inbox u’ by metis_tac[tot_ffi_quiet] >>
  first_x_assum drule_all >> strip_tac >> simp[] >> strip_tac >> gvs[]
  >- (‘tot_inbox v < tot_inbox u’
        by (gvs[recv_data_def] >> irule recv_data_ffi >> metis_tac[]) >>
      decide_tac)
  >> fs[] >> decide_tac
QED
