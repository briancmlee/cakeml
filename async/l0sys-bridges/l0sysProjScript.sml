(*
  B1's world: each process of an l0sys run sees an L0 world.  The world's
  environment, at the process's n-th call, delivers what the kernel
  delivered to it since its previous call.  Arrivals and non-blocking calls
  ignore the environment and the clock, and a blocking poll that may
  return returns at once, so the world answers each call as the run did.
*)
Theory l0sysProj
Ancestors
  honestL0World honestL0Rely l0sys l0sysInvCall l0sysStep l0sysRun l0sysReplay
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* The environment and the clock *)

Overload envck = “λ(w : l0world) E c. w with <| env := E; clock := c |>”

Theorem upd_lchan_envck[simp]:
  upd_lchan j g (envck w E c) = envck (upd_lchan j g w) E c
Proof
  simp[upd_lchan_def]
QED

Theorem l0_deliver_envck:
  l0_deliver (envck w E c) a = envck (l0_deliver w a) E c
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >> fs[]
QED

(* The helpers read neither the environment nor the clock *)
Theorem envck_reads1[simp]:
  l0_used (envck w E c) = l0_used w ∧
  l0_chan_of (envck w E c) f = l0_chan_of w f ∧
  is_listener_fd (envck w E c) f = is_listener_fd w f ∧
  fail (envck w E c) e = fail w e ∧
  chan_revents (envck w E c) j ev = chan_revents w j ev ∧
  enc_err_val (envck w E c) e v = enc_err_val w e v
Proof
  simp[l0_used_def, l0_chan_of_def, is_listener_fd_def, fail_def, chan_revents_def,
       enc_err_val_def]
QED

Theorem envck_reads2[simp]:
  lowest_fd (envck w E c) = lowest_fd w ∧
  l0_alloc (envck w E c) = l0_alloc w ∧
  not_chan (envck w E c) f = not_chan w f ∧
  fd_revents (envck w E c) = fd_revents w ∧
  enc_listen_fail (envck w E c) ke = enc_listen_fail w ke
Proof
  PairCases_on ‘ke’ >>
  simp[lowest_fd_def, l0_alloc_def, not_chan_def, FUN_EQ_THM, FORALL_PROD, fd_revents_def,
       enc_listen_fail_def]
QED

Theorem envck_reads3[simp]:
  any_revents (envck w E c) fes = any_revents w fes ∧
  poll_out (envck w E c) fes = poll_out w fes
Proof
  simp[any_revents_def, poll_out_def]
QED

Theorem FOLDL_upd_envck[simp]:
  ∀q w. FOLDL (λw j. upd_lchan j g w) (envck w E c) q =
        envck (FOLDL (λw j. upd_lchan j g w) w q) E c
Proof
  Induct >> simp[]
QED

Theorem close_fd_envck[simp]:
  close_fd f (envck w E c) = envck (close_fd f w) E c
Proof
  simp[close_fd_def] >> every_case_tac >> TRY (simp[upd_lchan_def] >> NO_TAC) >> simp[] >>
  qmatch_goalsub_abbrev_tac ‘w with <| listeners := L; env := E; clock := c |>’ >>
  ‘w with <| listeners := L; env := E; clock := c |> = envck (w with listeners := L) E c’
    by simp[] >>
  pop_assum SUBST1_TAC >> rewrite_tac[FOLDL_upd_envck]
QED

(* The operations commute with setting the environment and the clock *)
Theorem l0_listen_envck[simp]:
  l0_listen p (envck w E c) = (FST (l0_listen p w), envck (SND (l0_listen p w)) E c)
Proof
  rw[l0_listen_def] >> every_case_tac >> fs[upd_lchan_def]
QED

Theorem l0_accept_envck[simp]:
  l0_accept l (envck w E c) = (FST (l0_accept l w), envck (SND (l0_accept l w)) E c)
Proof
  rw[l0_accept_def] >> every_case_tac >> fs[upd_lchan_def]
QED

Theorem l0_recv_envck[simp]:
  l0_recv f n (envck w E c) = (FST (l0_recv f n w), FST (SND (l0_recv f n w)), envck (SND (SND (l0_recv f n w))) E c)
Proof
  rw[l0_recv_def] >> every_case_tac >> fs[upd_lchan_def]
QED

Theorem l0_send_envck[simp]:
  l0_send f bs (envck w E c) = (FST (l0_send f bs w), envck (SND (l0_send f bs w)) E c)
Proof
  rw[l0_send_def] >> every_case_tac >> fs[upd_lchan_def]
QED

Theorem l0_shutdown_envck[simp]:
  l0_shutdown f (envck w E c) = (FST (l0_shutdown f w), envck (SND (l0_shutdown f w)) E c)
Proof
  rw[l0_shutdown_def] >> every_case_tac >> fs[upd_lchan_def]
QED

Theorem l0_connect_envck[simp]:
  l0_connect p (envck w E c) = (FST (l0_connect p w), FST (SND (l0_connect p w)), envck (SND (SND (l0_connect p w))) E c)
Proof
  rw[l0_connect_def] >> every_case_tac >> fs[upd_lchan_def]
QED

Theorem l0_connerr_envck[simp]:
  l0_connerr f (envck w E c) = (FST (l0_connerr f w), envck (SND (l0_connerr f w)) E c)
Proof
  rw[l0_connerr_def] >> every_case_tac >> fs[upd_lchan_def]
QED

Theorem l0_close_envck[simp]:
  l0_close f (envck w E c) = (FST (l0_close f w), envck (SND (l0_close f w)) E c)
Proof
  rw[l0_close_def] >> every_case_tac >> fs[upd_lchan_def]
QED

Theorem w8_le1:
  w2n (x : word8) ≤ 1 ⇔ x = 0w ∨ x = 1w
Proof
  Cases_on ‘x’ >> simp[] >> eq_tac >> rw[] >> simp[]
QED

(* An unblocked poll that passes the checks is non-blocking *)
Theorem unblock_poll_hd:
  unblock «sys_poll» conf ≠ [] ∧ w2n (HD (unblock «sys_poll» conf)) ≤ 1 ⇒
  HD (unblock «sys_poll» conf) = 0w
Proof
  rw[unblock_def, w8_le1] >> fs[]
QED

Definition ffi_envck_def:
  ffi_envck E c (FFIreturn out w1) = FFIreturn out (envck w1 E c) ∧
  ffi_envck E c FFIdiverge = FFIdiverge
End

Theorem l0_call_envck_eq:
  l0_call nm (unblock nm conf) bytes (envck w E c) =
  OPTION_MAP (ffi_envck E c) (l0_call nm (unblock nm conf) bytes w)
Proof
  Cases_on ‘nm = «sys_poll»’
  >- (gvs[] >> once_rewrite_tac[l0_call_def] >> simp[] >>
      IF_CASES_TAC >> simp[] >>
      ‘HD (unblock «sys_poll» conf) = 0w’ by (irule unblock_poll_hd >> fs[]) >>
      simp[] >> CASE_TAC >> simp[ffi_envck_def]) >>
  simp[unblock_def] >> once_rewrite_tac[l0_call_def] >> simp[] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  rpt (pairarg_tac >> simp[]) >>
  every_case_tac >> fs[ffi_envck_def]
QED

Theorem l0_call_envck:
  l0_call nm (unblock nm conf) bytes w = SOME (FFIreturn out w1) ⇒
  l0_call nm (unblock nm conf) bytes (envck w E c) = SOME (FFIreturn out (envck w1 E c))
Proof
  simp[l0_call_envck_eq, ffi_envck_def]
QED

(* A blocking poll that may return answers at once, as the unblocked one *)
Theorem l0_wait_now:
  any_revents w fes ⇒ l0_wait fes w = SOME 0
Proof
  rw[l0_wait_def] >> TRY (qexists_tac ‘0’ >> simp[l0_ticks_def] >> NO_TAC) >>
  numLib.LEAST_ELIM_TAC >> conj_tac >- (qexists_tac ‘0’ >> simp[l0_ticks_def]) >>
  rw[] >> CCONTR_TAC >> ‘0 < n’ by simp[] >> res_tac >> fs[l0_ticks_def]
QED

Theorem l0_call_may_return:
  poll_may_return nm conf w ∧ l0_call nm (unblock nm conf) bytes w = SOME r ⇒
  l0_call nm conf bytes w = SOME r
Proof
  Cases_on ‘nm = «sys_poll» ∧ conf ≠ [] ∧ HD conf = 1w’
  >- (fs[unblock_def] >> Cases_on ‘conf’ >> fs[] >> rveq >>
      once_rewrite_tac[l0_call_def] >> simp[] >>
      strip_tac >> fs[] >> Cases_on ‘w.ch.transient w.hist’ >> fs[poll_may_return_def] >>
      imp_res_tac l0_wait_now >> fs[l0_ticks_def]) >>
  ‘unblock nm conf = conf’ by (fs[unblock_def] >> rw[] >> fs[]) >> simp[]
QED

(*---------------------------------------------------------------------------*)
(* One call: the world's tick delivers what the kernel delivered since the
   process's previous call, then the call answers as in the run *)

Theorem FOLDL_deliver_envck:
  ∀as w. FOLDL l0_deliver (envck w E c) as = envck (FOLDL l0_deliver w as) E c
Proof
  Induct >> simp[l0_deliver_envck]
QED

Theorem deliver_hist[simp]:
  (l0_deliver w a).hist = w.hist ∧ (l0_deliver w a).clock = w.clock ∧
  (l0_deliver w a).env = w.env
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def, upd_lchan_def] >> every_case_tac >> simp[]
QED

Theorem FOLDL_deliver_hist[simp]:
  ∀as w. (FOLDL l0_deliver w as).hist = w.hist ∧ (FOLDL l0_deliver w as).clock = w.clock ∧
         (FOLDL l0_deliver w as).env = w.env
Proof
  Induct >> simp[]
QED

Theorem poll_may_return_envck[simp]:
  poll_may_return nm conf (envck w E c) ⇔ poll_may_return nm conf w
Proof
  simp[poll_may_return_def]
QED

Theorem l0_oracle_call:
  l0_call nm (unblock nm conf) bytes wk = SOME (FFIreturn out w1) ∧
  poll_may_return nm conf wk ∧
  V.env = (λn h nm. A n) ∧ V.clock = wk.clock ∧
  wk with env := V.env = FOLDL l0_deliver V (A wk.clock) ⇒
  l0_oracle (ExtCall nm) V conf bytes =
  Oracle_return ((w1 with <| clock := wk.clock + 1; hist := wk.hist ++ [(nm, conf, bytes)] |>)
                   with env := V.env) out
Proof
  strip_tac >>
  ‘V.hist = wk.hist’
    by (‘(wk with env := V.env).hist = (FOLDL l0_deliver V (A wk.clock)).hist’ by metis_tac[] >>
        fs[]) >>
  ‘l0_tick nm V = envck wk V.env (wk.clock + 1)’
    by (‘V with clock := V.clock + 1 = envck V V.env (wk.clock + 1)’
          by simp[l0world_component_equality] >>
        ‘FOLDL l0_deliver V (A wk.clock) = wk with env := V.env’ by simp[] >>
        rewrite_tac[l0_tick_def] >> pop_assum mp_tac >> pop_assum mp_tac >>
        qpat_x_assum ‘V.env = _’ (fn th => rewrite_tac[th] >> assume_tac th) >>
        rpt strip_tac >> simp[FOLDL_deliver_envck]) >>
  ‘l0_call nm conf bytes (envck wk V.env (wk.clock + 1)) =
   SOME (FFIreturn out (envck w1 V.env (wk.clock + 1)))’
    by (irule l0_call_may_return >> simp[] >> irule l0_call_envck >> simp[]) >>
  simp[l0_oracle_def, l0_ffi_fn_def] >> rfs[] >> simp[l0world_component_equality]
QED

(*---------------------------------------------------------------------------*)
(* The world's answers, with the state they lead to *)

Definition agrees_to_def:
  (agrees_to orc st [] st' ⇔ st' = st) ∧
  (agrees_to orc st (IO_event n conf bl :: rest) st' ⇔
     ∃s1. orc n st conf (MAP FST bl) = Oracle_return s1 (MAP SND bl) ∧
          agrees_to orc s1 rest st')
End

Theorem agrees_to_SNOC:
  ∀evs st st'.
    agrees_to orc st (evs ++ [IO_event n conf bl]) st' ⇔
    ∃s1. agrees_to orc st evs s1 ∧ orc n s1 conf (MAP FST bl) = Oracle_return st' (MAP SND bl)
Proof
  Induct >> simp[agrees_to_def] >> Cases >> simp[agrees_to_def] >> metis_tac[]
QED

Theorem agrees_to_agrees:
  ∀evs st st'. agrees_to orc st evs st' ⇒ agrees orc st evs
Proof
  Induct >> simp[agrees_to_def, agrees_def] >> Cases >> simp[agrees_to_def, agrees_def] >>
  metis_tac[]
QED
