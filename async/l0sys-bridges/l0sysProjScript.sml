(*
  B1's world: each process of an l0sys run sees an L0 world.  The world's
  environment, at the process's n-th call, delivers what the kernel
  delivered to it since its previous call.  Arrivals and non-blocking calls
  ignore the environment and the clock, and a blocking poll that may
  return returns at once, so the world answers each call as the run did.
*)
Theory l0sysProj
Ancestors
  honestL0World honestL0WorldProps honestL0Rely l0sys l0sysInvCall l0sysStep l0sysRun l0sysReplay
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

(*---------------------------------------------------------------------------*)
(* One step of the run, seen by process k: its call (then arrivals), its
   exit, or arrivals only *)

Definition kstep_def:
  kstep k s r s' as ⇔
    (s'.alive k ⇒ s.alive k) ∧
    case r of
    | Call k0 nm conf bytes out =>
        if k0 = k then
          ∃w1. s.alive k ∧ poll_may_return nm conf (EL k s.procs) ∧
               l0_call nm (unblock nm conf) bytes (EL k s.procs) = SOME (FFIreturn out w1) ∧
               EL k s'.procs =
                 FOLDL l0_deliver
                   (w1 with <| clock := (EL k s.procs).clock + 1;
                               hist := (EL k s.procs).hist ++ [(nm, conf, bytes)] |>) as
        else EL k s'.procs = FOLDL l0_deliver (EL k s.procs) as
    | Exit k0 =>
        if k0 = k then ¬s'.alive k ∧ as = [] ∧ (EL k s'.procs).clock = (EL k s.procs).clock
        else EL k s'.procs = FOLDL l0_deliver (EL k s.procs) as
    | _ => EL k s'.procs = FOLDL l0_deliver (EL k s.procs) as
End

Theorem EL_sys_deliver:
  EL k (sys_deliver k' a s).procs =
  if k = k' ∧ k < LENGTH s.procs then l0_deliver (EL k s.procs) a else EL k s.procs
Proof
  rw[sys_deliver_def, EL_LUPDATE] >> fs[]
QED

Theorem sys_pair_fields[simp]:
  (sys_pair e k' p s).procs = (sys_deliver k' (LIncoming p) s).procs ∧
  (sys_pair e k' p s).alive = s.alive
Proof
  simp[sys_pair_def, sys_deliver_def]
QED

Theorem upd_lchan_clock[simp]:
  (upd_lchan j g w).clock = w.clock
Proof
  simp[upd_lchan_def]
QED

Theorem close_fd_clock[simp]:
  (close_fd f w).clock = w.clock
Proof
  ‘∀g q w. (FOLDL (λw j. upd_lchan j g w) w q).clock = w.clock’
    by (gen_tac >> Induct >> fs[]) >>
  rw[close_fd_def] >> every_case_tac >> fs[]
QED

Theorem close_all_clock[simp]:
  (close_all w).clock = w.clock
Proof
  simp[close_all_def] >>
  ‘∀fs w. (FOLDL (λw f. close_fd f w) w fs).clock = w.clock’ by (Induct >> fs[]) >>
  simp[]
QED

Theorem sys_deliver_alive[simp]:
  (sys_deliver k a s).alive = s.alive
Proof
  simp[sys_deliver_def]
QED

Theorem ex_FOLDL_deliver[simp]:
  (∃as. w = FOLDL l0_deliver w as) ∧
  (∃as. l0_deliver w a = FOLDL l0_deliver w as) ∧
  (∃as. l0_deliver (l0_deliver w a) b = FOLDL l0_deliver w as)
Proof
  rpt conj_tac
  >- (qexists_tac ‘[]’ >> simp[])
  >- (qexists_tac ‘[a]’ >> simp[]) >>
  qexists_tac ‘[a; b]’ >> simp[]
QED

Theorem kstep_exists:
  sys_step s r s' ∧ k < LENGTH s.procs ⇒ ∃as. kstep k s r s' as
Proof
  strip_tac >> simp[kstep_def] >> Cases_on ‘r’ >> fs[sys_step_def]
  >- ((* Call *)
      qpat_x_assum ‘if _ then _ else _’ mp_tac >> rw[] >>
      fs[sys_room_def] >> simp[EL_LUPDATE, EL_sys_deliver] >>
      Cases_on ‘n = k’ >> fs[] >> rveq >> rpt (IF_CASES_TAC >> fs[]) >> rveq >>
      FIRST [qexists_tac ‘[]’ >> simp[] >> NO_TAC,
             qexists_tac ‘[]’ >> simp[] >> qexists_tac ‘w1’ >> simp[] >> NO_TAC,
             qexists_tac ‘[LIncoming (w22n l)]’ >> simp[] >> NO_TAC,
             qexists_tac ‘[LIncoming (w22n l)]’ >> simp[] >> qexists_tac ‘w1’ >> simp[] >>
             NO_TAC])
  >- ((* Kern *)
      rename1 ‘Kern ks’ >> Cases_on ‘ks’ >> fs[sys_step_def] >>
      simp[EL_sys_deliver] >> rpt (IF_CASES_TAC >> fs[]))
  >- ((* Env *)
      rename1 ‘Env es’ >> Cases_on ‘es’ >> fs[sys_step_def] >>
      simp[EL_sys_deliver] >> rpt (IF_CASES_TAC >> fs[])) >>
  (* Exit *)
  rw[APPLY_UPDATE_THM, EL_LUPDATE] >> qexists_tac ‘[]’ >> rw[]
QED

(*---------------------------------------------------------------------------*)
(* Process k's clock along a run counts its calls *)

Definition is_kcall_def:
  is_kcall k r ⇔ ∃nm conf bytes out. r = Call k nm conf bytes out
End

Theorem kstep_clock:
  kstep k s r s' as ⇒
  (EL k s'.procs).clock = (EL k s.procs).clock + if is_kcall k r then 1 else 0
Proof
  Cases_on ‘r’ >> rw[kstep_def, is_kcall_def] >> fs[]
QED

Definition kclk_def:
  kclk k ss t = (EL k (EL t ss).procs).clock
End

Theorem kclk_mono:
  (∀t. t < L ⇒ kstep k (EL t ss) (EL t rs) (EL (t + 1) ss) (AS t)) ⇒
  ∀u v. u ≤ v ∧ v ≤ L ⇒ kclk k ss u ≤ kclk k ss v
Proof
  strip_tac >> ‘∀d u. u + d ≤ L ⇒ kclk k ss u ≤ kclk k ss (u + d)’ suffices_by
    (rpt strip_tac >> first_x_assum (qspecl_then [‘v - u’, ‘u’] mp_tac) >> simp[]) >>
  Induct >- simp[] >> rpt strip_tac >>
  ‘u + d < L ∧ u + d ≤ L’ by fs[] >>
  ‘kstep k (EL (u + d) ss) (EL (u + d) rs) (EL (u + d + 1) ss) (AS (u + d))’ by fs[] >>
  drule kstep_clock >> ‘kclk k ss u ≤ kclk k ss (u + d)’ by fs[] >>
  ‘u + SUC d = u + d + 1’ by simp[] >> pop_assum SUBST1_TAC >> fs[kclk_def] >> rw[] >> fs[]
QED

(* The environment: at clock n, the arrivals of the steps after which k's
   clock is n; and the arrivals since k's last call, at t *)
Definition kenv_def:
  kenv k ss AS L n = FLAT (MAP AS (FILTER (λu. kclk k ss (u + 1) = n) (COUNT_LIST L)))
End

Definition kseg_def:
  kseg k ss AS t =
    FLAT (MAP AS (FILTER (λu. kclk k ss (u + 1) = kclk k ss t) (COUNT_LIST t)))
End

Theorem kclk_call:
  (∀t. t < L ⇒ kstep k (EL t ss) (EL t rs) (EL (t + 1) ss) (AS t)) ∧ t < L ⇒
  kclk k ss (t + 1) = kclk k ss t + if is_kcall k (EL t rs) then 1 else 0
Proof
  rw[kclk_def] >> res_tac >> imp_res_tac kstep_clock >> fs[]
QED

Theorem kenv_call:
  (∀t. t < L ⇒ kstep k (EL t ss) (EL t rs) (EL (t + 1) ss) (AS t)) ∧ t < L ∧
  is_kcall k (EL t rs) ⇒
  kenv k ss AS L (kclk k ss t) = kseg k ss AS t
Proof
  strip_tac >> drule kclk_mono >> strip_tac >>
  ‘kclk k ss (t + 1) = kclk k ss t + 1’ by (drule_all kclk_call >> simp[]) >>
  ‘COUNT_LIST L = COUNT_LIST t ++ MAP (λi. i + t) (COUNT_LIST (L - t))’
    by (‘L = t + (L - t)’ by simp[] >> pop_assum (fn th => CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [th]))) >>
        simp[COUNT_LIST_ADD]) >>
  simp[kenv_def, kseg_def, FILTER_APPEND] >>
  ‘FILTER (λu. kclk k ss (u + 1) = kclk k ss t) (MAP (λi. i + t) (COUNT_LIST (L - t))) = []’
    suffices_by simp[] >>
  simp[FILTER_EQ_NIL, EVERY_MAP, EVERY_MEM, MEM_COUNT_LIST] >> rpt strip_tac >>
  ‘kclk k ss (t + 1) ≤ kclk k ss (i + t + 1)’ by (first_x_assum irule >> simp[]) >>
  fs[]
QED

Theorem kseg_call:
  (∀t. t < L ⇒ kstep k (EL t ss) (EL t rs) (EL (t + 1) ss) (AS t)) ∧ t < L ∧
  is_kcall k (EL t rs) ⇒
  kseg k ss AS (t + 1) = AS t
Proof
  strip_tac >> drule kclk_mono >> strip_tac >>
  ‘kclk k ss (t + 1) = kclk k ss t + 1’ by (drule_all kclk_call >> simp[]) >>
  simp[kseg_def, GSYM ADD1, COUNT_LIST_SNOC, FILTER_APPEND, SNOC_APPEND] >> simp[ADD1] >>
  ‘FILTER (λu. kclk k ss (u + 1) = kclk k ss t + 1) (COUNT_LIST t) = []’ suffices_by simp[] >>
  simp[FILTER_EQ_NIL, EVERY_MEM, MEM_COUNT_LIST] >> rpt strip_tac >>
  rename1 ‘u < t’ >> ‘kclk k ss (u + 1) ≤ kclk k ss t’ by (first_x_assum irule >> simp[]) >> fs[]
QED

Theorem kseg_other:
  (∀t. t < L ⇒ kstep k (EL t ss) (EL t rs) (EL (t + 1) ss) (AS t)) ∧ t < L ∧
  ¬is_kcall k (EL t rs) ⇒
  kseg k ss AS (t + 1) = kseg k ss AS t ++ AS t
Proof
  strip_tac >>
  ‘kclk k ss (t + 1) = kclk k ss t’ by (drule_all kclk_call >> simp[]) >>
  simp[kseg_def, GSYM ADD1, COUNT_LIST_SNOC, FILTER_APPEND, SNOC_APPEND] >> simp[ADD1]
QED

Theorem l0_deliver_env:
  l0_deliver (w with env := E) a = (l0_deliver w a) with env := E
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def, upd_lchan_def] >> every_case_tac >> fs[]
QED

Theorem FOLDL_deliver_env:
  ∀as w. FOLDL l0_deliver (w with env := E) as = (FOLDL l0_deliver w as) with env := E
Proof
  Induct >> simp[l0_deliver_env]
QED

(*---------------------------------------------------------------------------*)
(* The run, seen by k, against the world: its calls are the world's answers,
   and while k is alive its world is the world's after the arrivals since
   its last call *)

Theorem ksim:
  (∀t. t < LENGTH rs ⇒
       kstep k (EL t ss) (EL t rs) (EL (t + 1) ss) (AS t) ∧ l0_rely (EL k (EL t ss).procs)) ∧
  E = (λn h nm. kenv k ss AS (LENGTH rs) n) ∧ (EL 0 ss).alive k ⇒
  ∀t. t ≤ LENGTH rs ⇒
    ∃V. agrees_to l0_oracle ((EL k (EL 0 ss).procs) with env := E)
                  (proc_events k (TAKE t rs)) V ∧
        ((EL t ss).alive k ⇒
         V.env = E ∧ V.clock = kclk k ss t ∧
         (EL k (EL t ss).procs) with env := E = FOLDL l0_deliver V (kseg k ss AS t))
Proof
  strip_tac >>
  ‘∀t. t < LENGTH rs ⇒ kstep k (EL t ss) (EL t rs) (EL (t + 1) ss) (AS t)’ by metis_tac[] >>
  Induct
  >- (rw[proc_events_def, agrees_to_def, kseg_def, kclk_def, COUNT_LIST_def]) >>
  strip_tac >> ‘t < LENGTH rs’ by simp[] >> fs[] >>
  ‘kstep k (EL t ss) (EL t rs) (EL (t + 1) ss) (AS t) ∧ l0_rely (EL k (EL t ss).procs)’
    by metis_tac[] >>
  simp[ADD1, TAKE_SUC_SNOC, proc_events_SNOC] >>
  Cases_on ‘is_kcall k (EL t rs)’
  >- (‘∃nm conf bytes out. EL t rs = Call k nm conf bytes out’ by fs[is_kcall_def] >>
      fs[] >>
      qpat_x_assum ‘kstep _ _ (Call _ _ _ _ _) _ _’ mp_tac >> rewrite_tac[kstep_def] >>
      simp[] >> strip_tac >> fs[] >>
      qabbrev_tac ‘wk = EL k (EL t ss).procs’ >>
      ‘kenv k ss AS (LENGTH rs) (kclk k ss t) = kseg k ss AS t’
        by (irule kenv_call >> simp[] >> fs[is_kcall_def] >> metis_tac[]) >>
      ‘l0_oracle (ExtCall nm) V conf bytes =
       Oracle_return ((w1 with <| clock := wk.clock + 1; hist := wk.hist ++ [(nm, conf, bytes)] |>)
                        with env := V.env) out’
        by (irule l0_oracle_call >> simp[] >>
            ‘kclk k ss t = wk.clock’ by simp[kclk_def, Abbr ‘wk’] >>
            rfs[] >> qexists_tac ‘λn. kenv k ss AS (LENGTH rs) n’ >> rfs[] >> fs[]) >>
      ‘LENGTH out = LENGTH bytes’ by metis_tac[l0_call_length] >>
      qexists_tac ‘(w1 with <| clock := wk.clock + 1; hist := wk.hist ++ [(nm, conf, bytes)] |>)
                     with env := V.env’ >>
      conj_tac
      >- (simp[agrees_to_SNOC] >> qexists_tac ‘V’ >> rfs[MAP_ZIP]) >>
      strip_tac >>
      ‘kseg k ss AS (t + 1) = AS t’ by (irule kseg_call >> simp[is_kcall_def] >> metis_tac[]) >>
      rfs[kclk_def, FOLDL_deliver_env]) >>
  ‘(case EL t rs of
      Call k' nm conf bytes out =>
        if k' = k then [IO_event (ExtCall nm) conf (ZIP (bytes, out))] else []
    | Kern v13 => [] | Env v14 => [] | Exit v15 => []) = []’
    by (Cases_on ‘EL t rs’ >> fs[is_kcall_def]) >>
  pop_assum SUBST1_TAC >> qexists_tac ‘V’ >> rfs[] >> strip_tac >>
  ‘(EL t ss).alive k’ by fs[kstep_def] >> fs[] >>
  ‘kclk k ss (t + 1) = kclk k ss t’ by (drule_all kclk_call >> simp[]) >>
  ‘kseg k ss AS (t + 1) = kseg k ss AS t ++ AS t’ by (irule kseg_other >> simp[] >> metis_tac[]) >>
  simp[FOLDL_APPEND] >>
  qpat_x_assum ‘_ with env := _ = FOLDL _ _ _’ (SUBST1_TAC o SYM) >>
  simp[FOLDL_deliver_env] >>
  ‘kstep k (EL t ss) (EL t rs) (EL (t + 1) ss) (AS t)’ by simp[] >>
  Cases_on ‘EL t rs’ >> fs[is_kcall_def] >>
  qpat_x_assum ‘kstep _ _ _ _ _’ (strip_assume_tac o SIMP_RULE (srw_ss()) [kstep_def]) >>
  rfs[] >> Cases_on ‘n = k’ >> fs[]
QED

(* B1a: the world.  Process k's calls in a run are answered as recorded by
   its initial world, with the environment the run's arrivals give *)
Theorem l0sys_world:
  sys_init ps s0 ∧ sys_steps s0 rs ss ∧ k < LENGTH ps ⇒
  ∃E. agrees l0_oracle ((EL k s0.procs) with env := E) (proc_events k rs)
Proof
  strip_tac >> drule sys_steps_EL >> strip_tac >>
  ‘sinv [] s0 (K [])’
    by (irule sinv_init >> qexists_tac ‘ps’ >> rw[] >> irule l0_rely_small_ch >>
        fs[sys_init_def, LET_THM]) >>
  ‘∀t. t ≤ LENGTH rs ⇒ sinv (TAKE t rs) (EL t ss) (ghost ss rs (K []) t)’
    by (match_mp_tac sinv_run >> simp[]) >>
  ‘∀d. 0 + d ≤ LENGTH rs ⇒
       hist_inv (EL 0 ss) (ghost ss rs (K []) 0) (EL (0 + d) ss) (ghost ss rs (K []) (0 + d))’
    by (match_mp_tac hist_run >> simp[]) >>
  ‘EL 0 ss = s0’ by (Cases_on ‘ss’ >> fs[]) >>
  ‘∀t. t ≤ LENGTH rs ⇒ k < LENGTH (EL t ss).procs’
    by (rpt strip_tac >> first_x_assum (qspec_then ‘t’ mp_tac) >> simp[hist_inv_def] >>
        fs[sys_init_def]) >>
  ‘∀t. t < LENGTH rs ⇒ l0_rely (EL k (EL t ss).procs)’
    by (rpt strip_tac >>
        ‘sinv (TAKE t rs) (EL t ss) (ghost ss rs (K []) t) ∧ k < LENGTH (EL t ss).procs’
          by simp[] >>
        fs[sinv_def, pk_def]) >>
  qabbrev_tac ‘AS = λt. @as. kstep k (EL t ss) (EL t rs) (EL (t + 1) ss) as’ >>
  ‘∀t. t < LENGTH rs ⇒ kstep k (EL t ss) (EL t rs) (EL (t + 1) ss) (AS t)’
    by (rpt strip_tac >> simp[Abbr ‘AS’] >> SELECT_ELIM_TAC >> simp[] >>
        irule kstep_exists >> simp[]) >>
  qexists_tac ‘λn h nm. kenv k ss AS (LENGTH rs) n’ >>
  qspecl_then [‘rs’, ‘k’, ‘ss’, ‘AS’, ‘λn h nm. kenv k ss AS (LENGTH rs) n’] mp_tac
    (Q.GENL [‘rs’, ‘k’, ‘ss’, ‘AS’, ‘E’] ksim) >>
  impl_tac >- (simp[] >> fs[sys_init_def]) >>
  disch_then (qspec_then ‘LENGTH rs’ mp_tac) >> simp[] >> strip_tac >>
  irule agrees_to_agrees >> metis_tac[]
QED
