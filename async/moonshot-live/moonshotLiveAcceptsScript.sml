(*
  Moonshot liveness: the lift fact accepts_lt for the proxy (README §6).

  A process k whose accepts are all on a listener of port p ∈ ports, in an
  isolated run, accepts at most as many connections as the client cl has
  connect episodes to p, if no other process connects to p and cl never
  closes fd 0 (irun_accepts_le):
   - each accepted channel, and each queued one on a port of ports, has a
     peer (acc_inv; no stranger queues one: isolated);
   - the peer's target is p (pk), and an end with target p is a Connected p
     episode of its process (tinv), unless that process closed fd 0 (then a
     connect can get fd 0 and report "no socket": zinv);
   - peers are injective (kinv), so accepted episodes inject into cl's
     Connected p episodes;
   - an end broken right after its connect is never paired (irun_bb), so
     only those not broken then count (conns_ok, close-v2's D43 fact 1).
  accepts_lt_lift: then every prefix of k's trace has fewer than M accepts
  when cl's counted connect episodes are ≤ N < M (proxyL0Stmts' accepts_lt M io).
*)
Theory moonshotLiveAccepts
Ancestors
  moonshotLiveWorldDrains moonshotLiveCompose moonshotLiveDrains moonshotLiveDeliver moonshotLiveProjInf moonshotLiveObs
  moonshotLiveStmts l0sysFair l0sys l0sysRun l0sysStep l0sysInv l0sysInvCall l0sysMono
  l0sysCausal l0sysEpisodes honestEchoL0SpecCopy honestL0World honestL0Rely
  honestL0
Libs
  preamble

(* ------------------------------------------------------------------------
   Events
   ------------------------------------------------------------------------ *)

(* The process called close on fd 0 *)
Definition close0_def:
  close0 evs ⇔ ∃conf bl. MEM (IO_event (ExtCall «sys_close») conf bl) evs ∧ bytes_fd conf = 0w
End

(* The process called connect to port p *)
Definition conn_to_def:
  conn_to p evs ⇔ ∃conf bl. MEM (IO_event (ExtCall «sys_connect») conf bl) evs ∧ w22n conf = p
End

(* Its connect episodes to p: the connects that returned a socket *)
Definition conns_def:
  conns p evs = LENGTH (FILTER ($= (Connected p)) (ep_roles [] evs))
End

Definition is_acc_def:
  is_acc (Accepted q) = T ∧ is_acc (Connected q) = F
End

Theorem close0_append:
  close0 evs ⇒ close0 (evs ++ l)
Proof
  rw[close0_def] >> metis_tac[]
QED

Theorem conn_to_append:
  conn_to p evs ⇒ conn_to p (evs ++ l)
Proof
  rw[conn_to_def] >> metis_tac[]
QED

Theorem ev_new_INL_ev:
  ev_new ev = SOME (f, INL p) ⇒
  ∃conf bl. ev = IO_event (ExtCall «sys_connect») conf bl ∧ w22n conf = p
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bl’ >> Cases_on ‘nm’ >>
  rw[ev_new_def] >> every_case_tac >> gvs[]
QED

Theorem ep_roles_cons:
  ep_roles lst (ev :: evs) =
  ev_role lst ev ++
  ep_roles (case ev_listen ev of SOME (l, p) => (l, p) :: lst | NONE => lst) evs
Proof
  simp[ep_roles_def, ev_role_def]
QED

Theorem roles_conn_to:
  ∀evs lst. MEM (Connected p) (ep_roles lst evs) ⇒ conn_to p evs
Proof
  Induct >> simp[ep_roles_def] >> rpt gen_tac >>
  Cases_on ‘ev_new h’ >> simp[] >- (rw[] >> res_tac >> fs[conn_to_def] >> metis_tac[]) >>
  rename1 ‘ev_new h = SOME x’ >> PairCases_on ‘x’ >> Cases_on ‘x1’ >> simp[]
  >- (strip_tac >- (drule ev_new_INL_ev >> rw[conn_to_def] >> metis_tac[]) >>
      res_tac >> fs[conn_to_def] >> metis_tac[]) >>
  rw[] >> res_tac >> fs[conn_to_def] >> metis_tac[]
QED

Theorem acc_event:
  LENGTH (case l0_event_accepted ev of SOME f => [f] | NONE => []) =
  LENGTH (FILTER is_acc (ev_role lst ev))
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bl’ >> Cases_on ‘nm’ >>
  simp[l0_event_accepted_def, ev_role_def, ev_new_def, l0_ev_res_def] >>
  rw[] >> every_case_tac >> gvs[is_acc_def]
QED

Theorem l0_accepted_roles:
  ∀evs lst. LENGTH (l0_accepted evs) = LENGTH (FILTER is_acc (ep_roles lst evs))
Proof
  Induct >- simp[l0_accepted_def, ep_roles_def] >>
  rpt gen_tac >> simp[ep_roles_cons, FILTER_APPEND] >>
  pop_assum (fn th => simp[GSYM th]) >>
  simp[l0_accepted_def, acc_event]
QED

Theorem l0_accepted_append:
  l0_accepted (a ++ b) = l0_accepted a ++ l0_accepted b
Proof
  simp[l0_accepted_def]
QED

(* ------------------------------------------------------------------------
   fd 0 stays reserved until the process closes it
   ------------------------------------------------------------------------ *)

Theorem res_breaks:
  ∀q w. (FOLDL (λw j. upd_lchan j (break_lchan e b) w) w q).reserved = w.reserved
Proof
  Induct >> asm_simp_tac std_ss [FOLDL] >> simp[upd_lchan_def]
QED

Theorem res_close_fd:
  MEM x w.reserved ∧ x ≠ f ⇒ MEM x (close_fd f w).reserved
Proof
  rw[close_fd_def] >> every_case_tac >> simp[upd_lchan_def, res_breaks, MEM_FILTER]
QED

Theorem res_call:
  l0_call nm (unblock nm conf) bts w = SOME (FFIreturn out w1) ∧ MEM x w.reserved ∧
  ¬(nm = «sys_close» ∧ bytes_fd conf = x) ⇒ MEM x w1.reserved
Proof
  strip_tac >>
  Cases_on ‘nm = «sys_poll»’ >- (gvs[] >> drule l0_call_poll_unblock >> simp[]) >>
  gvs[unblock_other, l0_call_def, AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  FIRST [
    gvs[l0_listen_def, AllCaseEqs()] >> NO_TAC,
    drule l0_accept_cases >> strip_tac >> gvs[upd_lchan_def] >> NO_TAC,
    drule l0_recv_cases >> strip_tac >> gvs[upd_lchan_def] >> NO_TAC,
    drule l0_send_cases >> strip_tac >> gvs[upd_lchan_def] >> NO_TAC,
    gvs[l0_shutdown_def, AllCaseEqs(), upd_lchan_def] >> NO_TAC,
    drule l0_connect_cases >> simp[LET_THM] >> strip_tac >> gvs[upd_lchan_def] >> NO_TAC,
    gvs[l0_connerr_def, AllCaseEqs(), upd_lchan_def] >> NO_TAC,
    gvs[l0_close_def, AllCaseEqs()] >> rw[res_close_fd]]
QED

Theorem res_deliver[simp]:
  (l0_deliver w a).reserved = w.reserved
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >> simp[upd_lchan_def]
QED

Theorem pair_procs[simp]:
  (sys_pair e k' p s).procs = (sys_deliver k' (LIncoming p) s).procs
Proof
  simp[sys_pair_def]
QED

Theorem EL_deliver_res[simp]:
  k0 < LENGTH s.procs ⇒ (EL k0 (sys_deliver k a s).procs).reserved = (EL k0 s.procs).reserved
Proof
  rw[sys_deliver_def, EL_LUPDATE] >> rw[]
QED

Theorem call_res:
  sys_step s (Call k nm conf bts out) s' ∧ k0 < LENGTH s.procs ⇒
  ∃w1. l0_call nm (unblock nm conf) bts (EL k s.procs) = SOME (FFIreturn out w1) ∧
       (EL k0 s'.procs).reserved = if k0 = k then w1.reserved else (EL k0 s.procs).reserved
Proof
  simp[sys_step_def, LET_THM] >> strip_tac >> qexists_tac ‘w1’ >> simp[] >>
  qpat_x_assum ‘if _ then _ else _’ mp_tac >> rw[] >> gvs[EL_LUPDATE] >> rw[]
QED

Theorem res_step:
  sys_step s r s' ∧ k0 < LENGTH s.procs ∧ s'.alive k0 ∧ MEM x (EL k0 s.procs).reserved ⇒
  MEM x (EL k0 s'.procs).reserved ∨
  ∃conf bts out. r = Call k0 «sys_close» conf bts out ∧ bytes_fd conf = x
Proof
  Cases_on ‘r’
  >- (rename1 ‘Call k nm conf bts out’ >> strip_tac >> drule_all call_res >> strip_tac >>
      Cases_on ‘k0 = k’ >> fs[] >>
      Cases_on ‘nm = «sys_close» ∧ bytes_fd conf = x’ >- fs[] >>
      disj1_tac >> irule res_call >> metis_tac[])
  >- (rename1 ‘Kern ks’ >> Cases_on ‘ks’ >> simp[sys_step_def] >> strip_tac >>
      rveq >> asm_simp_tac (srw_ss()) [EL_deliver_res])
  >- (rename1 ‘Env es’ >> Cases_on ‘es’ >> simp[sys_step_def] >> strip_tac >>
      rveq >> asm_simp_tac (srw_ss()) [EL_deliver_res]) >>
  simp[sys_step_def] >> strip_tac >> gvs[EL_LUPDATE, APPLY_UPDATE_THM] >> rw[] >> gvs[]
QED

(* honestL0WorldInv's lowest_fd_free_lim (that theory is not built here) *)
Theorem lowest_fd_free:
  (∀x. MEM x (l0_used w) ⇒ w2n x < w.fd_limit) ∧ w.fd_limit ≤ 2 ** 31 ⇒
  ¬MEM (lowest_fd w) (l0_used w)
Proof
  rw[lowest_fd_def] >> numLib.LEAST_ELIM_TAC >> conj_tac
  >- (qexists_tac ‘2 ** 31’ >> strip_tac >> first_x_assum drule >> simp[]) >>
  rw[]
QED

Definition zinv_def:
  zinv rs (s : sysstate) ⇔
    ∀k. k < LENGTH s.procs ∧ s.alive k ⇒
        MEM 0w (EL k s.procs).reserved ∨ close0 (proc_events k rs)
End

Theorem alive_step:
  sys_step s r s' ∧ s'.alive k ⇒ s.alive k
Proof
  Cases_on ‘r’
  >- (simp[sys_step_def, LET_THM] >> strip_tac >> every_case_tac >> gvs[] >> rw[] >> gvs[])
  >- (rename1 ‘Kern ks’ >> Cases_on ‘ks’ >> simp[sys_step_def] >> strip_tac >> gvs[] >>
      simp[sys_pair_def])
  >- (rename1 ‘Env es’ >> Cases_on ‘es’ >> simp[sys_step_def] >> strip_tac >> gvs[]) >>
  simp[sys_step_def] >> strip_tac >> gvs[APPLY_UPDATE_THM] >> Cases_on ‘k = n’ >> gvs[]
QED

Theorem zinv_step:
  zinv rs s ∧ sys_ext s s' ∧ sys_step s r s' ⇒ zinv (rs ++ [r]) s'
Proof
  rewrite_tac[zinv_def] >> rpt strip_tac >>
  ‘LENGTH s'.procs = LENGTH s.procs’ by fs[sys_ext_def] >>
  ‘k < LENGTH s.procs’ by fs[] >>
  ‘s.alive k’ by metis_tac[alive_step] >>
  ‘∃l. proc_events k (rs ++ [r]) = proc_events k rs ++ l’ by simp[proc_events_SNOC] >>
  pop_assum strip_assume_tac >>
  Cases_on ‘close0 (proc_events k rs)’
  >- (disj2_tac >> pop_assum mp_tac >> pop_assum (fn th => rewrite_tac[th]) >>
      rewrite_tac[close0_append]) >>
  ‘MEM 0w (EL k s.procs).reserved’ by metis_tac[] >>
  drule_all res_step >> strip_tac >- simp[] >>
  disj2_tac >> qpat_x_assum ‘proc_events _ _ = _’ kall_tac >> rveq >>
  simp[proc_events_SNOC, close0_def] >> qexistsl_tac [‘conf’, ‘ZIP (bts, out)’] >> simp[]
QED

(* ------------------------------------------------------------------------
   An end with target p is a Connected p episode (or fd 0 was closed)
   ------------------------------------------------------------------------ *)

Theorem connect_alloc:
  l0_call «sys_connect» conf bts w = SOME (FFIreturn out w1) ∧
  LENGTH w1.chans = LENGTH w.chans + 1 ⇒
  ∃f. l0_alloc w = SOME f ∧ l0_chan_of w1 f = SOME (LENGTH w.chans)
Proof
  simp[l0_call_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule l0_connect_cases >> simp[LET_THM] >>
  strip_tac >> gvs[] >> simp[l0_chan_of_def, upd_lchan_def]
QED

Theorem alloc_ne0:
  l0_alloc w = SOME f ∧ MEM 0w w.reserved ∧ fds_lt w ∧ w.fd_limit ≤ 2 ** 31 ⇒ f ≠ 0w
Proof
  rw[l0_alloc_def] >> strip_tac >>
  ‘¬MEM (lowest_fd w) (l0_used w)’ by (irule lowest_fd_free >> fs[fds_lt_def]) >>
  gvs[l0_used_def]
QED

Theorem connect_role:
  l0_rely w ∧ small_ch w.ch ∧ pinv evs w cs ∧ MEM 0w w.reserved ∧
  l0_call «sys_connect» conf bts w = SOME (FFIreturn out w1) ∧
  LENGTH w1.chans = LENGTH w.chans + 1 ⇒
  new_chans w (IO_event (ExtCall «sys_connect») conf (ZIP (bts, out))) = [LENGTH w.chans] ∧
  ev_role (lsn evs) (IO_event (ExtCall «sys_connect») conf (ZIP (bts, out))) =
  [Connected (w22n conf)]
Proof
  strip_tac >>
  qabbrev_tac ‘ev = IO_event (ExtCall «sys_connect») conf (ZIP (bts, out))’ >>
  ‘pinv (evs ++ [ev]) w1 (cs ++ new_chans w ev)’
    by (simp[Abbr ‘ev’] >> irule pinv_call >> simp[unblock_other]) >>
  drule_all connect_alloc >> strip_tac >>
  ‘f ≠ 0w’
    by (irule alloc_ne0 >> qexists_tac ‘w’ >> fs[pinv_def, l0_rely_def]) >>
  ‘∃j. j < LENGTH (cs ++ new_chans w ev) ∧ EL j (cs ++ new_chans w ev) = LENGTH w.chans’
    by (qpat_x_assum ‘pinv (evs ++ [ev]) _ _’ mp_tac >> rewrite_tac[pinv_def] >> strip_tac >>
        qpat_x_assum ‘∀f c. l0_chan_of w1 f = SOME c ⇒ _’ drule >> simp[] >> metis_tac[]) >>
  ‘EVERY (λc. c < LENGTH w.chans) cs’ by fs[pinv_def] >>
  ‘¬(j < LENGTH cs)’
    by (strip_tac >> fs[EL_APPEND1, EVERY_EL] >> res_tac >> fs[]) >>
  Cases_on ‘ev_new ev’ >- fs[new_chans_def] >>
  rename1 ‘ev_new ev = SOME x’ >> PairCases_on ‘x’ >> Cases_on ‘x1’
  >- (qpat_x_assum ‘ev_new ev = _’ mp_tac >> simp[Abbr ‘ev’] >> strip_tac >>
      drule ev_new_INL >> strip_tac >> gvs[new_chans_def, ev_role_def]) >>
  qpat_x_assum ‘ev_new ev = _’ mp_tac >> simp[Abbr ‘ev’] >> strip_tac >>
  drule ev_new_INR >> simp[]
QED

Definition tinv_def:
  tinv rs (s : sysstate) css ⇔
    ∀k c p. s.target (k, c) = SOME p ⇒
      (∃i. i < LENGTH (css k) ∧ EL i (css k) = c ∧
           EL i (ep_roles [] (proc_events k rs)) = Connected p) ∨
      close0 (proc_events k rs) ∧ conn_to p (proc_events k rs)
End

Theorem call_target_eq:
  sys_step s (Call k nm conf bts out) s' ⇒
  ∃w1. l0_call nm (unblock nm conf) bts (EL k s.procs) = SOME (FFIreturn out w1) ∧
       s'.target = call_target s k nm conf w1
Proof
  simp[sys_step_def, LET_THM] >> strip_tac >> qexists_tac ‘w1’ >> simp[call_target_def] >>
  qpat_x_assum ‘if _ then _ else _’ mp_tac >> rw[] >> simp[sys_pair_def]
QED

Theorem target_step:
  sys_step s r s' ∧ (∀k nm conf bts out. r ≠ Call k nm conf bts out) ⇒ s'.target = s.target
Proof
  Cases_on ‘r’ >> simp[]
  >- (rename1 ‘Kern ks’ >> Cases_on ‘ks’ >> simp[sys_step_def] >> rw[] >> simp[sys_pair_def])
  >- (rename1 ‘Env es’ >> Cases_on ‘es’ >> simp[sys_step_def] >> rw[] >> simp[]) >>
  simp[sys_step_def] >> rw[] >> simp[]
QED

(* The ghost and the roles of process k's earlier episodes stay *)
Theorem roles_old:
  pinv (proc_events k rs) w (css k) ∧ i < LENGTH (css k) ⇒
  EL i (css k ++ l) = EL i (css k) ∧
  EL i (ep_roles [] (proc_events k rs ++ evs')) = EL i (ep_roles [] (proc_events k rs))
Proof
  strip_tac >> ‘LENGTH (ep_roles [] (proc_events k rs)) = LENGTH (css k)’
    by fs[pinv_def, LENGTH_ep_roles] >>
  ‘ep_roles [] (proc_events k rs) ≼ ep_roles [] (proc_events k rs ++ evs')’
    by simp[ep_roles_append] >>
  fs[IS_PREFIX_APPEND] >> simp[EL_APPEND1]
QED

Theorem tinv_call:
  sinv rs s css ∧ zinv rs s ∧ tinv rs s css ∧ sys_step s (Call k nm conf bts out) s' ⇒
  tinv (rs ++ [Call k nm conf bts out]) s' (call_css s k nm conf bts out css)
Proof
  strip_tac >>
  ‘k < LENGTH s.procs ∧ s.alive k’
    by (qpat_x_assum ‘sys_step _ _ _’ mp_tac >> rewrite_tac[sys_step_def] >> simp[]) >>
  drule call_target_eq >> strip_tac >>
  qabbrev_tac ‘w = EL k s.procs’ >>
  qabbrev_tac ‘ev = IO_event (ExtCall nm) conf (ZIP (bts, out))’ >>
  ‘pk rs s css k’ by fs[sinv_def] >>
  ‘l0_rely w ∧ small_ch w.ch ∧ pinv (proc_events k rs) w (css k)’
    by (qpat_x_assum ‘pk rs s css k’ mp_tac >> simp[pk_def, Abbr ‘w’]) >>
  ‘∀k0. proc_events k0 (rs ++ [Call k nm conf bts out]) =
        proc_events k0 rs ++ if k0 = k then [ev] else []’
    by (gen_tac >> simp[proc_events_SNOC, Abbr ‘ev’] >> Cases_on ‘k0 = k’ >> simp[]) >>
  ‘∀k0. call_css s k nm conf bts out css k0 =
        css k0 ++ if k0 = k then new_chans w ev else []’
    by (gen_tac >> simp[call_css_def, APPLY_UPDATE_THM, Abbr ‘w’, Abbr ‘ev’] >>
        Cases_on ‘k0 = k’ >> simp[]) >>
  rewrite_tac[tinv_def] >> qx_genl_tac [‘k0’, ‘c’, ‘p’] >>
  qpat_x_assum ‘s'.target = _’ (fn th => rewrite_tac[th]) >>
  qpat_x_assum ‘∀k0. proc_events k0 _ = _’ (fn th => rewrite_tac[th]) >>
  qpat_x_assum ‘∀k0. call_css _ _ _ _ _ _ _ _ = _’ (fn th => rewrite_tac[th]) >>
  Cases_on ‘nm = «sys_connect» ∧ LENGTH w1.chans = LENGTH w.chans + 1 ∧ k0 = k ∧
            c = LENGTH w.chans’
  >- (
    (* the connect's new end *)
    pop_assum strip_assume_tac >>
    qpat_x_assum ‘k0 = k’ SUBST_ALL_TAC >> qpat_x_assum ‘c = _’ SUBST_ALL_TAC >>
    qpat_x_assum ‘nm = _’ SUBST_ALL_TAC >>
    simp[call_target_def, APPLY_UPDATE_THM] >> strip_tac >>
    qpat_x_assum ‘_ = p’ (SUBST_ALL_TAC o SYM) >>
    ‘MEM 0w w.reserved ∨ close0 (proc_events k rs)’
      by (qpat_x_assum ‘zinv rs s’ mp_tac >> rewrite_tac[zinv_def] >>
          disch_then (qspec_then ‘k’ mp_tac) >> simp[Abbr ‘w’])
    >- (qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[unblock_other] >> strip_tac >>
        drule_all connect_role >> strip_tac >> disj1_tac >>
        qexists_tac ‘LENGTH (css k)’ >>
        ‘LENGTH (ep_roles [] (proc_events k rs)) = LENGTH (css k)’
          by fs[pinv_def, LENGTH_ep_roles] >>
        simp[EL_APPEND2, ep_roles_SNOC, Abbr ‘ev’]) >>
    disj2_tac >> simp[close0_append] >>
    simp[conn_to_def, Abbr ‘ev’] >> metis_tac[]) >>
  (* an old target *)
  ‘call_target s k nm conf w1 (k0, c) = s.target (k0, c)’
    by (rw[call_target_def, APPLY_UPDATE_THM] >> gvs[Abbr ‘w’]) >>
  pop_assum (fn th => rewrite_tac[th]) >> strip_tac >>
  qpat_x_assum ‘tinv rs s css’ mp_tac >> rewrite_tac[tinv_def] >>
  disch_then drule >> strip_tac
  >- (disj1_tac >> qexists_tac ‘i’ >> Cases_on ‘k0 = k’ >> simp[] >> rveq >>
      drule_all roles_old >> simp[]) >>
  disj2_tac >> simp[close0_append, conn_to_append]
QED

Theorem tinv_step:
  sinv rs s css ∧ zinv rs s ∧ tinv rs s css ∧ sys_step s r s' ⇒
  tinv (rs ++ [r]) s' (step_css s r css)
Proof
  Cases_on ‘r’ >> simp[step_css_def]
  >- metis_tac[tinv_call] >>
  strip_tac >> drule target_step >> simp[] >> strip_tac >>
  fs[tinv_def, proc_events_SNOC]
QED

(* ------------------------------------------------------------------------
   Accepted and queued channels on the ports have a peer
   ------------------------------------------------------------------------ *)

Definition acc_inv_def:
  acc_inv ports rs (s : sysstate) css ⇔
    (∀k l p q c. k < LENGTH s.procs ∧ MEM (l, p, q) (EL k s.procs).listeners ∧ MEM c q ∧
                 MEM p ports ⇒ s.peer (k, c) ≠ NONE) ∧
    (∀k j p. k < LENGTH s.procs ∧ j < LENGTH (css k) ∧
             EL j (ep_roles [] (proc_events k rs)) = Accepted p ∧ MEM p ports ⇒
             s.peer (k, EL j (css k)) ≠ NONE)
End

(* The queued channels on the ports after a step: old ones, or paired *)
Definition lq_def:
  lq ports (s : sysstate) (s' : sysstate) ⇔
    ∀k l p q c. k < LENGTH s.procs ∧ MEM (l, p, q) (EL k s'.procs).listeners ∧ MEM c q ∧
                MEM p ports ⇒
                (∃q0. MEM (l, p, q0) (EL k s.procs).listeners ∧ MEM c q0) ∨
                s'.peer (k, c) ≠ NONE
End

Definition pg_def:
  pg (s : sysstate) (s' : sysstate) ⇔ ∀e. s.peer e ≠ NONE ⇒ s'.peer e ≠ NONE
End

Theorem pg_ext:
  sys_ext s s' ⇒ pg s s'
Proof
  rw[sys_ext_def, pg_def] >> Cases_on ‘s.peer e’ >> fs[] >> res_tac >> fs[]
QED

Theorem acc_gen:
  acc_inv ports rs s css ∧ LENGTH s'.procs = LENGTH s.procs ∧ pg s s' ∧ lq ports s s' ∧
  (∀k j p. k < LENGTH s.procs ∧ j < LENGTH (css' k) ∧
           EL j (ep_roles [] (proc_events k rs')) = Accepted p ∧ MEM p ports ⇒
           j < LENGTH (css k) ∧ EL j (css' k) = EL j (css k) ∧
           EL j (ep_roles [] (proc_events k rs)) = Accepted p ∨
           ∃l q. MEM (l, p, q) (EL k s.procs).listeners ∧ MEM (EL j (css' k)) q) ⇒
  acc_inv ports rs' s' css'
Proof
  rewrite_tac[acc_inv_def, lq_def, pg_def] >> strip_tac >> conj_tac
  >- (rpt strip_tac >>
      ‘k < LENGTH s.procs’ by fs[] >>
      qpat_x_assum ‘∀k l p q c. _ ∧ MEM _ (EL k s'.procs).listeners ∧ _ ⇒ _’ drule_all >>
      strip_tac >- metis_tac[] >> fs[]) >>
  rpt strip_tac >>
  ‘k < LENGTH s.procs’ by fs[] >>
  qpat_x_assum ‘∀k j p. _ ∧ j < LENGTH (css' k) ∧ _ ⇒ _’ drule_all >>
  strip_tac >- metis_tac[] >> metis_tac[]
QED

Theorem lq_trans:
  lq ports s s1 ∧ lq ports s1 s2 ∧ pg s1 s2 ∧ LENGTH s1.procs = LENGTH s.procs ⇒ lq ports s s2
Proof
  rewrite_tac[lq_def, pg_def] >> rpt strip_tac >>
  ‘k < LENGTH s1.procs’ by fs[] >>
  qpat_x_assum ‘∀k l p q c. k < LENGTH s1.procs ∧ _ ⇒ _’ drule_all >> strip_tac >- metis_tac[] >>
  simp[]
QED

Theorem lq_lsub:
  (∀k. k < LENGTH s.procs ⇒ lsub (EL k s.procs) (EL k s'.procs)) ⇒ lq ports s s'
Proof
  rw[lq_def, lsub_def] >> metis_tac[]
QED

Theorem deliver_listeners:
  (∀p. a ≠ LIncoming p) ⇒ (l0_deliver w a).listeners = w.listeners
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >> simp[upd_lchan_def]
QED

Theorem lsub_deliver:
  (∀p. a ≠ LIncoming p) ∧ k0 < LENGTH s.procs ⇒
  lsub (EL k0 s.procs) (EL k0 (sys_deliver k a s).procs)
Proof
  rw[sys_deliver_def, EL_LUPDATE] >> rw[] >> simp[lsub_def, deliver_listeners] >> metis_tac[]
QED

Theorem lq_deliver:
  (∀p. a ≠ LIncoming p) ⇒ lq ports s (sys_deliver k a s) ∧ lq ports s (sys_deliver k a s with moved := X1) ∧
  lq ports s (sys_deliver k a s with acked := X2) ∧ lq ports s (sys_deliver k a s with finned := X3)
Proof
  strip_tac >> rpt conj_tac >> irule lq_lsub >> simp[lsub_deliver]
QED

Theorem incoming_q:
  k' < LENGTH s.procs ∧ FILTER (λ(l, p', q). p' = p) (EL k' s.procs).listeners ≠ [] ∧
  ALL_DISTINCT (MAP FST (EL k' s.procs).listeners) ∧ k0 < LENGTH s.procs ∧
  MEM (l, p0, q) (EL k0 (sys_deliver k' (LIncoming p) s).procs).listeners ∧ MEM c q ⇒
  (∃q0. MEM (l, p0, q0) (EL k0 s.procs).listeners ∧ MEM c q0) ∨
  k0 = k' ∧ c = LENGTH (EL k' s.procs).chans ∧ p0 = p
Proof
  strip_tac >> Cases_on ‘k0 = k'’ >> gvs[sys_deliver_def, EL_LUPDATE]
  >- (drule_all incoming_listeners >> metis_tac[]) >>
  metis_tac[]
QED

Theorem room_filter:
  sys_room s k' p ⇒ k' < LENGTH s.procs ∧ FILTER (λ(l, p', q). p' = p) (EL k' s.procs).listeners ≠ []
Proof
  rw[sys_room_def] >> strip_tac >> fs[]
QED

Theorem lq_pair:
  k' < LENGTH s.procs ∧ FILTER (λ(l, p', q). p' = p) (EL k' s.procs).listeners ≠ [] ∧
  ALL_DISTINCT (MAP FST (EL k' s.procs).listeners) ⇒
  lq ports s (sys_pair e k' p s) ∧ pg s (sys_pair e k' p s)
Proof
  strip_tac >> conj_tac
  >- (rewrite_tac[lq_def, pair_procs] >> rpt strip_tac >>
      drule_all incoming_q >> strip_tac >- metis_tac[] >>
      disj2_tac >> rveq >> simp[sys_pair_def, APPLY_UPDATE_THM] >> rw[]) >>
  rw[pg_def, sys_pair_def, APPLY_UPDATE_THM] >> rw[]
QED

Theorem lq_incoming:
  k' < LENGTH s.procs ∧ FILTER (λ(l, p', q). p' = p) (EL k' s.procs).listeners ≠ [] ∧
  ALL_DISTINCT (MAP FST (EL k' s.procs).listeners) ∧ ¬MEM p ports ⇒
  lq ports s (sys_deliver k' (LIncoming p) s)
Proof
  rewrite_tac[lq_def] >> rpt strip_tac >>
  drule_all incoming_q >> strip_tac >- metis_tac[] >> fs[]
QED

Theorem sinv_ldist:
  sinv rs s css ∧ k < LENGTH s.procs ⇒ ALL_DISTINCT (MAP FST (EL k s.procs).listeners)
Proof
  rw[sinv_def] >> first_x_assum drule >> simp[pk_def, pinv_def]
QED

Theorem accept_role:
  l0_rely w ∧ pinv evs w cs ∧
  l0_call «sys_accept» conf bts w = SOME (FFIreturn out w1) ∧
  ev_new (IO_event (ExtCall «sys_accept») conf (ZIP (bts, out))) = SOME (f, INR l) ⇒
  ∃p q. MEM (l, p, q) w.listeners ∧ MEM (pop_chan w l) q ∧
        ev_role (lsn evs) (IO_event (ExtCall «sys_accept») conf (ZIP (bts, out))) = [Accepted p] ∧
        new_chans w (IO_event (ExtCall «sys_accept») conf (ZIP (bts, out))) = [pop_chan w l]
Proof
  strip_tac >> drule_all accept_new_chan >> strip_tac >>
  rename1 ‘FILTER _ _ = (l1, p1, _ :: q1) :: _’ >>
  ‘MEM (l1, p1, pop_chan w l :: q1) (FILTER (λ(l', p, q). l' = l) w.listeners)’ by simp[] >>
  ‘l1 = l ∧ MEM (l, p1, pop_chan w l :: q1) w.listeners’
    by (qpat_x_assum ‘MEM _ (FILTER _ _)’ mp_tac >> rewrite_tac[MEM_FILTER] >>
        pairarg_tac >> fs[] >> strip_tac >> rveq >> fs[]) >>
  rveq >>
  ‘ALOOKUP (lsn evs) l = SOME p1’
    by (qpat_x_assum ‘pinv _ _ _’ mp_tac >> rewrite_tac[pinv_def] >> strip_tac >>
        first_x_assum drule >> simp[]) >>
  qexistsl_tac [‘p1’, ‘pop_chan w l :: q1’] >> simp[ev_role_def, new_chans_def]
QED

Theorem call_w1:
  sinv rs s css ∧ k < LENGTH s.procs ∧
  l0_call nm (unblock nm conf) bts (EL k s.procs) = SOME (FFIreturn out w1) ⇒
  lsub (EL k s.procs) w1 ∧ ALL_DISTINCT (MAP FST w1.listeners) ∧
  l0_rely (EL k s.procs) ∧ pinv (proc_events k rs) (EL k s.procs) (css k)
Proof
  strip_tac >> ‘pk rs s css k’ by fs[sinv_def] >>
  ‘l0_rely (EL k s.procs) ∧ small_ch (EL k s.procs).ch ∧
   pinv (proc_events k rs) (EL k s.procs) (css k)’
    by (qpat_x_assum ‘pk rs s css k’ mp_tac >> simp[pk_def]) >>
  drule_all pinv_call >> strip_tac >>
  drule lsub_call >> simp[] >> strip_tac >>
  qpat_x_assum ‘pinv _ w1 _’ mp_tac >> simp[pinv_def]
QED

Theorem call_lq:
  sinv rs s css ∧ sys_step s (Call k nm conf bts out) s' ⇒ lq ports s s'
Proof
  strip_tac >>
  qpat_x_assum ‘sys_step _ _ _’ mp_tac >> simp[sys_step_def, LET_THM] >> strip_tac >>
  drule_all call_w1 >> strip_tac >>
  qabbrev_tac ‘W1 = w1 with <| clock := (EL k s.procs).clock + 1;
                               hist := (EL k s.procs).hist ++ [(nm, conf, bts)] |>’ >>
  ‘W1.listeners = w1.listeners’ by simp[Abbr ‘W1’] >>
  ‘lsub (EL k s.procs) W1’ by (simp[Abbr ‘W1’] >> irule (cj 4 lsub_fields) >> simp[]) >>
  ‘∀k0. k0 < LENGTH s.procs ⇒ lsub (EL k0 s.procs) (EL k0 (LUPDATE W1 k s.procs))’
    by (rw[EL_LUPDATE] >> rw[]) >>
  ‘∀k0. k0 < LENGTH s.procs ⇒ ALL_DISTINCT (MAP FST (EL k0 (LUPDATE W1 k s.procs)).listeners)’
    by (rw[EL_LUPDATE] >> rw[] >> irule sinv_ldist >> metis_tac[]) >>
  ‘∀T. lq ports s (s with <| procs := LUPDATE W1 k s.procs; target := T |>)’
    by (gen_tac >> irule lq_lsub >> simp[]) >>
  ‘lq ports s (s with procs := LUPDATE W1 k s.procs)’ by (irule lq_lsub >> simp[]) >>
  qpat_x_assum ‘if _ then _ else _’ mp_tac >> rw[] >> simp[] >>
  irule lq_trans >> simp[] >>
  qmatch_goalsub_abbrev_tac ‘sys_pair _ _ _ S2’ >>
  qexists_tac ‘S2’ >> simp[Abbr ‘S2’] >>
  drule room_filter >> strip_tac >>
  qunabbrev_tac ‘W1’ >> irule (ONCE_REWRITE_RULE [CONJ_COMM] lq_pair) >>
  qpat_x_assum ‘k' < _’ mp_tac >> qpat_x_assum ‘FILTER _ _ ≠ []’ mp_tac >>
  qpat_x_assum ‘∀k0. _ ⇒ ALL_DISTINCT _’ mp_tac >> simp[]
QED

Theorem ev_new_INR_ev:
  ev_new ev = SOME (f, INR l) ⇒ ∃conf bl. ev = IO_event (ExtCall «sys_accept») conf bl
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bl’ >> Cases_on ‘nm’ >>
  rw[ev_new_def] >> every_case_tac >> gvs[]
QED

Theorem acc_new:
  l0_rely w ∧ pinv evs w cs ∧ l0_call nm (unblock nm conf) bts w = SOME (FFIreturn out w1) ∧
  ¬(j < LENGTH cs) ∧
  j < LENGTH (cs ++ new_chans w (IO_event (ExtCall nm) conf (ZIP (bts, out)))) ∧
  EL j (ep_roles [] (evs ++ [IO_event (ExtCall nm) conf (ZIP (bts, out))])) = Accepted p ⇒
  ∃l q. MEM (l, p, q) w.listeners ∧
        MEM (EL j (cs ++ new_chans w (IO_event (ExtCall nm) conf (ZIP (bts, out))))) q
Proof
  strip_tac >>
  ‘LENGTH (ep_roles [] evs) = LENGTH cs’ by fs[pinv_def, LENGTH_ep_roles] >>
  qabbrev_tac ‘ev = IO_event (ExtCall nm) conf (ZIP (bts, out))’ >>
  Cases_on ‘ev_new ev’ >- fs[new_chans_def] >>
  PairCases_on ‘x’ >> Cases_on ‘x1’
  >- (‘j = LENGTH cs’ by fs[new_chans_def] >>
      qpat_x_assum ‘EL _ _ = Accepted p’ mp_tac >>
      simp[ep_roles_SNOC, ev_role_def, EL_APPEND2]) >>
  rename1 ‘INR l’ >>
  drule ev_new_INR_ev >> strip_tac >>
  ‘nm = «sys_accept»’ by fs[Abbr ‘ev’] >>
  qpat_x_assum ‘ev = _’ kall_tac >>
  qpat_x_assum ‘nm = _’ SUBST_ALL_TAC >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[unblock_other] >> strip_tac >>
  ‘ev_new (IO_event (ExtCall «sys_accept») conf (ZIP (bts, out))) = SOME (x0, INR l)’
    by fs[Abbr ‘ev’] >>
  drule_all accept_role >> strip_tac >>
  ‘j = LENGTH cs’ by fs[Abbr ‘ev’] >>
  qpat_x_assum ‘EL _ _ = Accepted p’ mp_tac >>
  simp[ep_roles_SNOC, EL_APPEND2, Abbr ‘ev’] >> strip_tac >> rveq >>
  qexistsl_tac [‘l’, ‘q’] >> simp[EL_APPEND2]
QED

Theorem acc_call:
  sinv rs s css ∧ acc_inv ports rs s css ∧ sys_ext s s' ∧
  sys_step s (Call k nm conf bts out) s' ⇒
  acc_inv ports (rs ++ [Call k nm conf bts out]) s' (call_css s k nm conf bts out css)
Proof
  strip_tac >>
  ‘k < LENGTH s.procs ∧ s.alive k ∧
   ∃w1. l0_call nm (unblock nm conf) bts (EL k s.procs) = SOME (FFIreturn out w1)’
    by (qpat_x_assum ‘sys_step _ _ _’ mp_tac >> rewrite_tac[sys_step_def] >> simp[] >>
        metis_tac[]) >>
  ‘lq ports s s'’ by metis_tac[call_lq] >>
  ‘pg s s'’ by metis_tac[pg_ext] >>
  ‘LENGTH s'.procs = LENGTH s.procs’ by fs[sys_ext_def] >>
  qpat_x_assum ‘acc_inv _ _ _ _’
    (fn th => irule (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] acc_gen) th)) >>
  simp[] >>
  qabbrev_tac ‘w = EL k s.procs’ >>
  qabbrev_tac ‘ev = IO_event (ExtCall nm) conf (ZIP (bts, out))’ >>
  ‘pk rs s css k’ by fs[sinv_def] >>
  ‘l0_rely w ∧ pinv (proc_events k rs) w (css k)’
    by (qpat_x_assum ‘pk rs s css k’ mp_tac >> simp[pk_def, Abbr ‘w’]) >>
  ‘∀k0. proc_events k0 (rs ++ [Call k nm conf bts out]) =
        proc_events k0 rs ++ if k0 = k then [ev] else []’
    by (gen_tac >> simp[proc_events_SNOC, Abbr ‘ev’] >> Cases_on ‘k0 = k’ >> simp[]) >>
  ‘∀k0. call_css s k nm conf bts out css k0 =
        css k0 ++ if k0 = k then new_chans w ev else []’
    by (gen_tac >> simp[call_css_def, APPLY_UPDATE_THM, Abbr ‘w’, Abbr ‘ev’] >>
        Cases_on ‘k0 = k’ >> simp[]) >>
  qx_genl_tac [‘k0’, ‘j’, ‘p’] >>
  qpat_x_assum ‘∀k0. proc_events k0 _ = _’ (fn th => rewrite_tac[th]) >>
  qpat_x_assum ‘∀k0. call_css _ _ _ _ _ _ _ _ = _’ (fn th => rewrite_tac[th]) >>
  Cases_on ‘k0 = k’ >> simp[] >> rpt strip_tac >>
  qpat_x_assum ‘k0 = k’ SUBST_ALL_TAC >>
  Cases_on ‘j < LENGTH (css k)’
  >- (disj1_tac >> drule_all roles_old >> strip_tac >> fs[]) >>
  disj2_tac >> qunabbrev_tac ‘ev’ >>
  irule acc_new >> simp[] >> metis_tac[]
QED

Theorem deliver_lst:
  (∀p. a ≠ LIncoming p) ⇒
  LENGTH (sys_deliver k a s).procs = LENGTH s.procs ∧
  ∀k0. k0 < LENGTH s.procs ⇒ (EL k0 (sys_deliver k a s).procs).listeners = (EL k0 s.procs).listeners
Proof
  rw[sys_deliver_def, EL_LUPDATE] >> rw[deliver_listeners]
QED

Theorem arrival_ne:
  env_arrival_chan a = SOME j ⇒ ∀p. a ≠ LIncoming p
Proof
  Cases_on ‘a’ >> simp[env_arrival_chan_def]
QED

Theorem lq_step:
  sinv rs s css ∧ sys_step s r s' ∧ (∀k p. r = Env (EIncoming k p) ⇒ ¬MEM p ports) ⇒
  lq ports s s'
Proof
  Cases_on ‘r’
  >- metis_tac[call_lq]
  >- (rename1 ‘Kern ks’ >> Cases_on ‘ks’ >> rewrite_tac[sys_step_def] >> strip_tac >>
      rveq >> simp[lq_deliver] >>
      rename1 ‘sys_pair (k, j) k' p’ >>
      drule room_filter >> strip_tac >>
      ‘ALL_DISTINCT (MAP FST (EL k' s.procs).listeners)’ by metis_tac[sinv_ldist] >>
      ‘LENGTH (sys_deliver k (LConnUp j) s).procs = LENGTH s.procs ∧
       ∀k0. k0 < LENGTH s.procs ⇒
            (EL k0 (sys_deliver k (LConnUp j) s).procs).listeners = (EL k0 s.procs).listeners’
        by (irule deliver_lst >> simp[]) >>
      irule lq_trans >> qexists_tac ‘sys_deliver k (LConnUp j) s’ >> simp[lq_deliver] >>
      irule (ONCE_REWRITE_RULE [CONJ_COMM] lq_pair) >> simp[])
  >- (rename1 ‘Env es’ >> Cases_on ‘es’ >> rewrite_tac[sys_step_def] >> strip_tac >>
      rveq >> simp[lq_deliver]
      >- (rename1 ‘LIncoming p’ >> drule room_filter >> strip_tac >>
          irule lq_incoming >> fs[] >> metis_tac[sinv_ldist]) >>
      drule arrival_ne >> simp[lq_deliver]) >>
  rewrite_tac[sys_step_def] >> strip_tac >> rveq >>
  irule lq_lsub >> rw[EL_LUPDATE] >> rw[lsub_close_all]
QED

Theorem acc_other:
  acc_inv ports rs s css ∧ sys_ext s s' ∧ lq ports s s' ∧
  (∀k. proc_events k (rs ++ [r]) = proc_events k rs) ⇒
  acc_inv ports (rs ++ [r]) s' css
Proof
  strip_tac >>
  ‘pg s s'’ by metis_tac[pg_ext] >>
  ‘LENGTH s'.procs = LENGTH s.procs’ by fs[sys_ext_def] >>
  qpat_x_assum ‘acc_inv _ _ _ _’
    (fn th => irule (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] acc_gen) th)) >>
  asm_rewrite_tac[] >> rpt strip_tac >> disj1_tac >> fs[]
QED

Theorem acc_step:
  sinv rs s css ∧ acc_inv ports rs s css ∧ sys_ext s s' ∧ sys_step s r s' ∧
  (∀k p. r = Env (EIncoming k p) ⇒ ¬MEM p ports) ⇒
  acc_inv ports (rs ++ [r]) s' (step_css s r css)
Proof
  strip_tac >> Cases_on ‘r’
  >- (simp[step_css_def] >> metis_tac[acc_call]) >>
  simp[step_css_def] >> irule acc_other >> simp[proc_events_SNOC] >>
  qexists_tac ‘s’ >> simp[] >> irule lq_step >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   A connect end broken right after its connect never gets a peer
   ------------------------------------------------------------------------ *)

(* Step t is process k's connect that appended channel c, and c is broken
   right after it (an immediate failure that returned a socket) *)
Definition born_broken_def:
  born_broken ss rs t k c ⇔
    (∃conf bts out. rs t = Call k «sys_connect» conf bts out) ∧
    k < LENGTH (ss t).procs ∧ c = LENGTH (EL k (ss t).procs).chans ∧
    c < LENGTH (EL k (ss (SUC t)).procs).chans ∧
    (EL c (EL k (ss (SUC t)).procs).chans).broken
End

(* The client's connect episodes to p whose channel was not broken right
   after the connect (close-v2's narrow count, D43 fact 1) *)
Definition conns_ok_def:
  conns_ok p ss rs cl n =
    LENGTH (FILTER (λ(r, c). r = Connected p ∧ ∀t. t < n ⇒ ¬born_broken ss rs t cl c)
                   (ZIP (ep_roles [] (ptr rs cl n), run_css ss rs n cl)))
End

Theorem connect_broken:
  l0_call «sys_connect» conf bts w = SOME (FFIreturn out w1) ∧
  LENGTH w1.chans = LENGTH w.chans + 1 ∧ (EL (LENGTH w.chans) w1.chans).broken ⇒
  ¬(EL (LENGTH w.chans) w1.chans).connecting
Proof
  simp[l0_call_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule l0_connect_cases >> simp[LET_THM] >> strip_tac >>
  gvs[upd_lchan_def, EL_LUPDATE, EL_APPEND2, fresh_lchan_def]
QED

Theorem connect_len:
  l0_call «sys_connect» conf bts w = SOME (FFIreturn out w1) ⇒ LENGTH w1.chans ≤ LENGTH w.chans + 1
Proof
  simp[l0_call_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule l0_connect_cases >> simp[LET_THM] >> strip_tac >> gvs[upd_lchan_def]
QED

Theorem irun_end_mono:
  l0sys_irun ps ss rs ⇒ ∀t2 t1 e. t1 ≤ t2 ∧ is_end (ss t1) e ⇒ is_end (ss t2) e
Proof
  strip_tac >> drule irun_ext >> strip_tac >> Induct >- simp[] >>
  rpt strip_tac >> Cases_on ‘t1 = SUC t2’ >- fs[] >>
  irule is_end_ext >> qexists_tac ‘ss t2’ >> simp[] >>
  first_x_assum irule >> qexists_tac ‘t1’ >> simp[]
QED

(* The step that makes the end: no pairing, and not connecting *)
Theorem born_broken_step:
  kinv s ∧ sys_step s (Call k nm conf bts out) s' ∧ nm = «sys_connect» ∧
  k < LENGTH s.procs ∧ LENGTH (EL k s.procs).chans < LENGTH (EL k s'.procs).chans ∧
  (EL (LENGTH (EL k s.procs).chans) (EL k s'.procs).chans).broken ⇒
  ¬(sys_chan s' (k, LENGTH (EL k s.procs).chans)).connecting ∧
  s'.peer (k, LENGTH (EL k s.procs).chans) = NONE
Proof
  strip_tac >> qpat_x_assum ‘nm = _’ SUBST_ALL_TAC >>
  qpat_x_assum ‘sys_step _ _ _’ mp_tac >> simp[sys_step_def, LET_THM, unblock_other] >>
  qabbrev_tac ‘w = EL k s.procs’ >> strip_tac >>
  ‘s.peer (k, LENGTH w.chans) = NONE’
    by (‘¬is_end s (k, LENGTH w.chans)’ by simp[is_end_def, Abbr ‘w’] >>
        fs[kinv_def]) >>
  Cases_on ‘LENGTH w1.chans = LENGTH w.chans + 1’ >> fs[EL_LUPDATE] >>
  Cases_on ‘¬(EL (LENGTH w.chans) w1.chans).connecting ∧ ¬(EL (LENGTH w.chans) w1.chans).broken’
  >- (fs[] >> gvs[EL_LUPDATE]
      >- (gvs[sys_pair_def, sys_deliver_def, EL_LUPDATE] >> rw[] >>
          gvs[l0_deliver_def, AllCaseEqs()] >> every_case_tac >> gvs[EL_APPEND1])) >>
  gvs[EL_LUPDATE, sys_chan_def] >> imp_res_tac connect_len >> imp_res_tac connect_broken >> fs[]
QED

Theorem irun_bb:
  l0sys_irun ps ss rs ⇒
  ∀n t k c. t < n ∧ born_broken ss rs t k c ⇒
            ¬(sys_chan (ss n) (k, c)).connecting ∧ (ss n).peer (k, c) = NONE
Proof
  strip_tac >> drule irun_ext >> strip_tac >> drule irun_sinv_css >> strip_tac >>
  Induct >- simp[] >>
  qx_genl_tac [‘t’, ‘k’, ‘c’] >> strip_tac >>
  Cases_on ‘t = n’
  >- (qpat_x_assum ‘t = n’ SUBST_ALL_TAC >>
      qpat_x_assum ‘born_broken _ _ _ _ _’ mp_tac >> rewrite_tac[born_broken_def] >>
      strip_tac >> qpat_x_assum ‘c = _’ SUBST_ALL_TAC >>
      irule born_broken_step >> simp[] >>
      conj_tac >- metis_tac[sinv_def] >>
      qexistsl_tac [‘bts’, ‘conf’, ‘out’] >>
      ‘sys_step (ss n) (rs n) (ss (SUC n))’ by fs[l0sys_irun_def] >> rfs[]) >>
  ‘t < n’ by decide_tac >>
  ‘¬(sys_chan (ss n) (k, c)).connecting ∧ (ss n).peer (k, c) = NONE’ by metis_tac[] >>
  ‘is_end (ss (SUC t)) (k, c)’
    by (qpat_x_assum ‘born_broken _ _ _ _ _’ mp_tac >> rewrite_tac[born_broken_def] >>
        strip_tac >> simp[is_end_def] >>
        ‘LENGTH (ss (SUC t)).procs = LENGTH (ss t).procs’ by metis_tac[sys_ext_def] >>
        simp[]) >>
  ‘is_end (ss n) (k, c)’
    by (drule irun_end_mono >> disch_then (qspecl_then [‘n’, ‘SUC t’, ‘(k, c)’] mp_tac) >> simp[]) >>
  ‘sys_ext (ss n) (ss (SUC n))’ by metis_tac[] >>
  conj_tac
  >- (strip_tac >> drule_all connecting_ext >> simp[]) >>
  Cases_on ‘(ss (SUC n)).peer (k, c)’ >> simp[] >>
  qpat_x_assum ‘sys_ext (ss n) (ss (SUC n))’ mp_tac >> rewrite_tac[sys_ext_def] >>
  strip_tac >> first_x_assum (drule_then mp_tac) >> simp[new_pair_def]
QED

(* ------------------------------------------------------------------------
   Counting: each accepted episode on p is paired with its own Connected-p
   episode of the client
   ------------------------------------------------------------------------ *)

Theorem acc_peer:
  sinv rs s css ∧ tinv rs s css ∧ acc_inv ports rs s css ∧ MEM p ports ∧ k < LENGTH s.procs ∧
  ¬close0 (proc_events cl rs) ∧
  (∀k0. k0 < LENGTH s.procs ∧ k0 ≠ cl ⇒ ¬conn_to p (proc_events k0 rs)) ∧
  j < LENGTH (css k) ∧ EL j (ep_roles [] (proc_events k rs)) = Accepted p ⇒
  ∃i. i < LENGTH (css cl) ∧ EL i (ep_roles [] (proc_events cl rs)) = Connected p ∧
      s.peer (k, EL j (css k)) = SOME (cl, EL i (css cl))
Proof
  strip_tac >>
  ‘s.peer (k, EL j (css k)) ≠ NONE’
    by (qpat_x_assum ‘acc_inv _ _ _ _’ mp_tac >> rewrite_tac[acc_inv_def] >>
        disch_then (qspecl_then [‘k’, ‘j’, ‘p’] mp_tac o CONJUNCT2) >> simp[]) >>
  ‘∃e. s.peer (k, EL j (css k)) = SOME e’ by (Cases_on ‘s.peer (k, EL j (css k))’ >> fs[]) >>
  PairCases_on ‘e’ >>
  ‘kinv s’ by fs[sinv_def] >>
  ‘is_end s (e0, e1)’ by metis_tac[kinv_peer_end] >>
  ‘e0 < LENGTH s.procs’ by fs[is_end_def] >>
  ‘s.target (e0, e1) = SOME p’
    by (‘pk rs s css k’ by fs[sinv_def] >>
        qpat_x_assum ‘pk _ _ _ k’ mp_tac >> simp[pk_def, LET_THM] >> strip_tac >>
        qpat_x_assum ‘∀j p. j < LENGTH (css k) ∧ _ = Accepted p ⇒ _’
          (qspecl_then [‘j’, ‘p’] mp_tac) >> simp[]) >>
  qpat_x_assum ‘tinv _ _ _’ mp_tac >> rewrite_tac[tinv_def] >>
  disch_then drule >> strip_tac
  >- (‘pk rs s css e0’ by fs[sinv_def] >>
      ‘LENGTH (ep_roles [] (proc_events e0 rs)) = LENGTH (css e0)’
        by (qpat_x_assum ‘pk _ _ _ e0’ mp_tac >> simp[pk_def, LET_THM, pinv_def, LENGTH_ep_roles]) >>
      ‘conn_to p (proc_events e0 rs)’
        by (irule roles_conn_to >> qexists_tac ‘[]’ >> metis_tac[EL_MEM]) >>
      ‘e0 = cl’ by metis_tac[] >> rveq >>
      qexists_tac ‘i’ >> simp[]) >>
  ‘e0 = cl’ by metis_tac[] >> rveq >> fs[]
QED

Theorem card_filter:
  ∀l. FINITE {j | j < LENGTH l ∧ P (EL j l)} ∧
      CARD {j | j < LENGTH l ∧ P (EL j l)} = LENGTH (FILTER P l)
Proof
  Induct >- simp[] >> gen_tac >>
  ‘{j | j < LENGTH (h::l) ∧ P (EL j (h::l))} =
   if P h then 0 INSERT IMAGE SUC {j | j < LENGTH l ∧ P (EL j l)}
   else IMAGE SUC {j | j < LENGTH l ∧ P (EL j l)}’
    by (rw[EXTENSION] >> Cases_on ‘x’ >> simp[] >> metis_tac[]) >>
  pop_assum SUBST1_TAC >> rw[] >> simp[CARD_IMAGE_INJ]
QED

Theorem inj_count:
  (∀j. j < LENGTH l1 ∧ P (EL j l1) ⇒ ∃i. i < LENGTH l2 ∧ Q (EL i l2) ∧ R j i) ∧
  (∀j1 j2 i. j1 < LENGTH l1 ∧ P (EL j1 l1) ∧ j2 < LENGTH l1 ∧ P (EL j2 l1) ∧
             R j1 i ∧ R j2 i ⇒ j1 = j2) ⇒
  LENGTH (FILTER P l1) ≤ LENGTH (FILTER Q l2)
Proof
  strip_tac >>
  ‘∀j. ∃i. j < LENGTH l1 ∧ P (EL j l1) ⇒ i < LENGTH l2 ∧ Q (EL i l2) ∧ R j i’ by metis_tac[] >>
  pop_assum (strip_assume_tac o SIMP_RULE std_ss [SKOLEM_THM]) >>
  qspecl_then [‘l1’] (assume_tac o GEN_ALL) card_filter >>
  ‘CARD {j | j < LENGTH l1 ∧ P (EL j l1)} ≤ CARD {i | i < LENGTH l2 ∧ Q (EL i l2)}’
    suffices_by simp[card_filter] >>
  irule INJ_CARD >> simp[card_filter] >>
  qexists_tac ‘f’ >> simp[INJ_DEF] >> metis_tac[]
QED

Theorem accepts_le_state:
  ∀G. sinv rs s css ∧ tinv rs s css ∧ acc_inv ports rs s css ∧ MEM p ports ∧
  k < LENGTH s.procs ∧ cl < LENGTH s.procs ∧ ¬close0 (proc_events cl rs) ∧
  (∀k0. k0 < LENGTH s.procs ∧ k0 ≠ cl ⇒ ¬conn_to p (proc_events k0 rs)) ∧
  (∀c. s.peer (cl, c) ≠ NONE ⇒ G c) ⇒
  LENGTH (FILTER ($= (Accepted p)) (ep_roles [] (proc_events k rs))) ≤
  LENGTH (FILTER (λ(r, c). r = Connected p ∧ G c) (ZIP (ep_roles [] (proc_events cl rs), css cl)))
Proof
  rpt strip_tac >>
  ‘pk rs s css k ∧ pk rs s css cl ∧ kinv s’ by fs[sinv_def] >>
  ‘LENGTH (ep_roles [] (proc_events k rs)) = LENGTH (css k) ∧ ALL_DISTINCT (css k)’
    by (qpat_x_assum ‘pk _ _ _ k’ mp_tac >> simp[pk_def, LET_THM, pinv_def, LENGTH_ep_roles]) >>
  ‘LENGTH (ep_roles [] (proc_events cl rs)) = LENGTH (css cl)’
    by (qpat_x_assum ‘pk _ _ _ cl’ mp_tac >> simp[pk_def, LET_THM, pinv_def, LENGTH_ep_roles]) >>
  irule inj_count >>
  qexists_tac ‘λj i. s.peer (k, EL j (css k)) = SOME (cl, EL i (css cl))’ >> simp[] >>
  conj_tac
  >- (qx_genl_tac [‘j1’, ‘j2’, ‘i’] >> strip_tac >>
      ‘(k, EL j1 (css k)) = (k, EL j2 (css k))’ by metis_tac[kinv_peer_inj] >>
      fs[] >> metis_tac[ALL_DISTINCT_EL_IMP]) >>
  qx_gen_tac ‘j’ >> strip_tac >>
  ‘∃i. i < LENGTH (css cl) ∧ EL i (ep_roles [] (proc_events cl rs)) = Connected p ∧
       s.peer (k, EL j (css k)) = SOME (cl, EL i (css cl))’
    by (irule acc_peer >>
        rpt conj_tac >>
        FIRST [first_assum ACCEPT_TAC, qexists_tac ‘ports’ >> simp[] >> NO_TAC, fs[]]) >>
  ‘EL i (ZIP (ep_roles [] (proc_events cl rs), css cl)) =
   (EL i (ep_roles [] (proc_events cl rs)), EL i (css cl))’ by (irule EL_ZIP >> simp[]) >>
  qexists_tac ‘i’ >> simp[LENGTH_ZIP] >>
  first_x_assum irule >> drule_all kinv_peer_end >> simp[]
QED

(* ------------------------------------------------------------------------
   Over a run
   ------------------------------------------------------------------------ *)

Theorem irun_zinv:
  l0sys_irun ps ss rs ⇒ ∀n. zinv (GENLIST rs n) (ss n)
Proof
  strip_tac >> drule irun_ext >> strip_tac >> Induct
  >- (rw[zinv_def] >> fs[l0sys_irun_def, sys_init_def, LET_THM]) >>
  simp[GENLIST, SNOC_APPEND] >> irule zinv_step >>
  qexists_tac ‘ss n’ >> fs[l0sys_irun_def]
QED

Theorem irun_tinv:
  l0sys_irun ps ss rs ⇒ ∀n. tinv (GENLIST rs n) (ss n) (run_css ss rs n)
Proof
  strip_tac >> drule irun_sinv_css >> drule irun_zinv >> rpt strip_tac >> Induct_on ‘n’
  >- fs[tinv_def, l0sys_irun_def, sys_init_def] >>
  simp[run_css_def, GENLIST, SNOC_APPEND] >> irule tinv_step >> fs[l0sys_irun_def]
QED

Theorem irun_acc_inv:
  l0sys_irun ps ss rs ∧ isolated ports ss rs ⇒
  ∀n. acc_inv ports (GENLIST rs n) (ss n) (run_css ss rs n)
Proof
  strip_tac >> drule irun_sinv_css >> drule irun_ext >> rpt strip_tac >> Induct_on ‘n’
  >- (rw[acc_inv_def, run_css_def] >>
      fs[l0sys_irun_def, sys_init_def, LET_THM] >>
      qpat_x_assum ‘∀k'. k' < LENGTH ps ⇒ _’ (qspec_then ‘k’ mp_tac) >> simp[] >>
      strip_tac >> fs[]) >>
  simp[run_css_def, GENLIST, SNOC_APPEND] >> irule acc_step >> fs[l0sys_irun_def, isolated_def] >>
  metis_tac[]
QED

Theorem acc_filter:
  ∀l. (∀q. MEM (Accepted q) l ⇒ q = p) ⇒
      LENGTH (FILTER is_acc l) = LENGTH (FILTER ($= (Accepted p)) l)
Proof
  Induct >> simp[] >> Cases >> rw[is_acc_def] >> fs[] >> metis_tac[]
QED

Theorem irun_accepts_le:
  l0sys_irun ps ss rs ∧ isolated ports ss rs ∧ MEM p ports ∧ k < LENGTH ps ∧ cl < LENGTH ps ∧
  (∀q. MEM (Accepted q) (ep_roles [] (ptr rs k n)) ⇒ q = p) ∧ ¬close0 (ptr rs cl n) ∧
  (∀k0. k0 < LENGTH ps ∧ k0 ≠ cl ⇒ ¬conn_to p (ptr rs k0 n)) ⇒
  LENGTH (l0_accepted (ptr rs k n)) ≤ conns_ok p ss rs cl n
Proof
  strip_tac >> fs[ptr_def, conns_ok_def] >>
  ‘LENGTH (ss n).procs = LENGTH ps’ by metis_tac[irun_procs_length] >>
  ‘sinv (GENLIST rs n) (ss n) (run_css ss rs n)’ by metis_tac[irun_sinv_css] >>
  ‘tinv (GENLIST rs n) (ss n) (run_css ss rs n)’ by metis_tac[irun_tinv] >>
  ‘acc_inv ports (GENLIST rs n) (ss n) (run_css ss rs n)’ by metis_tac[irun_acc_inv] >>
  qspecl_then [‘proc_events k (GENLIST rs n)’, ‘[]’] SUBST1_TAC l0_accepted_roles >>
  drule acc_filter >> disch_then SUBST1_TAC >>
  qspec_then ‘λc. ∀t. t < n ⇒ ¬born_broken ss rs t cl c’ (irule o BETA_RULE) accepts_le_state >>
  simp[] >>
  qexistsl_tac [‘ports’, ‘ss n’] >> simp[] >>
  rpt strip_tac >> drule irun_bb >> disch_then drule_all >> simp[]
QED

Theorem accepts_lt_lift:
  l0sys_irun ps ss rs ∧ isolated ports ss rs ∧ MEM p ports ∧ k < LENGTH ps ∧ cl < LENGTH ps ∧
  (∀n q. MEM (Accepted q) (ep_roles [] (ptr rs k n)) ⇒ q = p) ∧ (∀n. ¬close0 (ptr rs cl n)) ∧
  (∀n k0. k0 < LENGTH ps ∧ k0 ≠ cl ⇒ ¬conn_to p (ptr rs k0 n)) ∧
  (∀n. conns_ok p ss rs cl n ≤ N) ∧ N < M ∧
  (∀evs. LPREFIX (fromList evs) tr ⇒ ∃n. evs ≼ ptr rs k n) ⇒
  ∀evs. LPREFIX (fromList evs) tr ⇒ LENGTH (l0_accepted evs) < M
Proof
  rpt strip_tac >>
  ‘∃n. evs ≼ ptr rs k n’ by metis_tac[] >>
  ‘LENGTH (l0_accepted (ptr rs k n)) ≤ conns_ok p ss rs cl n’
    by (irule irun_accepts_le >> simp[] >> metis_tac[]) >>
  ‘∃l. ptr rs k n = evs ++ l’ by metis_tac[IS_PREFIX_APPEND] >>
  ‘LENGTH (l0_accepted evs) ≤ LENGTH (l0_accepted (ptr rs k n))’
    by simp[l0_accepted_append] >>
  ‘conns_ok p ss rs cl n ≤ N’ by metis_tac[] >>
  decide_tac
QED

(* The form honest-ffi's conn_live_l0 takes (accepts_lt M tr), for the
   process's trace tr of l0sys_proj_inf, when k calls infinitely often (as
   for l0sys_proj_drains) *)
Theorem accepts_lt_irun:
  l0sys_irun ps ss rs ∧ isolated ports ss rs ∧ MEM p ports ∧ k < LENGTH ps ∧ cl < LENGTH ps ∧
  (∀n q. MEM (Accepted q) (ep_roles [] (ptr rs k n)) ⇒ q = p) ∧ (∀n. ¬close0 (ptr rs cl n)) ∧
  (∀n k0. k0 < LENGTH ps ∧ k0 ≠ cl ⇒ ¬conn_to p (ptr rs k0 n)) ∧
  (∀n. conns_ok p ss rs cl n ≤ N) ∧ N < M ∧
  (∀t. ∃t'. t ≤ t' ∧ is_kcall k (rs t')) ∧ (∀t. LPREFIX (fromList (ptr rs k t)) tr) ⇒
  ∀evs. LPREFIX (fromList evs) tr ⇒ LENGTH (l0_accepted evs) < M
Proof
  strip_tac >>
  ‘∀evs. LPREFIX (fromList evs) tr ⇒ ∃n. evs ≼ ptr rs k n’
    by (rpt strip_tac >> drule_all ptr_of_prefix >> strip_tac >>
        qexists_tac ‘t’ >> simp[]) >>
  qpat_x_assum ‘∀t. ∃t'. _’ kall_tac >> qpat_x_assum ‘∀t. LPREFIX _ _’ kall_tac >>
  metis_tac[accepts_lt_lift]
QED
