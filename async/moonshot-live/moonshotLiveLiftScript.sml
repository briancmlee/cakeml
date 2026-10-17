(*
  Shared pieces of the lifts from the L0 claims to the run obligations
  (moonshotLiveFinal): the world each process's L0 claim is applied at.

  MAIN: proj_world: for an infinite l0sys run and a process k, the world
    w0 of the projection (l0sys_proj_inf) is an l0_server_world, and
    F2_sys gives F2 at it.

  TEMPORARY COPIES (remove at merge): l0_server_world (honestEchoL0Spec)
  and F2 (honestL1BStmts), both on spike/kv-live-l0 @ 86b2fea01.
*)
Theory moonshotLiveLift
Ancestors
  moonshotLiveProjInf l0sysFair l0sysInv honestL0WorldProps
Libs
  preamble

Definition l0_server_world_def:
  l0_server_world w0 ⇔
    w0.listeners = [] ∧ w0.chans = [] ∧ w0.open_fds = [] ∧ w0.hist = [] ∧
    honestL0WorldProps$fds_lt w0 ∧ l0_rely w0
End

Definition F2_def:
  F2 (w0 : l0world) ⇔ ∀j h n. 0 < n ⇒ 0 < w0.ch.takes j h 0 n
End

Theorem fresh_server_world:
  l0_fresh w ∧ l0sysInv$fds_lt w ∧ l0_rely w ⇒ l0_server_world w
Proof
  rw[l0sysBridgesTheory.l0_fresh_def, l0_server_world_def] >>
  fs[l0sysInvTheory.fds_lt_def, honestL0WorldPropsTheory.fds_lt_def]
QED

Theorem proj_world:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ⇒
  ∃AS. (∀t. kstep k (ss t) (rs t) (ss (SUC t)) (AS t)) ∧
       let w0 = (EL k (ss 0).procs) with env := (λn h nm. fenv k ss AS n) in
         l0_server_world w0 ∧ (F2_sys ps ss ⇒ F2 w0) ∧
         (∀b. semantics_prog (init_state (l0_ffi w0)) init_env (EL k ps) b ∧ b ≠ Fail ⇒
              ∀t. LPREFIX (fromList (ptr rs k t)) (beh_io b))
Proof
  strip_tac >> drule_all l0sys_proj_inf >> strip_tac >>
  qexists_tac ‘AS’ >> fs[LET_THM] >> rpt conj_tac
  >- (irule fresh_server_world >> simp[])
  >> simp[F2_sys_def, F2_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[]
QED
