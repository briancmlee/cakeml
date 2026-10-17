(*
  A program's L0 claim at the run (README §6, "Final instantiation"): for
  process k of an infinite run that calls infinitely often (CALLS-IO), a
  claim of the live claims' shape

    ∀w0. l0_server_world w0 ⇒
      ∃io. (semantics_prog … (Diverge io) ∧ Q w0 io) ∨
           ∃evs. semantics_prog … (Terminate Success evs)

  (kv_live_claim and l0_echo2_claim have it: their listen-failed and
  stdio-closed outcomes are Terminate Success) gives Q at the projection's
  world w0 and an L0 trace tr of which every prefix of k's run is a
  prefix, with F2_sys ⇒ F2 w0 and sys_drains ⇒ drains w0 tr.  The
  terminating outcomes are ruled out: k's trace is unbounded (CALLS-IO).

  MAIN: claim_run.
*)
Theory moonshotLiveClaimRun
Ancestors
  moonshotLiveLift moonshotLiveWorldDrains moonshotLiveProjInf l0sysFair l0sysBridges llist
Libs
  preamble

(* k's run has no finite bound *)
Theorem ptr_not_finite:
  (∀t. ∃t'. t ≤ t' ∧ is_kcall k (rs t')) ⇒ ¬∀t. LPREFIX (fromList (ptr rs k t)) (fromList evs)
Proof
  rpt strip_tac >> drule ptr_len_hits >> disch_then (qspec_then ‘SUC (LENGTH evs)’ strip_assume_tac) >>
  ‘LPREFIX (fromList (ptr rs k t)) (fromList evs)’ by asm_rewrite_tac[] >>
  fs[LPREFIX_fromList, from_toList] >> imp_res_tac IS_PREFIX_LENGTH >> fs[]
QED

Theorem claim_run:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ∧ (∀t. ∃t'. t ≤ t' ∧ is_kcall k (rs t')) ∧
  (∀w0. l0_server_world w0 ⇒
        ∃iot. (semantics_prog (init_state (l0_ffi w0)) init_env (EL k ps) (Diverge iot) ∧ Q w0 iot) ∨
             ∃evs. semantics_prog (init_state (l0_ffi w0)) init_env (EL k ps) (Terminate Success evs)) ⇒
  ∃w0 tr. Q w0 tr ∧ (∀t. LPREFIX (fromList (ptr rs k t)) tr) ∧ (F2_sys ps ss ⇒ F2 w0) ∧
          ∀c. sys_drains ss (k, c) ⇒ drains w0 tr c
Proof
  strip_tac >> drule_all l0sys_proj_inf >> strip_tac >> fs[LET_THM] >>
  qabbrev_tac ‘w0 = (EL k (ss 0).procs) with env := (λn h nm. fenv k ss AS n)’ >>
  ‘l0_server_world w0’ by (irule fresh_server_world >> simp[]) >>
  qpat_x_assum ‘∀w0. l0_server_world w0 ⇒ _’ drule >> strip_tac
  >- (qexistsl_tac [‘w0’, ‘iot’] >>
      ‘∀t. LPREFIX (fromList (ptr rs k t)) iot’
        by (qpat_x_assum ‘∀b. _ ∧ b ≠ Fail ⇒ _’ (qspec_then ‘Diverge iot’ mp_tac) >>
            simp[beh_io_def]) >>
      rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- (simp[F2_sys_def, F2_def, Abbr ‘w0’] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
      rpt strip_tac >> irule world_drains >> simp[] >>
      qexistsl_tac [‘AS’, ‘k’, ‘ps’, ‘rs’, ‘ss’] >> simp[Abbr ‘w0’]) >>
  qpat_x_assum ‘∀b. _ ∧ b ≠ Fail ⇒ _’ (qspec_then ‘Terminate Success evs’ mp_tac) >>
  simp[beh_io_def] >> strip_tac >>
  drule ptr_not_finite >> disch_then (qspec_then ‘evs’ mp_tac) >> simp[]
QED
