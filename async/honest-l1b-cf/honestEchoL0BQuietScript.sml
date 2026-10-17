(*
  L3-09 (S5): quiet_on_kernel for the blocking echo program, as a
  corollary under the PF run's standing facts and the PF echo's guarantee
  (async-spike's loop-level liveness, the KV worker's safety), read in the
  reindexed post-listen world (echo_pf_facts).  Nothing here is trusted:
  every fact used is a hypothesis of the final theorem.

  Under echo_pf_facts the D25 guard never fires (its run_ok includes the
  PF run's handle bound), so the claim holds as L3-00 states it
  (echo_l0b_quiet); the form with the PENDING amendment #3 (¬accepts_below
  io in the Diverge excuse) follows (echo_l0b_quiet_a).  The amendment
  matters only where the PF facts are relaxed to allow handle exhaustion.

  MAIN: echo_l0b_quiet_world, echo_l0b_quiet.
*)
Theory honestEchoL0BQuiet
Ancestors
  llist ffi semantics honestL0 honestL0World honestL0WorldProps honestL0WorldInv honestL0Part
  honestL1Model honestL1PFModel honestL1PFLive honestL1PFConnRun honestL1PFOut honestL1PFProg
  honestEchoL0Spec honestEchoL0Prog honestEchoL0Sem
  honestL1BModel honestL1BSim honestL1BRefine honestL1BTransfer honestL1BConn honestL1BStable
  honestL1BStmts honestL1BQuiet honestL1BShift
  honestL1BSpec honestL1BTrace honestEchoL0BProg honestEchoL0BMain honestEchoL0BSem
  honestEchoL0BStutter
Libs
  preamble

(* The claim, with the pending amendment (#3) *)
Definition quiet_on_kernel_claim_a_def:
  quiet_on_kernel_claim_a guar prog ⇔
    ∀w0. l0_server_world w0 ⇒
      ∃b. semantics_prog (init_state (l0_ffi w0)) init_env prog b ∧
          (listen_failed b ∨
           (∃io. b = Diverge io ∧ guar w0 io) ∨
           (∃io. asleep_l0 b io ∧ guar w0 (fromList io))) ∧
          (arrivals_finite_l0 w0 ⇒
           listen_failed b ∨ (∃io. asleep_l0 b io) ∨
           ∃io. b = Diverge io ∧ (¬F1_io io ∨ accepts_fail_io io ∨ ¬accepts_below io))
End

(* The echo's L1 parameters on listener k *)
Overload elfd = “λk. n2w k : word64”
Overload epol = “pol_self echo_hw”
Overload eifds = “λk. interest [n2w k : word64]”
Overload esrv = “λk. srelabel (server k)”

(* The PF world: the post-listen world w1, reindexed by the blocking run *)
Overload epfw = “λk w1. reindex (btr (elfd k) epol (eifds k) (K F) (esrv k) (w1, pinit)) w1”

(* The PF run's standing facts and the PF echo's guarantee there, and the
   server's SQ; bquiet (echo_bquiet) and the world facts after the listen
   (listen_l0wf, listen_lone) are proved *)
Definition echo_pf_facts_def:
  echo_pf_facts KK k w1 ⇔
    run_ok (elfd k) epol (eifds k) (esrv k) (epfw k w1) ∧
    winv (epfw k w1) ∧ linv (elfd k) (epfw k w1) ∧ qfresh (epfw k w1) ∧
    MEM (elfd k) (l0_used (epfw k w1)) ∧
    (∀n. SND (pcm (elfd k) epol (eifds k) (esrv k) (epfw k w1) n) + 1 < dimword (:64)) ∧
    S1 (elfd k) epol (eifds k) (esrv k) (epfw k w1) ∧
    S2 (elfd k) epol (eifds k) (esrv k) (epfw k w1) ∧
    SQ (elfd k) epol (eifds k) (K F) (esrv k) (epfw k w1) ∧
    flush_ok (elfd k) epol (eifds k) (K F) (esrv k) w1 pinit ∧
    ∀io_p. ptrace (elfd k) epol (eifds k) (K F) (esrv k) w1 pinit io_p ⇒
           echo2_guar_l0 KK (epfw k w1) io_p
End

(* ------------------------------------------------------------------------
   The listen
   ------------------------------------------------------------------------ *)

Theorem listen_failed_echo:
  l0_rely w0 ∧ sys_listen_echo w0 = SOME (out, w1, ev) ∧ listen_fd out = NONE ⇒
  listen_failed (Terminate Success [ev])
Proof
  rw[sys_listen_echo_def, l0_do_def, AllCaseEqs(), listen_failed_def] >>
  drule_all l0_ffi_fn_length >> strip_tac >>
  simp[l0_ev_res_def, MAP_ZIP] >>
  gvs[listen_fd_def, l0_res_of_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

(* The world's arrivals (env) are fixed: no call changes them (as
   honestL0WorldProps's choices, ch) *)
Theorem deliver_env[local,simp]:
  (l0_deliver w a).env = w.env
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def, upd_lchan_def] >> every_case_tac >> simp[]
QED

Theorem FOLDL_deliver_env[local,simp]:
  ∀as w. (FOLDL l0_deliver w as).env = w.env
Proof
  Induct >> simp[]
QED

Theorem tick_env[local,simp]:
  (l0_tick nm w).env = w.env
Proof
  simp[l0_tick_def]
QED

Theorem ticks_env[local,simp]:
  ∀k w. (l0_ticks nm k w).env = w.env
Proof
  Induct >> simp[l0_ticks_def]
QED

Theorem upd_lchan_env[local,simp]:
  (upd_lchan j g w).env = w.env
Proof
  simp[upd_lchan_def]
QED

Theorem FOLDL_upd_env[local,simp]:
  ∀q w. (FOLDL (λw j. upd_lchan j (g j) w) w q).env = w.env
Proof
  Induct >> simp[]
QED

Theorem close_fd_env[local,simp]:
  (close_fd f w).env = w.env
Proof
  rw[close_fd_def] >> every_case_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac ‘FOLDL _ w0 q’ >>
  ‘∀q w0. (FOLDL (λw j. upd_lchan j (break_lchan E_CONNRESET F) w) w0 q).env = w0.env’
    by (Induct >> simp[]) >>
  simp[Abbr ‘w0’]
QED

Theorem ops_env[local]:
  (l0_listen p w = (x, w') ⇒ w'.env = w.env) ∧
  (l0_accept l w = (r, w') ⇒ w'.env = w.env) ∧
  (l0_recv f n w = (r, d, w') ⇒ w'.env = w.env) ∧
  (l0_send f bs w = (r, w') ⇒ w'.env = w.env) ∧
  (l0_shutdown f w = (r, w') ⇒ w'.env = w.env) ∧
  (l0_close f w = (r, w') ⇒ w'.env = w.env) ∧
  (l0_connect p w = (r, v, w') ⇒ w'.env = w.env) ∧
  (l0_connerr f w = (y, w') ⇒ w'.env = w.env)
Proof
  rpt conj_tac >> rw[l0_listen_def, l0_accept_def, l0_recv_def, l0_send_def,
                     l0_shutdown_def, l0_close_def, l0_connect_def, l0_connerr_def,
                     AllCaseEqs()] >> gvs[]
QED

Theorem l0_call_env[local]:
  l0_call n conf bytes w = SOME (FFIreturn bytes' w') ⇒ w'.env = w.env
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> imp_res_tac ops_env >> simp[]
QED

Theorem ffi_fn_env[local]:
  l0_ffi_fn n conf b w = SOME (FFIreturn out w') ⇒ w'.env = w.env
Proof
  rw[l0_ffi_fn_def, AllCaseEqs()] >> drule l0_call_env >> simp[]
QED

Theorem arrivals_finite_listen:
  sys_listen_echo w0 = SOME (out, w1, ev) ∧ arrivals_finite_l0 w0 ⇒ arrivals_finite_l0 w1
Proof
  rw[sys_listen_echo_def, l0_do_def, AllCaseEqs(), arrivals_finite_l0_def] >>
  drule ffi_fn_env >> simp[] >> metis_tac[]
QED

(* After the listen: the world is well formed, with the one listener *)
Theorem listen_l0wf:
  l0_server_world w0 ∧ sys_listen_echo w0 = SOME (out, w1, ev) ⇒ l0wf w1
Proof
  rw[sys_listen_echo_def, l0_do_def, AllCaseEqs()] >>
  irule l0wf_ffi_fn >> first_x_assum (irule_at Any) >>
  fs[l0_server_world_def, l0wf_def, used_chans_def]
QED

Theorem deliver_keys[local]:
  ∀as w. MAP FST (FOLDL l0_deliver w as).listeners = MAP FST w.listeners
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on ‘h’ >> simp[l0_deliver_def] >> rw[upd_lchan_def] >> every_case_tac >>
  simp[alistTheory.MAP_FST_AFUPDKEY]
QED

Theorem listen_lone:
  l0_server_world w0 ∧ sys_listen_echo w0 = SOME (out, w1, ev) ∧ listen_fd out = SOME k ⇒
  lone (n2w k) w1
Proof
  rw[sys_listen_echo_def, l0_do_def, l0_ffi_fn_def] >>
  ‘MAP FST (l0_tick «sys_listen» w0).listeners = []’
    by (REWRITE_TAC [l0_tick_def, deliver_keys] >> fs[l0_server_world_def]) >>
  gvs[AllCaseEqs(), l0_call_def, echo_port_conf_def]
  >- (‘dec_res (enc_res (Ok (w2n f)) ++ []) = SOME (Ok (w2n f))’
        by (irule dec_enc_res >> simp[l0_res_ok_def] >>
            assume_tac (INST_TYPE [alpha |-> “:64”] wordsTheory.w2n_lt) >> fs[]) >>
      gvs[listen_fd_def, l0_res_of_def] >>
      gvs[l0_listen_def, AllCaseEqs(), lone_def])
  >> PairCases_on ‘ke’ >>
  ‘n2w (err_code ke1) ≠ (0w:word8)’
    by (mp_tac (Q.INST [‘e’ |-> ‘ke1’] err_code_range) >> simp[wordsTheory.n2w_11]) >>
  gvs[enc_listen_fail_def, listen_fd_def, l0_res_of_def, dec_res_def, AllCaseEqs()]
QED

(* ------------------------------------------------------------------------
   The instance
   ------------------------------------------------------------------------ *)

(* MAIN: the claim's clause at one startup world *)
Theorem echo_l0b_quiet_world:
  l0_server_world w0 ∧
  (∀out w1 ev k. sys_listen_echo w0 = SOME (out, w1, ev) ∧ listen_fd out = SOME k ⇒
                 echo_pf_facts KK k w1) ⇒
  ∃b. semantics_prog (init_state (l0_ffi w0)) init_env echo_l0b_prog b ∧
      (listen_failed b ∨
       (∃io. b = Diverge io ∧ echo2_guar_l0 KK w0 io) ∨
       (∃io. asleep_l0 b io ∧ echo2_guar_l0 KK w0 (fromList io))) ∧
      (arrivals_finite_l0 w0 ⇒
       listen_failed b ∨ (∃io. asleep_l0 b io) ∨
       ∃io. b = Diverge io ∧ (¬F1_io io ∨ accepts_fail_io io))
Proof
  strip_tac >>
  ‘l0_rely w0 ∧ w0.hist = [] ∧ w0.listeners = []’ by fs[l0_server_world_def] >>
  drule_all echo_l0b_semantics_prog >> strip_tac
  >- ((* the listen fails *)
      qexists_tac ‘Terminate Success [ev]’ >> simp[] >>
      drule_all listen_failed_echo >> simp[]) >>
  (* the listen succeeds: the loop's facts, in the PF world *)
  first_x_assum drule_all >> simp[echo_pf_facts_def] >> strip_tac >>
  ‘l0wf w1 ∧ lone (elfd k) w1’ by metis_tac[listen_l0wf, listen_lone] >>
  ‘bquiet (esrv k) (eifds k) (K F)’ by simp[echo_bquiet] >>
  drule_all sys_listen_echo_shift >> strip_tac >>
  ‘l0_reach w0 w1’
    by (‘l0_reach w0 w0’ by simp[l0_reach_init] >>
        gvs[sys_listen_echo_def, l0_do_def, AllCaseEqs()] >> metis_tac[l0_reach_step]) >>
  ‘l0_rely w1’ by fs[l0_reach_def] >>
  ‘bt_guard (elfd k) echo_hw (eifds k) (esrv k) (w1, pinit)’
    by (irule bt_guard_ok >> simp[]) >>
  drule pf_trace_exists >> strip_tac >>
  ‘ptrace (elfd k) epol (eifds k) (K F) (esrv k) w1 pinit io’ by simp[ptrace_def] >>
  ‘echo2_guar_l0 KK (epfw k w1) io’ by metis_tac[] >>
  ‘∀n. SND (pcm (elfd k) epol (eifds k) (esrv k) (epfw k w1) n) + 1 < dimword (:64)’
    by fs[]
  >- ((* the loop never sleeps: the program diverges *)
      qexists_tac ‘Diverge (LCONS ev (echo_l0b_run k w1))’ >> simp[] >>
      drule_all div_btrace >> strip_tac >>
      drule_all l1b_quiet >> strip_tac >>
      conj_tac >- (disj2_tac >> disj1_tac >> irule echo2_guar_shift >> simp[] >> metis_tac[]) >>
      strip_tac >> drule_all arrivals_finite_listen >> strip_tac >>
      qpat_x_assum ‘arrivals_finite_l0 w1 ⇒ _’ drule >> strip_tac
      >- metis_tac[F1_shift]
      >- metis_tac[accepts_fail_shift]
      >> drule bt_guard_brounds >> disch_then (qspec_then ‘n’ mp_tac) >>
         qpat_x_assum ‘bt_awake _ _ _ _ _’
           (qspec_then ‘n’ strip_assume_tac o REWRITE_RULE [bt_awake_def]) >>
         simp[]) >>
  (* the loop sleeps in round n: the program stops in the final poll *)
  qexists_tac ‘Terminate (FFI_outcome (Final_event (ExtCall «sys_poll») (FST cb) (SND cb)
                                         FFI_diverged)) (ev :: evs)’ >> simp[] >>
  ‘asleep_l0 (Terminate (FFI_outcome (Final_event (ExtCall «sys_poll») (FST cb) (SND cb)
                                         FFI_diverged)) (ev :: evs)) (ev :: evs)’
    by simp[asleep_l0_def] >>
  drule_all sleep_btrace >> strip_tac >>
  drule_all l1b_quiet >> strip_tac >>
  ‘echo2_guar_l0 KK w0 (fromList (ev :: evs))’
    by (‘fromList (ev :: evs) = LCONS ev (fromList evs)’ by simp[] >>
        pop_assum SUBST1_TAC >> irule echo2_guar_shift >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

(* MAIN: the claim (L3-00's quiet_on_kernel_claim, with D29's cut-off
   excuse since c2b12a300, which this instance does not need), under the
   facts at every startup world *)
Theorem echo_l0b_quiet:
  (∀w0 out w1 ev k. l0_server_world w0 ∧ sys_listen_echo w0 = SOME (out, w1, ev) ∧
                    listen_fd out = SOME k ⇒ echo_pf_facts KK k w1) ⇒
  quiet_on_kernel_claim (echo2_guar_l0 KK) echo_l0b_prog
Proof
  rw[quiet_on_kernel_claim_def] >>
  ‘∃b. semantics_prog (init_state (l0_ffi w0)) init_env echo_l0b_prog b ∧
       (listen_failed b ∨
        (∃io. b = Diverge io ∧ echo2_guar_l0 KK w0 io) ∨
        (∃io. asleep_l0 b io ∧ echo2_guar_l0 KK w0 (fromList io))) ∧
       (arrivals_finite_l0 w0 ⇒
        listen_failed b ∨ (∃io. asleep_l0 b io) ∨
        ∃io. b = Diverge io ∧ (¬F1_io io ∨ accepts_fail_io io))’
    by (irule echo_l0b_quiet_world >> metis_tac[]) >>
  qexists_tac ‘b’ >> metis_tac[]
QED

(* The amended form (#3) follows *)
Theorem echo_l0b_quiet_a:
  (∀w0 out w1 ev k. l0_server_world w0 ∧ sys_listen_echo w0 = SOME (out, w1, ev) ∧
                    listen_fd out = SOME k ⇒ echo_pf_facts KK k w1) ⇒
  quiet_on_kernel_claim_a (echo2_guar_l0 KK) echo_l0b_prog
Proof
  strip_tac >> drule echo_l0b_quiet >>
  simp[quiet_on_kernel_claim_def, quiet_on_kernel_claim_a_def]
QED
