(*
  L3-09 (S5): quiet_on_kernel for the blocking echo program, as a
  corollary under the PF run's standing facts and the PF echo's guarantee
  (async-spike's loop-level liveness, the KV worker's safety), read in the
  reindexed post-listen world (echo_pf_facts).  Nothing here is trusted:
  every fact used is a hypothesis of the final theorem.

  The program first checks fds 0, 1 and 2 with sys_fdok (D33): if one is
  closed the run is stdio_closed; else the listen runs in the world after
  the three checks (stdio_prefix), and the guarantee moves across the
  four setup events (honestL1BShift).

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
  honestEchoL0BStutter honestL0Fdok honestL1PFRefine
Libs
  preamble

(* honestL0Outcome's stdio_closed is loaded too (via honestEchoL0Sem); the
   claim reads this copy's *)
val _ = bring_to_front_overload "stdio_closed" {Name = "stdio_closed", Thy = "honestL1BStmts"};

(* The claim, with amendment #3 (D29).  Since L3-00 c2b12a300 (and with
   D33's stdio_closed since 907c32fdc) this is quiet_on_kernel_claim; kept
   because D29 cites it *)
Definition quiet_on_kernel_claim_a_def:
  quiet_on_kernel_claim_a guar prog ⇔
    ∀w0. l0_server_world w0 ⇒
      ∃b. semantics_prog (init_state (l0_ffi w0)) init_env prog b ∧
          (stdio_closed b ∨ listen_failed b ∨
           (∃io. b = Diverge io ∧ guar w0 io) ∨
           (∃io. asleep_l0 b io ∧ guar w0 (fromList io))) ∧
          (arrivals_finite_l0 w0 ⇒
           stdio_closed b ∨ listen_failed b ∨ (∃io. asleep_l0 b io) ∨
           ∃io. b = Diverge io ∧ (¬F1_io io ∨ accepts_fail_io io ∨ ¬accepts_below io))
End

(* The echo's L1 parameters on listener k *)
Overload elfd = “λk. n2w k : word64”
Overload epol = “pol_self echo_hw”
Overload eifds = “λk. asyncM4LiveInterest$live [n2w k : word64] (log_of (srelabel (server k)))”
Overload esrv = “λk. srelabel (server k)”

(* The PF world: the post-listen world w1, reindexed by the blocking run *)
Overload epfw = “λk w1. reindex (btr (elfd k) epol (eifds k) (K F) (esrv k) (w1, pinit)) w1”

(* The world w3 after main's three sys_fdok calls from w0, all answering
   open (D33) *)
Definition stdio_prefix_def:
  stdio_prefix w0 w3 ⇔
    ∃o0 w1 e0 o1 w2 e1 o2 e2.
      l0_do «sys_fdok» [0w] 1 w0 = SOME (o0, w1, e0) ∧
      l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1) ∧
      l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2) ∧ stdio_all o0 o1 o2
End

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
    ∀io_p. ptrace (elfd k) epol (eifds k) (K F) (esrv k) w1 pinit io_p ⇒
           echo2_guar_l0 KK (epfw k w1) io_p
End

(* ------------------------------------------------------------------------
   The stdio checks and the listen
   ------------------------------------------------------------------------ *)

(* A closed stdio fd: the run is stdio_closed (as honestL0Fdok's
   fdok_closed, for this copy of stdio_closed) *)
Theorem stdio_closed_echo:
  l0_do «sys_fdok» [0w] 1 w0 = SOME (o0, w1, e0) ∧
  l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1) ∧
  l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2) ∧ ¬stdio_all o0 o1 o2 ⇒
  stdio_closed (Terminate Success [e0; e1; e2])
Proof
  rw[fdok_do, honestL1BStmtsTheory.stdio_closed_def, stdio_all_def] >> rw[] >> fs[]
QED

(* An open stdio fd's check, as listen_failed records it *)
Theorem fdok_open_ev[local]:
  l0_do «sys_fdok» [f] 1 w = SOME ([1w], w', ev) ⇒
  ev = IO_event (ExtCall «sys_fdok») [f] [(0w, 1w)]
Proof
  rw[fdok_do]
QED

Theorem listen_failed_echo:
  l0_do «sys_fdok» [0w] 1 w0 = SOME (o0, w1, e0) ∧
  l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1) ∧
  l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2) ∧ stdio_all o0 o1 o2 ∧
  l0_rely w3 ∧ sys_listen_echo w3 = SOME (out, w4, ev) ∧ listen_fd out = NONE ⇒
  listen_failed (Terminate Success [e0; e1; e2; ev])
Proof
  rw[stdio_all_def] >> imp_res_tac fdok_open_ev >> rveq >>
  qpat_x_assum ‘sys_listen_echo _ = _’ mp_tac >>
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

Theorem arrivals_finite_do[local]:
  l0_do n conf alen w0 = SOME (out, w1, ev) ∧ arrivals_finite_l0 w0 ⇒ arrivals_finite_l0 w1
Proof
  rw[l0_do_def, AllCaseEqs(), arrivals_finite_l0_def] >>
  drule ffi_fn_env >> simp[] >> metis_tac[]
QED

Theorem arrivals_finite_listen:
  sys_listen_echo w0 = SOME (out, w1, ev) ∧ arrivals_finite_l0 w0 ⇒ arrivals_finite_l0 w1
Proof
  rw[sys_listen_echo_def] >> metis_tac[arrivals_finite_do]
QED

(* After the listen from a fresh world: the world is well formed, with
   the one listener *)
Theorem listen_l0wf:
  l0_fresh_world w0 ∧ sys_listen_echo w0 = SOME (out, w1, ev) ⇒ l0wf w1
Proof
  rw[sys_listen_echo_def, l0_do_def, AllCaseEqs()] >>
  irule l0wf_ffi_fn >> first_x_assum (irule_at Any) >>
  fs[l0_fresh_world_def, l0wf_def, used_chans_def]
QED

Theorem deliver_keys[local]:
  ∀as w. MAP FST (FOLDL l0_deliver w as).listeners = MAP FST w.listeners
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on ‘h’ >> simp[l0_deliver_def] >> rw[upd_lchan_def] >> every_case_tac >>
  simp[alistTheory.MAP_FST_AFUPDKEY]
QED

Theorem listen_lone:
  l0_fresh_world w0 ∧ sys_listen_echo w0 = SOME (out, w1, ev) ∧ listen_fd out = SOME k ⇒
  lone (n2w k) w1
Proof
  rw[sys_listen_echo_def, l0_do_def, l0_ffi_fn_def] >>
  ‘MAP FST (l0_tick «sys_listen» w0).listeners = []’
    by (REWRITE_TAC [l0_tick_def, deliver_keys] >> fs[l0_fresh_world_def]) >>
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
   Across the four setup events
   ------------------------------------------------------------------------ *)

(* The world facts along the stdio checks, from a fresh relied-on world *)
Theorem stdio_worlds[local]:
  l0_rely w0 ∧ l0_fresh_world w0 ∧
  l0_do «sys_fdok» [0w] 1 w0 = SOME (o0, w1, e0) ∧
  l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1) ∧
  l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2) ⇒
  l0_rely w1 ∧ l0_rely w2 ∧ l0_rely w3 ∧
  l0_fresh_world w1 ∧ l0_fresh_world w2 ∧ l0_fresh_world w3
Proof
  strip_tac >>
  ‘l0_rely w1’ by (irule l0_do_rely >> metis_tac[]) >>
  ‘l0_rely w2’ by (irule l0_do_rely >> metis_tac[]) >>
  ‘l0_rely w3’ by (irule l0_do_rely >> metis_tac[]) >>
  ‘l0_fresh_world w1’ by metis_tac[fdok_fresh_step] >>
  ‘l0_fresh_world w2’ by metis_tac[fdok_fresh_step] >>
  ‘l0_fresh_world w3’ by metis_tac[fdok_fresh_step] >>
  simp[]
QED

(* The guarantee across the three checks and the listen *)
Theorem echo2_guar_setup:
  l0_rely w0 ∧ l0_fresh_world w0 ∧
  l0_do «sys_fdok» [0w] 1 w0 = SOME (o0, w1, e0) ∧
  l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1) ∧
  l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2) ∧
  sys_listen_echo w3 = SOME (out, w4, ev) ∧ echo2_guar_l0 KK w4 io ⇒
  echo2_guar_l0 KK w0 (LCONS e0 (LCONS e1 (LCONS e2 (LCONS ev io))))
Proof
  strip_tac >> drule_all stdio_worlds >> strip_tac >>
  qpat_x_assum ‘l0_do _ [0w] _ _ = _’ (strip_assume_tac o MATCH_MP fdok_shift_ev o
    CONJ (ASSUME “l0_rely w0”)) >>
  qpat_x_assum ‘l0_do _ [1w] _ _ = _’ (strip_assume_tac o MATCH_MP fdok_shift_ev o
    CONJ (ASSUME “l0_rely w1”)) >>
  qpat_x_assum ‘l0_do _ [2w] _ _ = _’ (strip_assume_tac o MATCH_MP fdok_shift_ev o
    CONJ (ASSUME “l0_rely w2”)) >>
  qpat_x_assum ‘sys_listen_echo _ = _’ (strip_assume_tac o MATCH_MP sys_listen_echo_shift o
    CONJ (ASSUME “l0_rely w3”)) >>
  fs[l0_fresh_world_def] >>
  irule echo2_guar_shift >> simp[] >>
  irule echo2_guar_shift >> simp[] >>
  irule echo2_guar_shift >> simp[] >>
  irule echo2_guar_shift >> simp[]
QED

Theorem F1_setup[local]:
  F1_io (LCONS e0 (LCONS e1 (LCONS e2 (LCONS ev io)))) ⇒ F1_io io
Proof
  metis_tac[F1_shift]
QED

Theorem accepts_fail_setup[local]:
  accepts_fail_io io ⇒ accepts_fail_io (LCONS e0 (LCONS e1 (LCONS e2 (LCONS ev io))))
Proof
  metis_tac[accepts_fail_shift]
QED

Theorem arrivals_finite_setup[local]:
  l0_do «sys_fdok» [0w] 1 w0 = SOME (o0, w1, e0) ∧
  l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1) ∧
  l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2) ∧
  sys_listen_echo w3 = SOME (out, w4, ev) ∧ arrivals_finite_l0 w0 ⇒ arrivals_finite_l0 w4
Proof
  metis_tac[arrivals_finite_do, arrivals_finite_listen]
QED

(* ------------------------------------------------------------------------
   The instance
   ------------------------------------------------------------------------ *)

(* MAIN: the claim's clause at one startup world *)
Theorem echo_l0b_quiet_world:
  l0_server_world w0 ∧
  (∀w3 out w4 ev k. stdio_prefix w0 w3 ∧ sys_listen_echo w3 = SOME (out, w4, ev) ∧
                    listen_fd out = SOME k ⇒ echo_pf_facts KK k w4) ⇒
  ∃b. semantics_prog (init_state (l0_ffi w0)) init_env echo_l0b_prog b ∧
      (stdio_closed b ∨ listen_failed b ∨
       (∃io. b = Diverge io ∧ echo2_guar_l0 KK w0 io) ∨
       (∃io. asleep_l0 b io ∧ echo2_guar_l0 KK w0 (fromList io))) ∧
      (arrivals_finite_l0 w0 ⇒
       stdio_closed b ∨ listen_failed b ∨ (∃io. asleep_l0 b io) ∨
       ∃io. b = Diverge io ∧ (¬F1_io io ∨ accepts_fail_io io))
Proof
  strip_tac >>
  ‘l0_rely w0 ∧ w0.hist = [] ∧ l0_fresh_world w0’
    by fs[l0_server_world_def, l0_fresh_world_def] >>
  drule_all echo_l0b_semantics_prog >> strip_tac
  >- ((* a stdio fd is closed *)
      qexists_tac ‘Terminate Success [e0; e1; e2]’ >> simp[] >>
      drule_all stdio_closed_echo >> simp[]) >>
  drule_all stdio_worlds >> strip_tac
  >- ((* the listen fails *)
      qexists_tac ‘Terminate Success [e0; e1; e2; ev]’ >> simp[] >>
      drule_all listen_failed_echo >> simp[]) >>
  (* the listen succeeds: the loop's facts, in the PF world *)
  first_x_assum (qspecl_then [‘w3’, ‘out’, ‘w4’, ‘ev’, ‘k’] mp_tac) >>
  (impl_tac
   >- (simp[stdio_prefix_def] >>
       qexistsl [‘o0’, ‘w1’, ‘e0’, ‘o1’, ‘w2’, ‘e1’, ‘o2’, ‘e2’] >> simp[])) >>
  simp[echo_pf_facts_def] >> strip_tac >>
  ‘l0wf w4 ∧ lone (elfd k) w4’ by metis_tac[listen_l0wf, listen_lone] >>
  ‘bquiet (esrv k) (eifds k) (K F)’ by simp[echo_bquiet_live] >>
  ‘l0_rely w4’ by (irule l0_do_rely >> fs[sys_listen_echo_def] >> metis_tac[]) >>
  ‘bt_guard (elfd k) echo_hw (eifds k) (esrv k) (w4, pinit)’
    by (irule bt_guard_ok >> simp[]) >>
  drule pf_trace_exists >> strip_tac >>
  ‘ptrace (elfd k) epol (eifds k) (K F) (esrv k) w4 pinit io’ by simp[ptrace_def] >>
  ‘echo2_guar_l0 KK (epfw k w4) io’ by metis_tac[] >>
  ‘∀n. SND (pcm (elfd k) epol (eifds k) (esrv k) (epfw k w4) n) + 1 < dimword (:64)’
    by fs[] >>
  ‘∀ps f. outbox_of ps.b f = [] ⇒ ¬epol ps f’ by simp[pol_self_def]
  >- ((* the loop never sleeps: the program diverges *)
      qexists_tac ‘Diverge (LAPPEND (fromList [e0; e1; e2; ev]) (echo_l0b_run k w4))’ >> simp[] >>
      drule_all div_btrace >> strip_tac >>
      drule_all l1b_quiet >> strip_tac >>
      conj_tac
      >- (disj2_tac >> disj2_tac >> disj1_tac >> irule echo2_guar_setup >> simp[] >>
          metis_tac[]) >>
      strip_tac >> drule_all arrivals_finite_setup >> strip_tac >>
      qpat_x_assum ‘arrivals_finite_l0 w4 ⇒ _’ drule >> strip_tac
      >- metis_tac[F1_setup]
      >- metis_tac[accepts_fail_setup]
      >> drule bt_guard_brounds >> disch_then (qspec_then ‘n’ mp_tac) >>
         qpat_x_assum ‘bt_awake _ _ _ _ _’
           (qspec_then ‘n’ strip_assume_tac o REWRITE_RULE [bt_awake_def]) >>
         simp[]) >>
  (* the loop sleeps in round n: the program stops in the final poll *)
  qexists_tac ‘Terminate (FFI_outcome (Final_event (ExtCall «sys_poll») (FST cb) (SND cb)
                                         FFI_diverged)) ([e0; e1; e2; ev] ++ evs)’ >> simp[] >>
  ‘asleep_l0 (Terminate (FFI_outcome (Final_event (ExtCall «sys_poll») (FST cb) (SND cb)
                                         FFI_diverged)) (e0 :: e1 :: e2 :: ev :: evs))
             (e0 :: e1 :: e2 :: ev :: evs)’
    by simp[asleep_l0_def] >>
  drule_all sleep_btrace >> strip_tac >>
  drule_all l1b_quiet >> strip_tac >>
  ‘echo2_guar_l0 KK w0 (fromList (e0 :: e1 :: e2 :: ev :: evs))’
    by (‘fromList (e0 :: e1 :: e2 :: ev :: evs) =
         LCONS e0 (LCONS e1 (LCONS e2 (LCONS ev (fromList evs))))’ by simp[] >>
        pop_assum SUBST1_TAC >> irule echo2_guar_setup >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

(* MAIN: the claim (L3-00's quiet_on_kernel_claim, with D29's cut-off
   excuse since c2b12a300, which this instance does not need, and D33's
   stdio_closed since 907c32fdc), under the facts at every startup world *)
Theorem echo_l0b_quiet:
  (∀w0 w3 out w4 ev k. l0_server_world w0 ∧ stdio_prefix w0 w3 ∧
                       sys_listen_echo w3 = SOME (out, w4, ev) ∧
                       listen_fd out = SOME k ⇒ echo_pf_facts KK k w4) ⇒
  quiet_on_kernel_claim (echo2_guar_l0 KK) echo_l0b_prog
Proof
  rw[quiet_on_kernel_claim_def] >>
  ‘∃b. semantics_prog (init_state (l0_ffi w0)) init_env echo_l0b_prog b ∧
       (stdio_closed b ∨ listen_failed b ∨
        (∃io. b = Diverge io ∧ echo2_guar_l0 KK w0 io) ∨
        (∃io. asleep_l0 b io ∧ echo2_guar_l0 KK w0 (fromList io))) ∧
       (arrivals_finite_l0 w0 ⇒
        stdio_closed b ∨ listen_failed b ∨ (∃io. asleep_l0 b io) ∨
        ∃io. b = Diverge io ∧ (¬F1_io io ∨ accepts_fail_io io))’
    by (irule echo_l0b_quiet_world >> metis_tac[]) >>
  qexists_tac ‘b’ >> metis_tac[]
QED

(* The amended form (#3) follows *)
Theorem echo_l0b_quiet_a:
  (∀w0 w3 out w4 ev k. l0_server_world w0 ∧ stdio_prefix w0 w3 ∧
                       sys_listen_echo w3 = SOME (out, w4, ev) ∧
                       listen_fd out = SOME k ⇒ echo_pf_facts KK k w4) ⇒
  quiet_on_kernel_claim_a (echo2_guar_l0 KK) echo_l0b_prog
Proof
  strip_tac >> drule echo_l0b_quiet >>
  simp[quiet_on_kernel_claim_def, quiet_on_kernel_claim_a_def]
QED
