(*
  L3-08: the PF echo program meets R4′ (l0_echo2_claim, K = pf_sendwait).
  D25′ (no loop guard, the listener's room test in the model) leaves no
  standing hypotheses: the PF run's run_ok holds in the world after the
  listen (echo_run_ok: the server's actions are well formed, server_pt_ok),
  and the world facts there are honestEchoL0Setup's post_listen_facts.

  - echo_l0_run_pftrace: the loop's trace after the listen is the PF
    model run's (pftrace), so honest-echo-live's chain applies there
    (echo_live_l0_pf, echo_conn_live_trace): echo_live_w4;
  - live_setup: across the three stdio checks and the listen
    (honestL1BShift);
  - safety and stdio_kept: the KV worker's echo_l0_safe, matched to this
    run since program semantics are deterministic.

  MAIN: echo_live_prog_world, echo_l0_echo2_claim.
*)
Theory honestEchoL0LiveProg
Ancestors
  llist rich_list asyncM4GTrans
  honestEchoL0Setup honestEchoL0Inv honestEchoL0TraceWrap honestL1BCorr honestL1BShift honestL1BStmts
  honestEchoL0LiveL0 honestEchoL0Live honestEchoL0Obl honestL1PFConnTrace honestL1PFFlush
  honestEchoL0Safe honestEchoL0Sem honestEchoL0Main honestEchoL0Spec honestEchoL0Prog honestL1PFSpec
  honestL1PFProg honestL1PFLive honestL1PFInv honestL1PFModel honestL1Inv honestL1Model honestL0Fdok honestL0Outcome honestL0WorldProps
  semanticsProps
Libs
  preamble

(* The echo loop's PF run after the listen on k (as honestEchoL0BQuiet) *)
Overload elfd = “λk. n2w k : word64”
Overload epol = “pol_self echo_hw”
Overload eifds = “λk. asyncM4LiveInterest$live [n2w k : word64] (log_of (srelabel (server k)))”
Overload esrv = “λk. srelabel (server k)”

(* ------------------------------------------------------------------------
   The PF run's standing facts hold after the listen (D25′)
   ------------------------------------------------------------------------ *)

Theorem echo_run_ok:
  l0_rely w3 ∧ sys_listen_echo w3 = SOME (out, w4, ev) ∧ listen_fd out = SOME k ⇒
  run_ok (elfd k) epol (eifds k) (esrv k) w4
Proof
  strip_tac >>
  ‘k < 2147483648’ by metis_tac[listen_fd_small] >>
  ‘l0_rely w4’ by (gvs[sys_listen_echo_def] >> metis_tac[l0_do_rely]) >>
  simp[run_ok_def, GSYM pt_ok_pl2_ok, server_pt_ok] >>
  simp[psmall_def, pinit_def, l1init_def, small_fds_def, small_def]
QED

(* ------------------------------------------------------------------------
   The loop's trace is the PF model run's
   ------------------------------------------------------------------------ *)

(* Prefixes of a flattened list of rounds (as honestL1BTrace's) *)
Theorem LENGTH_FLAT_GENLIST_mono[local]:
  ∀n m. n ≤ m ⇒ LENGTH (FLAT (GENLIST f n)) ≤ LENGTH (FLAT (GENLIST f m))
Proof
  Induct_on ‘m’ >> rw[] >> Cases_on ‘n = SUC m’ >> gvs[GENLIST, FLAT_SNOC] >>
  first_x_assum (qspec_then ‘n’ mp_tac) >> simp[]
QED

Theorem FLAT_GENLIST_bounded[local]:
  (∀n. LENGTH (FLAT (GENLIST f n)) < b) ⇒ ∃N. ∀i. N ≤ i ⇒ f i = []
Proof
  strip_tac >>
  ‘∃n. ∀m. LENGTH (FLAT (GENLIST f m)) ≤ LENGTH (FLAT (GENLIST f n))’
    by (CCONTR_TAC >> fs[NOT_LESS_EQUAL] >>
        ‘∀k. ∃m. k ≤ LENGTH (FLAT (GENLIST f m))’
          by (Induct >- simp[] >>
              pop_assum strip_assume_tac >>
              qpat_assum ‘∀n. ∃m. _’ (qspec_then ‘m’ strip_assume_tac) >>
              qexists_tac ‘m'’ >> simp[]) >>
        pop_assum (qspec_then ‘b’ strip_assume_tac) >>
        qpat_x_assum ‘∀n. LENGTH _ < b’ (qspec_then ‘m’ mp_tac) >> simp[]) >>
  qexists_tac ‘n’ >> rpt strip_tac >>
  ‘LENGTH (FLAT (GENLIST f n)) ≤ LENGTH (FLAT (GENLIST f i))’
    by (irule LENGTH_FLAT_GENLIST_mono >> simp[]) >>
  first_x_assum (qspec_then ‘SUC i’ mp_tac) >>
  simp[GENLIST, FLAT_SNOC] >> strip_tac >> Cases_on ‘f i’ >> fs[]
QED

Theorem LPREFIX_fromList_LAPPEND[local]:
  ∀X p. LPREFIX (fromList p) (LAPPEND (fromList X) R) ⇔
          p ≼ X ∨ ∃t. p = X ++ t ∧ LPREFIX (fromList t) R
Proof
  Induct >> simp[]
  >- (Cases >> simp[]) >>
  rpt gen_tac >> Cases_on ‘p’ >> simp[LPREFIX_LCONS] >> metis_tac[]
QED

Theorem LPREFIX_LFLATTEN[local]:
  LPREFIX (fromList p) (LFLATTEN (LGENLIST (λi. fromList (f i)) NONE)) ⇔
    ∃n. p ≼ FLAT (GENLIST f n)
Proof
  eq_tac >> strip_tac
  >- (Cases_on ‘∃n. LENGTH p ≤ LENGTH (FLAT (GENLIST f n))’
      >- (fs[] >> qexists_tac ‘n’ >>
          qpat_x_assum ‘LPREFIX _ _’ mp_tac >>
          ONCE_REWRITE_TAC [Q.SPEC ‘n’ (Q.GEN ‘n’ LFLATTEN_LGENLIST_chunk)] >>
          rw[LPREFIX_fromList_LAPPEND] >> fs[] >>
          ‘t = []’ by (Cases_on ‘t’ >> fs[]) >> simp[]) >>
      fs[NOT_LESS_EQUAL] >>
      drule FLAT_GENLIST_bounded >> strip_tac >>
      qexists_tac ‘N’ >>
      qpat_x_assum ‘LPREFIX _ _’ mp_tac >>
      ONCE_REWRITE_TAC [Q.SPEC ‘N’ (Q.GEN ‘n’ LFLATTEN_LGENLIST_chunk)] >>
      ‘LFLATTEN (LGENLIST (λi. fromList (f (N + i))) NONE) = [||]’
        by simp[LFLATTEN_EQ_NIL, every_LGENLIST] >>
      simp[LPREFIX_fromList_LAPPEND] >> rw[] >> simp[] >>
      Cases_on ‘t’ >> fs[LPREFIX_LCONS]) >>
  ONCE_REWRITE_TAC [Q.SPEC ‘n’ (Q.GEN ‘n’ LFLATTEN_LGENLIST_chunk)] >>
  simp[LPREFIX_fromList_LAPPEND]
QED

Theorem echo_l0_run_pftrace:
  run_ok (elfd k) epol (eifds k) (esrv k) w ⇒
  pftrace (elfd k) epol (eifds k) (esrv k) w (echo_l0_run k w)
Proof
  strip_tac >>
  drule prun_some >> strip_tac >>
  ‘∀n. prounds (elfd k) epol (eifds k) (esrv k) (w, pinit) n ≠ NONE’ by simp[] >>
  drule prun_FLAT >> strip_tac >>
  ‘∀n. FLAT (GENLIST (λi. pround_evs (elfd k) echo_hw (eifds k) (esrv k) (w,pinit) i) n) =
       FST (SND (SND (honestL1PFLive$prun (elfd k) epol (eifds k) (esrv k) w n)))’
    by (gen_tac >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
        asm_rewrite_tac [honestL1PFSpecTheory.prun_def, optionTheory.THE_DEF]) >>
  simp[pftrace_def, LPREFIX_LFLATTEN, ppre_def] >>
  gen_tac >> eq_tac >> strip_tac
  >- (qexists_tac ‘n’ >>
      Cases_on ‘honestL1PFLive$prun (elfd k) epol (eifds k) (esrv k) w n’ >>
      PairCases_on ‘r’ >> gvs[])
  >> qexists_tac ‘N’ >> simp[]
QED

(* ------------------------------------------------------------------------
   Liveness in the world after the listen
   ------------------------------------------------------------------------ *)

Theorem echo_live_unless_l3[local]:
  l3_echo_live_l0 KK w io ⇔ echo_live_l0 KK w io
Proof
  simp[l3_echo_live_l0_def, l3_echo_live_unless_def, echo_live_l0_def, echo_live_unless_def,
       honestEchoL0TraceWrapTheory.flushed_open_def, honestL1BStmtsTheory.flushed_open_def]
QED

Theorem F2_flush[local]:
  honestL1BStmts$F2 w ⇔ honestL1PFFlush$F2 w
Proof
  simp[honestL1BStmtsTheory.F2_def, honestL1PFFlushTheory.F2_def]
QED

Theorem echo_live_w4:
  run_ok (elfd k) epol (eifds k) (esrv k) w ∧ winv w ∧ linv (elfd k) w ∧ qfresh w ∧ qinb w ∧ nshut w ∧
  MEM (elfd k) (l0_used w) ∧ lone (elfd k) w ∧ k < dimword (:64) ∧
  F1_io (echo_l0_run k w) ∧ honestL1BStmts$F2 w ∧ accepts_below (echo_l0_run k w) ⇒
  echo_live_l0 pf_sendwait w (echo_l0_run k w) ∧ conn_live_l0 w (echo_l0_run k w)
Proof
  strip_tac >>
  drule echo_l0_run_pftrace >> strip_tac >>
  ‘∀n. SND (pcm (elfd k) epol (eifds k) (esrv k) w n) + 1 < dimword (:64)’
    by (irule pcm_bound_accepts_below >> metis_tac[]) >>
  ‘echo_run k epol w’
    by (PURE_REWRITE_TAC [echo_run_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rewrite_tac [GSYM echo_live_unless_l3] >> irule echo_live_l0_pf >>
      rewrite_tac [GSYM F2_flush] >> asm_rewrite_tac [] >> qexistsl [‘echo_hw’, ‘k’, ‘epol’] >>
      simp[pol_ok_self] >> irule F1_io_F1 >> conj_tac >- first_assum ACCEPT_TAC >>
      qexists_tac ‘echo_l0_run k w’ >> conj_tac >> first_assum ACCEPT_TAC) >>
  irule echo_conn_live_trace >> asm_rewrite_tac [] >> qexistsl [‘k’, ‘epol’] >> simp[]
QED

(* ------------------------------------------------------------------------
   Across the three stdio checks and the listen
   ------------------------------------------------------------------------ *)

Theorem live_shift[local]:
  setup_ev ev ∧ l0_step (SOME W0) (ev_lcall ev) = SOME w1 ∧ W0.listeners = [] ∧
  (F1_io io ∧ honestL1BStmts$F2 w1 ∧ accepts_below io ⇒
   echo_live_l0 KK w1 io ∧ conn_live_l0 w1 io) ⇒
  F1_io (LCONS ev io) ∧ honestL1BStmts$F2 W0 ∧ accepts_below (LCONS ev io) ⇒
  echo_live_l0 KK W0 (LCONS ev io) ∧ conn_live_l0 W0 (LCONS ev io)
Proof
  rpt strip_tac >>
  ‘F1_io io ∧ honestL1BStmts$F2 w1 ∧ accepts_below io’
    by metis_tac[F1_shift, F2_shift, accepts_below_shift] >>
  metis_tac[echo_live_shift, conn_live_shift]
QED

Theorem live_setup:
  l0_rely w0 ∧ l0_fresh_world w0 ∧
  l0_do «sys_fdok» [0w] 1 w0 = SOME (o0, w1, e0) ∧
  l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1) ∧
  l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2) ∧
  sys_listen_echo w3 = SOME (out, w4, ev) ∧
  (F1_io io ∧ honestL1BStmts$F2 w4 ∧ accepts_below io ⇒
   echo_live_l0 KK w4 io ∧ conn_live_l0 w4 io) ⇒
  let io0 = LCONS e0 (LCONS e1 (LCONS e2 (LCONS ev io))) in
  F1_io io0 ∧ honestL1BStmts$F2 w0 ∧ accepts_below io0 ⇒
  echo_live_l0 KK w0 io0 ∧ conn_live_l0 w0 io0
Proof
  strip_tac >>
  ‘l0_rely w1’ by (irule l0_do_rely >> metis_tac[]) >>
  ‘l0_rely w2’ by (irule l0_do_rely >> metis_tac[]) >>
  ‘l0_rely w3’ by (irule l0_do_rely >> metis_tac[]) >>
  ‘l0_fresh_world w1’ by metis_tac[fdok_fresh_step] >>
  ‘l0_fresh_world w2’ by metis_tac[fdok_fresh_step] >>
  ‘l0_fresh_world w3’ by metis_tac[fdok_fresh_step] >>
  qpat_x_assum ‘l0_do _ [0w] _ _ = _’ (strip_assume_tac o MATCH_MP fdok_shift_ev o
    CONJ (ASSUME “l0_rely w0”)) >>
  qpat_x_assum ‘l0_do _ [1w] _ _ = _’ (strip_assume_tac o MATCH_MP fdok_shift_ev o
    CONJ (ASSUME “l0_rely w1”)) >>
  qpat_x_assum ‘l0_do _ [2w] _ _ = _’ (strip_assume_tac o MATCH_MP fdok_shift_ev o
    CONJ (ASSUME “l0_rely w2”)) >>
  qpat_x_assum ‘sys_listen_echo _ = _’ (strip_assume_tac o MATCH_MP sys_listen_echo_shift o
    CONJ (ASSUME “l0_rely w3”)) >>
  fs[l0_fresh_world_def] >> simp[] >>
  mp_tac (Q.INST [‘W0’ |-> ‘w3’, ‘w1’ |-> ‘w4’] live_shift) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  mp_tac (Q.INST [‘ev’ |-> ‘e2’, ‘W0’ |-> ‘w2’, ‘w1’ |-> ‘w3’, ‘io’ |-> ‘LCONS ev io’]
            live_shift) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  mp_tac (Q.INST [‘ev’ |-> ‘e1’, ‘W0’ |-> ‘w1’, ‘w1’ |-> ‘w2’,
                  ‘io’ |-> ‘LCONS e2 (LCONS ev io)’] live_shift) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  mp_tac (Q.INST [‘ev’ |-> ‘e0’, ‘W0’ |-> ‘w0’,
                  ‘io’ |-> ‘LCONS e1 (LCONS e2 (LCONS ev io))’] live_shift) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]
QED

(* ------------------------------------------------------------------------
   The program
   ------------------------------------------------------------------------ *)

(* The setup's two early ends (as honestEchoL0BQuiet's) *)
Theorem stdio_closed_echo[local]:
  l0_do «sys_fdok» [0w] 1 w0 = SOME (o0, w1, e0) ∧
  l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1) ∧
  l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2) ∧ ¬stdio_all o0 o1 o2 ⇒
  honestL1BStmts$stdio_closed (Terminate Success [e0; e1; e2])
Proof
  rw[fdok_do, honestL1BStmtsTheory.stdio_closed_def, stdio_all_def] >> rw[] >> fs[]
QED

Theorem fdok_open_ev[local]:
  l0_do «sys_fdok» [f] 1 w = SOME ([1w], w', ev) ⇒
  ev = IO_event (ExtCall «sys_fdok») [f] [(0w, 1w)]
Proof
  rw[fdok_do]
QED

Theorem listen_failed_prog[local]:
  l0_do «sys_fdok» [0w] 1 w0 = SOME (o0, w1, e0) ∧
  l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1) ∧
  l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2) ∧ stdio_all o0 o1 o2 ∧
  l0_rely w3 ∧ sys_listen_echo w3 = SOME (out, w4, ev) ∧ listen_fd out = NONE ⇒
  honestL1BStmts$listen_failed (Terminate Success [e0; e1; e2; ev])
Proof
  rw[stdio_all_def] >> imp_res_tac fdok_open_ev >> rveq >>
  qpat_x_assum ‘sys_listen_echo _ = _’ mp_tac >>
  rw[sys_listen_echo_def, l0_do_def, AllCaseEqs(), honestL1BStmtsTheory.listen_failed_def,
     honestL1BStmtsTheory.listen_failed_on_def] >>
  drule_all l0_ffi_fn_length >> strip_tac >>
  simp[l0_ev_res_def, MAP_ZIP] >>
  gvs[listen_fd_def, l0_res_of_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem stdio_kept_outcome[local]:
  honestL1BStmts$stdio_kept io ⇔
  honestL0Outcome$stdio_open io ∧
  ∀evs. LPREFIX (fromList evs) io ⇒ honestL0Outcome$no_close_stdio evs
Proof
  simp[honestL1BStmtsTheory.stdio_kept_def, honestL1BStmtsTheory.stdio_open_def,
       honestL0OutcomeTheory.stdio_open_def, honestL1BStmtsTheory.no_close_stdio_def,
       honestL0OutcomeTheory.no_close_stdio_def]
QED

(* MAIN: the claim's clause at one startup world *)
Theorem echo_live_prog_world:
  l0_server_world w0 ⇒
  ∃b. semantics_prog (init_state (l0_ffi w0)) init_env echo_l0_prog b ∧
      (honestL1BStmts$stdio_closed b ∨ listen_failed_on honestL1BStmts$echo_port_conf b ∨
       ∃io. b = Diverge io ∧ honestL1BStmts$stdio_kept io ∧ echo_safe_l0 io ∧
            (F1_io io ∧ honestL1BStmts$F2 w0 ∧ accepts_below io ⇒
             echo_live_l0 pf_sendwait w0 io ∧ conn_live_l0 w0 io))
Proof
  strip_tac >>
  ‘l0_rely w0 ∧ w0.hist = [] ∧ l0_fresh_world w0’
    by fs[l0_server_world_def, l0_fresh_world_def] >>
  drule_all echo_l0_semantics_prog >> strip_tac
  >- ((* a stdio fd is closed *)
      qexists_tac ‘Terminate Success [e0; e1; e2]’ >> simp[] >>
      disj1_tac >> drule_all stdio_closed_echo >> simp[])
  >- ((* the listen fails *)
      qexists_tac ‘Terminate Success [e0; e1; e2; ev]’ >> simp[] >>
      ‘l0_rely w3’ by metis_tac[l0_do_rely] >>
      drule_all listen_failed_prog >> drule listen_conf_echo >>
      rpt strip_tac >>
      qpat_x_assum ‘listen_failed _’ (strip_assume_tac o SIMP_RULE (srw_ss())
        [honestL1BStmtsTheory.listen_failed_def, honestL1BStmtsTheory.listen_failed_on_def]) >>
      rveq >> disj2_tac >> fs[honestL1BStmtsTheory.listen_failed_on_def] >>
      qpat_x_assum ‘bs' = bs’ SUBST_ALL_TAC >>
      asm_rewrite_tac [honestL1BStmtsTheory.echo_port_conf_def,
                       honestEchoL0ProgTheory.echo_port_conf_def]) >>
  (* the listen succeeds: the program diverges with the loop's trace *)
  qabbrev_tac ‘io = LAPPEND (fromList [e0; e1; e2; ev]) (echo_l0_run k w4)’ >>
  (* safety and stdio: echo_l0_safe's run is this one *)
  ‘echo_safe_l0 io ∧ honestL0Outcome$stdio_open io ∧
   ∀evs. LPREFIX (fromList evs) io ⇒ honestL0Outcome$no_close_stdio evs’
    by (qpat_x_assum ‘l0_server_world _’ (strip_assume_tac o MATCH_MP echo_l0_safe) >>
        imp_res_tac semantics_prog_deterministic >> fs[]) >>
  qexists_tac ‘Diverge io’ >> simp[] >> disj2_tac >> disj2_tac >>
  conj_tac >- simp[stdio_kept_outcome] >> strip_tac >>
  (* liveness: in the world after the listen, then across the setup *)
  ‘l0_rely w3’ by metis_tac[l0_do_rely] >>
  ‘l0_fresh_world w3’ by metis_tac[fdok_fresh_step, l0_do_rely] >>
  ‘k < 2147483648’ by metis_tac[listen_fd_small] >>
  ‘stdio_prefix w0 w3’ by (simp[stdio_prefix_def] >> metis_tac[]) >>
  ‘run_ok (elfd k) epol (eifds k) (esrv k) w4’
    by (irule echo_run_ok >> qexistsl [‘ev’, ‘out’, ‘w3’] >> asm_rewrite_tac[]) >>
  ‘winv w4 ∧ linv (elfd k) w4 ∧ qfresh w4 ∧ qinb w4 ∧ nshut w4 ∧ MEM (elfd k) (l0_used w4)’
    by (irule post_listen_facts >> qexistsl [‘ev’, ‘out’, ‘w0’, ‘w3’] >> simp[]) >>
  ‘lone (elfd k) w4’ by metis_tac[listen_lone] >>
  mp_tac (Q.INST [‘io’ |-> ‘echo_l0_run k w4’, ‘KK’ |-> ‘pf_sendwait’] live_setup) >>
  impl_tac
  >- (simp[] >> strip_tac >> irule echo_live_w4 >> simp[]) >>
  qunabbrev_tac ‘io’ >>
  RULE_ASSUM_TAC (REWRITE_RULE [llistTheory.fromList_def, llistTheory.LAPPEND]) >>
  rewrite_tac [llistTheory.fromList_def, llistTheory.LAPPEND, LET_THM] >> BETA_TAC >>
  disch_then irule >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* MAIN (L3-08): R4′ for the PF echo program (D25′: no hypotheses) *)
Theorem echo_l0_echo2_claim:
  l0_echo2_claim pf_sendwait echo_l0_prog
Proof
  rw[l0_echo2_claim_def] >> irule echo_live_prog_world >> first_assum ACCEPT_TAC
QED
