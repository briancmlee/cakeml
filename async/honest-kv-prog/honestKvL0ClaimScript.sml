(*
  P4 step G (design/46): kv_l0_claim of the KV program.  The safety of
  its run past a successful listen (steps D/E) is honestKvL0Safe's
  kv_run_safe_live; kv_l0_claim_of_run proves everything else in the
  claim (the three outcomes, the stdio check, the topology, no close call
  on fds 0-2, the inert prefix) from that safety, and kv_l0_safe glues
  the two.
*)
Theory honestKvL0Claim
Ancestors
  llist ffi honestL0 honestL0World honestL0WorldProps honestL0Rely
  honestL0Outcome honestL0Fdok honestEchoL0Spec honestEchoL0Inv honestEchoL0Stdio honestEchoL0Safe
  honestHttpKvL0Spec honestKvL0Run asyncKvModel
  honestL1MainProg honestL1MainSpec honestL1MainWorld honestL1MainSafe
  honestKvL0Prog honestKvL0Main honestKvL0Sem honestKvL0Safe
Libs
  preamble

(* The KV run's rounds never stop *)
Theorem kv_prounds_total:
  l0_rely w ∧ sys_listen_at kv_port_conf w = SOME (out, w1, ev) ∧ l1_listen_fd out = SOME k ⇒
  ∀n. prounds_t (n2w k) kv_hw
        (asyncM4LiveInterest$live [n2w k] (log_of (srelabel (kv_server k))))
        (srelabel (kv_server k)) (w1, pinit) n ≠ NONE
Proof
  strip_tac >> irule prounds_total_at >> simp[kv_pt_ok] >> metis_tac[]
QED

(* MAIN: kv_l0_claim, given the safety of the run past a successful
   listen (with fds 0-2 in use) *)
Theorem kv_l0_claim_of_run:
  (∀w out w1 ev k.
     l0_rely w ∧ fds_lt w ∧ sys_listen_at kv_port_conf w = SOME (out, w1, ev) ∧
     l1_listen_fd out = SOME k ∧ (∀g. stdio_fd g ⇒ MEM g (l0_used w)) ⇒
     kv_safe_l0 (LCONS ev (kv_l0_run k w1))) ⇒
  kv_l0_claim 8081 kv_l0_prog
Proof
  rw[kv_l0_claim_def, l0_server_world_def] >>
  ‘l0_rely w0 ∧ w0.hist = []’ by simp[] >>
  drule_all kv_l0_semantics_prog >> strip_tac
  >- (qexists_tac ‘fromList [e0; e1; e2]’ >> disj2_tac >> disj2_tac >>
      qexists_tac ‘[e0; e1; e2]’ >> simp[] >>
      irule fdok_closed >> fs[l1_stdio_all_def] >> metis_tac[]) >>
  ‘l0_fresh_world w0’ by simp[l0_fresh_world_def] >>
  drule_all fdok_shift >> strip_tac >>
  ‘l0_rely w3 ∧ fds_lt w3’
    by (qpat_x_assum ‘w3 = _’ SUBST1_TAC >> conj_tac
        >- (irule l0_rely_ch >> qexists_tac ‘w0’ >> simp[]) >>
        qpat_x_assum ‘fds_lt w0’ mp_tac >> simp[fds_lt_def, l0_used_def]) >>
  ‘∀rest. stdio_open (e0 ::: e1 ::: e2 ::: rest)’ by metis_tac[stdio_open_l1]
  >- (qexists_tac ‘fromList [e0; e1; e2; ev]’ >> disj2_tac >> disj1_tac >>
      qexistsl [‘[e0; e1; e2]’, ‘ev’] >> simp[] >> metis_tac[listen_failed_at]) >>
  qexists_tac ‘LAPPEND (fromList [e0; e1; e2; ev]) (kv_l0_run k w4)’ >>
  disj1_tac >> simp[] >>
  ‘∀g. stdio_fd g ⇒ MEM g (l0_used w3)’
    by (qpat_x_assum ‘_ ⇔ _’ mp_tac >> fs[l1_stdio_all_def] >>
        qpat_x_assum ‘w3 = _’ SUBST1_TAC >> rw[stdio_fd_def, l0_used_def] >> simp[]) >>
  ‘∀n. prounds_t (n2w k) kv_hw
         (asyncM4LiveInterest$live [n2w k] (log_of (srelabel (kv_server k))))
         (srelabel (kv_server k)) (w4, pinit) n ≠ NONE’
    by (irule kv_prounds_total >> metis_tac[]) >>
  rpt conj_tac
  >- (‘kv_safe_l0 (LCONS ev (kv_l0_run k w4))’
        by (first_x_assum irule >> metis_tac[]) >>
      imp_res_tac fdok_inert >>
      rpt (irule kv_safe_l0_inert >> ASM_REWRITE_TAC[]))
  >- (‘l0_topology (w22n kv_port_conf) (LAPPEND (fromList [e0; e1; e2; ev]) (kv_l0_run k w4))’
        by (irule main_topology >> metis_tac[]) >>
      fs[kv_port]) >>
  simp[no_close_stdio_EVERY] >>
  ‘∀evs. LPREFIX (fromList evs) (kv_l0_run k w4) ⇒ EVERY ev_nostdio evs’
    by (match_mp_tac (Q.INST [‘w0’ |-> ‘w3’, ‘conf’ |-> ‘kv_port_conf’] run_nostdio_at) >>
        simp[kv_pt_ok, kv_writes_accepted] >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
  imp_res_tac fdok_nostdio >> imp_res_tac listen_nostdio_at >>
  rpt (match_mp_tac nostdio_LCONS >> conj_tac >- first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

(* MAIN (P4 G): the KV program meets kv_l0_claim on port 8081 *)
Theorem kv_l0_safe:
  kv_l0_claim 8081 kv_l0_prog
Proof
  irule kv_l0_claim_of_run >> rpt strip_tac >>
  ‘k < 2147483648’ by (drule_all l1_listen_fd_small >> simp[]) >>
  drule listen_inert_at >> strip_tac >>
  match_mp_tac kv_safe_l0_inert >> ASM_REWRITE_TAC[] >>
  ‘l0_rely w1’ by (drule_all listen_rely_at >> simp[]) >>
  ‘MEM (n2w k) (l0_used w1)’ by (drule_all listen_used_at >> simp[]) >>
  ‘fds_lt w1’
    by (qpat_x_assum ‘sys_listen_at _ _ = _’ mp_tac >> simp[sys_listen_at_def] >> strip_tac >>
        drule l0_do_fds_lt >> simp[]) >>
  ‘ri (n2w k) (srelabel (kv_server k)) ([], (w1, pinit), [])’
    by (match_mp_tac (Q.INST [‘w0’ |-> ‘w’, ‘conf’ |-> ‘kv_port_conf’] ri_base_at) >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all kv_prounds_total >> strip_tac >>
  match_mp_tac kv_run_safe_live >> simp[]
QED
