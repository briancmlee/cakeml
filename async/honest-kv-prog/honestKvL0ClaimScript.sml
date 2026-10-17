(*
  P4 step G's hand-off (design/46): kv_l0_claim of the KV program, from
  the safety of its run past a successful listen (steps D/E, proved
  separately).  Everything else in the claim (the three outcomes, the
  stdio check, the topology, no close call on fds 0-2, the inert prefix)
  is proved here.
*)
Theory honestKvL0Claim
Ancestors
  llist ffi honestL0 honestL0World honestL0WorldProps honestL0Rely
  honestL0Outcome honestL0Fdok honestEchoL0Spec honestEchoL0Stdio honestEchoL0Safe
  honestHttpKvL0Spec honestKvL0Run asyncKvModel
  honestL1MainProg honestL1MainSpec honestL1MainWorld honestL1MainSafe
  honestKvL0Prog honestKvL0Main honestKvL0Sem
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
  >- (‘8081 = w22n kv_port_conf’ by simp[kv_port] >> pop_assum SUBST1_TAC >>
      irule main_topology >> metis_tac[])
  >- (first_assum ACCEPT_TAC) >>
  simp[no_close_stdio_EVERY] >>
  ‘∀evs. LPREFIX (fromList evs) (kv_l0_run k w4) ⇒ EVERY ev_nostdio evs’
    by (irule run_nostdio_at >>
        simp[kv_pt_ok, uses_ok_writes_accepted, kv_server_uses_ok] >> metis_tac[]) >>
  imp_res_tac fdok_nostdio >> imp_res_tac listen_nostdio_at >>
  rpt (match_mp_tac nostdio_LCONS >> conj_tac >- first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED
