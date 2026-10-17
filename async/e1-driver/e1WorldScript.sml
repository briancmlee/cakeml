(*
  The L0 world where E1 starts: after the three fdok calls (D33) and a
  successful listen on the port, the rely and the fd bound still hold, and
  the listener fd is in use.  These are the world-side hypotheses of the
  E1 run lemmas (client_l1_total, erounds_no_close_stdio) at that world.

  listen_used_port, l0_do_fds_lt: as honest-echo's listen_used (echo port)
  and l0_do_fds_lt (honestEchoL0Inv), outside this directory's INCLUDES;
  to merge into a shared theory.
*)
Theory e1World
Ancestors
  honestL0 honestL0World honestL0WorldProps honestL0Rely honestL1Model honestL1PFRound honestL1PFRefine
  honestL1EPModel honestL0Fdok e1DriverProg e1DriverMain
Libs
  preamble

Theorem l0_do_fds_lt:
  l0_do n conf alen w = SOME (out, w', ev) ∧ fds_lt w ∧ n ≠ «sys_connect» ⇒ fds_lt w'
Proof
  rw[l0_do_def, l0_ffi_fn_def, AllCaseEqs()] >>
  ‘fds_lt (l0_tick n w)’ by simp[] >>
  drule_all fds_lt_call >> simp[fds_lt_def, l0_used_def]
QED

(* The listener a successful listen returns is in use *)
Theorem listen_used_port:
  l0_rely w ∧ sys_listen_port port w = SOME (out, w1, ev) ∧ listen_fd out = SOME k ⇒
  MEM (n2w k : word64) (l0_used w1)
Proof
  rw[sys_listen_port_def, l0_do_def, l0_ffi_fn_def] >>
  gvs[AllCaseEqs(), l0_call_def, port_bytes_def]
  >- (‘dec_res (enc_res (Ok (w2n f)) ++ []) = SOME (Ok (w2n f))’
        by (irule dec_enc_res >> simp[l0_res_ok_def] >>
            assume_tac (INST_TYPE [alpha |-> “:64”] wordsTheory.w2n_lt) >> fs[]) >>
      gvs[listen_fd_def, l0_res_of_def] >>
      gvs[l0_listen_def, AllCaseEqs(), l0_used_def]) >>
  PairCases_on ‘ke’ >>
  ‘n2w (err_code ke1) ≠ (0w:word8)’
    by (mp_tac (Q.INST [‘e’ |-> ‘ke1’] err_code_range) >> simp[wordsTheory.n2w_11]) >>
  gvs[enc_listen_fail_def, listen_fd_def, l0_res_of_def, dec_res_def, AllCaseEqs()]
QED

(* E1's start world: the rely, the fd bound, and the listener in use *)
Theorem e1_start_world:
  l0_rely w0 ∧ fds_lt w0 ∧ FDOK3 w0 w1 w2 w3 o0 o1 o2 e0 e1 e2 ∧
  sys_listen_port port w3 = SOME (out, w4, ev) ∧ listen_fd out = SOME k ⇒
  l0_rely w4 ∧ fds_lt w4 ∧ MEM (n2w k : word64) (l0_used w4)
Proof
  strip_tac >>
  ‘l0_rely w1’ by (irule l0_do_rely >> rpt (first_assum (irule_at Any))) >>
  ‘l0_rely w2’ by (irule l0_do_rely >> rpt (first_assum (irule_at Any))) >>
  ‘l0_rely w3’ by (irule l0_do_rely >> rpt (first_assum (irule_at Any))) >>
  ‘l0_rely w4’
    by (irule l0_do_rely >> gvs[sys_listen_port_def] >> rpt (first_assum (irule_at Any))) >>
  ‘fds_lt w1’
    by (irule l0_do_fds_lt >> qexistsl [‘1’, ‘[0w]’, ‘e0’, ‘«sys_fdok»’, ‘o0’, ‘w0’] >> simp[]) >>
  ‘fds_lt w2’
    by (irule l0_do_fds_lt >> qexistsl [‘1’, ‘[1w]’, ‘e1’, ‘«sys_fdok»’, ‘o1’, ‘w1’] >> simp[]) >>
  ‘fds_lt w3’
    by (irule l0_do_fds_lt >> qexistsl [‘1’, ‘[2w]’, ‘e2’, ‘«sys_fdok»’, ‘o2’, ‘w2’] >> simp[]) >>
  ‘fds_lt w4’
    by (irule l0_do_fds_lt >> gvs[sys_listen_port_def] >>
        qexistsl [‘13’, ‘port_bytes port’, ‘ev’, ‘«sys_listen»’, ‘out’, ‘w3’] >> simp[]) >>
  simp[] >> irule listen_used_port >> qexistsl [‘ev’, ‘out’, ‘port’, ‘w3’] >> simp[]
QED

(* A listen only adds fds *)
Theorem listen_used_mono:
  sys_listen_port port w = SOME (out, w', ev) ∧ MEM x (l0_used w) ⇒ MEM x (l0_used w')
Proof
  rw[sys_listen_port_def, l0_do_def, l0_ffi_fn_def] >>
  ‘∀y. MEM y (l0_tick «sys_listen» w).reserved ∨
       MEM y (MAP FST (l0_tick «sys_listen» w).listeners) ∨
       MEM y (MAP FST (l0_tick «sys_listen» w).open_fds) ⇔ MEM y (l0_used w)’
    by (mp_tac (Q.INST [‘nm’ |-> ‘«sys_listen»’] l0_tick_used) >>
        REWRITE_TAC [l0_used_def] >> strip_tac >>
        pop_assum (fn th => REWRITE_TAC [GSYM th]) >> simp[DISJ_ASSOC]) >>
  gvs[AllCaseEqs(), l0_call_def, port_bytes_def, l0_listen_def] >>
  simp[l0_used_def] >> metis_tac[]
QED

(* The stdio check passed: fds 0, 1, 2 are in use at E1's start world *)
Theorem l0_used_hist[local]:
  l0_used (w with hist := h) = l0_used w
Proof
  simp[l0_used_def]
QED

(* An fdok call keeps the fds in use, and answers 1 iff its fd is in use *)
Theorem fdok_used:
  l0_do «sys_fdok» [f] 1 w = SOME (out, w', ev) ⇒
  l0_used w' = l0_used w ∧ (out = [1w] ⇔ MEM (w2w f) (l0_used w))
Proof
  rw[fdok_do, l0_used_hist] >> rw[]
QED

Theorem e1_start_stdio_used:
  FDOK3 w0 w1 w2 w3 o0 o1 o2 e0 e1 e2 ∧ fdok_all o0 o1 o2 ∧
  sys_listen_port port w3 = SOME (out, w4, ev) ⇒
  MEM (0w : word64) (l0_used w4) ∧ MEM (1w : word64) (l0_used w4) ∧
  MEM (2w : word64) (l0_used w4)
Proof
  strip_tac >>
  ‘MEM (0w : word64) (l0_used w3) ∧ MEM (1w : word64) (l0_used w3) ∧
   MEM (2w : word64) (l0_used w3)’
    by (imp_res_tac fdok_used >> gvs[fdok_all_def]) >>
  rpt conj_tac >> irule listen_used_mono >>
  qexistsl [‘ev’, ‘out’, ‘port’, ‘w3’] >> simp[]
QED
