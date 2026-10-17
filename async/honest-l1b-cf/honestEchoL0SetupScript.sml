(*
  The world after the echo programs' setup (the three sys_fdok checks, D33,
  then the listen), shared by the blocking echo's quiet theorem (L3-09,
  honestEchoL0BQuiet) and the PF echo's program link (L3-08).

  post_listen_facts: from an l0_server_world, after stdio_prefix and a
  successful listen on k, the PF run's world standing facts hold:
     winv w4 ∧ linv (n2w k) w4 ∧ qfresh w4 ∧ qinb w4 ∧ nshut w4 ∧
     MEM (n2w k) (l0_used w4)
  and each survives a reindex (it changes only ch and env), for the
  blocking echo's reindexed world (post_listen_facts_reindex).

  MAIN: post_listen_facts, post_listen_facts_reindex.
*)
Theory honestEchoL0Setup
Ancestors
  honestL0 honestL0World honestL0WorldProps honestL0WorldInv honestL0Rely
  honestL0Fdok honestL0Reindex honestEchoL0Spec honestEchoL0Prog honestEchoL0Inv
  honestEchoL0Safe honestL1PFRound honestL1PFConn honestL1PFOut honestL1PFInput
  honestL1PFFlushLive honestL1BConn honestL1PFRefine honestL1Model
Libs
  preamble

(* The world w3 after main's three sys_fdok calls from w0, all answering
   open (D33) *)
Definition stdio_prefix_def:
  stdio_prefix w0 w3 ⇔
    ∃o0 w1 e0 o1 w2 e1 o2 e2.
      l0_do «sys_fdok» [0w] 1 w0 = SOME (o0, w1, e0) ∧
      l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1) ∧
      l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2) ∧ stdio_all o0 o1 o2
End

(* The world facts along the stdio checks, from a fresh relied-on world *)
Theorem stdio_worlds:
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
  gvs[AllCaseEqs(), l0_call_def, honestEchoL0ProgTheory.echo_port_conf_def]
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

Theorem listen_fail_fd[local]:
  listen_fd (enc_listen_fail w ke) ≠ SOME k
Proof
  PairCases_on ‘ke’ >>
  ‘n2w (err_code ke1) ≠ (0w:word8)’
    by (mp_tac (Q.INST [‘e’ |-> ‘ke1’] err_code_range) >> simp[wordsTheory.n2w_11]) >>
  gvs[enc_listen_fail_def, listen_fd_def, l0_res_of_def, dec_res_def, AllCaseEqs()]
QED

(* After the listen from a fresh world: no channels, no open fds, and the
   one listener, with an empty queue *)
Theorem listen_shape:
  l0_fresh_world w0 ∧ sys_listen_echo w0 = SOME (out, w1, ev) ∧ listen_fd out = SOME k ⇒
  w1.chans = [] ∧ w1.open_fds = [] ∧ ∃p. w1.listeners = [(n2w k, p, [])]
Proof
  rw[sys_listen_echo_def, l0_do_def, l0_ffi_fn_def] >>
  drule_then (qspec_then ‘«sys_listen»’ assume_tac) l0_tick_fresh >>
  fs[l0_fresh_world_def] >>
  gvs[AllCaseEqs(), l0_call_def, honestEchoL0ProgTheory.echo_port_conf_def, l0_listen_def]
  >~ [‘l0_alloc _ = SOME f’]
  >- (‘dec_res (enc_res (Ok (w2n f)) ++ []) = SOME (Ok (w2n f))’
        by (irule dec_enc_res >> simp[l0_res_ok_def] >>
            assume_tac (INST_TYPE [alpha |-> “:64”] wordsTheory.w2n_lt) >> fs[]) >>
      gvs[listen_fd_def, l0_res_of_def])
  >> gvs[listen_fail_fd]
QED

Theorem fdok_fds_lt[local]:
  l0_fresh_world w ∧ l0_do «sys_fdok» [f] 1 w = SOME (out, w', ev) ∧ fds_lt w ⇒ fds_lt w'
Proof
  strip_tac >> drule_all fdok_fresh_step >> strip_tac >>
  qpat_x_assum ‘w' = _’ SUBST_ALL_TAC >>
  qpat_x_assum ‘fds_lt w’ mp_tac >> simp[fds_lt_def, l0_used_def]
QED

(* MAIN: the world standing facts after the setup *)
Theorem post_listen_facts:
  l0_server_world w0 ∧ stdio_prefix w0 w3 ∧
  sys_listen_echo w3 = SOME (out, w4, ev) ∧ listen_fd out = SOME k ⇒
  winv w4 ∧ linv (n2w k) w4 ∧ qfresh w4 ∧ qinb w4 ∧ nshut w4 ∧
  MEM (n2w k) (l0_used w4)
Proof
  rewrite_tac[stdio_prefix_def] >> strip_tac >>
  ‘l0_rely w0 ∧ fds_lt w0 ∧ l0_fresh_world w0’
    by fs[l0_server_world_def, l0_fresh_world_def] >>
  mp_tac stdio_worlds >>
  ASM_REWRITE_TAC[] >> strip_tac >>
  ‘fds_lt w1’
    by (mp_tac (Q.INST [‘w’ |-> ‘w0’, ‘f’ |-> ‘0w’, ‘out’ |-> ‘o0’, ‘w'’ |-> ‘w1’, ‘ev’ |-> ‘e0’] fdok_fds_lt) >> ASM_REWRITE_TAC[]) >>
  ‘fds_lt w2’
    by (mp_tac (Q.INST [‘w’ |-> ‘w1’, ‘f’ |-> ‘1w’, ‘out’ |-> ‘o1’, ‘w'’ |-> ‘w2’, ‘ev’ |-> ‘e1’] fdok_fds_lt) >> ASM_REWRITE_TAC[]) >>
  ‘fds_lt w3’
    by (mp_tac (Q.INST [‘w’ |-> ‘w2’, ‘f’ |-> ‘2w’, ‘out’ |-> ‘o2’, ‘w'’ |-> ‘w3’, ‘ev’ |-> ‘e2’] fdok_fds_lt) >> ASM_REWRITE_TAC[]) >>
  qpat_assum ‘sys_listen_echo _ = _’ (assume_tac o REWRITE_RULE [sys_listen_echo_def]) >>
  ‘l0_rely w4’
    by (irule honestEchoL0InvTheory.l0_do_rely >>
        qpat_assum ‘l0_do «sys_listen» _ _ _ = _’ (irule_at Any) >> first_assum ACCEPT_TAC) >>
  ‘fds_lt w4’
    by (irule l0_do_fds_lt >>
        qpat_assum ‘l0_do «sys_listen» _ _ _ = _’ (irule_at Any) >>
        ASM_REWRITE_TAC[] >> EVAL_TAC) >>
  ‘l0wf w4’
    by (mp_tac (Q.INST [‘w0’ |-> ‘w3’, ‘w1’ |-> ‘w4’] listen_l0wf) >> ASM_REWRITE_TAC[]) >>
  ‘MEM (n2w k) (l0_used w4)’
    by (mp_tac (Q.INST [‘w’ |-> ‘w3’, ‘w1’ |-> ‘w4’] listen_used) >> ASM_REWRITE_TAC[]) >>
  mp_tac (Q.INST [‘w0’ |-> ‘w3’, ‘w1’ |-> ‘w4’] listen_shape) >>
  ASM_REWRITE_TAC[] >> strip_tac >>
  ASM_REWRITE_TAC[winv_def] >>
  simp[linv_def, qfresh_def, qinb_def, nshut_def, noconn_def, errb_def, used_chans_def]
QED

(* Each fact survives a reindex *)
Theorem reindex_fields[local,simp]:
  (reindex tr w).chans = w.chans ∧ (reindex tr w).listeners = w.listeners ∧
  (reindex tr w).open_fds = w.open_fds ∧ (reindex tr w).reserved = w.reserved ∧
  (reindex tr w).fd_limit = w.fd_limit
Proof
  simp[reindex_def]
QED

Theorem post_listen_facts_reindex:
  winv w ∧ linv l w ∧ qfresh w ∧ qinb w ∧ nshut w ∧ MEM l (l0_used w) ⇒
  winv (reindex tr w) ∧ linv l (reindex tr w) ∧ qfresh (reindex tr w) ∧
  qinb (reindex tr w) ∧ nshut (reindex tr w) ∧ MEM l (l0_used (reindex tr w))
Proof
  rewrite_tac[winv_def] >> strip_tac >>
  ‘l0_rely (reindex tr w)’ by (irule l0_rely_reindex >> first_assum ACCEPT_TAC) >>
  fs[l0wf_def, used_chans_def, noconn_def, fds_lt_def, l0_used_def,
     errb_def, linv_def, qfresh_def, csent_def, qinb_def, chin_def, nshut_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* MAIN: the same facts in the world reindexed by tr *)
Theorem post_listen_facts_reindexed:
  l0_server_world w0 ∧ stdio_prefix w0 w3 ∧
  sys_listen_echo w3 = SOME (out, w4, ev) ∧ listen_fd out = SOME k ⇒
  winv (reindex tr w4) ∧ linv (n2w k) (reindex tr w4) ∧ qfresh (reindex tr w4) ∧
  qinb (reindex tr w4) ∧ nshut (reindex tr w4) ∧ MEM (n2w k) (l0_used (reindex tr w4))
Proof
  strip_tac >> irule post_listen_facts_reindex >> mp_tac post_listen_facts >>
  impl_tac >- ASM_REWRITE_TAC[] >> strip_tac >> ASM_REWRITE_TAC[]
QED

(* The world after the stdio checks keeps the rely and the fd bound *)
Theorem stdio_prefix_lt:
  l0_server_world w0 ∧ stdio_prefix w0 w3 ⇒ l0_rely w3 ∧ fds_lt w3 ∧ l0_fresh_world w3
Proof
  rewrite_tac[stdio_prefix_def] >> strip_tac >>
  ‘l0_rely w0 ∧ fds_lt w0 ∧ l0_fresh_world w0’
    by fs[l0_server_world_def, l0_fresh_world_def] >>
  mp_tac stdio_worlds >>
  ASM_REWRITE_TAC[] >> strip_tac >>
  ‘fds_lt w1’
    by (mp_tac (Q.INST [‘w’ |-> ‘w0’, ‘f’ |-> ‘0w’, ‘out’ |-> ‘o0’, ‘w'’ |-> ‘w1’, ‘ev’ |-> ‘e0’] fdok_fds_lt) >> ASM_REWRITE_TAC[]) >>
  ‘fds_lt w2’
    by (mp_tac (Q.INST [‘w’ |-> ‘w1’, ‘f’ |-> ‘1w’, ‘out’ |-> ‘o1’, ‘w'’ |-> ‘w2’, ‘ev’ |-> ‘e1’] fdok_fds_lt) >> ASM_REWRITE_TAC[]) >>
  mp_tac (Q.INST [‘w’ |-> ‘w2’, ‘f’ |-> ‘2w’, ‘out’ |-> ‘o2’, ‘w'’ |-> ‘w3’, ‘ev’ |-> ‘e2’] fdok_fds_lt) >>
  ASM_REWRITE_TAC[]
QED

(* The run invariant survives a reindex of its world *)
Theorem ri_reindex:
  ri lfd m (h, (w, ps), evs) ⇒ ri lfd m (h, (reindex tr w, ps), evs)
Proof
  rewrite_tac[honestEchoL0RunTheory.ri_def, honestEchoL0InvTheory.wown_def] >> strip_tac >>
  ‘l0_rely (reindex tr w)’ by (irule l0_rely_reindex >> first_assum ACCEPT_TAC) >>
  fs[fds_lt_def, l0_used_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* MAIN: the run invariant at the start of the loop, in the world reindexed by tr *)
Theorem post_listen_ri:
  l0_server_world w0 ∧ stdio_prefix w0 w3 ∧
  sys_listen_echo w3 = SOME (out, w4, ev) ∧ listen_fd out = SOME k ⇒
  ri (n2w k) (srelabel (server k)) ([], (reindex tr w4, pinit), [])
Proof
  strip_tac >> irule ri_reindex >>
  mp_tac stdio_prefix_lt >> ASM_REWRITE_TAC[] >> strip_tac >>
  irule ri_echo_base >>
  qexistsl [‘ev’, ‘out’, ‘w3’] >> ASM_REWRITE_TAC[]
QED

(* MAIN: the listener is the world's only one and the world is well formed,
   in the world reindexed by tr *)
Theorem post_listen_wf_reindexed:
  l0_server_world w0 ∧ stdio_prefix w0 w3 ∧
  sys_listen_echo w3 = SOME (out, w4, ev) ∧ listen_fd out = SOME k ⇒
  l0wf (reindex tr w4) ∧ lone (n2w k) (reindex tr w4)
Proof
  strip_tac >>
  mp_tac stdio_prefix_lt >> ASM_REWRITE_TAC[] >> strip_tac >>
  ‘l0wf w4’ by (irule listen_l0wf >> qexistsl [‘ev’, ‘out’, ‘w3’] >> ASM_REWRITE_TAC[]) >>
  ‘lone (n2w k) w4’ by (irule listen_lone >> qexistsl [‘ev’, ‘out’, ‘w3’] >> ASM_REWRITE_TAC[]) >>
  qpat_x_assum ‘l0wf _’ mp_tac >> qpat_x_assum ‘lone _ _’ mp_tac >>
  REWRITE_TAC[l0wf_def, used_chans_def, lone_def, reindex_fields] >>
  rpt strip_tac >> ASM_REWRITE_TAC[]
QED
