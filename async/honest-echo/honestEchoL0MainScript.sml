(*
  The echo program's main on the honest L0 world (P3): its specs.  main
  first calls sys_fdok on fds 0, 1 and 2 (D33); if one is closed it
  returns.  Otherwise the listen fails and main returns, or it succeeds and
  main diverges, running the prefetching L1 loop with the echo server.
*)
Theory honestEchoL0Main
Ancestors
  ml_translator std_prelude cfDiv llist Marshalling
  asyncCore asyncLevel1 asyncChoose asyncCfActModel asyncCfActProg
  asyncTranscript asyncServer asyncServerSafety asyncM4Relabel asyncM4ServerUses
  asyncM3World asyncM3Prog asyncM3Loop asyncM4Loop asyncM4SockModel asyncM4SockServer
  honestL0 honestL0World honestL1Model honestL1Inv honestL1PFModel honestL1PFInv
  honestL0Part honestL0Prog honestL0Proof honestL1PFProg honestL1PFSpec
  honestEchoL0Prog
Libs
  preamble ml_translatorLib ml_progLib cfLib basisFunctionsLib cfDivLib

val _ = translation_extends "honestEchoL0Prog";

(* ------------------------------------------------------------------------
   The echo server's actions are L1's well-formed actions
   ------------------------------------------------------------------------ *)

(* In any history: it accepts only on the listener, and reads bufsz bytes *)
Theorem server_pact_ok:
  EVERY (pact_ok (n2w k)) (new_actions (log_of (srelabel (server k))) h)
Proof
  simp[new_actions_relabel, EVERY_MEM, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
  qmatch_asmsub_abbrev_tac ‘MEM a (new_actions _ h')’ >>
  ‘MEM a (server k h').actions’
    by (gvs[new_actions_def, log_of_def] >> every_case_tac >> gvs[] >>
        metis_tac[MEM_DROP_IMP]) >>
  ‘MEM a (MAP FST (trans (server k) h'))’ by simp[MAP_FST_trans, wf_server] >>
  qspecl_then [‘h'’] strip_assume_tac (Q.INST [‘lfd’ |-> ‘k’] server_uses_accepted) >>
  gvs[MEM_MAP, accepts_on_def, EVERY_MEM] >> first_x_assum drule >>
  Cases_on ‘FST y’ >>
  simp[sfa_def, pact_ok_def, honestL1InvTheory.act_ok_def, is_accept_def, bufsz_def]
QED

Theorem server_pt_ok:
  pt_ok (n2w k) hw ifds (srelabel (server k)) ws0
Proof
  simp[pt_ok_def, server_pact_ok]
QED

(* ------------------------------------------------------------------------
   main
   ------------------------------------------------------------------------ *)

Theorem c_listen_spec:
  UNIT_TYPE () uv ∧ sys_listen_echo wa = SOME (out, wb, ev) ⇒
  app (p:'ffi ffi_proj) c_listen_v [uv] (L0_EV w0 wa evs)
    (POSTv v. &LIST_TYPE WORD out v * L0_EV w0 wb (evs ++ [ev]))
Proof
  rpt strip_tac >> xcf_with_def (fetch "honestEchoL0Prog" "c_listen_v_def") >>
  assume_tac (fetch "honestEchoL0Prog" "echo_port_conf_v_thm") >>
  rpt (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &STRING_TYPE (bytes_str out) v * L0_EV w0 wb (evs ++ [ev])’
  >- (xapp_spec L0_listen_spec >> xsimpl >> qexists_tac ‘echo_port_conf’ >>
      gvs[sys_listen_echo_def, bytes_str_bytes_to_str]) >>
  xapp >> xsimpl >> qexists_tac ‘bytes_str out’ >>
  simp[bytes_str_bytes_to_str, str_to_bytes_bytes_to_str]
QED

(* D33: one sys_fdok call on fd f *)
Theorem c_fdok_spec:
  NUM f fv ∧ l0_do «sys_fdok» [n2w f] 1 wa = SOME (out, wb, ev) ⇒
  app (p:'ffi ffi_proj) c_fdok_v [fv] (L0_EV w0 wa evs)
    (POSTv v. &LIST_TYPE WORD out v * L0_EV w0 wb (evs ++ [ev]))
Proof
  rpt strip_tac >> xcf_with_def (fetch "honestEchoL0Prog" "c_fdok_v_def") >>
  rpt (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &STRING_TYPE (bytes_str out) v * L0_EV w0 wb (evs ++ [ev])’
  >- (xapp_spec L0_fdok_spec >> xsimpl >> qexists_tac ‘[n2w f]’ >>
      gvs[fdok_conf_def, bytes_str_bytes_to_str]) >>
  xapp >> xsimpl >> qexists_tac ‘bytes_str out’ >>
  simp[bytes_str_bytes_to_str, str_to_bytes_bytes_to_str]
QED

(* main's first three calls, sys_fdok on fds 0, 1 and 2 *)
val stdio_tac =
  xcf_with_def (fetch "honestEchoL0Prog" "main_v_def") >>
  xlet ‘POSTv v. &LIST_TYPE WORD o0 v * L0_EV w0 w1 [e0]’
  >- (xapp_spec (Q.INST [‘f’ |-> ‘0’] c_fdok_spec) >>
      qexistsl [‘emp’, ‘w1’, ‘w’, ‘w0’, ‘o0’, ‘[]’, ‘e0’] >> xsimpl >> simp[NUM_def, INT_def]) >>
  xlet ‘POSTv v. &LIST_TYPE WORD o1 v * L0_EV w0 w2 [e0; e1]’
  >- (xapp_spec (Q.INST [‘f’ |-> ‘1’] c_fdok_spec) >>
      qexistsl [‘emp’, ‘w2’, ‘w1’, ‘w0’, ‘o1’, ‘[e0]’, ‘e1’] >> xsimpl >> simp[NUM_def, INT_def]) >>
  xlet ‘POSTv v. &LIST_TYPE WORD o2 v * L0_EV w0 w3 [e0; e1; e2]’
  >- (xapp_spec (Q.INST [‘f’ |-> ‘2’] c_fdok_spec) >>
      qexistsl [‘emp’, ‘w3’, ‘w2’, ‘w0’, ‘o2’, ‘[e0; e1]’, ‘e2’] >> xsimpl >> simp[NUM_def, INT_def]) >>
  (xlet_auto >- xsimpl) >> xif >> asm_exists_tac >> simp[];

(* A closed stdio fd: main returns after the three calls *)
Theorem main_stdio_spec:
  UNIT_TYPE () uv ∧
  l0_do «sys_fdok» [0w] 1 w = SOME (o0, w1, e0) ∧
  l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1) ∧
  l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2) ∧ ¬stdio_all o0 o1 o2 ⇒
  app (p:'ffi ffi_proj) main_v [uv] (L0_EV w0 w [])
    (POSTv v. &UNIT_TYPE () v * L0_EV w0 w3 [e0; e1; e2])
Proof
  rpt strip_tac >> stdio_tac >> xcon >> xsimpl
QED

Theorem w82n_lt[local]:
  LENGTH (b : word8 list) = 8 ⇒ w82n b < 256 ** 8
Proof
  rw[LENGTH_EQ_NUM_compute] >> simp[w82n_def] >>
  (fn (g as (_, w)) =>
     MAP_EVERY (fn v => assume_tac (ISPEC v wordsTheory.w2n_lt))
       (filter (fn v => type_of v = “:word8”) (free_vars w)) g) >>
  fs[]
QED

Theorem listen_fd_lt:
  listen_fd out = SOME k ⇒ k < dimword (:64)
Proof
  rw[listen_fd_def, l0_res_of_def, AllCaseEqs(), dec_res_def] >>
  ‘LENGTH (TAKE 8 (TL out)) = 8’ by (Cases_on ‘out’ >> gvs[LENGTH_TAKE_EQ]) >>
  ‘w82n (TAKE 8 (TL out)) < 256 ** 8’ by (irule w82n_lt >> simp[]) >> fs[]
QED

(* The stdio fds are open and the listen fails: main returns *)
Theorem main_fail_spec:
  UNIT_TYPE () uv ∧
  l0_do «sys_fdok» [0w] 1 w = SOME (o0, w1, e0) ∧
  l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1) ∧
  l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2) ∧ stdio_all o0 o1 o2 ∧
  sys_listen_echo w3 = SOME (out, w', ev) ∧ listen_fd out = NONE ⇒
  app (p:'ffi ffi_proj) main_v [uv] (L0_EV w0 w [])
    (POSTv v. &UNIT_TYPE () v * L0_EV w0 w' [e0; e1; e2; ev])
Proof
  rpt strip_tac >> stdio_tac >>
  (xlet_auto >- (xcon >> xsimpl)) >>
  xlet ‘POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w' [e0; e1; e2; ev]’
  >- (xapp_spec c_listen_spec >> qexistsl [‘emp’, ‘w'’, ‘w3’, ‘w0’, ‘out’, ‘[e0; e1; e2]’, ‘ev’] >>
      xsimpl >> simp[]) >>
  rpt (xlet_auto >- xsimpl) >> gvs[OPTION_TYPE_def] >> xmatch >>
  xcon >> xsimpl
QED

(* The stdio fds are open and the listen succeeds with listener k: main
   runs the L1 loop forever *)
Overload echo_l0_run = “λk w1. LFLATTEN (LGENLIST (λi. fromList
  (pround_evs (n2w k) echo_hw (asyncM4LiveInterest$live [n2w k] (log_of (srelabel (server k)))) (srelabel (server k)) (w1, pinit) i)) NONE)”

Theorem main_div_spec:
  limited_parts l0_names p ∧ l0_reach w0 w ∧ UNIT_TYPE () uv ∧
  l0_do «sys_fdok» [0w] 1 w = SOME (o0, w1, e0) ∧
  l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1) ∧
  l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2) ∧ stdio_all o0 o1 o2 ∧
  sys_listen_echo w3 = SOME (out, w4, ev) ∧ listen_fd out = SOME k ∧ k < 2147483648 ⇒
  app (p:'ffi ffi_proj) main_v [uv] (L0_EV w0 w [])
    (POSTd io. io = LAPPEND (fromList [e0; e1; e2; ev]) (echo_l0_run k w4))
Proof
  rpt strip_tac >> drule listen_fd_lt >> strip_tac >>
  ‘l0_reach w0 w4’
    by (gvs[sys_listen_echo_def, l0_do_def, AllCaseEqs()] >> metis_tac[l0_reach_step]) >>
  stdio_tac >>
  (xlet_auto >- (xcon >> xsimpl)) >>
  xlet ‘POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w4 [e0; e1; e2; ev]’
  >- (xapp_spec c_listen_spec >> qexistsl [‘emp’, ‘w4’, ‘w3’, ‘w0’, ‘out’, ‘[e0; e1; e2]’, ‘ev’] >>
      xsimpl >> simp[]) >>
  rpt (xlet_auto >- xsimpl) >> gvs[OPTION_TYPE_def] >> xmatch >>
  assume_tac (fetch "honestEchoL0Prog" "echo_hw_v_thm") >>
  assume_tac (fetch "honestEchoL0Prog" "pinit_v_thm") >>
  xlet ‘POSTv cv. &COMP p SACT UNIT_TYPE SSNAP (srelabel (server k)) cv * L0_EV w0 w4 [e0; e1; e2; ev]’
  >- (xapp_spec sserver_spec >> xsimpl >> qexists_tac ‘k’ >> simp[]) >>
  rpt (xlet_auto >- (TRY xcon >> xsimpl)) >>
  gvs[] >> xapp_spec (INST_TYPE [alpha |-> “:unit”] run_pf_spec) >>
  qexistsl [‘emp’, ‘w0’, ‘w4’, ‘pinit’, ‘srelabel (server k)’, ‘n2w k’, ‘echo_hw’, ‘[n2w k]’, ‘[e0; e1; e2; ev]’] >>
  simp[wf_relabel, wf_server, server_pt_ok, LIST_TYPE_def, psmall_def, pinit_def, l1init_def,
       small_fds_def, small_def] >>
  conj_tac >- metis_tac[] >> xsimpl
QED
