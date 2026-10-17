(*
  The blocking echo program's main on the honest L0 world: main first
  calls sys_fdok on fds 0, 1 and 2 (D33); if one is closed it returns.
  Otherwise the listen fails and main returns; or it succeeds and main runs the blocking L1
  loop with the echo server, which either never sleeps (main diverges)
  or sleeps in a blocking poll (main stops in that FFI call).
  As honestEchoL0Main, with run_pfb for run_pf.
*)
Theory honestEchoL0BMain
Ancestors
  ml_translator std_prelude cfDiv llist Marshalling
  asyncCore asyncLevel1 asyncChoose asyncCfActModel asyncCfActProg
  asyncTranscript asyncServer asyncServerSafety asyncM4Relabel asyncM4ServerUses
  asyncM3World asyncM3Prog asyncM3Loop asyncM4Loop asyncM4SockModel asyncM4SockServer
  honestL0 honestL0World honestL1Model honestL1Inv honestL1PFModel honestL1PFInv
  honestL0Part honestL0Prog honestL0Proof honestL1PFProg honestL1PFSpec
  honestEchoL0Prog honestEchoL0Main honestL1BModel honestL1BProg honestL1BSpec
  honestEchoL0BProg
Libs
  preamble ml_translatorLib ml_progLib cfLib basisFunctionsLib cfDivLib

val _ = translation_extends "honestEchoL0BProg";

Theorem server_bt_ok:
  bt_ok (n2w k) hw ifds (srelabel (server k)) ws0
Proof
  simp[bt_ok_def, server_pact_ok]
QED

Theorem c_listen_spec:
  UNIT_TYPE () uv ∧ sys_listen_echo wa = SOME (out, wb, ev) ⇒
  app (p:'ffi ffi_proj) c_listen_v [uv] (L0_EV w0 wa evs)
    (POSTv v. &LIST_TYPE WORD out v * L0_EV w0 wb (evs ++ [ev]))
Proof
  rpt strip_tac >> xcf_with_def (fetch "honestEchoL0BProg" "c_listen_v_def") >>
  assume_tac (fetch "honestEchoL0BProg" "echo_port_conf_v_thm") >>
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
  rpt strip_tac >> xcf_with_def (fetch "honestEchoL0BProg" "c_fdok_v_def") >>
  rpt (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &STRING_TYPE (bytes_str out) v * L0_EV w0 wb (evs ++ [ev])’
  >- (xapp_spec L0_fdok_spec >> xsimpl >> qexists_tac ‘[n2w f]’ >>
      gvs[fdok_conf_def, bytes_str_bytes_to_str]) >>
  xapp >> xsimpl >> qexists_tac ‘bytes_str out’ >>
  simp[bytes_str_bytes_to_str, str_to_bytes_bytes_to_str]
QED

(* main's first three calls, sys_fdok on fds 0, 1 and 2 *)
val stdio_tac =
  xcf_with_def (fetch "honestEchoL0BProg" "main_v_def") >>
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

(* The blocking loop's run for the echo on listener k, from w1 (the world
   after the listen) *)
Overload echo_b_rounds = “λk w1. brounds_t (n2w k) echo_hw (asyncM4LiveInterest$live [n2w k] (log_of (srelabel (server k))))
                                   (srelabel (server k)) (w1, pinit)”

Overload echo_l0b_run = “λk w1. LFLATTEN (LGENLIST (λi. fromList
  (bround_evs (n2w k) echo_hw (asyncM4LiveInterest$live [n2w k] (log_of (srelabel (server k)))) (srelabel (server k)) (w1, pinit) i)) NONE)”

(* main up to the loop, then the loop's spec *)
fun main_tac loop_spec =
  rpt strip_tac >> drule listen_fd_lt >> strip_tac >>
  ‘l0_reach w0 w4’
    by (gvs[sys_listen_echo_def, l0_do_def, AllCaseEqs()] >> metis_tac[l0_reach_step]) >>
  stdio_tac >>
  (xlet_auto >- (xcon >> xsimpl)) >>
  xlet ‘POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w4 [e0; e1; e2; ev]’
  >- (xapp_spec c_listen_spec >> qexistsl [‘emp’, ‘w4’, ‘w3’, ‘w0’, ‘out’, ‘[e0; e1; e2]’, ‘ev’] >>
      xsimpl >> simp[]) >>
  rpt (xlet_auto >- xsimpl) >> gvs[OPTION_TYPE_def] >> xmatch >>
  assume_tac (fetch "honestEchoL0BProg" "echo_hw_v_thm") >>
  assume_tac (fetch "honestEchoL0BProg" "pinit_v_thm") >>
  xlet ‘POSTv cv. &COMP p SACT UNIT_TYPE SSNAP (srelabel (server k)) cv * L0_EV w0 w4 [e0; e1; e2; ev]’
  >- (xapp_spec sserver_spec >> xsimpl >> qexists_tac ‘k’ >> simp[]) >>
  rpt (xlet_auto >- (TRY xcon >> xsimpl)) >>
  gvs[] >> xapp_spec (INST_TYPE [alpha |-> “:unit”] loop_spec);

(* The stdio fds are open, the listen succeeds with listener k and the
   loop never sleeps: main diverges *)
Theorem main_div_spec:
  limited_parts l0_names p ∧ l0_reach w0 w ∧ UNIT_TYPE () uv ∧
  l0_do «sys_fdok» [0w] 1 w = SOME (o0, w1, e0) ∧
  l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1) ∧
  l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2) ∧ stdio_all o0 o1 o2 ∧
  sys_listen_echo w3 = SOME (out, w4, ev) ∧ listen_fd out = SOME k ∧ k < 2147483648 ∧
  bt_awake (n2w k) echo_hw (asyncM4LiveInterest$live [n2w k] (log_of (srelabel (server k)))) (srelabel (server k)) (w4, pinit) ⇒
  app (p:'ffi ffi_proj) main_v [uv] (L0_EV w0 w [])
    (POSTd io. io = LAPPEND (fromList [e0; e1; e2; ev]) (echo_l0b_run k w4))
Proof
  main_tac run_pfb_div_spec >>
  qexistsl [‘emp’, ‘w0’, ‘w4’, ‘pinit’, ‘srelabel (server k)’, ‘n2w k’, ‘echo_hw’, ‘[n2w k]’, ‘[e0; e1; e2; ev]’] >>
  simp[wf_relabel, wf_server, server_bt_ok, LIST_TYPE_def, psmall_def, pinit_def, l1init_def,
       small_fds_def, small_def] >>
  conj_tac >- metis_tac[] >> xsimpl
QED

(* The stdio fds are open, the listen succeeds with listener k and the
   loop sleeps in round n: main stops in the final blocking poll *)
Theorem main_sleep_spec:
  limited_parts l0_names p ∧ l0_reach w0 w ∧ UNIT_TYPE () uv ∧
  l0_do «sys_fdok» [0w] 1 w = SOME (o0, w1, e0) ∧
  l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1) ∧
  l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2) ∧ stdio_all o0 o1 o2 ∧
  sys_listen_echo w3 = SOME (out, w4, ev) ∧ listen_fd out = SOME k ∧ k < 2147483648 ∧
  echo_b_rounds k w4 n = SOME (BSlept h evs cb) ⇒
  app (p:'ffi ffi_proj) main_v [uv] (L0_EV w0 w [])
    (POSTf nm. λc b. &(nm = «sys_poll» ∧ (c, b) = cb) *
                     (SEP_EXISTS w5. L0_EV w0 w5 ([e0; e1; e2; ev] ++ evs)) * GC)
Proof
  main_tac run_pfb_sleep_spec >>
  qexistsl [‘emp’, ‘w0’, ‘w4’, ‘[e0; e1; e2; ev]’, ‘evs’, ‘cb’] >>
  conj_tac
  >- (simp[] >>
      qexistsl [‘UNIT_TYPE’, ‘[n2w k]’, ‘h’, ‘echo_hw’, ‘n2w k’, ‘srelabel (server k)’, ‘n’,
                ‘pinit’] >>
      simp[wf_relabel, wf_server, server_bt_ok, LIST_TYPE_def, psmall_def, pinit_def, l1init_def,
           small_fds_def, small_def] >>
      metis_tac[]) >>
  xsimpl
QED
