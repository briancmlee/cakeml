(*
  The blocking echo program's main on the honest L0 world: the listen
  fails and main returns; or it succeeds and main runs the blocking L1
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

(* The listen fails: main returns *)
Theorem main_fail_spec:
  UNIT_TYPE () uv ∧ sys_listen_echo w = SOME (out, w', ev) ∧ listen_fd out = NONE ⇒
  app (p:'ffi ffi_proj) main_v [uv] (L0_EV w0 w [])
    (POSTv v. &UNIT_TYPE () v * L0_EV w0 w' [ev])
Proof
  rpt strip_tac >> xcf_with_def (fetch "honestEchoL0BProg" "main_v_def") >>
  (xlet_auto >- (xcon >> xsimpl)) >>
  xlet ‘POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w' [ev]’
  >- (xapp_spec c_listen_spec >> qexistsl [‘emp’, ‘w'’, ‘w’, ‘w0’, ‘out’, ‘[]’, ‘ev’] >>
      xsimpl >> simp[]) >>
  rpt (xlet_auto >- xsimpl) >> gvs[OPTION_TYPE_def] >> xmatch >>
  xcon >> xsimpl
QED

(* The blocking loop's run for the echo on listener k, from w1 *)
Overload echo_b_rounds = “λk w1. brounds_t (n2w k) echo_hw (asyncM4LiveInterest$live [n2w k] (log_of (srelabel (server k))))
                                   (srelabel (server k)) (w1, pinit)”

Overload echo_l0b_run = “λk w1. LFLATTEN (LGENLIST (λi. fromList
  (bround_evs (n2w k) echo_hw (asyncM4LiveInterest$live [n2w k] (log_of (srelabel (server k)))) (srelabel (server k)) (w1, pinit) i)) NONE)”

(* main up to the loop, then the loop's spec *)
fun main_tac loop_spec =
  rpt strip_tac >> drule listen_fd_lt >> strip_tac >>
  ‘l0_reach w0 w1’
    by (gvs[sys_listen_echo_def, l0_do_def, AllCaseEqs()] >> metis_tac[l0_reach_step]) >>
  xcf_with_def (fetch "honestEchoL0BProg" "main_v_def") >>
  (xlet_auto >- (xcon >> xsimpl)) >>
  xlet ‘POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w1 [ev]’
  >- (xapp_spec c_listen_spec >> qexistsl [‘emp’, ‘w1’, ‘w’, ‘w0’, ‘out’, ‘[]’, ‘ev’] >>
      xsimpl >> simp[]) >>
  rpt (xlet_auto >- xsimpl) >> gvs[OPTION_TYPE_def] >> xmatch >>
  assume_tac (fetch "honestEchoL0BProg" "echo_hw_v_thm") >>
  assume_tac (fetch "honestEchoL0BProg" "pinit_v_thm") >>
  xlet ‘POSTv cv. &COMP p SACT UNIT_TYPE SSNAP (srelabel (server k)) cv * L0_EV w0 w1 [ev]’
  >- (xapp_spec sserver_spec >> xsimpl >> qexists_tac ‘k’ >> simp[]) >>
  rpt (xlet_auto >- (TRY xcon >> xsimpl)) >>
  gvs[] >> xapp_spec (INST_TYPE [alpha |-> “:unit”] loop_spec);

(* The listen succeeds with listener k and the loop never sleeps: main
   diverges *)
Theorem main_div_spec:
  limited_parts l0_names p ∧ l0_reach w0 w ∧ UNIT_TYPE () uv ∧
  sys_listen_echo w = SOME (out, w1, ev) ∧ listen_fd out = SOME k ∧ k < 2147483648 ∧
  bt_awake (n2w k) echo_hw (asyncM4LiveInterest$live [n2w k] (log_of (srelabel (server k)))) (srelabel (server k)) (w1, pinit) ⇒
  app (p:'ffi ffi_proj) main_v [uv] (L0_EV w0 w [])
    (POSTd io. io = LAPPEND (fromList [ev]) (echo_l0b_run k w1))
Proof
  main_tac run_pfb_div_spec >>
  qexistsl [‘emp’, ‘w0’, ‘w1’, ‘pinit’, ‘srelabel (server k)’, ‘n2w k’, ‘echo_hw’, ‘[n2w k]’, ‘[ev]’] >>
  simp[wf_relabel, wf_server, server_bt_ok, LIST_TYPE_def, psmall_def, pinit_def, l1init_def,
       small_fds_def, small_def] >>
  conj_tac >- metis_tac[] >> xsimpl
QED

(* The listen succeeds with listener k and the loop sleeps in round n:
   main stops in the final blocking poll *)
Theorem main_sleep_spec:
  limited_parts l0_names p ∧ l0_reach w0 w ∧ UNIT_TYPE () uv ∧
  sys_listen_echo w = SOME (out, w1, ev) ∧ listen_fd out = SOME k ∧ k < 2147483648 ∧
  echo_b_rounds k w1 n = SOME (BSlept h evs cb) ⇒
  app (p:'ffi ffi_proj) main_v [uv] (L0_EV w0 w [])
    (POSTf nm. λc b. &(nm = «sys_poll» ∧ (c, b) = cb) *
                     (SEP_EXISTS w2. L0_EV w0 w2 ([ev] ++ evs)) * GC)
Proof
  main_tac run_pfb_sleep_spec >>
  qexistsl [‘emp’, ‘w0’, ‘w1’, ‘[ev]’, ‘evs’, ‘cb’] >>
  conj_tac
  >- (simp[] >>
      qexistsl [‘UNIT_TYPE’, ‘[n2w k]’, ‘h’, ‘echo_hw’, ‘n2w k’, ‘srelabel (server k)’, ‘n’,
                ‘pinit’] >>
      simp[wf_relabel, wf_server, server_bt_ok, LIST_TYPE_def, psmall_def, pinit_def, l1init_def,
           small_fds_def, small_def] >>
      metis_tac[]) >>
  xsimpl
QED
