(*
  The KV program's main on the honest L0 world (P4 step F): its specs, by
  honestL1MainSpec's specs of l1_main with the KV server (gkv_server_spec)
  and its L1 obligations (wf, pt_ok from kv_server_uses_ok).
*)
Theory honestKvL0Main
Ancestors
  ml_translator std_prelude cfDiv llist Marshalling
  asyncCore asyncLevel1 asyncCfActModel asyncCfActProg asyncM4Relabel asyncM4ServerUses
  asyncM3World asyncM3Prog asyncM3Loop asyncM4Loop asyncM4SockModel asyncRunOkGen
  asyncKvModel asyncTranslateKv
  honestL0 honestL0World honestL1Model honestL1PFModel
  honestL0Part honestL0Prog honestL0Proof honestL1PFProg honestL1PFSpec
  honestL1MainProg honestL1MainSpec honestKvL0Prog
Libs
  preamble ml_translatorLib ml_progLib cfLib basisFunctionsLib cfDivLib

val _ = translation_extends "honestKvL0Prog";

(* The loop's events after the listen gave listener k in world w1 *)
Overload kv_l0_run = “λk w1. l1_run kv_hw (srelabel (kv_server k)) k w1”

Theorem kv_pt_ok:
  pt_ok (n2w k) hw ifds (srelabel (kv_server k)) ws0
Proof
  irule relabel_pt_ok >> simp[wf_kv_server] >>
  metis_tac[REWRITE_RULE [uses_ok_def] kv_server_uses_ok]
QED

Theorem kv_port_conf_len:
  LENGTH kv_port_conf = 2
Proof
  EVAL_TAC
QED

Theorem kv_main_stdio_spec:
  UNIT_TYPE () uv ∧
  l0_do «sys_fdok» [0w] 1 w = SOME (o0, w1, e0) ∧
  l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1) ∧
  l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2) ∧ ¬l1_stdio_all o0 o1 o2 ⇒
  app (p:'ffi ffi_proj) main_v [uv] (L0_EV w0 w [])
    (POSTv v. &UNIT_TYPE () v * L0_EV w0 w3 [e0; e1; e2])
Proof
  rpt strip_tac >> xcf_with_def (fetch "honestKvL0Prog" "main_v_def") >>
  xapp_spec l1_main_stdio_spec >> xsimpl >> metis_tac[]
QED

Theorem kv_main_fail_spec:
  UNIT_TYPE () uv ∧
  l0_do «sys_fdok» [0w] 1 w = SOME (o0, w1, e0) ∧
  l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1) ∧
  l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2) ∧ l1_stdio_all o0 o1 o2 ∧
  sys_listen_at kv_port_conf w3 = SOME (out, w', ev) ∧ l1_listen_fd out = NONE ⇒
  app (p:'ffi ffi_proj) main_v [uv] (L0_EV w0 w [])
    (POSTv v. &UNIT_TYPE () v * L0_EV w0 w' [e0; e1; e2; ev])
Proof
  rpt strip_tac >> xcf_with_def (fetch "honestKvL0Prog" "main_v_def") >>
  assume_tac (fetch "honestKvL0Prog" "kv_port_conf_v_thm") >>
  xapp_spec l1_main_fail_spec >> xsimpl >> metis_tac[]
QED

Theorem kv_main_div_spec:
  limited_parts l0_names p ∧ l0_reach w0 w ∧ UNIT_TYPE () uv ∧
  l0_do «sys_fdok» [0w] 1 w = SOME (o0, w1, e0) ∧
  l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1) ∧
  l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2) ∧ l1_stdio_all o0 o1 o2 ∧
  sys_listen_at kv_port_conf w3 = SOME (out, w4, ev) ∧ l1_listen_fd out = SOME k ∧
  k < 2147483648 ⇒
  app (p:'ffi ffi_proj) main_v [uv] (L0_EV w0 w [])
    (POSTd io. io = LAPPEND (fromList [e0; e1; e2; ev]) (kv_l0_run k w4))
Proof
  rpt strip_tac >> xcf_with_def (fetch "honestKvL0Prog" "main_v_def") >>
  assume_tac (fetch "honestKvL0Prog" "kv_port_conf_v_thm") >>
  assume_tac (fetch "honestKvL0Prog" "kv_hw_v_thm") >>
  xapp_spec l1_main_div_spec >>
  qexistsl [‘emp’, ‘w4’, ‘w0’, ‘w’, ‘srelabel (kv_server k)’, ‘k’, ‘kv_hw’,
            ‘ev’, ‘e2’, ‘e1’, ‘e0’] >>
  simp[wf_relabel, wf_kv_server, kv_pt_ok] >> rpt conj_tac >>
  FIRST [
    rpt strip_tac >> xapp_spec gkv_server_spec >> simp[] >> NO_TAC,
    qexistsl [‘kv_port_conf’, ‘out’] >> simp[] >> NO_TAC,
    xsimpl >> NO_TAC]
QED
