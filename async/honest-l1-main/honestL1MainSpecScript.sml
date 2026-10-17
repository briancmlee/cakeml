(*
  The specs of the generic main l1_main conf hw mk (honestL1MainProg).
  It first calls sys_fdok on fds 0, 1 and 2 (D33); if one is closed it
  returns.  Otherwise the listen fails and it returns, or the listen
  succeeds with listener k and it diverges, running the prefetching L1
  loop with the server mk k.  The server enters only through mk's spec
  (a COMP of some model m), wf m and pt_ok (its actions are L1's
  well-formed actions).
*)
Theory honestL1MainSpec
Ancestors
  ml_translator std_prelude cfDiv llist Marshalling
  asyncCore asyncLevel1 asyncCfActModel asyncCfActProg
  asyncChoose asyncTranscript asyncServer asyncServerSafety asyncM4Relabel asyncM4ServerUses
  asyncM3World asyncM3Prog asyncM3Loop asyncM4Loop asyncM4SockModel asyncM4SockServer
  honestL1Inv honestL1PFInv
  honestL0 honestL0World honestL1Model honestL1PFModel
  honestL0Part honestL0Prog honestL0Proof honestL1PFProg honestL1PFSpec
  honestL1MainProg
Libs
  preamble ml_translatorLib ml_progLib cfLib basisFunctionsLib cfDivLib

val _ = translation_extends "honestL1MainProg";

(* The loop's events after the listen gave listener k in world w1 *)
Overload l1_run = “λhw m k w1. LFLATTEN (LGENLIST (λi. fromList
  (pround_evs (n2w k) hw (asyncM4LiveInterest$live [n2w k] (log_of m)) m (w1, pinit) i)) NONE)”

(* ------------------------------------------------------------------------
   A server's actions are L1's well-formed actions
   ------------------------------------------------------------------------ *)

(* In any history, a server in the socket vocabulary that accepts only on
   the listener k makes only well-formed L1 actions (reads are bufsz
   bytes, by the relabelling) *)
Theorem relabel_pact_ok:
  wf m0 ∧ (∀h. accepts_on k (trans m0 h)) ⇒
  EVERY (pact_ok (n2w k)) (new_actions (log_of (srelabel m0)) h)
Proof
  strip_tac >>
  simp[new_actions_relabel, EVERY_MEM, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
  qmatch_asmsub_abbrev_tac ‘MEM a (new_actions _ h')’ >>
  ‘MEM a (m0 h').actions’
    by (gvs[new_actions_def, log_of_def] >> every_case_tac >> gvs[] >>
        metis_tac[MEM_DROP_IMP]) >>
  ‘MEM a (MAP FST (trans m0 h'))’ by simp[MAP_FST_trans] >>
  first_x_assum (qspec_then ‘h'’ assume_tac) >>
  gvs[MEM_MAP, accepts_on_def, EVERY_MEM] >> first_x_assum drule >>
  Cases_on ‘FST y’ >>
  simp[sfa_def, pact_ok_def, honestL1InvTheory.act_ok_def, is_accept_def, bufsz_def]
QED

Theorem relabel_pt_ok:
  wf m0 ∧ (∀h. accepts_on k (trans m0 h)) ⇒
  pt_ok (n2w k) hw ifds (srelabel m0) ws0
Proof
  simp[pt_ok_def, relabel_pact_ok]
QED

(* ------------------------------------------------------------------------
   l1_main
   ------------------------------------------------------------------------ *)

Theorem l1_listen_spec:
  LIST_TYPE WORD conf confv ∧ sys_listen_at conf wa = SOME (out, wb, ev) ⇒
  app (p:'ffi ffi_proj) l1_listen_v [confv] (L0_EV w0 wa evs)
    (POSTv v. &LIST_TYPE WORD out v * L0_EV w0 wb (evs ++ [ev]))
Proof
  rpt strip_tac >> xcf_with_def (fetch "honestL1MainProg" "l1_listen_v_def") >>
  rpt (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &STRING_TYPE (bytes_str out) v * L0_EV w0 wb (evs ++ [ev])’
  >- (xapp_spec L0_listen_spec >> xsimpl >> qexists_tac ‘conf’ >>
      gvs[sys_listen_at_def, bytes_str_bytes_to_str]) >>
  xapp >> xsimpl >> qexists_tac ‘bytes_str out’ >>
  simp[bytes_str_bytes_to_str, str_to_bytes_bytes_to_str]
QED

(* D33: one sys_fdok call on fd f *)
Theorem l1_fdok_spec:
  NUM f fv ∧ l0_do «sys_fdok» [n2w f] 1 wa = SOME (out, wb, ev) ⇒
  app (p:'ffi ffi_proj) l1_fdok_v [fv] (L0_EV w0 wa evs)
    (POSTv v. &LIST_TYPE WORD out v * L0_EV w0 wb (evs ++ [ev]))
Proof
  rpt strip_tac >> xcf_with_def (fetch "honestL1MainProg" "l1_fdok_v_def") >>
  rpt (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &STRING_TYPE (bytes_str out) v * L0_EV w0 wb (evs ++ [ev])’
  >- (xapp_spec L0_fdok_spec >> xsimpl >> qexists_tac ‘[n2w f]’ >>
      gvs[l1_fdok_conf_def, bytes_str_bytes_to_str]) >>
  xapp >> xsimpl >> qexists_tac ‘bytes_str out’ >>
  simp[bytes_str_bytes_to_str, str_to_bytes_bytes_to_str]
QED

(* l1_main's first three calls, sys_fdok on fds 0, 1 and 2 *)
val stdio_tac =
  xcf_with_def (fetch "honestL1MainProg" "l1_main_v_def") >>
  xlet ‘POSTv v. &LIST_TYPE WORD o0 v * L0_EV w0 w1 [e0]’
  >- (xapp_spec (Q.INST [‘f’ |-> ‘0’] l1_fdok_spec) >>
      qexistsl [‘emp’, ‘w1’, ‘w’, ‘w0’, ‘o0’, ‘[]’, ‘e0’] >> xsimpl >> simp[NUM_def, INT_def]) >>
  xlet ‘POSTv v. &LIST_TYPE WORD o1 v * L0_EV w0 w2 [e0; e1]’
  >- (xapp_spec (Q.INST [‘f’ |-> ‘1’] l1_fdok_spec) >>
      qexistsl [‘emp’, ‘w2’, ‘w1’, ‘w0’, ‘o1’, ‘[e0]’, ‘e1’] >> xsimpl >> simp[NUM_def, INT_def]) >>
  xlet ‘POSTv v. &LIST_TYPE WORD o2 v * L0_EV w0 w3 [e0; e1; e2]’
  >- (xapp_spec (Q.INST [‘f’ |-> ‘2’] l1_fdok_spec) >>
      qexistsl [‘emp’, ‘w3’, ‘w2’, ‘w0’, ‘o2’, ‘[e0; e1]’, ‘e2’] >> xsimpl >> simp[NUM_def, INT_def]) >>
  (xlet_auto >- xsimpl) >> xif >> asm_exists_tac >> simp[];

(* A closed stdio fd: l1_main returns after the three calls *)
Theorem l1_main_stdio_spec:
  l0_do «sys_fdok» [0w] 1 w = SOME (o0, w1, e0) ∧
  l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1) ∧
  l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2) ∧ ¬l1_stdio_all o0 o1 o2 ⇒
  app (p:'ffi ffi_proj) l1_main_v [confv; hwv; mkv] (L0_EV w0 w [])
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

Theorem l1_listen_fd_lt:
  l1_listen_fd out = SOME k ⇒ k < dimword (:64)
Proof
  rw[l1_listen_fd_def, l0_res_of_def, AllCaseEqs(), dec_res_def] >>
  ‘LENGTH (TAKE 8 (TL out)) = 8’ by (Cases_on ‘out’ >> gvs[LENGTH_TAKE_EQ]) >>
  ‘w82n (TAKE 8 (TL out)) < 256 ** 8’ by (irule w82n_lt >> simp[]) >> fs[]
QED

(* The stdio fds are open and the listen fails: l1_main returns *)
Theorem l1_main_fail_spec:
  LIST_TYPE WORD conf confv ∧
  l0_do «sys_fdok» [0w] 1 w = SOME (o0, w1, e0) ∧
  l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1) ∧
  l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2) ∧ l1_stdio_all o0 o1 o2 ∧
  sys_listen_at conf w3 = SOME (out, w', ev) ∧ l1_listen_fd out = NONE ⇒
  app (p:'ffi ffi_proj) l1_main_v [confv; hwv; mkv] (L0_EV w0 w [])
    (POSTv v. &UNIT_TYPE () v * L0_EV w0 w' [e0; e1; e2; ev])
Proof
  rpt strip_tac >> stdio_tac >>
  xlet ‘POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w' [e0; e1; e2; ev]’
  >- (xapp_spec l1_listen_spec >>
      qexistsl [‘emp’, ‘w'’, ‘w3’, ‘w0’, ‘out’, ‘[e0; e1; e2]’, ‘ev’] >>
      rpt conj_tac >- (qexists_tac ‘conf’ >> simp[]) >> xsimpl) >>
  rpt (xlet_auto >- xsimpl) >> gvs[OPTION_TYPE_def] >> xmatch >>
  xcon >> xsimpl
QED

(* The stdio fds are open and the listen succeeds with a small listener k:
   l1_main runs the L1 loop with the server mk k forever *)
Theorem l1_main_div_spec:
  limited_parts l0_names p ∧ l0_reach w0 w ∧
  LIST_TYPE WORD conf confv ∧ NUM hw hwv ∧
  l0_do «sys_fdok» [0w] 1 w = SOME (o0, w1, e0) ∧
  l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1) ∧
  l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2) ∧ l1_stdio_all o0 o1 o2 ∧
  sys_listen_at conf w3 = SOME (out, w4, ev) ∧ l1_listen_fd out = SOME k ∧ k < 2147483648 ∧
  wf m ∧ pt_ok (n2w k) hw (asyncM4LiveInterest$live [n2w k] (log_of m)) m (w4, pinit) ∧
  (∀kv. NUM k kv ⇒
        app p mkv [kv] emp (POSTv cv. &COMP p SACT UNIT_TYPE SSNAP m cv)) ⇒
  app (p:'ffi ffi_proj) l1_main_v [confv; hwv; mkv] (L0_EV w0 w [])
    (POSTd io. io = LAPPEND (fromList [e0; e1; e2; ev]) (l1_run hw m k w4))
Proof
  rpt strip_tac >> drule l1_listen_fd_lt >> strip_tac >>
  ‘l0_reach w0 w4’
    by (gvs[sys_listen_at_def, l0_do_def, AllCaseEqs()] >> metis_tac[l0_reach_step]) >>
  stdio_tac >>
  xlet ‘POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w4 [e0; e1; e2; ev]’
  >- (xapp_spec l1_listen_spec >>
      qexistsl [‘emp’, ‘w4’, ‘w3’, ‘w0’, ‘out’, ‘[e0; e1; e2]’, ‘ev’] >>
      rpt conj_tac >- (qexists_tac ‘conf’ >> simp[]) >> xsimpl) >>
  rpt (xlet_auto >- xsimpl) >> gvs[OPTION_TYPE_def] >> xmatch >>
  assume_tac (fetch "honestL1MainProg" "pinit_v_thm") >>
  xlet ‘POSTv cv. &COMP p SACT UNIT_TYPE SSNAP m cv * L0_EV w0 w4 [e0; e1; e2; ev]’
  >- (qpat_x_assum ‘∀kv. NUM k kv ⇒ _’ xapp_spec >> xsimpl >> simp[]) >>
  rpt (xlet_auto >- (TRY xcon >> xsimpl)) >>
  gvs[] >> xapp_spec (INST_TYPE [alpha |-> “:unit”] run_pf_spec) >>
  qexistsl [‘emp’, ‘w0’, ‘w4’, ‘pinit’, ‘m’, ‘n2w k’, ‘hw’, ‘[n2w k]’, ‘[e0; e1; e2; ev]’] >>
  simp[LIST_TYPE_def, psmall_def, pinit_def, l1init_def, small_fds_def, small_def] >>
  rpt conj_tac >- (qexists_tac ‘UNIT_TYPE’ >> first_assum ACCEPT_TAC) >>
  xsimpl
QED
