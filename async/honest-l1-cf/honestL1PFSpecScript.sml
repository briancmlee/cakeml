(*
  The CF specs of the prefetching L1's CakeML code (honestL1PFProg)
  against its model (honestL1PFModel).

  Every world function's spec is stated with the model function itself:
  if the model's step returns SOME (results, (w', ps'), events), the code,
  from L0_EV w0 w evs, returns the same results and state, and ends in
  L0_EV w0 w' (evs ++ events).  The code's calls are the model's calls
  (honestL0Proof's L0_x_spec is stated with l0_do, which the model's
  sys_* use), so the trace of the code is the model's trace.
*)
Theory honestL1PFSpec
Ancestors
  ml_translator cfHeapsBase Word8ArrayProof mlstring
  honestL0 honestL0World honestL1Model honestL1PFModel honestL0Part
  honestL0Prog honestL0Proof honestL1PFProg ffiSpikeSocketFFI
Libs
  preamble ml_translatorLib ml_progLib cfLib basisFunctionsLib

val _ = translation_extends "honestL1PFProg";

Theorem bytes_str_bytes_to_str:
  bytes_str bs = bytes_to_str bs
Proof
  simp[bytes_to_str_def, combinTheory.o_DEF]
QED

(* ------------------------------------------------------------------------
   The calls
   ------------------------------------------------------------------------ *)

(* c_x: the model's sys_x, through L0.x *)
fun call_tac vdef l0spec =
  rpt strip_tac >> xcf_with_def vdef >>
  rpt (xlet_auto >- xsimpl) >>
  xlet ‘POSTv v. &STRING_TYPE (bytes_str out) v * L0_EV w0 w' (evs ++ [ev])’
  >- (xapp_spec l0spec >> xsimpl >>
      gvs[sys_accept_def, sys_recv_def, sys_send_def, sys_close_def, sys_poll_def,
          bytes_str_bytes_to_str] >> metis_tac[]) >>
  xapp >> xsimpl >> qexists_tac ‘bytes_str out’ >>
  simp[bytes_str_bytes_to_str, str_to_bytes_bytes_to_str];

Theorem c_accept_spec:
  WORD l lv ∧ sys_accept l w = SOME (out, w', ev) ⇒
  app (p:'ffi ffi_proj) c_accept_v [lv] (L0_EV w0 w evs)
    (POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w' (evs ++ [ev]))
Proof
  call_tac (fetch "honestL1PFProg" "c_accept_v_def") L0_accept_spec
QED

Theorem c_recv_spec:
  WORD f fv ∧ NUM n nv ∧ sys_recv f n w = SOME (out, w', ev) ⇒
  app (p:'ffi ffi_proj) c_recv_v [fv; nv] (L0_EV w0 w evs)
    (POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w' (evs ++ [ev]))
Proof
  call_tac (fetch "honestL1PFProg" "c_recv_v_def") L0_recv_spec
QED

Theorem c_send_spec:
  WORD f fv ∧ LIST_TYPE WORD bs bsv ∧ sys_send f bs w = SOME (out, w', ev) ⇒
  app (p:'ffi ffi_proj) c_send_v [fv; bsv] (L0_EV w0 w evs)
    (POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w' (evs ++ [ev]))
Proof
  call_tac (fetch "honestL1PFProg" "c_send_v_def") L0_send_spec
QED

Theorem c_close_spec:
  WORD f fv ∧ sys_close f w = SOME (out, w', ev) ⇒
  app (p:'ffi ffi_proj) c_close_v [fv] (L0_EV w0 w evs)
    (POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w' (evs ++ [ev]))
Proof
  call_tac (fetch "honestL1PFProg" "c_close_v_def") L0_close_spec
QED

Theorem c_poll_spec:
  LIST_TYPE (PAIR_TYPE WORD NUM) fes fesv ∧ sys_poll fes w = SOME (out, w', ev) ⇒
  app (p:'ffi ffi_proj) c_poll_v [fesv] (L0_EV w0 w evs)
    (POSTv v. &LIST_TYPE WORD out v * L0_EV w0 w' (evs ++ [ev]))
Proof
  call_tac (fetch "honestL1PFProg" "c_poll_v_def") L0_poll_spec
QED

(* ------------------------------------------------------------------------
   The model's pdo, as the code splits it
   ------------------------------------------------------------------------ *)

Theorem pdo_Accept_split:
  pdo lfd (w, ps) (Accept l) = SOME (r, (w', ps'), evs1) ⇒
  w' = w ∧ evs1 = [] ∧
  (pacc lfd ps = NONE ∧ r = Accepted NONE ∧ ps' = ps ∨
   ∃h. pacc lfd ps = SOME (h, ps') ∧ r = Accepted (SOME h))
Proof
  rw[pdo_def, pacc_def, AllCaseEqs()] >> simp[]
QED

Theorem pdo_Read_split:
  pdo lfd (w, ps) (Read h n) = SOME (r, (w', ps'), evs1) ⇒
  (∃ro. pread_step ps h n = RkGot ro ps' ∧ r = Got ro ∧ w' = w ∧ evs1 = []) ∨
  (∃f ps0 out ev. pread_step ps h n = RkClose f ps0 ∧
     sys_close f w = SOME (out, w', ev) ∧ ps' = pclose_upd f ps0 ∧
     r = Got (SOME []) ∧ evs1 = [ev])
Proof
  rw[pdo_def, pread_step_def, AllCaseEqs(), l1_close_def, pclose_upd_def] >>
  gvs[] >> pairarg_tac >> gvs[]
QED

Theorem pdo_Write_split:
  pdo lfd (w, ps) (Write h bs) = SOME (r, (w', ps'), evs1) ⇒
  r = Wrote ∧
  ((pwrite_step ps h bs = WkDone ps' ∧ w' = w ∧ evs1 = []) ∨
   (∃f out ev. pwrite_step ps h bs = WkSend f ∧ sys_send f bs w = SOME (out, w', ev) ∧
      ps' = psend_upd f bs out ps ∧ evs1 = [ev]))
Proof
  rw[pdo_def, l1do_def, pwrite_step_def, psend_upd_def, AllCaseEqs()] >> gvs[]
QED
