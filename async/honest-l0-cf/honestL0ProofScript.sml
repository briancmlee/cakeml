(*
  The CF specs of the L0 module (honestL0Prog) against the honest L0
  world, through its FFI part (honestL0Part).

  L0_EV w0 w evs: the program owns the L0 world part, in state w reachable
  from the start world w0, with the events evs so far.  Each wrapper's spec
  is stated with L1's own call function (honestL1Model's l0_do), so L1's
  model and its CakeML code make the same calls by construction:

     l0_do «sys_x» conf alen w = SOME (out, w', ev) ⇒
     L0.x (bytes_str conf) alen  returns  bytes_str out,
       from L0_EV w0 w evs  to  L0_EV w0 w' (evs ++ [ev])
*)
Theory honestL0Proof
Ancestors
  ml_translator cfHeapsBase cfMain Word8ArrayProof mlstring
  honestL0 honestL0World honestL0Rely honestL1Model honestL0Part honestL0Prog
Libs
  preamble ml_translatorLib ml_progLib cfLib basisFunctionsLib

val _ = translation_extends "honestL0Prog";

Overload bytes_str = “λbs:word8 list. implode (MAP (CHR o w2n) bs)”

(* L0_EV w0 w evs: the program owns the L0 part, in a state reachable from
   w0, with the events evs *)
Definition L0_EV_def:
  L0_EV w0 w evs =
    one (FFI_part (l0_enc w0 w) (l0_next w0) l0_names evs) * &(l0_reach w0 w)
End

(* The part answers a reachable state's call as l0_ffi_fn does *)
Theorem l0_next_call:
  l0_reach w0 w ∧ MEM n l0_names ∧
  l0_ffi_fn n conf bytes w = SOME (FFIreturn out w') ⇒
  l0_next w0 n conf bytes (l0_enc w0 w) = SOME (FFIreturn out (l0_enc w0 w')) ∧
  l0_reach w0 w'
Proof
  strip_tac >> ‘l0_reach w0 w'’ by metis_tac[l0_reach_step] >>
  gvs[l0_next_def, l0_enc_def] >> fs[l0_reach_def]
QED

Theorem l0_do_ffi:
  l0_do n conf alen w = SOME (out, w', ev) ⇒
  l0_ffi_fn n conf (REPLICATE alen 0w) w = SOME (FFIreturn out w') ∧
  ev = IO_event (ExtCall n) conf (ZIP (REPLICATE alen 0w, out))
Proof
  simp[l0_do_def, AllCaseEqs()] >> rw[] >> simp[]
QED

Theorem l0_do_length:
  l0_reach w0 w ∧ l0_do n conf alen w = SOME (out, w', ev) ⇒ LENGTH out = alen
Proof
  rw[] >> drule l0_do_ffi >> strip_tac >> fs[l0_reach_def] >>
  drule_all honestL0WorldPropsTheory.l0_ffi_fn_length >> simp[]
QED

(* One FFI call on a fresh buffer of alen zero bytes, then the buffer as a
   string *)
fun l0_call_tac vdef name =
  rpt strip_tac >> xcf_with_def vdef >> simp[L0_EV_def] >> xpull >>
  drule l0_do_ffi >> strip_tac >>
  ‘LENGTH out = alen’ by (irule l0_do_length >> metis_tac[]) >>
  ‘MEM ^name l0_names’ by simp[l0_names_def] >>
  drule_all l0_next_call >> strip_tac >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  rename1 ‘W8ARRAY av (REPLICATE _ _)’ >>
  xlet ‘POSTv uv. W8ARRAY av out *
          one (FFI_part (l0_enc w0 w') (l0_next w0) l0_names (evs ++ [ev]))’
  >- (xffi >> xsimpl >> gvs[STRING_TYPE_def] >>
      qexistsl [‘conf’, ‘emp’, ‘l0_enc w0 w’, ‘l0_next w0’, ‘l0_names’, ‘evs’] >>
      simp[] >> conj_tac >- EVAL_TAC >> xsimpl) >>
  xapp >>
  qexistsl [‘one (FFI_part (l0_enc w0 w') (l0_next w0) l0_names (evs ++ [ev]))’,
            ‘0’, ‘out’, ‘alen’] >>
  xsimpl >> simp[NUM_def, INT_def, TAKE_LENGTH_ID_rwt];

Theorem L0_listen_spec:
  STRING_TYPE (bytes_str conf) confv ∧ NUM alen alenv ∧
  l0_do «sys_listen» conf alen w = SOME (out, w', ev) ⇒
  app (p:'ffi ffi_proj) L0_listen_v [confv; alenv] (L0_EV w0 w evs)
    (POSTv v. &STRING_TYPE (bytes_str out) v * L0_EV w0 w' (evs ++ [ev]))
Proof
  l0_call_tac (fetch "honestL0Prog" "L0_listen_v_def") “«sys_listen»”
QED

Theorem l0_do_buf_ffi:
  l0_do_buf n conf bytes w = SOME (out, w', ev) ⇒
  l0_ffi_fn n conf bytes w = SOME (FFIreturn out w') ∧
  ev = IO_event (ExtCall n) conf (ZIP (bytes, out))
Proof
  simp[l0_do_buf_def, AllCaseEqs()] >> rw[] >> simp[]
QED

Theorem bytes_str_bytes[local]:
  MAP (n2w o ORD) (explode (bytes_str bs)) = bs : word8 list ∧
  strlen (bytes_str bs) = LENGTH bs
Proof
  simp[MAP_MAP_o, o_DEF] >>
  ‘∀b : word8. w2n b < 256’ by (gen_tac >> assume_tac (INST_TYPE [alpha |-> “:8”] w2n_lt) >> fs[]) >>
  simp[ORD_CHR] >> Induct_on ‘bs’ >> simp[]
QED

(* D20: the call's buffer carries the entries in *)
Theorem L0_poll_spec:
  STRING_TYPE (bytes_str conf) confv ∧ STRING_TYPE (bytes_str bytes) bufv ∧
  l0_do_buf «sys_poll» conf bytes w = SOME (out, w', ev) ⇒
  app (p:'ffi ffi_proj) L0_poll_v [confv; bufv] (L0_EV w0 w evs)
    (POSTv v. &STRING_TYPE (bytes_str out) v * L0_EV w0 w' (evs ++ [ev]))
Proof
  rpt strip_tac >> xcf_with_def (fetch "honestL0Prog" "L0_poll_v_def") >>
  simp[L0_EV_def] >> xpull >>
  drule l0_do_buf_ffi >> strip_tac >>
  ‘LENGTH out = LENGTH bytes’
    by (fs[l0_reach_def] >> drule_all honestL0WorldPropsTheory.l0_ffi_fn_length >> simp[]) >>
  ‘MEM «sys_poll» l0_names’ by simp[l0_names_def] >>
  drule_all l0_next_call >> strip_tac >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  rename1 ‘W8ARRAY av (REPLICATE _ _)’ >>
  xlet ‘POSTv uv. W8ARRAY av bytes * one (FFI_part (l0_enc w0 w) (l0_next w0) l0_names evs)’
  >- (xapp >> xsimpl >> qexistsl [‘bytes_str bytes’, ‘LENGTH bytes’] >>
      simp[bytes_str_bytes, mlstringTheory.substring_def] >>
      ‘SEG (LENGTH bytes) 0 (MAP (CHR ∘ w2n) bytes) = MAP (CHR ∘ w2n) bytes’
        by metis_tac[SEG_LENGTH_ID, LENGTH_MAP] >>
      simp[] >> qspec_then ‘bytes’ mp_tac (Q.GEN ‘bs’ (cj 1 bytes_str_bytes)) >> simp[]) >>
  xlet ‘POSTv uv. W8ARRAY av out *
          one (FFI_part (l0_enc w0 w') (l0_next w0) l0_names (evs ++ [ev]))’
  >- (xffi >> xsimpl >> gvs[STRING_TYPE_def] >>
      qexistsl [‘conf’, ‘emp’, ‘l0_enc w0 w’, ‘l0_next w0’, ‘l0_names’, ‘evs’] >>
      simp[] >> conj_tac >- EVAL_TAC >> xsimpl) >>
  xapp >>
  qexistsl [‘one (FFI_part (l0_enc w0 w') (l0_next w0) l0_names (evs ++ [ev]))’,
            ‘0’, ‘out’, ‘LENGTH bytes’] >>
  xsimpl >> simp[NUM_def, INT_def, TAKE_LENGTH_ID_rwt]
QED

Theorem L0_accept_spec:
  STRING_TYPE (bytes_str conf) confv ∧ NUM alen alenv ∧
  l0_do «sys_accept» conf alen w = SOME (out, w', ev) ⇒
  app (p:'ffi ffi_proj) L0_accept_v [confv; alenv] (L0_EV w0 w evs)
    (POSTv v. &STRING_TYPE (bytes_str out) v * L0_EV w0 w' (evs ++ [ev]))
Proof
  l0_call_tac (fetch "honestL0Prog" "L0_accept_v_def") “«sys_accept»”
QED

Theorem L0_recv_spec:
  STRING_TYPE (bytes_str conf) confv ∧ NUM alen alenv ∧
  l0_do «sys_recv» conf alen w = SOME (out, w', ev) ⇒
  app (p:'ffi ffi_proj) L0_recv_v [confv; alenv] (L0_EV w0 w evs)
    (POSTv v. &STRING_TYPE (bytes_str out) v * L0_EV w0 w' (evs ++ [ev]))
Proof
  l0_call_tac (fetch "honestL0Prog" "L0_recv_v_def") “«sys_recv»”
QED

Theorem L0_send_spec:
  STRING_TYPE (bytes_str conf) confv ∧ NUM alen alenv ∧
  l0_do «sys_send» conf alen w = SOME (out, w', ev) ⇒
  app (p:'ffi ffi_proj) L0_send_v [confv; alenv] (L0_EV w0 w evs)
    (POSTv v. &STRING_TYPE (bytes_str out) v * L0_EV w0 w' (evs ++ [ev]))
Proof
  l0_call_tac (fetch "honestL0Prog" "L0_send_v_def") “«sys_send»”
QED

Theorem L0_shutdown_spec:
  STRING_TYPE (bytes_str conf) confv ∧ NUM alen alenv ∧
  l0_do «sys_shutdown» conf alen w = SOME (out, w', ev) ⇒
  app (p:'ffi ffi_proj) L0_shutdown_v [confv; alenv] (L0_EV w0 w evs)
    (POSTv v. &STRING_TYPE (bytes_str out) v * L0_EV w0 w' (evs ++ [ev]))
Proof
  l0_call_tac (fetch "honestL0Prog" "L0_shutdown_v_def") “«sys_shutdown»”
QED

Theorem L0_close_spec:
  STRING_TYPE (bytes_str conf) confv ∧ NUM alen alenv ∧
  l0_do «sys_close» conf alen w = SOME (out, w', ev) ⇒
  app (p:'ffi ffi_proj) L0_close_v [confv; alenv] (L0_EV w0 w evs)
    (POSTv v. &STRING_TYPE (bytes_str out) v * L0_EV w0 w' (evs ++ [ev]))
Proof
  l0_call_tac (fetch "honestL0Prog" "L0_close_v_def") “«sys_close»”
QED
