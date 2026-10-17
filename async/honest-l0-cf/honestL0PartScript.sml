(*
  The honest L0 world (honestL0World) as a CakeML FFI part, for the CF
  specs of the sys_* wrappers.

  Minimal by construction: the part is parameterised by the starting world
  w0, and a state is encoded by its call history alone.  A state is
  reachable from w0 (l0_reach) if it satisfies the rely and replaying its
  history from w0 gives it back; every successful call keeps that
  (l0_reach_step), since l0_ffi_fn records exactly the call it answered.
  The part's ffi_next replays w0 along the decoded history and answers
  with l0_ffi_fn itself; an unreachable state is encoded as Num 0, on which
  every call fails.  None of the world's choice functions is encoded.

  MAIN: l0_parts_ok, the adequacy of the part: on every state, whenever
  the part answers a call, the L0 oracle (l0_oracle, the approved and
  conformance-tested world) answers it in the same way, and the part's
  new state is the encoding of the oracle's.  So CakeML's CF specs over
  this part are about init_state (l0_ffi w0) and nothing else.
*)
Theory honestL0Part
Ancestors
  cfHeapsBase cfStore cfFFIType ffi honestL0 honestL0World honestL0Rely
  honestL0WorldProps
Libs
  preamble

(* ------------------------------------------------------------------------
   Replaying a history
   ------------------------------------------------------------------------ *)

Definition l0_step_def:
  l0_step (SOME w) ((n, conf, bytes) : lcall) =
    (case l0_ffi_fn n conf bytes w of
     | SOME (FFIreturn _ w') => SOME w'
     | _ => NONE) ∧
  l0_step NONE _ = NONE
End

Definition l0_replay_def:
  l0_replay w0 (h : lcall list) = FOLDL l0_step (SOME w0) h
End

(* w is reachable from w0: it keeps the rely, and replaying its history
   from w0 gives it *)
Definition l0_reach_def:
  l0_reach w0 w ⇔ l0_rely w ∧ l0_replay w0 w.hist = SOME w
End

Theorem l0_ffi_fn_hist:
  l0_ffi_fn n conf bytes w = SOME (FFIreturn bytes' w') ⇒
  w'.hist = w.hist ++ [(n, conf, bytes)]
Proof
  simp[l0_ffi_fn_def, AllCaseEqs()] >> rw[] >> simp[]
QED

Theorem l0_reach_init:
  l0_rely w0 ∧ w0.hist = [] ⇒ l0_reach w0 w0
Proof
  simp[l0_reach_def, l0_replay_def]
QED

(* MAIN: a successful call keeps reachability *)
Theorem l0_reach_step:
  l0_reach w0 w ∧ l0_ffi_fn n conf bytes w = SOME (FFIreturn bytes' w') ⇒
  l0_reach w0 w'
Proof
  rw[l0_reach_def] >- metis_tac[l0_ffi_fn_length] >>
  drule l0_ffi_fn_hist >> simp[l0_replay_def, FOLDL_SNOC, GSYM SNOC_APPEND] >>
  strip_tac >> gvs[l0_replay_def, l0_step_def]
QED

(* ------------------------------------------------------------------------
   The encoding of a history
   ------------------------------------------------------------------------ *)

Definition enc_bytes_def:
  enc_bytes (bs : word8 list) = encode_list (Num o w2n) bs
End

Definition enc_lcall_def:
  enc_lcall ((n, conf, bytes) : lcall) =
    Cons (Str n) (Cons (enc_bytes conf) (enc_bytes bytes))
End

Definition enc_hist_def:
  enc_hist h = Cons (Num 1) (encode_list enc_lcall h)
End

Theorem enc_bytes_11[local]:
  enc_bytes x = enc_bytes y ⇔ x = y
Proof
  rw[enc_bytes_def, EQ_IMP_THM] >> irule encode_list_11 >>
  first_x_assum (irule_at Any) >> simp[]
QED

Theorem enc_lcall_11[local]:
  enc_lcall x = enc_lcall y ⇔ x = y
Proof
  PairCases_on ‘x’ >> PairCases_on ‘y’ >> rw[enc_lcall_def, enc_bytes_11]
QED

Theorem enc_hist_11:
  enc_hist x = enc_hist y ⇔ x = y
Proof
  rw[enc_hist_def, EQ_IMP_THM] >> irule encode_list_11 >>
  first_x_assum (irule_at Any) >> simp[enc_lcall_11]
QED

Definition dec_hist_def:
  dec_hist s = some h. enc_hist h = s
End

Theorem dec_hist_enc[simp]:
  dec_hist (enc_hist h) = SOME h
Proof
  simp[dec_hist_def, enc_hist_11]
QED

(* ------------------------------------------------------------------------
   The part
   ------------------------------------------------------------------------ *)

(* The C entry points the servers use (sys_connect / sys_connerr: client
   side, later) *)
Definition l0_names_def:
  l0_names = [«sys_listen»; «sys_poll»; «sys_accept»; «sys_recv»; «sys_send»;
              «sys_shutdown»; «sys_close»; «sys_connect»; «sys_connerr»; «sys_fdok»]
End

Definition l0_enc_def:
  l0_enc w0 w = if l0_reach w0 w then enc_hist w.hist else Num 0
End

Definition l0_next_def:
  l0_next w0 (m : mlstring) conf bytes s =
    case dec_hist s of
    | NONE => NONE
    | SOME h =>
        case l0_replay w0 h of
        | NONE => NONE
        | SOME w =>
            if ¬l0_reach w0 w ∨ ¬MEM m l0_names then NONE else
            case l0_ffi_fn m conf bytes w of
            | SOME (FFIreturn bytes' w') => SOME (FFIreturn bytes' (enc_hist w'.hist))
            | SOME FFIdiverge => SOME FFIdiverge
            | NONE => NONE
End

Definition l0_proj_def:
  l0_proj w0 : l0world ffi_proj =
    ((λw. FEMPTY |++ MAP (λn. (n, l0_enc w0 w)) l0_names),
     [(l0_names, l0_next w0)])
End

Theorem dec_hist_Num0[local]:
  dec_hist (Num 0) = NONE
Proof
  simp[dec_hist_def] >> DEEP_INTRO_TAC some_intro >> simp[enc_hist_def]
QED

Theorem names_apply[local]:
  MEM m l0_names ⇒ (FEMPTY |++ MAP (λn. (n, v)) l0_names) ' m = v
Proof
  simp[l0_names_def] >> strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem names_lookup[local]:
  MEM m l0_names ⇒ FLOOKUP (FEMPTY |++ MAP (λn. (n, v)) l0_names) m = SOME v
Proof
  simp[l0_names_def] >> strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem names_update[local]:
  FEMPTY |++ MAP (λn. (n, v)) l0_names |++ MAP (λn. (n, v')) l0_names =
  FEMPTY |++ MAP (λn. (n, v')) l0_names
Proof
  rw[fmap_eq_flookup, FLOOKUP_FUPDATE_LIST, l0_names_def] >> rw[]
QED

Theorem l0_replay_reach[local]:
  l0_reach w0 x ∧ l0_replay w0 x.hist = SOME w ⇒ w = x
Proof
  rw[l0_reach_def] >> gvs[]
QED

Theorem l0_next_return[local]:
  l0_next w0 m conf bytes (l0_enc w0 x) = SOME (FFIreturn nb s) ⇒
  ∃x'. l0_reach w0 x ∧ l0_ffi_fn m conf bytes x = SOME (FFIreturn nb x') ∧
       s = l0_enc w0 x'
Proof
  Cases_on ‘l0_reach w0 x’ >> simp[l0_enc_def, l0_next_def, dec_hist_Num0] >>
  simp[AllCaseEqs()] >> strip_tac >>
  ‘w = x’ by metis_tac[l0_replay_reach] >> gvs[] >>
  ‘l0_reach w0 w'’ by metis_tac[l0_reach_step] >> simp[]
QED

Theorem l0_next_diverge[local]:
  l0_next w0 m conf bytes (l0_enc w0 x) = SOME FFIdiverge ⇒
  l0_ffi_fn m conf bytes x = SOME FFIdiverge
Proof
  Cases_on ‘l0_reach w0 x’ >> simp[l0_enc_def, l0_next_def, dec_hist_Num0] >>
  simp[AllCaseEqs()] >> strip_tac >>
  ‘w = x’ by metis_tac[l0_replay_reach] >> gvs[]
QED

(* MAIN: the part is adequate.  On every state, a call the part answers is
   answered by the L0 oracle the same way, and the part's new state
   encodes the oracle's *)
Theorem l0_parts_ok:
  l0_rely w0 ∧ w0.hist = [] ⇒ parts_ok (l0_ffi w0) (l0_proj w0)
Proof
  strip_tac >> simp[parts_ok_def, l0_proj_def, l0_ffi_def] >> rpt conj_tac
  >- simp[l0_names_def]
  >- (qexists_tac ‘l0_enc w0 w0’ >> simp[names_lookup])
  >- (rpt strip_tac >> gvs[names_apply] >> drule l0_next_diverge >>
      simp[l0_oracle_def])
  >> rpt gen_tac >> strip_tac >> gvs[names_apply] >>
  drule l0_next_return >> strip_tac >> gvs[] >>
  qpat_assum ‘l0_reach w0 _’ (strip_assume_tac o REWRITE_RULE [l0_reach_def]) >>
  conj_tac >- metis_tac[l0_ffi_fn_length] >>
  simp[l0_oracle_def, names_update]
QED
