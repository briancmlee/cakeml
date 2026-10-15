(*
  The blocking event loop (Level 2), proved with CakeML's divergence CF.

      fun bstep c = case c of (acts, s) =>
        let val rs = bperform acts
            val b  = case s of Done2 x => bget_ready ()
                     | Pending2 es k => (case acts of [] => bselect es
                                                   | _ => bget_ready ())
        in poll2 c (b, 0, rs) end
      fun brun c = brun (bstep c)

  When the computation has no action to perform and is waiting, the loop
  does not poll: it blocks in `select` on the events the computation
  declares (its Level 2 interest), and the world lets the other rounds
  pass.  The FFI is asyncL2BlkFfi (cf-actions' byte stream plus select).

  MAIN (brun_spec): the loop diverges, and its I/O trace is the
  concatenation of bround_events c ws i over all rounds i.  With
  trace_actions_brounds and blocking_same_actions, the actions in the
  trace are the model computation's action log, which is the same as
  under the polling loop of cf-actions (no busy waiting).
*)
Theory asyncL2BlkLoop
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncLevel2 asyncSched2 asyncCfActModel
  asyncCfActProg asyncCfActWorld asyncL2BlkModel asyncL2BlkProg
  asyncL2BlkSpec asyncL2BlkWorld asyncL2BlkFfi cfDiv ml_translator
  mlbasicsProg Word8Prog Word8ArrayProof llist
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib
  ml_translatorLib

val _ = translation_extends "asyncL2BlkProg"

(* ------------------------------------------------------------------------
   The code
   ------------------------------------------------------------------------ *)

(* The declared events, as the config string of select *)
Definition byte_chr_def:
  byte_chr (w:word8) = CHR (w2n w)
End

val r = translate byte_chr_def;

Theorem byte_chr_side[local]:
  byte_chr_side w
Proof
  simp[fetch "-" "byte_chr_side_def", w2n_lt_256]
QED

val _ = update_precondition byte_chr_side;

Definition bytes_str_def:
  bytes_str l = implode (MAP byte_chr l)
End

val r = translate bytes_str_def;

Quote add_cakeml:
  fun bdo_act a =
    let
      val buf = Word8Array.array 1 a
      val _ = #(act) "" buf
    in Word8Array.sub buf 0 end;

  fun bperform acts =
    case acts of
      [] => []
    | a :: rest => let val r = bdo_act a in r :: bperform rest end;

  fun bget_ready u =
    let
      val buf = Word8Array.array 1 (Word8.fromInt 0)
      val _ = #(ready) "" buf
    in Word8Array.sub buf 0 end;

  fun bselect es =
    let
      val buf = Word8Array.array 1 (Word8.fromInt 0)
      val _ = #(select) (bytes_str es) buf
    in Word8Array.sub buf 0 end;

  fun bstep c =
    case c of (acts, s) =>
      let
        val rs = bperform acts
        val b = (case s of
                   Done2 x => bget_ready ()
                 | Pending2 es k =>
                     (case acts of [] => bselect es | a :: r => bget_ready ()))
      in poll2 c (b, 0, rs) end;
End

Quote add_cakeml:
  fun brun c = brun (bstep c);
End

val st = get_ml_prog_state ();

(* ------------------------------------------------------------------------
   Specs of the FFI wrappers
   ------------------------------------------------------------------------ *)


Definition BREADY1_def:
  BREADY1 rdy v ⇔ ∃b:word8. rdy = {b} ∧ WORD b v
End

Theorem sdrop_1[local]:
  sdrop 1 ws = ws o SUC
Proof
  simp[sdrop_def, FUN_EQ_THM, ADD1]
QED

Theorem bdo_act_spec:
  limited_parts io2_names p ∧ WORD a av ⇒
  app (p:'ffi ffi_proj) bdo_act_v [av] (IOS2 ws evs)
    (POSTv v. &WORD (ws 0) v * IOS2 (sdrop 1 ws) (evs ++ [act_event a (ws 0)]))
Proof
  rpt strip_tac >> xcf_with_def (fetch "-" "bdo_act_v_def") >>
  xlet_auto >- xsimpl >>
  rename1 ‘W8ARRAY bv’ >>
  ‘REPLICATE 1 a = [a]’ by EVAL_TAC >>
  xlet ‘POSTv u. W8ARRAY bv [ws 0] * IOS2 (sdrop 1 ws) (evs ++ [act_event a (ws 0)])’
  >- (xffi >> xsimpl >>
      qexistsl [‘emp’, ‘io_state ws’, ‘io2_update’, ‘io2_names’, ‘evs’] >>
      simp[io2_names_def, IOS2_def, io2_update_act_ready, act_event_def] >>
      xsimpl) >>
  xapp >> xsimpl >> simp[]
QED

Theorem bperform_spec:
  ∀acts av ws evs.
    limited_parts io2_names p ∧ LIST_TYPE WORD acts av ⇒
    app (p:'ffi ffi_proj) bperform_v [av] (IOS2 ws evs)
      (POSTv v. &LIST_TYPE WORD (GENLIST ws (LENGTH acts)) v *
                IOS2 (sdrop (LENGTH acts) ws)
                   (evs ++ MAP2 act_event acts (GENLIST ws (LENGTH acts))))
Proof
  Induct >> rpt strip_tac >> xcf_with_def (fetch "-" "bperform_v_def") >>
  gvs[LIST_TYPE_def] >> xmatch
  >- (xcon >> xsimpl >> simp[LIST_TYPE_def])
  >- (xlet ‘POSTv r. &WORD (ws 0) r * IOS2 (sdrop 1 ws) (evs ++ [act_event h (ws 0)])’
      >- (xapp >> simp[]) >>
      xlet ‘POSTv rv. &LIST_TYPE WORD (GENLIST (sdrop 1 ws) (LENGTH acts)) rv *
              IOS2 (sdrop (LENGTH acts) (sdrop 1 ws))
                 (evs ++ [act_event h (ws 0)] ++
                  MAP2 act_event acts (GENLIST (sdrop 1 ws) (LENGTH acts)))’
      >- (xapp >> simp[]) >>
      xcon >> simp[sdrop_sdrop, GENLIST_CONS, GSYM sdrop_1, ADD1] >>
      REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
      xsimpl >> simp[LIST_TYPE_def])
QED

Theorem bget_ready_spec:
  limited_parts io2_names p ∧ UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) bget_ready_v [uv] (IOS2 ws evs)
    (POSTv v. &WORD (ws 0) v * IOS2 (sdrop 1 ws) (evs ++ [ready_event (ws 0)]))
Proof
  rpt strip_tac >> xcf_with_def (fetch "-" "bget_ready_v_def") >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  rename1 ‘W8ARRAY bv’ >>
  xlet ‘POSTv u. W8ARRAY bv [ws 0] * IOS2 (sdrop 1 ws) (evs ++ [ready_event (ws 0)])’
  >- (xffi >> xsimpl >>
      qexistsl [‘emp’, ‘io_state ws’, ‘io2_update’, ‘io2_names’, ‘evs’] >>
      simp[io2_names_def, IOS2_def, EVAL “REPLICATE 1 (0w:word8)”] >>
      simp[io2_update_act_ready, ready_event_def] >>
      xsimpl) >>
  xapp >> xsimpl >> simp[]
QED

Theorem byte_chr_eq[local]:
  byte_chr = CHR o w2n
Proof
  simp[FUN_EQ_THM, byte_chr_def]
QED

(* MAIN: select on the declared events E blocks until the first declared
   byte of the stream, at position j = skips E ws 0, returns it, and
   records one select event; the bytes before it are consumed. *)
Theorem bselect_spec:
  limited_parts io2_names p ∧ EVLIST WORD E esv ∧ (∃j. ws j ∈ E) ⇒
  app (p:'ffi ffi_proj) bselect_v [esv] (IOS2 ws evs)
    (POSTv v. &WORD (ws (skips E ws 0)) v *
              IOS2 (sdrop (SUC (skips E ws 0)) ws)
                (evs ++ [select_event (SET_TO_LIST E) (ws (skips E ws 0))]))
Proof
  rpt strip_tac >> gvs[EVLIST_def] >>
  ‘io2_update «select» (SET_TO_LIST E) [0w:word8] (io_state ws) =
     SOME (FFIreturn [ws (skips E ws 0)]
             (io_state (sdrop (SUC (skips E ws 0)) ws)))’
    by (‘skips E ws 0 = skips (set (SET_TO_LIST E)) ws 0’
          by simp[SET_TO_LIST_INV] >>
        pop_assum SUBST1_TAC >> irule io2_update_select >>
        gvs[MEM_SET_TO_LIST] >> metis_tac[]) >>
  xcf_with_def (fetch "-" "bselect_v_def") >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  rename1 ‘W8ARRAY bv’ >>
  xlet ‘POSTv sv. &STRING_TYPE (bytes_str (SET_TO_LIST E)) sv * W8ARRAY bv [0w] *
                  IOS2 ws evs’
  >- (xapp >> xsimpl >> qexists_tac ‘SET_TO_LIST E’ >> simp[] >> EVAL_TAC) >>
  xlet ‘POSTv u. W8ARRAY bv [ws (skips E ws 0)] *
          IOS2 (sdrop (SUC (skips E ws 0)) ws)
            (evs ++ [select_event (SET_TO_LIST E) (ws (skips E ws 0))])’
  >- (xffi >> xsimpl >>
      gvs[STRING_TYPE_def, bytes_str_def, byte_chr_eq] >>
      qexistsl [‘SET_TO_LIST E’, ‘emp’, ‘io_state ws’, ‘io2_update’,
                ‘io2_names’, ‘evs’] >>
      gvs[io2_names_def, IOS2_def, select_event_def] >> xsimpl) >>
  xapp >> xsimpl >> simp[]
QED
