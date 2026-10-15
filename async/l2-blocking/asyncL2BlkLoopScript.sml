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
