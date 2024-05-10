(*
  Module with functions that aid converting to and from the byte
  arrays that CakeML foreign-function interface (FFI) uses.
*)
open preamble ml_translatorLib ml_progLib basisFunctionsLib cfLib
     DoubleProgTheory MarshallingTheory Word8ArrayProofTheory

val _ = new_theory "MarshallingProg";

val _ = translation_extends "DoubleProg";

(* Word8 module -- translated *)

val _ = ml_prog_update (open_module "Marshalling");

val _ = process_topdecs`fun n2w2 n bytes off =
  let val a = Word8Array.update bytes off     (Word8.fromInt (n div 256))
      val a = Word8Array.update bytes (off+1) (Word8.fromInt n)
  in () end` |> append_prog;

val _ = process_topdecs`fun w22n bytes off =
  let val b1 = Word8Array.sub bytes off
      val b0 = Word8Array.sub bytes (off+1)
  in Word8.toInt b1 * 256 + Word8.toInt b0 end` |> append_prog;

val _ = process_topdecs`fun n2w8 n bytes off =
  let val a = Word8Array.update bytes off     (Word8.fromInt (n div 72057594037927936))
      val a = Word8Array.update bytes (off+1) (Word8.fromInt (n div 281474976710656))
      val a = Word8Array.update bytes (off+2) (Word8.fromInt (n div 1099511627776))
      val a = Word8Array.update bytes (off+3) (Word8.fromInt (n div 4294967296))
      val a = Word8Array.update bytes (off+4) (Word8.fromInt (n div 16777216))
      val a = Word8Array.update bytes (off+5) (Word8.fromInt (n div 65536))
      val a = Word8Array.update bytes (off+6) (Word8.fromInt (n div 256))
      val a = Word8Array.update bytes (off+7) (Word8.fromInt (n))
  in () end` |> append_prog;

val _ = process_topdecs`fun w82n bytes off =
  let val b7 = Word8Array.sub bytes off
      val b6 = Word8Array.sub bytes (off+1)
      val b5 = Word8Array.sub bytes (off+2)
      val b4 = Word8Array.sub bytes (off+3)
      val b3 = Word8Array.sub bytes (off+4)
      val b2 = Word8Array.sub bytes (off+5)
      val b1 = Word8Array.sub bytes (off+6)
      val b0 = Word8Array.sub bytes (off+7)
  in
    Word8.toInt b7 * 72057594037927936 +
    Word8.toInt b6 * 281474976710656 +
    Word8.toInt b5 * 1099511627776 +
    Word8.toInt b4 * 4294967296 +
    Word8.toInt b3 * 16777216 +
    Word8.toInt b2 * 65536 +
    Word8.toInt b1 * 256 +
    Word8.toInt b0
  end` |> append_prog;

val _ = ml_prog_update (close_module NONE);

(* if any more theorems get added here, probably should create Word8ProofTheory *)

open ml_translatorTheory

Theorem n2w2_UNICITY_R[xlet_auto_match]:
  !n1 n2.n1 < 256**2 ==> ((n2w2 n1 = n2w2 n2 /\ n2 < 256**2) <=> n1 = n2)
Proof
 rw[n2w2_def] >> eq_tac >> rw[DIV_MOD_MOD_DIV] >>
 `0 < (256 : num)` by fs[] >> imp_res_tac DIVISION >> fs[] >>
 first_assum (assume_tac o Q.SPEC`n1`) >> fs[] >>
 first_x_assum (assume_tac o Q.SPEC`n2`) >> fs[]
QED

Theorem WORD_n2w2_UNICITY_L[xlet_auto_match]:
  !n1 n2 f. n1 < 256**2 /\ LIST_TYPE WORD (n2w2 n1) f ==>
   (LIST_TYPE WORD (n2w2 n2) f /\ n2 < 256**2 <=> n1 = n2)
Proof
 rw[] >> eq_tac >> rw[] >> fs[n2w2_def,LIST_TYPE_def] >> rw[] >>
 imp_res_tac Word8ProgTheory.WORD_UNICITY_L >> rw[] >> fs[n2w_11] >> rw[] >>
 `(n1 DIV 256) MOD 256 = (n1 DIV 256)` by fs[DIV_LT_X] >>
 `(n2 DIV 256) MOD 256 = (n2 DIV 256)` by fs[DIV_LT_X] >>
 `0 < (256 : num)` by fs[] >> imp_res_tac DIVISION >> fs[] >> rw[] >>
 first_assum (assume_tac o Q.SPEC`n1`) >> fs[] >>
 first_x_assum (assume_tac o Q.SPEC`n2`) >> fs[]
QED

(* needed? *)
Theorem n2w8_UNICITY_R[xlet_auto_match]:
   !n1 n2.n1 < 256**8 ==> ((n2w8 n1 = n2w8 n2 /\ n2 < 256**8) <=> n1 = n2)
Proof
  rw[] >> eq_tac >> rw[DIV_MOD_MOD_DIV] >>
  `0 < (256 : num)` by fs[] >> imp_res_tac DIVISION >> fs[] >> rw[] >>
  NTAC 7(
    qmatch_abbrev_tac`x1 = x2` >>
    `x1 DIV 256 = x2 DIV 256` suffices_by (
      first_assum (assume_tac o Q.SPEC`x1`) >> fs[] >>
      first_assum (assume_tac o Q.SPEC`x2`) >> fs[] >>
      unabbrev_all_tac >> fs[n2w8_def,DIV_MOD_MOD_DIV]) >>
     unabbrev_all_tac >> fs[DIV_DIV_DIV_MULT] >> rw[]) >>
  `n1 = n1 MOD 256**8` by fs[] >>
  `n2 = n2 MOD 256**8` by fs[] >>
  qmatch_abbrev_tac`x1 = x2` >>
  `x1 DIV 256 = x2 DIV 256` suffices_by (
      unabbrev_all_tac >> fs[n2w8_def,DIV_MOD_MOD_DIV]) >>
  unabbrev_all_tac >> fs[DIV_DIV_DIV_MULT] >> rw[] >>
  fs[LESS_DIV_EQ_ZERO]
QED

Theorem WORD_n2w8_UNICITY_L[xlet_auto_match]:
  !n1 n2 f. n1 < 256**8 /\ LIST_TYPE WORD (n2w8 n1) f ==>
   (LIST_TYPE WORD (n2w8 n2) f /\ n2 < 256**8 <=> n1 = n2)
Proof
 rw[] >> eq_tac >> rw[] >> fs[n2w8_def,LIST_TYPE_def] >> rw[] >>
 imp_res_tac Word8ProgTheory.WORD_UNICITY_L >> rw[] >> fs[n2w_11] >> rw[] >>
 mp_tac (Q.SPEC `256` DIVISION) >> rw[] >>

 NTAC 8(qmatch_abbrev_tac`x1 = x2` >>
        first_assum(fn x => simp[Once (Q.SPEC `x2` x)]) >>
        `(x1 DIV 256) = (x2 DIV 256)` suffices_by fs[] >>
        unabbrev_all_tac >> fs[DIV_DIV_DIV_MULT]) >>
 fs[LESS_DIV_EQ_ZERO]
QED

Theorem n2w2_spec:
  !n off b nv offv bl. NUM n nv /\ NUM off offv /\ off + 2 <= LENGTH b ==>
    app (p:'ffi ffi_proj) ^(fetch_v "Marshalling.n2w2" (get_ml_prog_state())) [nv; bl; offv]
       (W8ARRAY bl b)
       (POSTv u. &UNIT_TYPE () u * W8ARRAY bl (insert_atI (n2w2 n) off b))
Proof
  xcf "Marshalling.n2w2" (get_ml_prog_state()) >>
  NTAC 6 (xlet_auto >- xsimpl) >>
  xcon >> xsimpl >>
  fs[n2w2_def] >>
  Cases_on`b` >- fs[] >> Cases_on`t` >>
  fs[insert_atI_CONS,insert_atI_def,LUPDATE_commutes]
QED

Theorem n2w8_spec:
  !n off b nv offv bl. NUM n nv /\ NUM off offv /\ off + 8 <= LENGTH b ==>
    app (p:'ffi ffi_proj) ^(fetch_v "Marshalling.n2w8" (get_ml_prog_state())) [nv; bl; offv]
      (W8ARRAY bl b)
      (POSTv u. &UNIT_TYPE () u * W8ARRAY bl (insert_atI (n2w8 n) off b))
Proof
  xcf "Marshalling.n2w8" (get_ml_prog_state()) >>
  NTAC 30 (xlet_auto >- xsimpl) >>
  xcon >> xsimpl >>
  fs[n2w8_def] >>
  Cases_on‘b’ >- fs[] >> Cases_on‘t’ >>
  fs[insert_atI_CONS,insert_atI_def,LUPDATE_commutes]
QED

Theorem w22n_spec:
  !off b offv bl. NUM off offv /\ off + 2 <= LENGTH b ==>
    app (p:'ffi ffi_proj) ^(fetch_v "Marshalling.w22n" (get_ml_prog_state())) [bl; offv]
       (W8ARRAY bl b)
       (POSTv nv. &NUM (w22n [EL off b; EL (off+1) b]) nv * W8ARRAY bl b)
Proof
  xcf "Marshalling.w22n" (get_ml_prog_state()) >>
  NTAC 6 (xlet_auto >- xsimpl) >>
  xapp >> xsimpl  >> fs[w22n_def,NUM_def,INT_def,integerTheory.INT_ADD]
QED

Theorem w82n_spec:
  !off b offv bl. NUM off offv /\ off + 8 <= LENGTH b ==>
    app (p:'ffi ffi_proj) ^(fetch_v "Marshalling.w82n" (get_ml_prog_state())) [bl; offv]
        (W8ARRAY bl b)
        (POSTv nv. &NUM (w82n [EL off b; EL (off+1) b; EL (off+2) b; EL (off+3) b; EL (off+4) b; EL (off+5) b; EL (off+6) b; EL (off+7) b]) nv * W8ARRAY bl b)
Proof
  xcf "Marshalling.w82n" (get_ml_prog_state()) >>
  NTAC 36 (xlet_auto >- xsimpl) >>
  xapp >> xsimpl  >> fs[w82n_def,NUM_def,INT_def,integerTheory.INT_ADD]
QED

val _ = export_theory()
