(*
  Logical model of UNIX wall time
*)
open preamble cfHeapsBaseTheory MarshallingTheory cfFFITypeTheory

val _ = new_theory"tsFFI"

val _ = option_monadsyntax.temp_add_option_monadsyntax();

val _ = Datatype`
  IO_ts = <| latest_time: num;
             microseconds_elapsed: num -> int option
           |>`

Definition getNow_def:
  getNow ts =
    do
      elapsed <- ts.microseconds_elapsed 0;
      let latest_time = Num (int_max (&(ts.latest_time) + elapsed) 0) in
      let ts' = <| latest_time := latest_time;
                   microseconds_elapsed := ts.microseconds_elapsed o SUC |> in
      return (ts'.latest_time, ts')
    od
End

Definition ffi_now_def:
  ffi_now (conf: word8 list) bytes ts =
    do
      assert(9 <= LENGTH bytes);
      (now, ts') <- getNow ts;
      return (FFIreturn (0w :: n2w8 now ++ (DROP 9 bytes)) ts')
    od ++
    do
      assert(0 < LENGTH bytes);
      return (FFIreturn (LUPDATE 1w 0 bytes) ts)
    od
End

Theorem ffi_now_length:
  ffi_now conf bytes args = SOME (FFIreturn bytes' args') ⇒
    LENGTH bytes' = LENGTH bytes
Proof
  rw[ffi_now_def] \\ fs[option_eq_some]
  \\ TRY(pairarg_tac) \\ rw[] \\ fs[] \\ rw[] \\ fs[n2w8_def]
QED

(* Theorem REP_CLASS_11[simp]: *)
(*   int_REP_CLASS i1 = int_REP_CLASS i2 <=> i1 = i2 *)
(* Proof *)
(*   metis_tac[integerTheory.int_ABS_REP_CLASS] *)
(* QED *)

(* Theorem REP_ABS_equiv[simp]: *)
(*   int_REP_CLASS (int_ABS_CLASS (tint_eq r)) = tint_eq r *)
(* Proof *)
(*   simp[GSYM (CONJUNCT2 integerTheory.int_ABS_REP_CLASS)] \\ qexists ‘r’ \\ *)
(*   fs[integerTheory.TINT_EQ_REFL] *)
(* QED *)

(* Theorem ABS_CLASS_onto: *)
(*   !fs. ?r.  fs = int_ABS_CLASS (tint_eq r) *)
(* Proof *)
(*   metis_tac[integerTheory.int_ABS_REP_CLASS] *)
(* QED *)

(* Theorem REP_CLASS_NONEMPTY: *)
(*   !fs. ?x. int_REP_CLASS fs x *)
(* Proof *)
(*   gen_tac >> qspec_then ‘fs’ (qx_choose_then ‘r’ assume_tac) ABS_CLASS_onto >> *)
(*   simp[] >> metis_tac[integerTheory.TINT_EQ_REFL] *)
(* QED *)

(* Theorem int_ABS_REP[simp]: *)
(*   int_ABS (int_REP s) = s *)
(* Proof *)
(*   simp[integerTheory.int_REP_def, integerTheory.int_ABS_def] >> *)
(*   ‘tint_eq ($@ (int_REP_CLASS s)) = int_REP_CLASS s’ *)
(*     suffices_by metis_tac[REP_CLASS_11, REP_ABS_equiv] >> *)
(*   simp[FUN_EQ_THM] >> qx_gen_tac ‘a’ >> SELECT_ELIM_TAC >> conj_tac *)
(*   >- metis_tac[REP_CLASS_NONEMPTY] >> *)
(*   rw[EQ_IMP_THM] >> *)
(*   qspec_then ‘s’ (qx_choose_then ‘r’ assume_tac) ABS_CLASS_onto >> fs[] >> *)
(*   metis_tac[quotientTheory.EQUIV_def, integerTheory.TINT_EQ_EQUIV] *)
(* QED *)

(* Theorem int_REP_11[simp]: *)
(*   int_REP i1 = int_REP i2 <=> i1 = i2 *)
(* Proof *)
(*   metis_tac[int_ABS_REP] *)
(* QED *)

Definition Int_def[nocompute]:
  (Int (n:int)):ffi = Cons (Num (if (n ≥ 0) then 0n else 1n)) (Num (Num n))
End

Theorem Int_11[simp]:
  Int x = Int y ⇔ x = y
Proof
  reverse eq_tac >- fs[Int_def] \\
  fs[Int_def,integerTheory.Num_EQ] \\
  rpt IF_CASES_TAC \\ rw[] \\ ‘y = 0’ suffices_by rw[] \\
  fs[integerTheory.INT_GE_CALCULATE] \\
  qspecl_then [‘y’,‘0’] mp_tac integerTheory.INT_LE_ANTISYM \\
  rw[] \\ rw[] \\ rw[] \\
  fs[integerTheory.INT_NOT_LE] \\ imp_res_tac integerTheory.INT_LT_ANTISYM
QED

Definition dest_iNum_def[nocompute]:
  dest_iNum (iNum n) = n
End

(* Packaging up the model as an ffi_part *)
Definition encode_def[nocompute]:
  encode ts =
    Cons
      (Num ts.latest_time)
      (Fun (\ x:ffi_inner. Option
                           (OPTION_MAP Int (ts.microseconds_elapsed (dest_iNum x)))))
End

Theorem encode_11[simp]:
  !x y. encode x = encode y <=> x = y
Proof
  rw [] \\ eq_tac \\ fs [encode_def] \\ rw [] \\
  fs[FUN_EQ_THM, fetch "-" "IO_ts_component_equality"] \\
  rpt strip_tac \\ last_x_assum (qspec_then ‘iNum x'’ mp_tac) \\
  fs [dest_iNum_def] \\
  qabbrev_tac ‘f = OPTION_MAP Int’ \\
  qsuff_tac ‘∀a b. f a = f b ⇔ a = b’ >- rw[] \\
  fs[Abbr‘f’] \\ rpt strip_tac \\ reverse eq_tac >- fs[] \\
  Cases_on ‘a’ \\ Cases_on ‘b’ \\ rw[] \\ rw[] \\ rw[]
QED

val decode_encode = new_specification("decode_encode",["decode"],
  prove(``?decode. !cls. decode (encode cls) = SOME cls``,
        qexists_tac `\f. some c. encode c = f` \\ fs [encode_11]));
val _ = export_rewrites ["decode_encode"];

val ts_ffi_part_def = Define`
  ts_ffi_part =
    (encode,decode,
      [("now",ffi_now)])`;

val _ = export_theory();
