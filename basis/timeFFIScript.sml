(*
  Logical model of UNIX wall time
*)
open preamble cfHeapsBaseTheory MarshallingTheory cfFFITypeTheory

val _ = new_theory"timeFFI"

val _ = option_monadsyntax.temp_add_option_monadsyntax();

val _ = Datatype`
  IO_ts = <| latest_time: num;
             microseconds_elapsed: num -> int
           |>`

Definition getNowMilliseconds_def:
  getNowMilliseconds ts =
    let elapsed = ts.microseconds_elapsed 0 in
    let latest_time = Num (int_max (&(ts.latest_time) + elapsed) 0) in
    let ts' = <| latest_time := latest_time;
                 microseconds_elapsed := \n. ts.microseconds_elapsed (n+1) |> in
    (ts'.latest_time DIV 1000, ts')
End

Definition ffi_get_now_milliseconds_def:
  ffi_get_now_milliseconds (conf: word8 list) bytes ts =
    do
      assert(9 <= LENGTH bytes);
      (now, ts') <<- getNowMilliseconds ts;
      return (FFIreturn (0w :: n2w8 now ++ (DROP 9 bytes)) ts')
    od ++
    do
      assert(0 < LENGTH bytes);
      return (FFIreturn (LUPDATE 1w 0 bytes) ts)
    od
End

Theorem ffi_get_now_milliseconds_length:
  ffi_get_now_milliseconds conf bytes args = SOME (FFIreturn bytes' args') ⇒
    LENGTH bytes' = LENGTH bytes
Proof
  rw[ffi_get_now_milliseconds_def] \\ fs[option_eq_some]
  \\ TRY(pairarg_tac) \\ rw[] \\ fs[] \\ rw[] \\ fs[n2w8_def]
QED

Theorem REP_CLASS_11[simp]:
  int_REP_CLASS i1 = int_REP_CLASS i2 <=> i1 = i2
Proof
  metis_tac[integerTheory.int_ABS_REP_CLASS]
QED

Theorem REP_ABS_equiv[simp]:
  int_REP_CLASS (int_ABS_CLASS (tint_eq r)) = tint_eq r
Proof
  simp[GSYM (CONJUNCT2 integerTheory.int_ABS_REP_CLASS)] \\ qexists ‘r’ \\
  fs[integerTheory.TINT_EQ_REFL]
QED

Theorem ABS_CLASS_onto:
  !fs. ?r.  fs = int_ABS_CLASS (tint_eq r)
Proof
  metis_tac[integerTheory.int_ABS_REP_CLASS]
QED

Theorem REP_CLASS_NONEMPTY:
  !fs. ?x. int_REP_CLASS fs x
Proof
  gen_tac >> qspec_then ‘fs’ (qx_choose_then ‘r’ assume_tac) ABS_CLASS_onto >>
  simp[] >> metis_tac[integerTheory.TINT_EQ_REFL]
QED

Theorem int_ABS_REP[simp]:
  int_ABS (int_REP s) = s
Proof
  simp[integerTheory.int_REP_def, integerTheory.int_ABS_def] >>
  ‘tint_eq ($@ (int_REP_CLASS s)) = int_REP_CLASS s’
    suffices_by metis_tac[REP_CLASS_11, REP_ABS_equiv] >>
  simp[FUN_EQ_THM] >> qx_gen_tac ‘a’ >> SELECT_ELIM_TAC >> conj_tac
  >- metis_tac[REP_CLASS_NONEMPTY] >>
  rw[EQ_IMP_THM] >>
  qspec_then ‘s’ (qx_choose_then ‘r’ assume_tac) ABS_CLASS_onto >> fs[] >>
  metis_tac[quotientTheory.EQUIV_def, integerTheory.TINT_EQ_EQUIV]
QED

Theorem int_REP_11[simp]:
  int_REP i1 = int_REP i2 <=> i1 = i2
Proof
  metis_tac[int_ABS_REP]
QED

val dest_iNum_def = Define `
  dest_iNum (iNum n) = n `;

(* Packaging up the model as an ffi_part *)
val encode_def = zDefine‘
  encode ts = Cons
              (Num ts.latest_time)
              (Fun (\ x:ffi_inner.
                      let elapsed = ts.microseconds_elapsed (dest_iNum x) in
                      let (elapsed_a, elapsed_b) = int_REP elapsed in
                      Cons (Num elapsed_a) (Num elapsed_b)))’;

Theorem encode_11[simp]:
  !x y. encode x = encode y <=> x = y
Proof
  rw [] \\ eq_tac \\ fs [encode_def] \\ rw [] \\
  fs[FUN_EQ_THM, fetch "-" "IO_ts_component_equality"] \\
  rpt strip_tac \\ last_x_assum (qspec_then ‘iNum x'’ mp_tac) \\
  fs [dest_iNum_def] \\
  qabbrev_tac ‘f = λ(elapsed_a,elapsed_b). Cons (Num elapsed_a) (Num elapsed_b)’ \\
  qsuff_tac ‘∀a b. f a = f b ⇔ a = b’ >- rw[] \\
  fs[Abbr‘f’] \\ rpt strip_tac \\ eq_tac
  >- (Cases_on ‘a’ \\ Cases_on ‘b’ \\ fs[]) \\
  fs[FUN_EQ_THM]
QED

val decode_encode = new_specification("decode_encode",["decode"],
  prove(``?decode. !cls. decode (encode cls) = SOME cls``,
        qexists_tac `\f. some c. encode c = f` \\ fs [encode_11]));
val _ = export_rewrites ["decode_encode"];

val ts_ffi_part_def = Define`
  ts_ffi_part =
    (encode,decode,
      [("get_now_milliseconds",ffi_get_now_milliseconds)])`;

val _ = export_theory();
