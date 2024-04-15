(*
  Logical model of UNIX wall time
*)
open preamble cfHeapsBaseTheory MarshallingTheory

val _ = new_theory"timeFFI"

val _ = option_monadsyntax.temp_add_option_monadsyntax();

val _ = Datatype`
  IO_ts = <| latest_time: num;
             microseconds_elapsed: num llist
           |>`

val getNowMilliseconds_def = Define`
  getNowMilliseconds ts =
    do
      elapsed <- LHD ts.microseconds_elapsed;
      let ts' = <| latest_time := ts.latest_time + elapsed;
                microseconds_elapsed := THE(LTL ts.microseconds_elapsed) |> in
      return (ts'.latest_time DIV 1000, ts');
    od
`;

val ffi_get_now_milliseconds = Define`
  ffi_get_now_milliseconds (conf: word8 list) bytes ts =
    do
      assert(9 <= LENGTH bytes);
      (now, ts') <- getNowMilliseconds ts;
      return (FFIreturn (0w :: n2w8 now ++ (DROP 9 bytes)) ts')
    od`;

(* Packaging up the model as an ffi_part *)
val encode_def = zDefine`
  encode ts = Cons
    (Num ts.latest_time)
    (Stream ts.microseconds_elapsed)`;

Theorem encode_11[simp]:
  !x y. encode x = encode y <=> x = y
Proof
  Cases \\ Cases \\ rw[encode_def]
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
