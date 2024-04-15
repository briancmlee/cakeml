(*
  Module for getting UNIX epoch time.
*)

open preamble
     ml_translatorTheory ml_translatorLib ml_progLib basisFunctionsLib
     CommandLineProgTheory MarshallingProgTheory
     semanticPrimitivesSyntax

val _ = new_theory"TimeProg";

val _ = translation_extends "MarshallingProg";

val _ = ml_prog_update (open_module "Time");

val _ = ml_prog_update open_local_block;

Datatype:
  time = Milliseconds num
End

Definition get_milliseconds_def:
  get_milliseconds (Milliseconds t) = t
End

val _ = (use_full_type_names := false);
val _ = register_type ``:time``;
val _ = (use_full_type_names := true);

val _ = (next_ml_names := ["get_milliseconds"]);
val _ = translate get_milliseconds_def;

val _ = ml_prog_update open_local_block;

val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [] "time" (Atapp [] (Short "time"))`` I);

val _ = process_topdecs `
  exception GetTimeFailed
` |> append_prog

val _ = ml_prog_update open_local_block;

fun get_exn_conv name =
  EVAL ``lookup_cons (Short ^name) ^(get_env (get_ml_prog_state ()))``
  |> concl |> rand |> rand |> rand

val GetTimeFailed = get_exn_conv ``"GetTimeFailed"``;

val GetTimeFailed_exn_def = Define ‘
  GetTimeFailed_exn v = (v = Conv (SOME ^GetTimeFailed) [])’;

val _ = ml_prog_update open_local_in_block;

val _ = process_topdecs ‘
  fun nowMilliseconds () =
    let val b = Word8Array.array 9 (Word8.fromInt 0)
        val a = #(get_now_milliseconds) "" b
    in
        if Word8Array.sub b 0 = Word8.fromInt 0
        then Marshalling.w82n b 1
        else raise GetTimeFailed
    end
’ |> append_prog;

val _ = ml_prog_update close_local_blocks;
val _ = ml_prog_update (close_module NONE);

val _ = export_theory();