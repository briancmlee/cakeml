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

val () = generate_sigs := true;

val _ = ml_prog_update open_local_block;

Datatype:
  time = Time int
End

val _ = (use_full_type_names := false);
val _ = register_type “:time”;
val _ = (use_full_type_names := true);

Definition get_time_def:
  get_time (Time t) = t
End
val _ = (next_ml_names := ["get_time"]);
val r = translate get_time_def;

val _ = ml_prog_update open_local_in_block;

val _ = ml_prog_update (add_dec
  “Dtabbrev unknown_loc [] "time" (Atapp [] (Short "time"))” I);

Definition fromMicroseconds_def:
  fromMicroseconds t = Time t
End

Definition toMicroseconds_def:
  toMicroseconds (Time t) = t
End

val _ = (next_ml_names := ["fromMicroseconds","toMicroseconds"]);
val r = translate fromMicroseconds_def;
val r = translate toMicroseconds_def;

Definition fromMilliseconds_def:
  fromMilliseconds t = Time (t * 1000)
End

Definition toMilliseconds_def:
  toMilliseconds (Time t) = t / 1000
End

val _ = (next_ml_names := ["fromMilliseconds","toMilliseconds"]);
val r = translate fromMilliseconds_def;
val r = translate toMilliseconds_def;

Definition fromSeconds_def:
  fromSeconds t = Time (t * 1000000)
End

Definition toSeconds_def:
  toSeconds (Time t) = t / 1000000
End

val _ = (next_ml_names := ["fromSeconds","toSeconds"]);
val r = translate fromSeconds_def;
val r = translate toSeconds_def;

val binopn_lift_def = zDefine ‘
  binopn_lift (f:int->int->int) =
    λa b. Time (f (get_time a) (get_time b))’;

fun binopn f_tm =
  “binopn_lift ^f_tm” |> REWR_CONV binopn_lift_def |> concl |> rhs;

val binopb_lift_def = zDefine ‘
  binopb_lift (f:int->int->bool) =
    λa b. f (get_time a) (get_time b)’;

fun binopb f_tm =
  “binopb_lift ^f_tm” |> REWR_CONV binopb_lift_def |> concl |> rhs;

val _ = trans "+" (binopn intSyntax.plus_tm);
val _ = trans "-" (binopn intSyntax.minus_tm);
val _ = trans "*" (binopn intSyntax.mult_tm);
val _ = trans "div" (binopn intSyntax.div_tm);
val _ = trans "mod" (binopn intSyntax.mod_tm);
val _ = trans "<" (binopb intSyntax.less_tm);
val _ = trans ">" (binopb intSyntax.greater_tm);
val _ = trans "<=" (binopb intSyntax.leq_tm);
val _ = trans ">=" (binopb intSyntax.geq_tm);
val _ = trans "~" “\t. Time (- (get_time t))”;

val _ = process_topdecs ‘exception GetNowFailed’ |> append_prog;

fun get_exn_conv name =
  EVAL “lookup_cons (Short ^name) ^(get_env (get_ml_prog_state ()))”
  |> concl |> rand |> rand |> rand

val GetNowFailed = get_exn_conv “"GetNowFailed"”

val _ = ml_prog_update open_local_block;

val _ = process_topdecs ‘
  fun getNow () =
    let val b = Word8Array.array 9 (Word8.fromInt 0)
        val a = #(now) "" b
    in
      if Word8Array.sub b 0 = Word8.fromInt 0
      then Marshalling.w82n b 1
      else raise GetNowFailed
    end
’ |> append_prog;

val _ = ml_prog_update open_local_in_block

val _ = process_topdecs ‘fun now () = fromMicroseconds (getNow ())’ |> append_prog;

val _ = ml_prog_update close_local_blocks;
val _ = ml_prog_update (close_module NONE);

val _ = export_theory();
