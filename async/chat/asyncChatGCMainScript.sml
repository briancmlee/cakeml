(*
  The runnable GC chat server: asyncChatGCProg's program, then

     fun main u = run_i ([3], gc_server 3);
     main ();

  exported to chat_server_gc.sexp.
*)
Theory asyncChatGCMain
Ancestors
  asyncChatGCProg asyncChatGCSpec basisProg ffiSpikeDivMain
Libs
  preamble basis ml_translatorLib ml_progLib basisFunctionsLib sexpV3479Lib

val _ = translation_extends "asyncChatGCProg"

Quote add_cakeml:
  fun main u = run_i ([3], gc_server 3);
End

val gc_decs_tm =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> concl |> strip_comb |> snd |> (fn args => List.nth (args, 2));

Definition chat_gc_decs_def:
  chat_gc_decs = ^gc_decs_tm
End

Definition chat_prog_gc_def:
  chat_prog_gc = SNOC (main_call «main») chat_gc_decs
End

Theorem chat_prog_gc_eq =
  REWRITE_CONV [chat_prog_gc_def, chat_gc_decs_def, main_call_def,
                listTheory.SNOC_APPEND, listTheory.APPEND] “chat_prog_gc”;

val chat_prog_gc = chat_prog_gc_eq |> concl |> rhs;

val basis_decls =
  basisProgTheory.basis_def |> concl |> rhs |> listSyntax.dest_list |> fst;
val (all_decls, dec_ty) = listSyntax.dest_list chat_prog_gc;
val n_basis = length basis_decls;

val _ =
  if n_basis <= length all_decls andalso
     ListPair.allEq (uncurry aconv) (basis_decls, List.take (all_decls, n_basis))
  then ()
  else failwith "the program does not start with the basis";

val user_decls = List.drop (all_decls, n_basis);

val _ = write_ast_to_file "chat_server_gc.sexp" (listSyntax.mk_list (user_decls, dec_ty));
