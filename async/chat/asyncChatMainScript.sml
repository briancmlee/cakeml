(*
  The runnable chat server: asyncChatProg's program (the basis, Socket,
  the Async library, M4's dynamic-interest loop run_i, with_tap, the hub
  and the server), then main and its call:

     fun main u = run_i ([3], chat_server 3);
     main ();

  The listening socket is fd 3, created by the C side (runnable/socket_ffi.c).
  Export: every declaration after the basis is written to chat_server.sexp
  in release v3479's S-expression format (runnable/sexpV3479Lib).
*)
Theory asyncChatMain
Ancestors
  asyncChatProg asyncChatSpec basisProg ffiSpikeDivMain
Libs
  preamble basis ml_translatorLib ml_progLib basisFunctionsLib sexpV3479Lib

val _ = translation_extends "asyncChatProg"

Quote add_cakeml:
  fun main u = run_i ([3], chat_server 3);
End

(* The program's declarations (basis to main) *)
val chat_decs_tm =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> concl |> strip_comb |> snd |> (fn args => List.nth (args, 2));

Definition chat_decs_def:
  chat_decs = ^chat_decs_tm
End

(* The whole program: the declarations, then main () *)
Definition chat_prog_def:
  chat_prog = SNOC (main_call «main») chat_decs
End

(* The whole program as an explicit list of declarations *)
Theorem chat_prog_eq =
  REWRITE_CONV [chat_prog_def, chat_decs_def, main_call_def,
                listTheory.SNOC_APPEND, listTheory.APPEND] “chat_prog”;

val chat_prog = chat_prog_eq |> concl |> rhs;

val basis_decls =
  basisProgTheory.basis_def |> concl |> rhs |> listSyntax.dest_list |> fst;
val (all_decls, dec_ty) = listSyntax.dest_list chat_prog;
val n_basis = length basis_decls;

(* The program starts with the basis, exactly *)
val _ =
  if n_basis <= length all_decls andalso
     ListPair.allEq (uncurry aconv) (basis_decls, List.take (all_decls, n_basis))
  then ()
  else failwith "the program does not start with the basis";

val user_decls = List.drop (all_decls, n_basis);

val _ = print ("asyncChatMain: " ^ Int.toString n_basis ^ " basis declarations, " ^
               Int.toString (length user_decls) ^ " program declarations\n");

val _ = write_ast_to_file "chat_server.sexp" (listSyntax.mk_list (user_decls, dec_ty));
