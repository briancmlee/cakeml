(*
  The runnable bodies HTTP server: as asyncHttpMain, with http_server_b
  (spec/HttpSpecBodies) in place of http_server.

  The program is asyncHttpSockProg's: the basis, Socket, the Async library,
  M4's dynamic-interest loop (run_i), the echo server's code (unused), the
  translated parser and responder, and the socket-vocabulary HTTP server.
  The new declarations are the file map demo_files (translated), main and
  its call:

     fun main u = run_i ([3], http_server_b demo_files 3);
     main ();

  The listening socket is fd 3, created by the C side (runnable/socket_ffi.c).
  Export: every declaration after the basis is written to http_server.sexp
  in release v3479's S-expression format (runnable/sexpV3479Lib).
*)
Theory asyncHttpMainB
Ancestors
  asyncHttpSockProgB asyncHttpSockSpecB asyncHttpMain basisProg ffiSpikeDivMain
Libs
  preamble basis ml_translatorLib ml_progLib basisFunctionsLib sexpV3479Lib

val _ = translation_extends "asyncHttpSockProgB"

(* demo_files (asyncHttpMain's definition) is translated again in this program *)
val r = translate demo_files_def;

Quote add_cakeml:
  fun main u = run_i ([3], http_server_b demo_files 3);
End

(* The program's declarations (basis to main) *)
val http_decs_b_tm =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> concl |> strip_comb |> snd |> (fn args => List.nth (args, 2));

Definition http_decs_b_def:
  http_decs_b = ^http_decs_b_tm
End

(* The whole program: the declarations, then main () *)
Definition http_prog_b_def:
  http_prog_b = SNOC (main_call «main») http_decs_b
End

(* The whole program as an explicit list of declarations *)
Theorem http_prog_b_eq =
  REWRITE_CONV [http_prog_b_def, http_decs_b_def, main_call_def,
                listTheory.SNOC_APPEND, listTheory.APPEND] “http_prog_b”;

val http_prog_b = http_prog_b_eq |> concl |> rhs;

val basis_decls =
  basisProgTheory.basis_def |> concl |> rhs |> listSyntax.dest_list |> fst;
val (all_decls, dec_ty) = listSyntax.dest_list http_prog_b;
val n_basis = length basis_decls;

(* The program starts with the basis, exactly *)
val _ =
  if n_basis <= length all_decls andalso
     ListPair.allEq (uncurry aconv) (basis_decls, List.take (all_decls, n_basis))
  then ()
  else failwith "the program does not start with the basis";

val user_decls = List.drop (all_decls, n_basis);

val _ = print ("asyncHttpMainB: " ^ Int.toString n_basis ^ " basis declarations, " ^
               Int.toString (length user_decls) ^ " program declarations\n");

val _ = write_ast_to_file "http_server_b.sexp" (listSyntax.mk_list (user_decls, dec_ty));
