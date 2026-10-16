(*
  The runnable key-value server: as httpProg's main, with kv_server in
  place of the generic protocol server.

     fun main u = run_i ([3], kv_server 3);
     main ();

  The listening socket is fd 3, created by the C side (the runnable socket FFI).
  Export: every declaration after the basis is written to kv_server.sexp
  in release v3479's S-expression format (programs/echo's sexpV3479Lib).
*)
Theory kvMain
Ancestors
  kvProg kvSockSpec basisProg divMain
Libs
  preamble basis ml_translatorLib ml_progLib basisFunctionsLib sexpV3479Lib

val _ = translation_extends "kvProg"

Quote add_cakeml:
  fun main u = run_i ([3], kv_server 3);
End

val kv_decs_tm =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> concl |> strip_comb |> snd |> (fn args => List.nth (args, 2));

Definition kv_decs_def:
  kv_decs = ^kv_decs_tm
End

(* The whole program: the declarations, then main () *)
Definition kv_prog_def:
  kv_prog = SNOC (main_call «main») kv_decs
End

Theorem kv_prog_eq =
  REWRITE_CONV [kv_prog_def, kv_decs_def, main_call_def,
                listTheory.SNOC_APPEND, listTheory.APPEND] “kv_prog”;

val kv_prog = kv_prog_eq |> concl |> rhs;

val basis_decls =
  basisProgTheory.basis_def |> concl |> rhs |> listSyntax.dest_list |> fst;
val (all_decls, dec_ty) = listSyntax.dest_list kv_prog;
val n_basis = length basis_decls;

val _ =
  if n_basis <= length all_decls andalso
     ListPair.allEq (uncurry aconv) (basis_decls, List.take (all_decls, n_basis))
  then ()
  else failwith "the program does not start with the basis";

val user_decls = List.drop (all_decls, n_basis);

val _ = print ("asyncKvMain: " ^ Int.toString n_basis ^ " basis declarations, " ^
               Int.toString (length user_decls) ^ " program declarations\n");

val _ = write_ast_to_file "kv_server.sexp" (listSyntax.mk_list (user_decls, dec_ty));
