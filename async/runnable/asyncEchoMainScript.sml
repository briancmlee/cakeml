(*
  The runnable echo server: the verified program plus a main declaration,
  exported for the CakeML release compiler.

  The program is spike/m4-safety's (asyncM4SockServer): the basis, the
  Socket module (ffiSpikeSocketProg), the Async library (asyncM3Prog),
  M4's event loop with a growing interest list (asyncM4Loop: add_accepted,
  step_i, run_i) and the echo server in the socket vocabulary (handler,
  server).  The only new declaration is main:

     val _ = run_i ([3], server 3);

  i.e. run the loop with interest list [3] on the server listening on
  fd 3.  The listening socket is created by the C side before cml_main
  runs (socket_ffi.c), as fd 3: this is the initial world of the socket
  model (a listener with an empty queue), which has no operation for
  creating listeners.

  Export: every declaration after the basis is written to
  echo_server.sexp in the S-expression format of the CakeML release v3479
  (sexpV3479Lib); the release compiler adds its own copy of the basis.
*)
Theory asyncEchoMain
Ancestors
  asyncM4SockServer basisProg ffiSpikeDivMain
Libs
  preamble basis ml_progLib basisFunctionsLib sexpV3479Lib

val _ = translation_extends "asyncM4SockServer"

Quote add_cakeml:
  fun main u = run_i ([3], server 3);
End

(* The program's declarations (basis to main), as the Decls theorem of
   the translation state has them *)
val echo_decs_tm =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> concl |> strip_comb |> snd |> (fn args => List.nth (args, 2));

Definition echo_decs_def:
  echo_decs = ^echo_decs_tm
End

(* The whole program: the declarations, then main () *)
Definition echo_prog_def:
  echo_prog = SNOC (main_call «main») echo_decs
End

(* The whole program as an explicit list of declarations *)
Theorem echo_prog_eq =
  REWRITE_CONV [echo_prog_def, echo_decs_def, main_call_def,
                listTheory.SNOC_APPEND, listTheory.APPEND] “echo_prog”;

val echo_prog = echo_prog_eq |> concl |> rhs;

val basis_decls =
  basisProgTheory.basis_def |> concl |> rhs |> listSyntax.dest_list |> fst;
val (all_decls, dec_ty) = listSyntax.dest_list echo_prog;
val n_basis = length basis_decls;

(* The program starts with the basis, exactly *)
val _ =
  if n_basis <= length all_decls andalso
     ListPair.allEq (uncurry aconv) (basis_decls, List.take (all_decls, n_basis))
  then ()
  else failwith "the program does not start with the basis";

val user_decls = List.drop (all_decls, n_basis);

val _ = print ("asyncEchoMain: " ^ Int.toString n_basis ^ " basis declarations, " ^
               Int.toString (length user_decls) ^ " program declarations\n");

val _ = write_ast_to_file "echo_server.sexp" (listSyntax.mk_list (user_decls, dec_ty));
