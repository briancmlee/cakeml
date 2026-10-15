(*
  The runnable HTTP server: the verified program plus a file map and a main
  declaration, exported for the CakeML release compiler (as
  runnable/asyncEchoMain does for echo).

  The program is asyncHttpSockProg's: the basis, Socket, the Async library,
  M4's dynamic-interest loop (run_i), the echo server's code (unused), the
  translated parser and responder, and the socket-vocabulary HTTP server.
  The new declarations are the file map demo_files (translated), main and
  its call:

     fun main u = run_i ([3], http_server demo_files 3);
     main ();

  The listening socket is fd 3, created by the C side (runnable/socket_ffi.c).
  Export: every declaration after the basis is written to http_server.sexp
  in release v3479's S-expression format (runnable/sexpV3479Lib).
*)
Theory asyncHttpMain
Ancestors
  asyncHttpSockProg asyncHttpSockSpec basisProg ffiSpikeDivMain
Libs
  preamble basis ml_translatorLib ml_progLib basisFunctionsLib sexpV3479Lib

val _ = translation_extends "asyncHttpSockProg"

(* The files the demo server serves *)
Definition demo_files_def:
  demo_files =
    [("/", "Hello from a verified CakeML HTTP server!\n");
     ("/index.html",
      "<html><body><h1>Verified CakeML</h1><p>Served by http_server, " ++
      "whose socket trace is proved to satisfy HttpSpec's http_safe.</p>" ++
      "</body></html>\n");
     ("/about", "HttpSpec subset: GET <path> HTTP/1.0, then a blank line.\n")]
End

val r = translate demo_files_def;

Quote add_cakeml:
  fun main u = run_i ([3], http_server demo_files 3);
End

(* The program's declarations (basis to main) *)
val http_decs_tm =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> concl |> strip_comb |> snd |> (fn args => List.nth (args, 2));

Definition http_decs_def:
  http_decs = ^http_decs_tm
End

(* The whole program: the declarations, then main () *)
Definition http_prog_def:
  http_prog = SNOC (main_call «main») http_decs
End

(* The whole program as an explicit list of declarations *)
Theorem http_prog_eq =
  REWRITE_CONV [http_prog_def, http_decs_def, main_call_def,
                listTheory.SNOC_APPEND, listTheory.APPEND] “http_prog”;

val http_prog = http_prog_eq |> concl |> rhs;

val basis_decls =
  basisProgTheory.basis_def |> concl |> rhs |> listSyntax.dest_list |> fst;
val (all_decls, dec_ty) = listSyntax.dest_list http_prog;
val n_basis = length basis_decls;

(* The program starts with the basis, exactly *)
val _ =
  if n_basis <= length all_decls andalso
     ListPair.allEq (uncurry aconv) (basis_decls, List.take (all_decls, n_basis))
  then ()
  else failwith "the program does not start with the basis";

val user_decls = List.drop (all_decls, n_basis);

val _ = print ("asyncHttpMain: " ^ Int.toString n_basis ^ " basis declarations, " ^
               Int.toString (length user_decls) ^ " program declarations\n");

val _ = write_ast_to_file "http_server.sexp" (listSyntax.mk_list (user_decls, dec_ty));
