(*
  The runnable blocking HTTP server that selects on the live connections:
  http-blocking's verified program, exported for the CakeML release
  compiler.

  The program is exactly the one asyncHttpBlkMain's http_blk_semantics,
  http_blk_spec and http_blk_spec_fair are about:

     SNOC (main_call «main») http_l_prog

  where http_l_prog is the basis, Socket, the Async library, M4's loop,
  the echo server's program, the live-fd blocking loop (run_l), the
  header-tolerant HTTP server (asyncHttpBlkProg), and

     fun main u = run_l ([3], [3], http_server_h demo_files 3);

  As in ../echo-blocking: the declarations after the basis are written to
  http_live.sexp (sexpV3479Lib).
*)
Theory asyncHttpBlkExport
Ancestors
  asyncHttpBlkMain ffiSpikeDivMain basisProg
Libs
  preamble sexpV3479Lib

(* The verified whole program, as a list of declarations *)
val prog =
  “SNOC (main_call «main») http_l_prog”
  |> (REWRITE_CONV [asyncHttpBlkMainTheory.http_l_prog_def,
                    ffiSpikeDivMainTheory.main_call_def, SNOC_APPEND, APPEND]
      THENC REWRITE_CONV [GSYM SNOC_APPEND] THENC REWRITE_CONV [SNOC, APPEND])
  |> concl |> rhs;

val basis_decls =
  basisProgTheory.basis_def |> concl |> rhs |> listSyntax.dest_list |> fst;
val (all_decls, dec_ty) = listSyntax.dest_list prog;
val n_basis = length basis_decls;

(* The program starts with the basis, exactly *)
val _ =
  if n_basis <= length all_decls andalso
     ListPair.allEq (uncurry aconv) (basis_decls, List.take (all_decls, n_basis))
  then ()
  else failwith "the program does not start with the basis";

val user_decls = List.drop (all_decls, n_basis);

val _ = print ("asyncHttpBlkExport: " ^ Int.toString n_basis ^ " basis declarations, " ^
               Int.toString (length user_decls) ^ " program declarations\n");

val _ = write_ast_to_file "http_live.sexp" (listSyntax.mk_list (user_decls, dec_ty));
