(*
  The runnable HTTP-bodies server on the select-on-interest loop (option
  C): the verified program, exported for the CakeML release compiler.

  The program is exactly the one httpBlockingSemantics's http_blocking_semantics and
  http_blocking_spec, and httpQuietStable's http_blocking_quiet_stable, are about:

     SNOC (main_call «main») http_blocking_prog

  with  fun main u = run_q ([3], proto_server2 b_parse bresp_demo 3).
  As in ../echo-blocking: the declarations after the basis are written to
  http_headers_quiet.sexp (sexpV3479Lib).
*)
Theory httpBlockingExport
Ancestors
  httpBlockingSemantics divMain basisProg
Libs
  preamble sexpV3479Lib

val prog =
  “SNOC (main_call «main») http_blocking_prog”
  |> (REWRITE_CONV [httpBlockingSemanticsTheory.http_blocking_prog_def,
                    divMainTheory.main_call_def, SNOC_APPEND, APPEND]
      THENC REWRITE_CONV [GSYM SNOC_APPEND] THENC REWRITE_CONV [SNOC, APPEND])
  |> concl |> rhs;

val basis_decls =
  basisProgTheory.basis_def |> concl |> rhs |> listSyntax.dest_list |> fst;
val (all_decls, dec_ty) = listSyntax.dest_list prog;
val n_basis = length basis_decls;

val _ =
  if n_basis <= length all_decls andalso
     ListPair.allEq (uncurry aconv) (basis_decls, List.take (all_decls, n_basis))
  then ()
  else failwith "the program does not start with the basis";

val user_decls = List.drop (all_decls, n_basis);

val _ = print ("asyncOCHttpExport: " ^ Int.toString n_basis ^ " basis declarations, " ^
               Int.toString (length user_decls) ^ " program declarations\n");

val _ = write_ast_to_file "http_quiet.sexp" (listSyntax.mk_list (user_decls, dec_ty));
