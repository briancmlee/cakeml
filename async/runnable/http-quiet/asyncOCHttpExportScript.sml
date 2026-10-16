(*
  The runnable HTTP-bodies server on the select-on-interest loop (option
  C): the verified program, exported for the CakeML release compiler.

  The program is exactly the one asyncOCSemB's http_q_semantics and
  http_q_spec, and asyncOCQuietB's http_q_quiet_b, are about:

     SNOC (main_call «main») http_q_prog

  with  fun main u = run_q ([3], proto_server2 b_parse bresp_demo 3).
  As in ../echo-blocking: the declarations after the basis are written to
  http_quiet.sexp (sexpV3479Lib).
*)
Theory asyncOCHttpExport
Ancestors
  asyncOCSemB ffiSpikeDivMain basisProg
Libs
  preamble sexpV3479Lib

val prog =
  “SNOC (main_call «main») http_q_prog”
  |> (REWRITE_CONV [asyncOCSemBTheory.http_q_prog_def,
                    ffiSpikeDivMainTheory.main_call_def, SNOC_APPEND, APPEND]
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
