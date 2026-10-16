(*
  The runnable HTTP-bodies server (polling loop): the verified program,
  exported for the CakeML release compiler.

  The program is exactly the one httpSemantics's http_prog_spec is
  about:

     http_prog = SNOC (main_call «main») http_decs_pb

  with  fun main u = proto_main b_parse bresp_demo u.  As in
  ../echo-blocking and ../http-quiet: the declarations after the basis are
  written to http_server_pb.sexp (sexpV3479Lib).
*)
Theory httpExport
Ancestors
  httpSemantics basisProg
Libs
  preamble sexpV3479Lib

val prog = httpSemanticsTheory.http_prog_eq |> concl |> rhs;

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

val _ = print ("asyncProtoBExport: " ^ Int.toString n_basis ^ " basis declarations, " ^
               Int.toString (length user_decls) ^ " program declarations\n");

val _ = write_ast_to_file "http_server_pb.sexp" (listSyntax.mk_list (user_decls, dec_ty));
