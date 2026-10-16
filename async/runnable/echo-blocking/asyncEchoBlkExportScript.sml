(*
  The runnable blocking echo server: m4-blocking's verified program,
  exported for the CakeML release compiler.

  The program is exactly the one asyncM4BlkMain's echo_blocking_semantics
  and echo_blocking_spec are about:

     SNOC (main_call «main») echo_b_prog

  where echo_b_prog is the basis, Socket, the Async library, M4's loop,
  the echo server (spike/m4-safety's asyncM4SockServer), the blocking loop
  (asyncM4BlkLoop: wait_ready, step_b, run_b) and

     fun main u = run_b ([3], server 3);

  As in ../runnable (asyncEchoMain): the declarations after the basis are
  written to echo_blocking.sexp in the S-expression format of the CakeML
  release v3479 (sexpV3479Lib); the release compiler adds its own basis.
*)
Theory asyncEchoBlkExport
Ancestors
  asyncM4BlkMain ffiSpikeDivMain basisProg
Libs
  preamble sexpV3479Lib

(* The verified whole program, as a list of declarations *)
val prog =
  “SNOC (main_call «main») echo_b_prog”
  |> (REWRITE_CONV [asyncM4BlkMainTheory.echo_b_prog_def,
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

val _ = print ("asyncEchoBlkExport: " ^ Int.toString n_basis ^ " basis declarations, " ^
               Int.toString (length user_decls) ^ " program declarations\n");

val _ = write_ast_to_file "echo_blocking.sexp" (listSyntax.mk_list (user_decls, dec_ty));
