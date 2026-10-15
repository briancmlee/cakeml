(*
  The runnable blocking echo server that selects on the live connections:
  m4-blocking-live's verified program,
  exported for the CakeML release compiler.

  The program is exactly the one asyncM4LiveMain's echo_live_semantics
  and echo_live_spec are about:

     SNOC (main_call «main») echo_l_prog

  where echo_l_prog is the basis, Socket, the Async library, M4's loop,
  the echo server (spike/m4-safety's asyncM4SockServer), the blocking loop
  (asyncM4LiveLoop: upd_live, step_l, run_l) and

     fun main u = run_l ([3], [3], server 3);

  As in ../runnable (asyncEchoMain): the declarations after the basis are
  written to echo_live.sexp in the S-expression format of the CakeML
  release v3479 (sexpV3479Lib); the release compiler adds its own basis.
*)
Theory asyncEchoLiveExport
Ancestors
  asyncM4LiveMain ffiSpikeDivMain basisProg
Libs
  preamble sexpV3479Lib

(* The verified whole program, as a list of declarations *)
val prog =
  “SNOC (main_call «main») echo_l_prog”
  |> (REWRITE_CONV [asyncM4LiveMainTheory.echo_l_prog_def,
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

val _ = print ("asyncEchoLiveExport: " ^ Int.toString n_basis ^ " basis declarations, " ^
               Int.toString (length user_decls) ^ " program declarations\n");

val _ = write_ast_to_file "echo_live.sexp" (listSyntax.mk_list (user_decls, dec_ty));
