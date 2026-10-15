(*
  prove_sem_thm for the socket world: turns a socket_whole_prog_spec of main
  into a semantics_dec_list theorem about the whole program.

  This is ffiSpikeClockWorldLib.prove_sem_thm with the clock world replaced by
  ours: only the FFI term and the instantiated theorem differ.
*)
structure ffiSpikeSocketWorldLib =
struct

open preamble ml_progLib ffiSpikeSocketWorldTheory

(* The initial FFI state, from the arguments of the spec
   socket_whole_prog_spec fv cl fs clk sk post.  (basis_ffiLib can use a fixed
   term instead, since its spec never instantiates the FFI state.) *)
fun socket_world_ffi_term spec = let
  val (_, args) = strip_comb (concl spec)
  in list_mk_comb (prim_mk_const {Thy = "ffiSpikeSocketWorld",
                                  Name = "socket_world_ffi"},
                   [List.nth (args,1), List.nth (args,2), List.nth (args,3), List.nth (args,4)])
  end;

fun prove_sem_thm name code_const_name spec = let
  val Decls_lemma =
    ml_translatorLib.get_ml_prog_state ()
    |> ml_progLib.get_thm
    |> REWRITE_RULE [ml_progTheory.ML_code_def,ml_progTheory.ML_code_env_def]
  val spec = spec |> UNDISCH_ALL
  val socket_world_ffi_term = socket_world_ffi_term spec
  val th1 = CONJ spec (Decls_lemma |> GEN_ALL
                                   |> ISPEC socket_world_ffi_term |> SPEC_ALL)
  val th2 = MATCH_MP socket_whole_prog_spec_semantics th1
  val remove_snocs_conv =
        PURE_REWRITE_CONV [listTheory.SNOC_APPEND] THENC
        PURE_REWRITE_CONV [GSYM listTheory.APPEND_ASSOC] THENC
        PURE_REWRITE_CONV [listTheory.APPEND]
  val th3 = SPEC (mlstringSyntax.mk_mlstring name) th2
            |> CONV_RULE (RAND_CONV remove_snocs_conv)
  val code_tm = th3 |> concl |> rand
  val code_v = mk_var(code_const_name, type_of code_tm)
  val code_def = new_definition(code_const_name ^ "_def[compute]",
                                mk_eq(code_v,code_tm))
  val th4 = th3 |> CONV_RULE (RAND_CONV (K (SYM code_def)))
                |> CONV_RULE (REWR_CONV LET_THM THENC BETA_CONV)
  (* main is bound in the final environment *)
  val th5 = let
    val g1 = th4 |> concl |> dest_imp |> fst
    val l = dest_eq g1 |> fst |> nsLookup_conv
    val l1 = prove(g1,REWRITE_TAC [l])
    in MP th4 l1 end
  (* the library's declarations make no FFI calls *)
  val th6 = let
    val g2 = th5 |> concl |> dest_imp |> fst
    val l2 = prove(g2,EVAL_TAC)
    in MP th5 l2 end
  (* the first two references are the basis library's buffers *)
  val th7 = let
    val g2 = th6 |> concl |> dest_imp |> fst
    val l2 = prove(g2,
                   EVAL_TAC
                   \\ REWRITE_TAC [semanticPrimitivesTheory.store_v_11,
                                   APPEND, CONS_11, basis_ffiTheory.basis_refs_eqs]
                   \\ simp_tac std_ss []
                   \\ EVAL_TAC)
    in MP th6 l2 end
  in th7 |> DISCH_ALL |> SIMP_RULE bool_ss [GSYM CONJ_ASSOC, AND_IMP_INTRO] end;

end
