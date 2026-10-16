(*
  translateGlueLib: the glue around a generated handler (design/44 §9).

  A server program is its handler (translateLib) inside three layers of
  glue, the same for every program:

   - translate_server: the server, the library's skeleton applied to the
     handler (fun S xs lfd = SKEL (fn fd => H xs fd INIT) lfd), proved from
     the skeleton's spec, whose hypothesis is the handler's spec;
   - translate_store: optionally, with_store around it
     (fun S' lfd = with_store DELTA STORE0 (S lfd)), proved from
     with_store_spec and the store step's DELTA theorem;
   - translate_main: main () = run_i ([3], SERVER 3), proved from run_i_spec;
   - translate_program: the whole program (the translation's declarations,
     then main ()), its main lookup, prog_syntax_ok, and its semantics:
     semantics_prog ... prog (Diverge (TRACE s0)).

  Each writes the CakeML and proves the statement it is given (the server
  and main statements are the model's; the program statement is derived).
*)
structure translateGlueLib =
struct

open HolKernel boolLib bossLib
open cfTacticsLib ml_translatorLib basisFunctionsLib ml_progLib cfLetAutoLib

val ERR = mk_HOL_ERR "translateGlueLib"

fun add_code code =
  (print ("translateGlueLib: generated\n" ^ code ^ "\n");
   append_prog (process_topdecs [QUOTE code]))

fun v_def name = DB.fetch "-" (name ^ "_v_def")

(* ------------------------------------------------------------------------
   The server: the skeleton applied to the handler
   ------------------------------------------------------------------------ *)

(* Statements (goal) and posts are quotations, parsed after the code is
   added (they mention its constants).

   translate_server {name, params, skel, handler, goal, model_defs,
                     skel_spec, hyp_defs, handler_spec}:
     fun name params lfd = skel (fn fd => handler params fd init) lfd;
   goal: the server's spec, whose hypotheses give the params' invariants;
   model_defs: the model server's definition (skeleton applied to the
   handler); skel_spec: the skeleton's spec, whose hypothesis (hyp_defs,
   e.g. SHANDLER_def) is the handler's spec; handler_spec: the generated
   handler's spec, in the skeleton's vocabulary. init is the initial
   buffer, the empty string. *)
fun translate_server {name, params, skel, handler, goal, model_defs,
                      skel_spec, hyp_defs, handler_spec, wfs} =
  let
    val ps = String.concatWith " " params
    val code = "fun " ^ name ^ " " ^ ps ^ (if null params then "" else " ") ^
               "lfd = " ^ skel ^ " (fn fd => " ^ handler ^ " " ^ ps ^
               (if null params then "" else " ") ^ "fd []) lfd;"
    val _ = add_code code
  in
    store_thm (name ^ "_spec", Term goal,
      rpt strip_tac >> xcf_with_def (v_def name) >> xfun ‘h’ >>
      simp model_defs >> xapp_spec skel_spec >>
      simp (hyp_defs @ wfs) >> rpt strip_tac >>
      qpat_x_assum ‘curried _ _ h ∧ _’ (irule o CONJUNCT2) >>
      xlet ‘POSTv bv. &LIST_TYPE CHAR "" bv’
      >- (xcon >> xsimpl >> simp [ml_translatorTheory.LIST_TYPE_def]) >>
      xapp_spec handler_spec >> simp [] >> metis_tac [])
  end

(* ------------------------------------------------------------------------
   with_store around the server
   ------------------------------------------------------------------------ *)

(* translate_store {name, inner, delta, store0, goal, model_defs,
                    inner_post, store0_post, inner_spec, with_store_spec,
                    wf_inner, witnesses, simps}:
     fun name lfd = with_store delta store0 (inner lfd);
   inner_post: the inner server's post (POSTv cv. ...), store0_post the
   initial store value's (POSTv sv. ...); witnesses instantiate
   with_store_spec's relations (answers, queries, store), simps prove its
   DELTA and initial-store hypotheses. *)
fun translate_store {name, inner, delta, store0, goal, model_defs,
                     inner_post, store0_post, inner_spec, with_store_spec,
                     wf_inner, witnesses, simps} =
  let
    val code = "fun " ^ name ^ " lfd = with_store " ^ delta ^ " " ^ store0 ^
               " (" ^ inner ^ " lfd);"
    val _ = add_code code
  in
    store_thm (name ^ "_spec", Term goal,
      rpt strip_tac >> xcf_with_def (v_def name) >> simp model_defs >>
      xlet inner_post >- (xapp_spec inner_spec >> simp []) >>
      xlet store0_post
      >- (xcon >> xsimpl >> simp [ml_translatorTheory.LIST_TYPE_def]) >>
      xapp_spec with_store_spec >> simp [wf_inner] >>
      MAP_EVERY qexists_tac witnesses >>
      simp simps >> TRY (qexists_tac ‘[]’ >> simp []))
  end

(* ------------------------------------------------------------------------
   main () = run_i ([3], SERVER 3)
   ------------------------------------------------------------------------ *)

(* translate_main {name, server_call, goal, server_post, server_tac,
                   run_ok_tac}:
     fun name u = run_i ([3], server_call);
   goal: main's spec, app p name_v [uv] (SOCKETS_EV s0 [])
   (POSTd io. io = TRACE s0); server_post: the server's value's post (with
   * SOCKETS_EV s0 []); server_tac proves it; run_ok_tac proves
   run_i_spec's side conditions (wf and run_ok of the server). *)
fun translate_main {name, server_call, goal, server_post, server_tac,
                    run_ok_tac} =
  let
    val code = "fun " ^ name ^ " u = run_i ([3], " ^ server_call ^ ");"
    val _ = add_code code
    val goal = Term goal
    val app_goal = snd (dest_imp (snd (strip_forall goal)))
    val (_, app_args) = strip_comb app_goal
    val p = hd app_args and post = List.last app_args
    val app_tm = “app ^p run_i_v [Conv NONE [Conv (SOME (TypeStamp «::» 1))
                     [Litv (IntLit 3); Conv (SOME (TypeStamp «[]» 1)) []]; cv]]
                     (SOCKETS_EV s0 []) ^post”
  in
    store_thm (name ^ "_spec", goal,
      rpt strip_tac >> xcf_with_def (v_def name) >>
      xlet server_post >- server_tac >>
      rpt (xlet_auto >- (xcon >> xsimpl)) >> gvs [] >>
      (* the run_i call, from run_i_spec *)
      (SUBGOAL_THEN app_tm (fn th => xapp_spec th)
       >- (irule (DB.fetch "loopPollDyn" "run_i_spec") >> run_ok_tac)))
  end

(* ------------------------------------------------------------------------
   The whole program and its semantics
   ------------------------------------------------------------------------ *)

(* translate_program {prefix, main_v, main_spec, trace, hyps}:
   prefix_decs = the current translation's declarations,
   prefix_prog = SNOC (main_call «main») prefix_decs,
   prefix_prog_syntax_ok, and
     prefix_semantics_prog : hyps s0 ⇒
       semantics_prog (init_state (socket_only_ffi s0)) init_env prefix_prog
         (Diverge (trace s0))
   from main_spec : limited_parts socket_names p ∧ hyps s0 ∧ UNIT_TYPE () uv
   ⇒ app p main_v [uv] (SOCKETS_EV s0 []) (POSTd io. io = trace s0).
   main_v must be bound to «main» in the program. *)
fun translate_program {prefix, main_v, main_spec, trace, hyps} =
  let
    val decs_tm =
      get_ml_prog_state () |> ml_progLib.get_thm
      |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
      |> concl |> strip_comb |> snd |> (fn args => List.nth (args, 2))
    val decs_def = new_definition (prefix ^ "_decs_def",
                     mk_eq (mk_var (prefix ^ "_decs", type_of decs_tm), decs_tm))
    val decs_c = lhs (concl decs_def)
    val prog_def = new_definition (prefix ^ "_prog_def",
                     mk_eq (mk_var (prefix ^ "_prog", type_of decs_tm),
                            “SNOC (main_call «main») ^decs_c”))
    val prog_c = lhs (concl prog_def)
    val prog_eq = save_thm (prefix ^ "_prog_eq",
      REWRITE_CONV [prog_def, decs_def, DB.fetch "divMain" "main_call_def",
                    listTheory.SNOC_APPEND, listTheory.APPEND] prog_c)
    val Decls_th =
      get_ml_prog_state () |> ml_progLib.get_thm
      |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
      |> GEN_ALL |> ISPEC “socket_only_ffi s0” |> SPEC_ALL
      |> REWRITE_RULE [GSYM decs_def]
    val (_, decls_args) = strip_comb (concl Decls_th)
    val env2_tm = List.nth (decls_args, 3)
    val st2_tm = List.nth (decls_args, 4)
    val lookup_main =
      let val g = “nsLookup (^env2_tm).v (Short «main») = SOME ^main_v”
      in prove (g, REWRITE_TAC [fst (dest_eq g) |> nsLookup_conv]) end
    val st2_ffi = prove (“(^st2_tm).ffi = socket_only_ffi s0”, EVAL_TAC)
    val s0 = “s0 : sockets”
    val hyp = mk_comb (hyps, s0) |> BETA_CONV |> concl |> rhs
    val tr = mk_comb (trace, s0) |> BETA_CONV |> concl |> rhs
    val sem_dec = prove (
      mk_imp (hyp, “semantics_dec_list (init_state (socket_only_ffi s0)) init_env
                      ^prog_c (Diverge ^tr)”),
      strip_tac
      \\ assume_tac Decls_th
      \\ drule (DB.fetch "divMain" "call_main_thm_div") \\ strip_tac
      \\ assume_tac st2_ffi
      \\ drule (DB.fetch "socketDiv" "sonly_init_heap") \\ strip_tac
      \\ first_x_assum (qspecl_then [‘sonly_proj2’, ‘sonly_proj1’, ‘h2’, ‘h1’,
           [ANTIQUOTE main_v], ‘«main»’, [ANTIQUOTE “λio. io = ^tr”],
           ‘SOCKETS_EV s0 []’] mp_tac)
      \\ impl_tac
      >- (simp [ml_progTheory.lookup_var_def, lookup_main]
          \\ irule main_spec
          \\ simp [DB.fetch "socketDiv" "limited_parts_sonly"])
      \\ rw [prog_def] \\ fs [])
    val syntax_ok = store_thm (prefix ^ "_prog_syntax_ok",
      “prog_syntax_ok ^prog_c”,
      REWRITE_TAC [prog_eq, ml_progTheory.prog_syntax_ok_def] >> EVAL_TAC)
    val sem = store_thm (prefix ^ "_semantics_prog",
      mk_imp (hyp, “semantics_prog (init_state (socket_only_ffi s0)) init_env
                      ^prog_c (Diverge ^tr)”),
      strip_tac >> drule sem_dec >>
      simp [GSYM (MATCH_MP ml_progTheory.prog_syntax_ok_semantics syntax_ok)])
  in {prog_def = prog_def, semantics_prog = sem} end

end
