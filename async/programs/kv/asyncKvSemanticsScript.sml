(*
  The whole key-value program's semantics: it diverges, its I/O trace is
  the socket-model run of kv_server under M4's dynamic-interest loop, and
  that trace is linearizable (HttpKvSpec's kv_safe).  As
  asyncHttpSemanticsB:
   - main_spec: main () runs run_i on ([3], kv_server 3)
     (run_i_spec with kv_server_spec; no misuse by gen_grun_ok);
   - safety: kv_comp_safe (asyncKvSafe).
*)
Theory asyncKvSemantics
Ancestors
  asyncCore asyncLevel1 asyncCfActModel asyncCfActProg asyncM3World
  asyncM3Prog asyncM3Loop asyncM4GRounds asyncM4Loop asyncM4SockModel
  asyncM4SockApprox asyncM4SockServer asyncRunOkGen
  HttpSpec HttpSpecBodies HttpKvSpec asyncWithStore asyncKvModel
  asyncKvSockModel asyncKvSafe asyncKvProg asyncKvSpec asyncKvMain
  ffiSpikeSocketFFI ffiSpikeSocketProof ffiSpikeSocketDiv ffiSpikeDivMain
  cfDiv ml_translator ml_prog std_prelude llist
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncKvMain"

Overload kv_trace =
  “λs0. LFLATTEN (LGENLIST
          (λi. fromList (grounds_events (interest [3w])
                           (srelabel (kv_server 3)) s0 i))
          NONE)”

Overload start_world = “λs0:sockets. s0.listeners = [(3w, [])] ∧ s0.conns = []”

(* MAIN (helper): main () runs the event loop on the key-value server *)
Theorem main_spec:
  limited_parts socket_names p ∧ start_world s0 ∧ UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) asyncKvMain$main_v [uv] (SOCKETS_EV s0 [])
    (POSTd io. io = kv_trace s0)
Proof
  rpt strip_tac >> xcf_with_def asyncKvMainTheory.main_v_def >>
  xlet ‘POSTv cv. &COMP p SACT UNIT_TYPE SSNAP (srelabel (kv_server 3)) cv *
                  SOCKETS_EV s0 []’
  >- (xapp_spec kv_server_spec >> xsimpl) >>
  rpt (xlet_auto >- (xcon >> xsimpl)) >>
  gvs[] >>
  ‘app p run_i_v [Conv NONE [Conv (SOME (TypeStamp «::» 1))
                     [Litv (IntLit 3); Conv (SOME (TypeStamp «[]» 1)) []]; cv]]
     (SOCKETS_EV s0 []) (POSTd io. io = kv_trace s0)’
    by (irule run_i_spec >> simp[wf_skv_server, LIST_TYPE_def] >>
        conj_tac
        >- (irule gen_grun_ok >> simp[] >> qexists_tac ‘3’ >>
            simp[kv_server_uses_ok]) >>
        metis_tac[]) >>
  qpat_x_assum ‘app _ run_i_v _ _ _’ xapp_spec
QED

val Decls_th =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> GEN_ALL |> ISPEC “socket_only_ffi s0” |> SPEC_ALL
  |> REWRITE_RULE [GSYM kv_decs_def];

val (_, decls_args) = strip_comb (concl Decls_th);
val env2_tm = List.nth (decls_args, 3);
val st2_tm = List.nth (decls_args, 4);

val lookup_main = let
  val g = “nsLookup (^env2_tm).v (Short «main») = SOME asyncKvMain$main_v”
  in prove (g, REWRITE_TAC [fst (dest_eq g) |> nsLookup_conv]) end;

val st2_ffi = prove (“(^st2_tm).ffi = socket_only_ffi s0”, EVAL_TAC);

(* MAIN: in a sockets-only world with one listener 3w and no connections,
   the key-value program diverges, and its I/O trace is linearizable *)
Theorem kv_semantics:
  start_world s0 ⇒
  ∃io. semantics_dec_list (init_state (socket_only_ffi s0)) init_env
         kv_prog (Diverge io) ∧
       io = kv_trace s0 ∧ kv_safe io
Proof
  strip_tac
  \\ assume_tac Decls_th
  \\ drule call_main_thm_div \\ strip_tac
  \\ assume_tac st2_ffi
  \\ drule sonly_init_heap \\ strip_tac
  \\ first_x_assum (qspecl_then [‘sonly_proj2’, ‘sonly_proj1’, ‘h2’, ‘h1’,
       ‘asyncKvMain$main_v’, ‘«main»’, ‘λio. io = kv_trace s0’,
       ‘SOCKETS_EV s0 []’] mp_tac)
  \\ impl_tac
  >- (simp [lookup_var_def, lookup_main]
      \\ irule main_spec \\ simp [limited_parts_sonly])
  \\ rw [kv_prog_def]
  \\ irule kv_comp_safe \\ simp []
QED

Theorem kv_prog_syntax_ok:
  prog_syntax_ok kv_prog
Proof
  REWRITE_TAC [kv_prog_eq, prog_syntax_ok_def] >> EVAL_TAC
QED

(* MAIN: the same, as semantics_prog (the form compile_correct takes) *)
Theorem kv_semantics_prog:
  start_world s0 ⇒
  semantics_prog (init_state (socket_only_ffi s0)) init_env kv_prog
    (Diverge (kv_trace s0)) ∧
  kv_safe (kv_trace s0)
Proof
  strip_tac >> drule kv_semantics >> strip_tac >>
  gvs [GSYM (MATCH_MP prog_syntax_ok_semantics kv_prog_syntax_ok)]
QED
