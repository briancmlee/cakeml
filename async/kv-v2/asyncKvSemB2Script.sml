(*
  THE RESULT for the key-value server on version 2: kv_server (http-kv,
  unchanged), run by the handle-layer loop, meets the approved HttpKvSpec2:

     kv_prog2_spec : kv_spec2 3w kv_prog2

      fun main2 u = run_h (3, [3], ([], 0), kv_server 3)

  As asyncProtoSemB2 for HTTP:
  - main2_kv_spec: main2 () is run_h on the key-value server
    (kv_server_spec, run_h_spec);
  - kv_semantics_prog2: in a version-2 world, if no action is a misuse,
    the program diverges with the handle loop's run as its trace;
  - kv_prog2_spec: the misuse hypothesis by hrun_ok_gen, the three
    clauses by kv2_model.
*)
Theory asyncKvSemB2
Ancestors
  asyncCore asyncLevel1 asyncCfActModel asyncCfActProg asyncM3World
  asyncM3Prog asyncM3Loop asyncM4GRounds asyncM4Loop asyncM4SockModel
  asyncM4SockApprox asyncM4SockServer asyncM4Relabel
  socketV2FFI socketV2Fair socketV2Part socketV2Proof socketV2Div
  EchoSpec2 HttpKvSpec2 asyncHLModel asyncHLProg asyncHLLoop
  asyncWithStore asyncKvModel asyncKvSockModel asyncKvProg asyncKvSpec
  asyncHLSimRunGen asyncKv2Model ffiSpikeDivMain
  cfDiv ml_translator ml_prog std_prelude llist
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncKvProg"

Quote add_cakeml:
  fun main2 u = run_h (3, [3], ([], 0), kv_server 3);
End

Overload kv2_trace = “λs0. gtrace2 (kv_server 3) 3 s0”
Overload kv2_run_ok =
  “λs0. hrun_ok 3w (interest [3w]) (srelabel (kv_server 3)) s0”

(* main2 () runs the handle loop on the key-value server *)
Theorem main2_kv_spec:
  limited_parts socket2_names p ∧ kv2_run_ok s0 ∧ UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) main2_v [uv] (SOCKETS2_EV s0 []) (POSTd io. io = kv2_trace s0)
Proof
  rpt strip_tac >> xcf_with_def (fetch "-" "main2_v_def") >>
  xlet ‘POSTv cv. &COMP p SACT UNIT_TYPE SSNAP (srelabel (kv_server 3)) cv *
                  SOCKETS2_EV s0 []’
  >- (xapp_spec kv_server_spec >> xsimpl) >>
  rpt (xlet_auto >- (xcon >> xsimpl)) >>
  gvs[] >>
  ‘app p run_h_v [Conv NONE [Litv (IntLit 3);
                     Conv (SOME (TypeStamp «::» 1))
                       [Litv (IntLit 3); Conv (SOME (TypeStamp «[]» 1)) []];
                     Conv NONE [Conv (SOME (TypeStamp «[]» 1)) []; Litv (IntLit 0)];
                     cv]]
     (SOCKETS2_EV s0 []) (POSTd io. io = kv2_trace s0)’
    by (irule run_h_spec >>
        simp[wf_skv_server, LIST_TYPE_def, HSV_def, hinit_def] >> metis_tac[]) >>
  qpat_x_assum ‘app _ run_h_v _ _ _’ xapp_spec
QED

(* ------------------------------------------------------------------------
   The whole program
   ------------------------------------------------------------------------ *)

val kv_decs2_tm =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> concl |> strip_comb |> snd |> (fn args => List.nth (args, 2));

Definition kv_decs2_def:
  kv_decs2 = ^kv_decs2_tm
End

Definition kv_prog2_def:
  kv_prog2 = SNOC (main_call «main2») kv_decs2
End

Theorem kv_prog2_eq =
  REWRITE_CONV [kv_prog2_def, kv_decs2_def, main_call_def,
                listTheory.SNOC_APPEND, listTheory.APPEND] “kv_prog2”;

val Decls_th =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> GEN_ALL |> ISPEC “socket2_only_ffi s0” |> SPEC_ALL
  |> REWRITE_RULE [GSYM kv_decs2_def];

val (_, decls_args) = strip_comb (concl Decls_th);
val env2_tm = List.nth (decls_args, 3);
val st2_tm = List.nth (decls_args, 4);

val lookup_main2 = let
  val g = “nsLookup (^env2_tm).v (Short «main2») = SOME main2_v”
  in prove (g, REWRITE_TAC [fst (dest_eq g) |> nsLookup_conv]) end;

val st2_ffi = prove (“(^st2_tm).ffi = socket2_only_ffi s0”, EVAL_TAC);

Theorem kv_semantics2[local]:
  kv2_run_ok s0 ⇒
  semantics_dec_list (init_state (socket2_only_ffi s0)) init_env
    kv_prog2 (Diverge (kv2_trace s0))
Proof
  strip_tac
  \\ assume_tac Decls_th
  \\ drule call_main_thm_div \\ strip_tac
  \\ assume_tac st2_ffi
  \\ drule s2only_init_heap \\ strip_tac
  \\ first_x_assum (qspecl_then [‘s2only_proj2’, ‘s2only_proj1’, ‘h2’, ‘h1’,
       ‘main2_v’, ‘«main2»’, ‘λio. io = kv2_trace s0’, ‘SOCKETS2_EV s0 []’] mp_tac)
  \\ impl_tac
  >- (simp [lookup_var_def, lookup_main2]
      \\ irule main2_kv_spec \\ simp [limited_parts_s2only])
  \\ rw [kv_prog2_def] \\ gvs []
QED

Theorem kv_prog2_syntax_ok:
  prog_syntax_ok kv_prog2
Proof
  REWRITE_TAC [kv_prog2_eq, prog_syntax_ok_def] >> EVAL_TAC
QED

(* MAIN: in a version-2 world, if no action is a misuse, the program
   diverges with the handle loop's run of the key-value server as its trace *)
Theorem kv_semantics_prog2:
  kv2_run_ok sk ⇒
  semantics_prog (init_state (socket2_ffi sk)) init_env kv_prog2
    (Diverge (kv2_trace sk))
Proof
  strip_tac >> drule kv_semantics2 >>
  simp [socket2_only_ffi_eq,
        GSYM (MATCH_MP prog_syntax_ok_semantics kv_prog2_syntax_ok)]
QED

(* MAIN: the key-value program on the handle layer meets the approved
   version-2 specification *)
Theorem kv_prog2_spec:
  kv_spec2 3w kv_prog2
Proof
  rw[kv_spec2_def, server_world2_def] >>
  qexists_tac ‘kv2_trace sk’ >>
  ‘kv2_run_ok sk’
    by (qspecl_then [‘sk’, ‘3’, ‘kv_server 3’] mp_tac
          (Q.GENL [‘s2’, ‘lfdn’, ‘m’] hrun_ok_gen) >> simp[kv_server_uses_ok]) >>
  simp[kv_semantics_prog2] >>
  qspecl_then [‘sk’, ‘3’] mp_tac (Q.GENL [‘s2’, ‘lfdn’] kv2_model) >> simp[]
QED
