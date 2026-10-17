(*
  THE RESULT for HTTP with bodies on version 2: the generic protocol
  server for HttpSpecBodies' requests (asyncProtoProgB's b_parse and
  bresp_demo, unchanged), run by the handle-layer loop, meets the
  approved HttpSpecBodies2:

     http_prog_pb2_spec : http_spec_b2 3w demo_files http_prog_pb2

      fun main2 u = run_h (3, [3], ([], 0), proto_server b_parse bresp_demo 3)

  On the canonical library translation chain (asyncM4SockServer →
  socketV2Prog → asyncHLProg → asyncHttpSockProg → … → asyncProtoProgB),
  the program is version 1's http_prog_pb with this main.
  - main2_pb_spec: main2 () is run_h on the protocol server
    (sproto_server_spec, run_h_spec);
  - http_semantics_prog_pb2: in a version-2 world, if no action is a
    misuse, the program diverges with the handle loop's run as its trace;
  - http_prog_pb2_spec: the misuse hypothesis by hrun_ok_gen, the three
    clauses by proto2_model, and http_spec_b2_proto.
*)
Theory asyncProtoSemB2
Ancestors
  asyncCore asyncLevel1 asyncCfActModel asyncCfActProg asyncM3World
  asyncM3Prog asyncM3Loop asyncM4GRounds asyncM4Loop asyncM4SockModel
  asyncM4SockApprox asyncM4SockServer asyncM4Relabel asyncServerWith
  socketV2FFI socketV2Fair socketV2Part socketV2Proof socketV2Div
  EchoSpec2 HttpSpecBodies HttpSpecBodies2 asyncHLModel asyncHLProg asyncHLLoop
  asyncHttpMain asyncProto asyncProtoServer asyncProtoSockSpec asyncProtoProg
  asyncProtoB asyncProtoProgB asyncProtoSemB asyncProtoSafe asyncRunOkGen asyncProtoEof
  asyncHLSimRunGen asyncProto2 asyncProto2Model ffiSpikeDivMain
  cfDiv ml_translator ml_prog std_prelude llist
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncProtoProgB"

Overload resp_b = “print_response o bhandle demo_files”

Quote add_cakeml:
  fun main2 u = run_h (3, [3], ([], 0), proto_server b_parse bresp_demo 3);
End

Overload pb2_trace = “λs0. gtrace2 (proto_server P_b resp_b 3) 3 s0”
Overload pb2_run_ok =
  “λs0. hrun_ok 3w (interest [3w]) (srelabel (proto_server P_b resp_b 3)) s0”

(* main2 () runs the handle loop on the protocol server *)
Theorem main2_pb_spec:
  limited_parts socket2_names p ∧ pb2_run_ok s0 ∧ UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) main2_v [uv] (SOCKETS2_EV s0 []) (POSTd io. io = pb2_trace s0)
Proof
  rpt strip_tac >> xcf_with_def (fetch "-" "main2_v_def") >>
  xlet ‘POSTv cv. &COMP p SACT UNIT_TYPE SSNAP (srelabel (proto_server P_b resp_b 3)) cv *
                  SOCKETS2_EV s0 []’
  >- (xapp_spec (INST_TYPE [alpha |-> “:brequest”] sproto_server_spec) >> xsimpl >>
      qexistsl_tac [‘resp_b’, ‘P_b’, ‘HTTPSPECBODIES_BREQUEST_TYPE’] >> simp[] >>
      irule proto_impl_b >>
      mp_tac (fetch "asyncProtoProgB" "bresp_demo_v_thm") >> simp[bresp_demo_eq]) >>
  rpt (xlet_auto >- (xcon >> xsimpl)) >>
  gvs[] >>
  ‘app p run_h_v [Conv NONE [Litv (IntLit 3);
                     Conv (SOME (TypeStamp «::» 1))
                       [Litv (IntLit 3); Conv (SOME (TypeStamp «[]» 1)) []];
                     Conv NONE [Conv (SOME (TypeStamp «[]» 1)) []; Litv (IntLit 0)];
                     cv]]
     (SOCKETS2_EV s0 []) (POSTd io. io = pb2_trace s0)’
    by (irule run_h_spec >>
        simp[wf_relabel, wf_proto_server, LIST_TYPE_def, HSV_def, hinit_def] >> metis_tac[]) >>
  qpat_x_assum ‘app _ run_h_v _ _ _’ xapp_spec
QED

(* ------------------------------------------------------------------------
   The whole program
   ------------------------------------------------------------------------ *)

val http_decs_pb2_tm =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> concl |> strip_comb |> snd |> (fn args => List.nth (args, 2));

Definition http_decs_pb2_def:
  http_decs_pb2 = ^http_decs_pb2_tm
End

Definition http_prog_pb2_def:
  http_prog_pb2 = SNOC (main_call «main2») http_decs_pb2
End

Theorem http_prog_pb2_eq =
  REWRITE_CONV [http_prog_pb2_def, http_decs_pb2_def, main_call_def,
                listTheory.SNOC_APPEND, listTheory.APPEND] “http_prog_pb2”;

val Decls_th =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> GEN_ALL |> ISPEC “socket2_only_ffi s0” |> SPEC_ALL
  |> REWRITE_RULE [GSYM http_decs_pb2_def];

val (_, decls_args) = strip_comb (concl Decls_th);
val env2_tm = List.nth (decls_args, 3);
val st2_tm = List.nth (decls_args, 4);

val lookup_main2 = let
  val g = “nsLookup (^env2_tm).v (Short «main2») = SOME main2_v”
  in prove (g, REWRITE_TAC [fst (dest_eq g) |> nsLookup_conv]) end;

val st2_ffi = prove (“(^st2_tm).ffi = socket2_only_ffi s0”, EVAL_TAC);

Theorem http_semantics_pb2[local]:
  pb2_run_ok s0 ⇒
  semantics_dec_list (init_state (socket2_only_ffi s0)) init_env
    http_prog_pb2 (Diverge (pb2_trace s0))
Proof
  strip_tac
  \\ assume_tac Decls_th
  \\ drule call_main_thm_div \\ strip_tac
  \\ assume_tac st2_ffi
  \\ drule s2only_init_heap \\ strip_tac
  \\ first_x_assum (qspecl_then [‘s2only_proj2’, ‘s2only_proj1’, ‘h2’, ‘h1’,
       ‘main2_v’, ‘«main2»’, ‘λio. io = pb2_trace s0’, ‘SOCKETS2_EV s0 []’] mp_tac)
  \\ impl_tac
  >- (simp [lookup_var_def, lookup_main2]
      \\ irule main2_pb_spec \\ simp [limited_parts_s2only])
  \\ rw [http_prog_pb2_def] \\ gvs []
QED

Theorem http_prog_pb2_syntax_ok:
  prog_syntax_ok http_prog_pb2
Proof
  REWRITE_TAC [http_prog_pb2_eq, prog_syntax_ok_def] >> EVAL_TAC
QED

(* MAIN: in a version-2 world, if no action is a misuse, the program
   diverges with the handle loop's run of the protocol server as its trace *)
Theorem http_semantics_prog_pb2:
  pb2_run_ok sk ⇒
  semantics_prog (init_state (socket2_ffi sk)) init_env http_prog_pb2
    (Diverge (pb2_trace sk))
Proof
  strip_tac >> drule http_semantics_pb2 >>
  simp [socket2_only_ffi_eq,
        GSYM (MATCH_MP prog_syntax_ok_semantics http_prog_pb2_syntax_ok)]
QED

(* MAIN: the bodies HTTP program on the handle layer meets the approved
   version-2 specification *)
Theorem http_prog_pb2_spec:
  http_spec_b2 3w demo_files http_prog_pb2
Proof
  rw[http_spec_b2_proto, proto_spec2_def, server_world2_def] >>
  qexists_tac ‘pb2_trace sk’ >>
  ‘uses_ok 3 (proto_server P_b resp_b 3)’
    by simp[uses_ok_def, proto_server_uses_accepted, proto_ok_b] >>
  ‘pb2_run_ok sk’
    by (qspecl_then [‘sk’, ‘3’, ‘proto_server P_b resp_b 3’] mp_tac
          (Q.GENL [‘s2’, ‘lfdn’, ‘m’] hrun_ok_gen) >> simp[]) >>
  simp[http_semantics_prog_pb2] >>
  qspecl_then [‘P_b’, ‘sk’, ‘3’, ‘resp_b’] mp_tac
    (Q.GENL [‘P’, ‘s2’, ‘lfdn’, ‘resp’] proto2_model) >>
  simp[proto_ok_b]
QED
