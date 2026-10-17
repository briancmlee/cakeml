(*
  asyncProtoSemB: the bodies HTTP program built on the generic CakeML
  handler (asyncProtoProgB) meets HttpSpecBodies' whole specification,
  through the generic pipeline (design/32 phase 4):

     http_prog_pb_spec : http_spec_b 3w demo_files http_prog_pb

  - main_pb_spec: main () is proto_main on the translated parser and
    responder (proto_main_spec, with PROTO_IMPL from the translator's
    certificates);
  - http_semantics_prog_pb: the program diverges with the generic
    server's run as its trace (the per-program Decls / lookup / syntax
    boilerplate, as asyncHttpSemanticsB);
  - http_prog_pb_spec: http_spec_b_proto and proto_spec_of_semantics.

  The existing program http_prog_b and its theorem are untouched; this is
  a second program for the same specification, proved generically.
*)
Theory asyncProtoSemB
Ancestors
  asyncCore asyncLevel1 asyncCfActModel asyncCfActProg asyncM3World
  asyncM3Prog asyncM3Loop asyncM4GRounds asyncM4Loop asyncM4SockModel
  asyncM4SockApprox asyncM4SockServer asyncServerWith
  ffiSpikeSocketFFI ffiSpikeSocketProof ffiSpikeSocketDiv ffiSpikeDivMain
  EchoSpec HttpSpec HttpSpecHeaders HttpSpecBodies asyncHttpMain asyncHeadline
  asyncProto asyncProtoServer asyncProtoSockSpec asyncProtoMain asyncProtoProg
  asyncProtoB asyncProtoProgB
  cfDiv ml_translator ml_prog std_prelude llist
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncProtoProgB"

Overload resp_b = “print_response o bhandle demo_files”

(* The translated parser and responder implement P_b.parse and resp_b *)
Theorem proto_impl_b:
  (HTTPSPECBODIES_BREQUEST_TYPE --> LIST_TYPE CHAR) resp_b respv ⇒
  PROTO_IMPL HTTPSPECBODIES_BREQUEST_TYPE P_b resp_b b_parse_v respv
Proof
  simp[PROTO_IMPL_def] >> strip_tac >>
  mp_tac (fetch "asyncProtoProgB" "b_parse_v_thm") >> simp[b_parse_P_b]
QED

(* MAIN (helper): main () is the generic main on the bodies protocol *)
Theorem main_pb_spec:
  limited_parts socket_names p ∧
  s0.listeners = [(3w, [])] ∧ s0.conns = [] ∧ UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) asyncProtoProgB$main_v [uv] (SOCKETS_EV s0 [])
    (POSTd io. io = proto_trace P_b resp_b s0)
Proof
  rpt strip_tac >> xcf_with_def asyncProtoProgBTheory.main_v_def >>
  xapp_spec proto_main_spec >> xsimpl >>
  simp[proto_ok_b] >> qexists_tac ‘HTTPSPECBODIES_BREQUEST_TYPE’ >>
  irule proto_impl_b >>
  mp_tac (fetch "asyncProtoProgB" "bresp_demo_v_thm") >> simp[bresp_demo_eq]
QED

(* ------------------------------------------------------------------------
   The whole program
   ------------------------------------------------------------------------ *)

val http_decs_pb_tm =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> concl |> strip_comb |> snd |> (fn args => List.nth (args, 2));

Definition http_decs_pb_def:
  http_decs_pb = ^http_decs_pb_tm
End

Definition http_prog_pb_def:
  http_prog_pb = SNOC (main_call «main») http_decs_pb
End

Theorem http_prog_pb_eq =
  REWRITE_CONV [http_prog_pb_def, http_decs_pb_def, main_call_def,
                listTheory.SNOC_APPEND, listTheory.APPEND] “http_prog_pb”;

val Decls_th =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> GEN_ALL |> ISPEC “socket_only_ffi s0” |> SPEC_ALL
  |> REWRITE_RULE [GSYM http_decs_pb_def];

val (_, decls_args) = strip_comb (concl Decls_th);
val env2_tm = List.nth (decls_args, 3);
val st2_tm = List.nth (decls_args, 4);

val lookup_main = let
  val g = “nsLookup (^env2_tm).v (Short «main») = SOME asyncProtoProgB$main_v”
  in prove (g, REWRITE_TAC [fst (dest_eq g) |> nsLookup_conv]) end;

val st2_ffi = prove (“(^st2_tm).ffi = socket_only_ffi s0”, EVAL_TAC);

Theorem http_semantics_pb[local]:
  s0.listeners = [(3w, [])] ∧ s0.conns = [] ⇒
  semantics_dec_list (init_state (socket_only_ffi s0)) init_env
    http_prog_pb (Diverge (proto_trace P_b resp_b s0))
Proof
  strip_tac
  \\ assume_tac Decls_th
  \\ drule call_main_thm_div \\ strip_tac
  \\ assume_tac st2_ffi
  \\ drule sonly_init_heap \\ strip_tac
  \\ first_x_assum (qspecl_then [‘sonly_proj2’, ‘sonly_proj1’, ‘h2’, ‘h1’,
       ‘asyncProtoProgB$main_v’, ‘«main»’, ‘λio. io = proto_trace P_b resp_b s0’,
       ‘SOCKETS_EV s0 []’] mp_tac)
  \\ impl_tac
  >- (simp [lookup_var_def, lookup_main]
      \\ irule main_pb_spec \\ simp [limited_parts_sonly])
  \\ rw [http_prog_pb_def] \\ fs[]
QED

Theorem http_prog_pb_syntax_ok:
  prog_syntax_ok http_prog_pb
Proof
  REWRITE_TAC [http_prog_pb_eq, prog_syntax_ok_def] >> EVAL_TAC
QED

(* MAIN: the program's semantics_prog behaviour is the generic server's run *)
Theorem http_semantics_prog_pb:
  s0.listeners = [(3w, [])] ∧ s0.conns = [] ⇒
  semantics_prog (init_state (socket_only_ffi s0)) init_env http_prog_pb
    (Diverge (proto_trace P_b resp_b s0))
Proof
  strip_tac >> drule http_semantics_pb >>
  simp [GSYM (MATCH_MP prog_syntax_ok_semantics http_prog_pb_syntax_ok)]
QED

(* MAIN: the bodies program built on the generic handler meets
   HttpSpecBodies' whole specification *)
Theorem http_prog_pb_spec:
  http_spec_b 3w demo_files http_prog_pb
Proof
  simp[http_spec_b_proto] >> irule proto_spec_of_semantics >>
  simp[proto_ok_b, http_semantics_prog_pb]
QED
