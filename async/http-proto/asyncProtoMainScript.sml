(*
  asyncProtoMain: the generic program-level results (design/32 §2.4,
  phase 4).

  - proto_main_spec: the CakeML proto_main runs M4's dynamic-interest loop
    on the generic server; it never terminates, and its I/O trace is the
    server's run (proto_trace).  asyncHttpSemanticsB's main_spec, with the
    protocol as arguments.
  - proto_spec_of_semantics: a program whose semantics, in every start
    world, is that trace meets proto_spec (safety from proto_comp_safe,
    liveness from proto_live_rounds).

  What stays per instance is the program's Decls theorem, the lookup of
  main and prog_syntax_ok, computed by evaluation (§2.4).
*)
Theory asyncProtoMain
Ancestors
  asyncCore asyncLevel1 asyncCfActModel asyncCfActProg asyncM3World
  asyncM3Prog asyncM3Loop asyncM4GRounds asyncM4Loop asyncM4SockModel
  asyncM4SockApprox asyncM4SockServer asyncServerWith asyncServerWithUses
  asyncRunOkGen asyncHttpSockProg asyncHttpSockSpec
  ffiSpikeSocketFFI ffiSpikeSocketProof ffiSpikeSocketDiv ffiSpikeDivMain
  EchoSpec HttpSpec asyncProto asyncProtoServer asyncProtoSafe asyncProtoSockModel
  asyncProtoLive asyncProtoProg asyncProtoSockSpec
  asyncHeadline cfDiv ml_translator ml_prog std_prelude llist
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncProtoProg"

(* The generic server's run against the socket world s0: round i polls
   listener 3w and every connection accepted so far *)
Overload proto_trace =
  “λP resp s0. LFLATTEN (LGENLIST
     (λi. fromList (grounds_events (interest [3w])
                      (srelabel (proto_server P resp 3)) s0 i))
     NONE)”

(* MAIN (helper): proto_main runs the event loop on the generic server: it
   never terminates, and its I/O trace is the server's run *)
Theorem proto_main_spec:
  proto_ok P ∧ PROTO_IMPL R P resp parsev respv ∧
  limited_parts socket_names p ∧
  s0.listeners = [(3w, [])] ∧ s0.conns = [] ∧ UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) asyncProtoProg$proto_main_v [parsev; respv; uv] (SOCKETS_EV s0 [])
    (POSTd io. io = proto_trace P resp s0)
Proof
  rpt strip_tac >> xcf_with_def asyncProtoProgTheory.proto_main_v_def >>
  xlet ‘POSTv cv. &COMP p SACT UNIT_TYPE SSNAP
                     (srelabel (proto_server P resp 3)) cv * SOCKETS_EV s0 []’
  >- (xapp_spec sproto_server_spec >> xsimpl >> metis_tac[]) >>
  rpt (xlet_auto >- (xcon >> xsimpl)) >>
  gvs[] >>
  ‘app p run_i_v [Conv NONE [Conv (SOME (TypeStamp «::» 1))
                     [Litv (IntLit 3); Conv (SOME (TypeStamp «[]» 1)) []]; cv]]
     (SOCKETS_EV s0 []) (POSTd io. io = proto_trace P resp s0)’
    by (irule run_i_spec >> simp[wf_sproto_server, LIST_TYPE_def] >>
        conj_tac
        >- (irule gen_grun_ok >> simp[] >> qexists_tac ‘3’ >>
            simp[uses_ok_def, proto_server_uses_accepted]) >>
        metis_tac[]) >>
  qpat_x_assum ‘app _ run_i_v _ _ _’ xapp_spec
QED

(* MAIN: a program whose semantics, in every start world, is the generic
   server's run meets the protocol's whole specification *)
Theorem proto_spec_of_semantics:
  proto_ok P ∧
  (∀s0. s0.listeners = [(3w, [])] ∧ s0.conns = [] ⇒
        semantics_prog (init_state (socket_only_ffi s0)) init_env prog
          (Diverge (proto_trace P resp s0))) ⇒
  proto_spec P resp 3w prog
Proof
  rw[proto_spec_def, server_world_def, GSYM socket_only_ffi_eq] >>
  qexists_tac ‘proto_trace P resp sk’ >> simp[] >> conj_tac
  >- (irule proto_comp_safe >> simp[]) >>
  mp_tac (Q.INST [‘s0’ |-> ‘sk’, ‘lfdn’ |-> ‘3’] proto_live_rounds) >>
  simp[]
QED
