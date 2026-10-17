(*
  Hand-written glue for the generated proto handler (asyncTranslateProto):
  the generated model is the chain's (gproto_eq, by uniqueness of
  fixpoints), so the generated code meets sproto_handler_spec's statement
  (gproto_handler_spec); the server and main plug it into the chain's
  sserver_with and run_i, as asyncProtoProg's do.
*)
Theory asyncTranslateProtoGlue
Ancestors
  asyncCore asyncLevel1 asyncCfActModel asyncCfActProg asyncM4Approx
  asyncM3World asyncM3Prog asyncM3Loop asyncM4Relabel asyncM4SockModel
  asyncM4SockApprox asyncM4SockServer asyncServerWith asyncHttpSockSpec
  asyncProto asyncProtoServer asyncProtoSockModel asyncProtoProg
  asyncProtoSockSpec asyncTranslateSock asyncTranslateProto ml_translator mlstring std_prelude
  ListProg asyncM4GRounds asyncM4Loop asyncServerWithUses asyncRunOkGen
  asyncHttpSockProg ffiSpikeSocketFFI ffiSpikeSocketProof ffiSpikeSocketDiv
  ffiSpikeDivMain EchoSpec HttpSpec asyncProtoSafe asyncProtoLive
  asyncProtoMain asyncHeadline cfDiv ml_prog llist
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib
  cfDivLib asyncTranslateLib

val _ = translation_extends "asyncTranslateProto"

(* ------------------------------------------------------------------------
   Glue: the generated model is the hand-written one
   ------------------------------------------------------------------------ *)

Theorem gproto_eq:
  ∀fd buf. gproto P.parse resp fd buf = srelabel (proto_handler P resp (fd, buf))
Proof
  ‘fix (gproto_body P.parse resp) = (λq. srelabel (proto_handler P resp q))’
    suffices_by rw[gproto_def] >>
  CONV_TAC SYM_CONV >> irule fix_unique >> simp[gproto_body_contractive] >>
  CONV_TAC FUN_EQ_CONV >> qx_gen_tac ‘q’ >> PairCases_on ‘q’ >>
  simp_tac std_ss [gproto_body_def] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [sproto_handler_unfold])) >>
  Cases_on ‘P.parse q1’ >> simp[swrite_def, sread_def, bind_map] >>
  AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> ABS_TAC >>
  Cases_on ‘r’ >> simp[] >> every_case_tac >> gvs[]
QED

(* MAIN: the generated handler implements the model's proto handler, in the
   socket vocabulary, for every protocol: sproto_handler_spec's statement *)
Theorem gproto_handler_spec:
  PROTO_IMPL R P resp parsev respv ∧
  NUM fd fdv ∧ fd < dimword(:64) ∧ LIST_TYPE CHAR buf bufv ⇒
  app (p:'ffi ffi_proj) gproto_g_v [parsev; respv; fdv; bufv] emp
    (POSTv v. &COMP p SACT UNIT_TYPE SSNAP (srelabel (proto_handler P resp (fd, buf))) v)
Proof
  rw[PROTO_IMPL_def, GSYM gproto_eq] >> irule gproto_g_spec >> simp[] >>
  qexists_tac ‘R’ >> simp[]
QED

(* ------------------------------------------------------------------------
   Glue: the server and main, plugging the generated handler into the
   chain's sserver_with and run_i (Tcp.serve-style library primitives)
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  fun gproto_server prs resp lfd =
    sserver_with (fn fd => gproto_g prs resp fd []) lfd;

  fun gproto_main prs resp u = run_i ([3], gproto_server prs resp 3);
End

Theorem gproto_server_spec:
  PROTO_IMPL R P resp parsev respv ∧ NUM lfd lfdv ∧ lfd < dimword(:64) ⇒
  app (p:'ffi ffi_proj) gproto_server_v [parsev; respv; lfdv] emp
    (POSTv v. &COMP p SACT UNIT_TYPE SSNAP (srelabel (proto_server P resp lfd)) v)
Proof
  rpt strip_tac >> xcf_with_def (fetch "-" "gproto_server_v_def") >> xfun ‘h’ >>
  simp[proto_server_def] >> xapp_spec sserver_with_spec >>
  simp[SHANDLER_def, wf_proto_handler] >> rpt strip_tac >>
  qpat_x_assum ‘curried _ _ h ∧ _’ (irule o CONJUNCT2) >>
  xlet ‘POSTv bv. &LIST_TYPE CHAR "" bv’
  >- (xcon >> xsimpl >> simp[LIST_TYPE_def]) >>
  xapp_spec gproto_handler_spec >> simp[] >> metis_tac[]
QED

Theorem gproto_main_spec:
  proto_ok P ∧ PROTO_IMPL R P resp parsev respv ∧
  limited_parts socket_names p ∧
  s0.listeners = [(3w, [])] ∧ s0.conns = [] ∧ UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) gproto_main_v [parsev; respv; uv] (SOCKETS_EV s0 [])
    (POSTd io. io = proto_trace P resp s0)
Proof
  rpt strip_tac >> xcf_with_def (fetch "-" "gproto_main_v_def") >>
  xlet ‘POSTv cv. &COMP p SACT UNIT_TYPE SSNAP
                     (srelabel (proto_server P resp 3)) cv * SOCKETS_EV s0 []’
  >- (xapp_spec gproto_server_spec >> xsimpl >> metis_tac[]) >>
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
