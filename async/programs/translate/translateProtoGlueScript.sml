(*
  Hand-written glue for the generated proto handler (translateProto):
  the generated model is the chain's (gproto_eq, by uniqueness of
  fixpoints), so the generated code meets sproto_handler_spec's statement
  (gproto_handler_spec); the server and main plug it into the chain's
  sserver_with and run_i, as protoProg's do.
*)
Theory translateProtoGlue
Ancestors
  asyncCore asyncLevel1 libModel libProg loopPollWorld loopPollProg loopPoll
  loopRounds loopPollDyn echoSockModel libSockApprox echoSockServer skeleton
  skeletonUses skeletonRunOk socketWorld socketProof socketDiv divMain
  EchoSpec HttpGetSpec protoInterface protoServer protoSafe protoSockModel
  protoLive protoProg protoSockSpec echoSafeHeadline cfDiv ml_translator
  ml_prog std_prelude llist httpProg ListProg mlstring translateSock
  translateProto
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib
  cfDivLib translateLib translateGlueLib

val _ = translation_extends "translateProto"

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
   The server, generated (translateGlueLib): the skeleton sserver_with on
   the generated handler, for every protocol (parser and responder as
   functional parameters)
   ------------------------------------------------------------------------ *)

val gproto_server_spec = translate_server {
  name = "gproto_server", params = ["prs", "resp"], skel = "sserver_with",
  handler = "gproto_g",
  goal = ‘PROTO_IMPL R P resp parsev respv ∧ NUM lfd lfdv ∧ lfd < dimword(:64) ⇒
          app (p:'ffi ffi_proj) gproto_server_v [parsev; respv; lfdv] emp
            (POSTv v. &COMP p SACT UNIT_TYPE SSNAP
                        (srelabel (proto_server P resp lfd)) v)’,
  model_defs = [proto_server_def], skel_spec = sserver_with_spec,
  hyp_defs = [SHANDLER_def], handler_spec = gproto_handler_spec,
  wfs = [wf_proto_handler]}
