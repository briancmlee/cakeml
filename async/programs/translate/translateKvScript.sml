(*
  The key-value handler, written once as a recursive equation in the
  vocabulary of with_store (translateKvSock) and translated: no
  hand-written CakeML for the handler, no hand-written CF proof.

  gkkv_handler_spec has the statement of the hand-written
  kkv_handler_spec (kvSockSpec) for the generated code; the bridge gkv_eq
  (the generated model is krelabel (kv_handler ...), by uniqueness of
  fixpoints) is model-level glue.
*)
Theory translateKv
Ancestors
  asyncCore asyncLevel1 asyncChoose echoServer libModel libProg libApprox
  loopPollWorld loopPollProg loopPoll relabel relabelDist echoSockModel
  libSockApprox echoSockServer HttpGetSpec HttpHeadersSpec HttpSpec KvSpec
  httpGetParse httpHeadersParse httpParse protoInterface protoProg withStore
  withStoreStep skeletonK kvHandler kvModel kvSockModel kvProg withStoreSpec
  ml_translator mlstring std_prelude kvSockSpec ListProg translateKvSock
  loopRounds loopPollDyn skeletonRunOk socketWorld socketProof socketDiv divMain
  kvSafe kvLive EchoSpec echoSafeHeadline cfDiv ml_prog llist
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib
  cfDivLib translateLib translateGlueLib

val _ = translation_extends "translateKvSock"

val ksock_vocab : vocab =
  {bind = "Async.bind", map = "async_map", both = "async_both",
   bind_guarded = Async_bind_guarded_any, bind_d = Async_bind_spec_d,
   map_d = async_map_spec_d, both_d = async_both_spec_d}

val prims : prim list = [
  {const = “asyncLevel1$return”, name = "Async.return",
   spec = Async_return_spec, guard = NONE, wf = asyncLevel1Theory.wf_return},
  {const = “echoSockModel$sreadable”, name = "sreadable",
   spec = ksreadable_spec, guard = SOME sreadable_NIL, wf = wf_sreadable},
  {const = “translateKvSock$kswrite”, name = "kswrite",
   spec = kswrite_spec, guard = SOME kswrite_NIL, wf = wf_kswrite},
  {const = “translateKvSock$ksread”, name = "ksread",
   spec = ksread_spec, guard = SOME ksread_NIL, wf = wf_ksread},
  {const = “translateKvSock$kquery”, name = "kquery",
   spec = kquery_spec, guard = SOME kquery_NIL, wf = wf_kquery}]

val wfs = [asyncLevel1Theory.wf_return, wf_sreadable, wf_kswrite, wf_ksread,
           wf_kquery, asyncLevel1Theory.wf_bind, asyncLevel1Theory.wf_map,
           asyncLevel1Theory.wf_both]
val guards = [sreadable_NIL, kswrite_NIL, ksread_NIL, kquery_NIL]

(* The handler, written once: ask the store about each complete request and
   write its answer, else read *)
val gkv = define_async "gkv" 0
  ‘gkv fd buf =
     case parse_brequest buf of
       BComplete req rest =>
         bind (kquery (fd, req)) (λa.
           case a of
             SOME ans => bind (kswrite fd (sprint_response ans)) (λw. gkv fd rest)
           | NONE => return ())
     | BIncomplete =>
         bind (sreadable fd) (λu.
         bind (ksread fd) (λro.
           case ro of
             SOME s => if s = [] then return () else gkv fd (buf ++ s)
           | NONE => gkv fd buf))
     | BInvalid => return ()’ guards wfs

val gkv_g = translate_async {
  name = "gkv_g", unfold = #unfold gkv, prims = prims,
  wfs = #wf gkv :: wfs, act = “KSACT”, snap = “KSSNAP”, guard = NONE,
  vocab = ksock_vocab, pre = [“fd < dimword(:64)”], defs = []}

(* ------------------------------------------------------------------------
   Glue: the generated model is the hand-written one
   ------------------------------------------------------------------------ *)

Theorem gkv_eq:
  ∀fd buf. gkv fd buf = krelabel (kv_handler (fd, buf))
Proof
  ‘fix gkv_body = (λq. krelabel (kv_handler q))’
    suffices_by rw[#def gkv] >>
  CONV_TAC SYM_CONV >> irule fix_unique >> simp[#contractive gkv] >>
  CONV_TAC FUN_EQ_CONV >> qx_gen_tac ‘q’ >> PairCases_on ‘q’ >>
  simp_tac std_ss [#body_def gkv] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [kkv_handler_unfold])) >>
  Cases_on ‘parse_brequest q1’ >>
  simp[kswrite_def, ksread_def, kquery_def, bind_map, sprint_response_thm] >>
  AP_TERM_TAC >> ABS_TAC >> TRY (AP_TERM_TAC >> ABS_TAC) >>
  every_case_tac >> gvs[]
QED

(* MAIN: the generated handler implements the KV handler in the vocabulary
   of with_store: kkv_handler_spec's statement *)
Theorem gkkv_handler_spec:
  NUM fd fdv ∧ fd < dimword(:64) ∧ LIST_TYPE CHAR buf bufv ⇒
  app (p:'ffi ffi_proj) gkv_g_v [fdv; bufv] emp
    (POSTv v. &COMP p KSACT UNIT_TYPE KSSNAP (krelabel (kv_handler (fd, buf))) v)
Proof
  rw[GSYM gkv_eq] >> irule (#spec gkv_g) >> simp[]
QED

(* ------------------------------------------------------------------------
   Glue, generated (translateGlueLib): the skeleton, with_store, main, and
   the whole program
   ------------------------------------------------------------------------ *)

(* the server: the tagged skeleton on the generated handler *)
val gkv_inner_spec = translate_server {
  name = "gkv_inner", params = [], skel = "sserver_with_k", handler = "gkv_g",
  goal = ‘NUM lfd lfdv ∧ lfd < dimword(:64) ⇒
          app (p:'ffi ffi_proj) gkv_inner_v [lfdv] emp
            (POSTv v. &COMP p KSACT UNIT_TYPE KSSNAP (krelabel (kv_inner lfd)) v)’,
  model_defs = [kv_inner_def], skel_spec = kserver_with_k_spec,
  hyp_defs = [KHANDLER_def], handler_spec = gkkv_handler_spec,
  wfs = [wf_kv_handler]}

(* with_store around it, with the association-list store *)
val gkv_server_spec = translate_store {
  name = "gkv_server", inner = "gkv_inner", delta = "kv_delta_al", store0 = "[]",
  goal = ‘NUM lfd lfdv ∧ lfd < dimword(:64) ⇒
          app (p:'ffi ffi_proj) gkv_server_v [lfdv] emp
            (POSTv v. &COMP p SACT UNIT_TYPE SSNAP (srelabel (kv_server lfd)) v)’,
  model_defs = [srelabel_kv_server],
  inner_post = ‘POSTv cv. &COMP p KSACT UNIT_TYPE KSSNAP (krelabel (kv_inner lfd)) cv’,
  store0_post = ‘POSTv sv. &KVAL [] sv’,
  inner_spec = gkv_inner_spec, with_store_spec = with_store_spec,
  wf_inner = wf_kkv_inner, witnesses = [‘KANS’, ‘KQRY’, ‘STORE_AL’],
  simps = [kv_delta_al_DELTA, STORE_AL_def, al_store_def]}

(* The generated program's run: kvSemantics's kv_trace, for this program *)
Overload gkv_trace =
  “λs0. LFLATTEN (LGENLIST
          (λi. fromList (grounds_events (interest [3w])
                           (srelabel (kv_server 3)) s0 i))
          NONE)”

val gkv_main_spec = translate_main {
  name = "main", server_call = "gkv_server 3",
  goal = ‘limited_parts socket_names p ∧
          s0.listeners = [(3w, [])] ∧ s0.conns = [] ∧ UNIT_TYPE () uv ⇒
          app (p:'ffi ffi_proj) translateKv$main_v [uv] (SOCKETS_EV s0 [])
            (POSTd io. io = gkv_trace s0)’,
  server_post = ‘POSTv cv. &COMP p SACT UNIT_TYPE SSNAP (srelabel (kv_server 3)) cv *
                           SOCKETS_EV s0 []’,
  server_tac = (xapp_spec gkv_server_spec >> xsimpl),
  run_ok_tac = (simp [wf_skv_server, LIST_TYPE_def] >> conj_tac
                >- (irule gen_grun_ok >> simp [] >> qexists_tac ‘3’ >>
                    simp [kv_server_uses_ok]) >>
                metis_tac [])}

val gkv = translate_program {
  prefix = "gkv", main_v = lhs (concl (fetch "-" "main_v_def")),
  main_spec = gkv_main_spec,
  trace = “λs0. gkv_trace s0”,
  hyps = “λs0:sockets. s0.listeners = [(3w, [])] ∧ s0.conns = []”}

(* MAIN: the key-value program whose handler, server and main were
   generated meets the trusted KV specification *)
Theorem gkv_prog_spec:
  kv_spec 3w gkv_prog
Proof
  rw[kv_spec_def, server_world_def, socket_ffi_socket_only_ffi] >>
  qexists_tac ‘gkv_trace sk’ >>
  simp[Q.INST [‘s0’ |-> ‘sk’] (#semantics_prog gkv)] >>
  conj_tac >- (irule kv_comp_safe >> simp[]) >>
  mp_tac (Q.INST [‘s0’ |-> ‘sk’, ‘lfdn’ |-> ‘3’] kv_live_rounds) >> simp[]
QED
