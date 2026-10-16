(*
  The key-value handler, written once as a recursive equation in the
  vocabulary of with_store (asyncTranslateKvSock) and translated: no
  hand-written CakeML for the handler, no hand-written CF proof.

  gkkv_handler_spec has the statement of the hand-written
  kkv_handler_spec (asyncKvSpec) for the generated code; the bridge gkv_eq
  (the generated model is krelabel (kv_handler ...), by uniqueness of
  fixpoints) is model-level glue.
*)
Theory asyncTranslateKv
Ancestors
  asyncCore asyncLevel1 asyncCfActModel asyncCfActProg asyncM4Approx
  asyncM3World asyncM3Prog asyncM3Loop asyncM4Relabel asyncM4SockModel
  asyncM4SockApprox asyncM4SockServer HttpSpec HttpSpecBodies
  asyncHttpParseB asyncWithStore asyncKvHandler asyncKvSockModel
  asyncKvProg asyncWithStoreSpec asyncKvModel asyncKvSpec
  asyncTranslateKvSock ml_translator
  mlstring std_prelude ListProg
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib
  asyncTranslateLib

val _ = translation_extends "asyncTranslateKvSock"

val ksock_vocab : vocab =
  {bind = "Async.bind", map = "async_map", both = "async_both",
   bind_guarded = Async_bind_guarded_any, bind_d = Async_bind_spec_d,
   map_d = async_map_spec_d, both_d = async_both_spec_d}

val prims : prim list = [
  {const = “asyncLevel1$return”, name = "Async.return",
   spec = Async_return_spec, guard = NONE, wf = asyncLevel1Theory.wf_return},
  {const = “asyncM4SockModel$sreadable”, name = "sreadable",
   spec = ksreadable_spec, guard = SOME sreadable_NIL, wf = wf_sreadable},
  {const = “asyncTranslateKvSock$kswrite”, name = "kswrite",
   spec = kswrite_spec, guard = SOME kswrite_NIL, wf = wf_kswrite},
  {const = “asyncTranslateKvSock$ksread”, name = "ksread",
   spec = ksread_spec, guard = SOME ksread_NIL, wf = wf_ksread},
  {const = “asyncTranslateKvSock$kquery”, name = "kquery",
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
   Glue: the generated handler in the chain's skeleton and with_store
   (asyncKvSpec's kkv_inner_spec / kv_server_spec, for the generated code)
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  fun gkv_inner lfd = sserver_with_k (fn fd => gkv_g fd []) lfd;

  fun gkv_server lfd = with_store kv_delta_al [] (gkv_inner lfd);
End

Theorem gkv_inner_spec:
  NUM lfd lfdv ∧ lfd < dimword(:64) ⇒
  app (p:'ffi ffi_proj) gkv_inner_v [lfdv] emp
    (POSTv v. &COMP p KSACT UNIT_TYPE KSSNAP (krelabel (kv_inner lfd)) v)
Proof
  rpt strip_tac >> xcf_with_def (fetch "-" "gkv_inner_v_def") >> xfun ‘h’ >>
  simp[kv_inner_def] >> xapp_spec kserver_with_k_spec >>
  simp[KHANDLER_def, wf_kv_handler] >> rpt strip_tac >>
  qpat_x_assum ‘curried _ _ h ∧ _’ (irule o CONJUNCT2) >>
  xlet ‘POSTv bv. &LIST_TYPE CHAR "" bv’
  >- (xcon >> xsimpl >> simp[LIST_TYPE_def]) >>
  xapp_spec gkkv_handler_spec >> simp[]
QED

(* MAIN: the key-value server with the generated handler implements the
   model's kv_server, in the socket vocabulary: kv_server_spec's statement *)
Theorem gkv_server_spec:
  NUM lfd lfdv ∧ lfd < dimword(:64) ⇒
  app (p:'ffi ffi_proj) gkv_server_v [lfdv] emp
    (POSTv v. &COMP p SACT UNIT_TYPE SSNAP (srelabel (kv_server lfd)) v)
Proof
  rpt strip_tac >> xcf_with_def (fetch "-" "gkv_server_v_def") >>
  simp[srelabel_kv_server] >>
  xlet ‘POSTv cv. &COMP p KSACT UNIT_TYPE KSSNAP (krelabel (kv_inner lfd)) cv’
  >- (xapp_spec gkv_inner_spec >> simp[]) >>
  xlet ‘POSTv sv. &KVAL [] sv’
  >- (xcon >> xsimpl >> simp[LIST_TYPE_def]) >>
  xapp_spec with_store_spec >> simp[wf_kkv_inner] >>
  qexistsl [‘KANS’, ‘KQRY’, ‘STORE_AL’] >>
  simp[kv_delta_al_DELTA, STORE_AL_def, al_store_def] >>
  qexists_tac ‘[]’ >> simp[]
QED
