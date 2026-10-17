(*
  asyncProtoSockSpec: CF specs of the generic CakeML handler and server
  (asyncProtoProg), proved once for every protocol: they implement
  srelabel (proto_handler P resp ...) and srelabel (proto_server P resp lfd),
  given CakeML values parsev and respv that implement P.parse and resp
  (the translator's certificates, (LIST_TYPE CHAR --> ASYNCPROTO_PRESULT_TYPE R)
  and (R --> LIST_TYPE CHAR)).  asyncHttpSockSpecB, with the protocol as
  arguments; the skeleton's spec (sserver_with_spec) is reused.
  design/32 §2.4, phase 4.
*)
Theory asyncProtoSockSpec
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncServer asyncCfActModel
  asyncCfActProg asyncM4Approx asyncM3World asyncM3Prog asyncM3Loop
  asyncM4Relabel asyncM4RelabelDist asyncM4SockModel asyncM4SockApprox
  asyncM4SockServer asyncServerWith HttpSpec asyncHttpParse
  asyncHttpImplProg asyncHttpSockModel asyncHttpSockProg asyncHttpSockSpec
  asyncProto asyncProtoServer asyncProtoSockModel asyncProtoProg
  ml_translator mlstring std_prelude
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncProtoProg"

val eq_string_v_thm =
  MATCH_MP (DISCH_ALL (fetch "mlbasicsProg" "eq_v_thm"))
           (EqualityType_NUM_BOOL |> CONJUNCTS |> el 6);

(* Strings as bytes and back *)
Theorem bytes_str_chars[local]:
  bytes_str (MAP (n2w o ORD) s : word8 list) = implode s
Proof
  AP_TERM_TAC >> Induct_on ‘s’ >> simp[] >> rpt strip_tac >>
  ‘ORD h < 256’ by simp[ORD_BOUND] >> simp[CHR_ORD]
QED

Theorem NUM_w2n_n2w[local]:
  fd < dimword(:64) ⇒ (NUM (w2n (n2w fd : word64)) v ⇔ NUM fd v)
Proof
  simp[]
QED

(* return (), at any depth *)
val return_unit_tac =
  xlet ‘POSTv uv. &UNIT_TYPE () uv’ >- (xcon >> xsimpl) >>
  ‘app p Async_return_v [uv] emp
     (POSTv v. &COMP p SACT UNIT_TYPE SSNAP (return ()) v)’
    by (irule Async_return_spec >> simp[]) >>
  qpat_x_assum ‘app _ Async_return_v _ _ _’ xapp_spec >> xsimpl >>
  simp[COMP_IMP_COMPd];

(* emit a, for a CakeML action value av *)
fun emit_tac a =
  ‘app p Async_emit_v [av] emp
     (POSTv v. &COMP p SACT SRESP SSNAP (emit ^a) v)’
    by (irule Async_emit_spec >> simp[]) >>
  qpat_x_assum ‘app _ Async_emit_v _ _ _’ xapp_spec >> xsimpl;

(* ------------------------------------------------------------------------
   The handler
   ------------------------------------------------------------------------ *)

(* A guarded bind, at any depth n *)
Theorem Async_bind_guarded_spec_any[local]:
  wf m ∧ (m []).result = NONE ∧ COMP p ACT A (SNAPSHOT READY R) m mv ∧
  (0 < n ⇒
   ∀x xv. A x xv ⇒
     returns p gv [xv]
       (COMPd p ACT B (SNAPSHOT READY (R : 'r -> v -> bool)) (n - 1) (g x))) ⇒
  app (p:'ffi ffi_proj) Async_bind_v [mv; gv] emp
    (POSTv v. &COMPd p (ACT : 'act -> v -> bool) B (SNAPSHOT READY R) n
                (bind m g) v)
Proof
  Cases_on ‘n’ >> rpt strip_tac
  >- (irule Async_bind_guarded_spec_0 >> simp[] >> metis_tac[COMP_IMP_COMPd])
  >> irule Async_bind_guarded_spec_d >> gs[] >> qexists_tac ‘A’ >>
  simp[COMP_IMP_COMPd]
QED

(* The protocol's parser and responder, as CakeML values *)
Definition PROTO_IMPL_def:
  PROTO_IMPL R P resp parsev respv ⇔
    (LIST_TYPE CHAR --> ASYNCPROTO_PRESULT_TYPE R) P.parse parsev ∧
    (R --> LIST_TYPE CHAR) resp respv
End

(* MAIN (helper): the CakeML handler implements the socket-vocabulary
   handler up to any depth n, for every buffer *)
Theorem sproto_handler_spec_d:
  ∀n buf bufv fd fdv.
    PROTO_IMPL R P resp parsev respv ∧
    NUM fd fdv ∧ fd < dimword(:64) ∧ LIST_TYPE CHAR buf bufv ⇒
    app (p:'ffi ffi_proj) asyncProtoProg$proto_handler_v [parsev; respv; fdv; bufv] emp
      (POSTv v. &COMPd p SACT UNIT_TYPE SSNAP n
                  (srelabel (proto_handler P resp (fd, buf))) v)
Proof
  completeInduct_on ‘n’ >> rpt strip_tac >>
  gvs[PROTO_IMPL_def] >>
  xcf_with_def asyncProtoProgTheory.proto_handler_v_def >>
  xlet ‘POSTv rv. &ASYNCPROTO_PRESULT_TYPE R (P.parse buf) rv’
  >- (qpat_assum ‘(_ --> _) P.parse _’ xapp_spec >> simp[]) >>
  simp_tac std_ss [Once sproto_handler_unfold] >>
  Cases_on ‘P.parse buf’ >>
  gvs[ASYNCPROTO_PRESULT_TYPE_def]
  >- ((* a complete request: write the response, then the handler on rest *)
      xmatch >>
      qmatch_goalsub_rename_tac ‘resp req’ >>
      qmatch_goalsub_rename_tac ‘proto_handler P resp (fd, rest)’ >>
      xfun ‘k1’ >>
      xlet ‘POSTv sv. &LIST_TYPE CHAR (resp req) sv’
      >- (qpat_assum ‘(_ --> _) resp _’ xapp_spec >> simp[] >> metis_tac[]) >>
      xlet ‘POSTv tv. &STRING_TYPE (implode (resp req)) tv’
      >- (xapp >> simp[PROTO_IMPL_def]) >>
      qabbrev_tac ‘bs = MAP ((n2w : num -> word8) o ORD) (resp req)’ >>
      xlet ‘POSTv av. &SACT (Write (n2w fd) bs) av’
      >- (xcon >> xsimpl >> gs[SACT_def, Abbr ‘bs’, bytes_str_chars]) >>
      xlet ‘POSTv ev. &COMP p SACT SRESP SSNAP (emit (Write (n2w fd) bs)) ev’
      >- emit_tac “Write (n2w fd) bs” >>
      ‘app p Async_bind_v [ev; k1] emp
         (POSTv v. &COMPd p SACT UNIT_TYPE SSNAP n
                     (bind (emit (Write (n2w fd) bs))
                           (λw. srelabel (proto_handler P resp (fd, rest)))) v)’
        by (irule Async_bind_guarded_spec_any >>
            simp[wf_emit, emit_needs_snapshot] >>
            qexists_tac ‘SRESP’ >> rpt strip_tac >> simp[returns_def] >>
            qpat_x_assum ‘curried _ _ k1 ∧ _’ (irule o CONJUNCT2) >>
            first_x_assum (qspec_then ‘n - 1’ mp_tac) >> simp[] >>
            strip_tac >> xapp >> simp[PROTO_IMPL_def]) >>
      qpat_x_assum ‘app _ Async_bind_v _ _ _’ xapp_spec >> xsimpl >>
      simp[Abbr ‘bs’])
  >- ((* Incomplete: wait for fd to be readable, read, and continue *)
      xmatch >> xfun ‘k1’ >>
      xlet ‘POSTv r. &COMP p SACT UNIT_TYPE SSNAP (sreadable fd) r’
      >- (xapp_spec sreadable_spec >> simp[]) >>
      qmatch_goalsub_abbrev_tac ‘bind (sreadable fd) G’ >>
      ‘0 < n ⇒ ∀x xv. UNIT_TYPE x xv ⇒
         returns p k1 [xv] (COMPd p SACT UNIT_TYPE SSNAP (n - 1) (G x))’
        by (rpt strip_tac >> simp[returns_def, Abbr ‘G’] >>
            first_x_assum (qspec_then ‘n - 1’ mp_tac) >> simp[] >> strip_tac >>
            qpat_x_assum ‘curried _ _ k1 ∧ _’ (irule o CONJUNCT2) >>
            xfun ‘k2’ >>
            xlet ‘POSTv av. &SACT (Read (n2w fd) bufsz) av’
            >- (xcon >> xsimpl >> gs[SACT_def, bufsz_def, NUM_def, INT_def]) >>
            xlet ‘POSTv ev. &COMP p SACT SRESP SSNAP (emit (Read (n2w fd) bufsz)) ev’
            >- emit_tac “Read (n2w fd) bufsz” >>
            qmatch_goalsub_abbrev_tac ‘bind (emit _) G2’ >>
            ‘∀res resv. SRESP res resv ⇒
               returns p k2 [resv]
                 (COMPd p SACT UNIT_TYPE SSNAP (n - 1) (G2 res))’
              by (rpt strip_tac >> simp[returns_def, Abbr ‘G2’] >>
                  qpat_x_assum ‘curried _ _ k2 ∧ _’ (irule o CONJUNCT2) >>
                  Cases_on ‘res’ >> gvs[SRESP_def]
                  >~ [‘TypeStamp «Got» _’]
                  >- (rename1 ‘OPTION_MAP _ ro’ >> Cases_on ‘ro’ >>
                      gvs[OPTION_TYPE_def] >> xmatch
                      >- (xapp >> simp[PROTO_IMPL_def])
                      >> rename1 ‘STRING_TYPE (bytes_str bs) sv’ >>
                      xlet ‘POSTv bv. &BOOL (bs = []) bv’
                      >- (xapp_spec eq_string_v_thm >> xsimpl >>
                          qexists_tac ‘bytes_str bs’ >> simp[] >>
                          Cases_on ‘bs’ >> simp[]) >>
                      xif
                      >- (gvs[] >> return_unit_tac) >>
                      (* data bs: the handler on buf ++ chars of bs *)
                      gs[] >>
                      xlet ‘POSTv cv. &LIST_TYPE CHAR (MAP (CHR o w2n) bs) cv’
                      >- (xapp >> xsimpl >> qexists_tac ‘bytes_str bs’ >>
                          gs[mlstringTheory.explode_implode]) >>
                      xlet ‘POSTv bv2. &LIST_TYPE CHAR (buf ++ MAP (CHR o w2n) bs) bv2’
                      >- (xapp >> simp[PROTO_IMPL_def] >> metis_tac[]) >>
                      xapp >> simp[PROTO_IMPL_def]) >>
                  (* any other response: the handler on buf again *)
                  xmatch >> xapp >> simp[PROTO_IMPL_def]) >>
            ‘app p Async_bind_v [ev; k2] emp
               (POSTv v. &COMPd p SACT UNIT_TYPE SSNAP (n - 1)
                           (bind (emit (Read (n2w fd) bufsz)) G2) v)’
              by (irule Async_bind_spec_d >> simp[wf_emit] >>
                  qexists_tac ‘SRESP’ >> simp[COMP_IMP_COMPd] >> metis_tac[]) >>
            qpat_x_assum ‘app _ Async_bind_v _ _ _’ xapp_spec >> xsimpl) >>
      ‘app p Async_bind_v [r; k1] emp
         (POSTv v. &COMPd p SACT UNIT_TYPE SSNAP n (bind (sreadable fd) G) v)’
        by (irule Async_bind_guarded_spec_any >> simp[wf_sreadable, sreadable_NIL] >>
            metis_tac[]) >>
      qpat_x_assum ‘app _ Async_bind_v _ _ _’ xapp_spec >> xsimpl) >>
  (* Invalid: stop *)
  xmatch >> return_unit_tac
QED

(* MAIN: the CakeML handler implements the model's handler, in the socket
   vocabulary, for every protocol *)
Theorem sproto_handler_spec:
  PROTO_IMPL R P resp parsev respv ∧
  NUM fd fdv ∧ fd < dimword(:64) ∧ LIST_TYPE CHAR buf bufv ⇒
  app (p:'ffi ffi_proj) asyncProtoProg$proto_handler_v [parsev; respv; fdv; bufv] emp
    (POSTv v. &COMP p SACT UNIT_TYPE SSNAP (srelabel (proto_handler P resp (fd, buf))) v)
Proof
  strip_tac >> irule app_COMP_of_approxd >> simp[] >> gen_tac >>
  metis_tac[sproto_handler_spec_d]
QED

(* MAIN: the CakeML server implements the model's proto_server, in the
   socket vocabulary: the instance of sserver_with_spec for the handler *)
Theorem sproto_server_spec:
  PROTO_IMPL R P resp parsev respv ∧ NUM lfd lfdv ∧ lfd < dimword(:64) ⇒
  app (p:'ffi ffi_proj) asyncProtoProg$proto_server_v [parsev; respv; lfdv] emp
    (POSTv v. &COMP p SACT UNIT_TYPE SSNAP (srelabel (proto_server P resp lfd)) v)
Proof
  rpt strip_tac >> xcf_with_def asyncProtoProgTheory.proto_server_v_def >> xfun ‘h’ >>
  simp[proto_server_def] >> xapp_spec sserver_with_spec >>
  simp[SHANDLER_def, wf_proto_handler] >> rpt strip_tac >>
  qpat_x_assum ‘curried _ _ h ∧ _’ (irule o CONJUNCT2) >>
  xlet ‘POSTv bv. &LIST_TYPE CHAR "" bv’
  >- (xcon >> xsimpl >> simp[LIST_TYPE_def]) >>
  xapp_spec sproto_handler_spec >> simp[] >> metis_tac[]
QED
