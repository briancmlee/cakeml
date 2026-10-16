(*
  The socket library in the vocabulary of with_store (Sock a | Kv q), as
  the async translator sees it: kswrite / ksread as swrite / sread
  (translateSock) under Sock, and kquery q, which asks the store and
  returns its answer.  Written once: model, CakeML, COMP spec, guard, wf.
  On the KV chain (withStoreSpec, the KV worker's split of the
  generic with_store specs).
*)
Theory translateKvSock
Ancestors
  asyncCore asyncLevel1 asyncChoose echoServer libModel libProg libApprox
  loopPollWorld loopPollProg loopPoll relabel relabelDist echoSockModel
  libSockApprox echoSockServer HttpGetSpec HttpHeadersSpec HttpSpec KvSpec
  httpGetParse httpHeadersParse httpParse protoInterface protoProg withStore
  withStoreStep skeletonK kvHandler kvModel kvSockModel kvProg ml_translator
  mlstring std_prelude withStoreSpec
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "withStoreSpec"

(* ------------------------------------------------------------------------
   The models
   ------------------------------------------------------------------------ *)

Definition kswrite_def:
  kswrite fd s =
    map (λr. ())
      (emit (Sock (loopPollWorld$Write (n2w fd) (MAP (n2w o ORD) s))))
End

Definition ksread_def:
  ksread fd =
    map (λr. case r of SockR (Got (SOME bs)) => SOME (MAP (CHR o w2n) bs)
                     | _ => NONE)
        (emit (Sock (loopPollWorld$Read (n2w fd) bufsz)))
End

Definition kquery_def:
  kquery q = map (λa. case a of KvR b => SOME b | _ => NONE) (emit (Kv q))
End

Theorem kswrite_NIL:
  (kswrite fd s []).result = NONE
Proof
  simp[kswrite_def, asyncLevel1Theory.map_def, emit_needs_snapshot]
QED

Theorem ksread_NIL:
  (ksread fd []).result = NONE
Proof
  simp[ksread_def, asyncLevel1Theory.map_def, emit_needs_snapshot]
QED

Theorem kquery_NIL:
  (kquery q []).result = NONE
Proof
  simp[kquery_def, asyncLevel1Theory.map_def, emit_needs_snapshot]
QED

Theorem wf_kswrite:
  wf (kswrite fd s)
Proof
  simp[kswrite_def, asyncLevel1Theory.wf_map, asyncLevel1Theory.wf_emit]
QED

Theorem wf_ksread:
  wf (ksread fd)
Proof
  simp[ksread_def, asyncLevel1Theory.wf_map, asyncLevel1Theory.wf_emit]
QED

Theorem wf_kquery:
  wf (kquery q)
Proof
  simp[kquery_def, asyncLevel1Theory.wf_map, asyncLevel1Theory.wf_emit]
QED

(* ------------------------------------------------------------------------
   The code
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  fun kswrite fd s =
    async_map (fn r => ()) (Async.emit (Sock (Write fd (String.implode s))));

  fun ksread fd =
    async_map (fn r => case r of
                         Sockr g =>
                           (case g of
                              Got ro =>
                                (case ro of Some s => Some (String.explode s)
                                          | None => None)
                            | _ => None)
                       | _ => None)
              (Async.emit (Sock (Read fd 4096)));

  fun kquery q =
    async_map (fn a => case a of Kvr b => Some b | _ => None) (Async.emit (Kv q));
End

(* ------------------------------------------------------------------------
   The specs
   ------------------------------------------------------------------------ *)

Theorem bytes_str_chars[local]:
  bytes_str (MAP (n2w o ORD) s : word8 list) = implode s
Proof
  AP_TERM_TAC >> Induct_on ‘s’ >> simp[] >> rpt strip_tac >>
  ‘ORD h < 256’ by simp[ORD_BOUND] >> simp[CHR_ORD]
QED

Theorem kswrite_spec:
  NUM fd fdv ∧ fd < dimword(:64) ∧ LIST_TYPE CHAR s sv ⇒
  app (p:'ffi ffi_proj) kswrite_v [fdv; sv] emp
    (POSTv v. &COMP p KSACT UNIT_TYPE KSSNAP (kswrite fd s) v)
Proof
  strip_tac >> irule app_COMP_of_approxd >> simp[] >> gen_tac >>
  xcf_with_def (fetch "-" "kswrite_v_def") >>
  xlet ‘POSTv tv. &STRING_TYPE (implode s) tv’ >- (xapp >> metis_tac[]) >>
  xlet ‘POSTv av. &SACT (Write (n2w fd) (MAP (n2w o ORD) s)) av’
  >- (xcon >> xsimpl >> gs[SACT_def, bytes_str_chars]) >>
  xlet ‘POSTv kv. &KSACT (Sock (Write (n2w fd) (MAP (n2w o ORD) s))) kv’
  >- (xcon >> xsimpl >> simp[KACT_def]) >>
  xlet ‘POSTv ev. &COMP p KSACT KSRESP KSSNAP
                     (emit (Sock (Write (n2w fd) (MAP (n2w o ORD) s)))) ev’
  >- (xapp_spec Async_emit_spec >> simp[]) >> xfun ‘f’ >>
  ‘app p async_map_v [f; ev] emp
     (POSTv v. &COMPd p KSACT UNIT_TYPE KSSNAP n (kswrite fd s) v)’
    by (simp[kswrite_def] >> irule async_map_spec_d >>
        simp[asyncLevel1Theory.wf_emit] >>
        qexists_tac ‘KSRESP’ >> simp[COMP_IMP_COMPd] >> rpt strip_tac >>
        simp[returns_def] >>
        qpat_x_assum ‘curried _ _ f ∧ _’ (irule o CONJUNCT2) >>
        xcon >> xsimpl) >>
  qpat_x_assum ‘app _ async_map_v _ _ _’ xapp_spec >> xsimpl
QED

Theorem ksread_spec:
  NUM fd fdv ∧ fd < dimword(:64) ⇒
  app (p:'ffi ffi_proj) ksread_v [fdv] emp
    (POSTv v. &COMP p KSACT (OPTION_TYPE (LIST_TYPE CHAR)) KSSNAP (ksread fd) v)
Proof
  strip_tac >> irule app_COMP_of_approxd >> simp[] >> gen_tac >>
  xcf_with_def (fetch "-" "ksread_v_def") >>
  xlet ‘POSTv av. &SACT (Read (n2w fd) bufsz) av’
  >- (xcon >> xsimpl >> gs[SACT_def, bufsz_def, NUM_def, INT_def]) >>
  xlet ‘POSTv kv. &KSACT (Sock (Read (n2w fd) bufsz)) kv’
  >- (xcon >> xsimpl >> simp[KACT_def]) >>
  xlet ‘POSTv ev. &COMP p KSACT KSRESP KSSNAP (emit (Sock (Read (n2w fd) bufsz))) ev’
  >- (xapp_spec Async_emit_spec >> simp[]) >> xfun ‘f’ >>
  ‘app p async_map_v [f; ev] emp
     (POSTv v. &COMPd p KSACT (OPTION_TYPE (LIST_TYPE CHAR)) KSSNAP n (ksread fd) v)’
    by (simp[ksread_def] >> irule async_map_spec_d >>
        simp[asyncLevel1Theory.wf_emit] >>
        qexists_tac ‘KSRESP’ >> simp[COMP_IMP_COMPd] >> rpt strip_tac >>
        simp[returns_def] >>
        qpat_x_assum ‘curried _ _ f ∧ _’ (irule o CONJUNCT2) >>
        Cases_on ‘x’ >> gvs[KRES_def] >> xmatch
        >- (rename1 ‘SRESP r rv’ >> Cases_on ‘r’ >> gvs[SRESP_def] >> xmatch
            >- (xcon >> xsimpl >> simp[OPTION_TYPE_def])
            >- (rename1 ‘OPTION_MAP _ ro’ >> Cases_on ‘ro’ >>
                gvs[OPTION_TYPE_def] >> xmatch
                >- (xcon >> xsimpl >> simp[OPTION_TYPE_def]) >>
                xlet ‘POSTv cv. &LIST_TYPE CHAR (MAP (CHR o w2n) x) cv’
                >- (xapp >> xsimpl >> first_assum (irule_at Any) >>
                    simp[mlstringTheory.explode_implode]) >>
                xcon >> xsimpl >> simp[OPTION_TYPE_def]) >>
            xcon >> xsimpl >> simp[OPTION_TYPE_def]) >>
        xcon >> xsimpl >> simp[OPTION_TYPE_def]) >>
  qpat_x_assum ‘app _ async_map_v _ _ _’ xapp_spec >> xsimpl
QED

Theorem kquery_spec:
  KQRY q qv ⇒
  app (p:'ffi ffi_proj) kquery_v [qv] emp
    (POSTv v. &COMP p KSACT (OPTION_TYPE KANS) KSSNAP (kquery q) v)
Proof
  strip_tac >> irule app_COMP_of_approxd >> simp[] >> gen_tac >>
  xcf_with_def (fetch "-" "kquery_v_def") >>
  xlet ‘POSTv kv. &KSACT (Kv q) kv’
  >- (xcon >> xsimpl >> simp[KACT_def]) >>
  xlet ‘POSTv ev. &COMP p KSACT KSRESP KSSNAP (emit (Kv q)) ev’
  >- (xapp_spec Async_emit_spec >> simp[]) >> xfun ‘f’ >>
  ‘app p async_map_v [f; ev] emp
     (POSTv v. &COMPd p KSACT (OPTION_TYPE KANS) KSSNAP n (kquery q) v)’
    by (simp[kquery_def] >> irule async_map_spec_d >>
        simp[asyncLevel1Theory.wf_emit] >>
        qexists_tac ‘KSRESP’ >> simp[COMP_IMP_COMPd] >> rpt strip_tac >>
        simp[returns_def] >>
        qpat_x_assum ‘curried _ _ f ∧ _’ (irule o CONJUNCT2) >>
        Cases_on ‘x’ >> gvs[KRES_def] >> xmatch >>
        xcon >> xsimpl >> simp[OPTION_TYPE_def]) >>
  qpat_x_assum ‘app _ async_map_v _ _ _’ xapp_spec >> xsimpl
QED

(* The guarded bind for Async.bind (as translateSock) *)
Theorem Async_bind_guarded_any:
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
