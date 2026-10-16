(*
  The socket library, as the async translator sees it (design/44 §5–6):
  two library wrappers written once, in the style of OCaml Async's
  Writer.write / Reader.read, each with its model, CakeML code, COMP spec,
  guard and wf, on top of close-v2's chain (protoProg):

     swrite fd s : unit          writes the string s to fd
     sread fd    : string option  reads up to bufsz bytes from fd
                                  (SOME "" at end of stream, NONE on error)

  plus the guarded-bind rule for Async.bind (Async_bind_guarded_any; the
  chain keeps local copies of it in five files) and sock_vocab, the
  translator's view of the library (Async.bind, async_map, async_both).
*)
Theory translateSock
Ancestors
  asyncCore asyncLevel1 asyncChoose echoServer libModel libProg libApprox
  loopPollWorld loopPollProg loopPoll relabel relabelDist echoSockModel
  libSockApprox echoSockServer HttpGetSpec HttpHeadersSpec HttpSpec
  httpGetParse httpHeadersParse httpParse protoInterface httpProto protoProg
  protoSockSpec ml_translator mlstring mlint std_prelude ListProg httpProg
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

(* on the chain's last program (the bodies HTTP instance), so that the
   generated server can reuse its translated parser and responder *)
val _ = translation_extends "httpProg"

(* ------------------------------------------------------------------------
   The models
   ------------------------------------------------------------------------ *)

Definition swrite_def:
  swrite fd s =
    map (λr. ()) (emit (loopPollWorld$Write (n2w fd) (MAP (n2w o ORD) s)))
End

Definition sread_def:
  sread fd =
    map (λr. case r of Got (SOME bs) => SOME (MAP (CHR o w2n) bs) | _ => NONE)
        (emit (loopPollWorld$Read (n2w fd) bufsz))
End

Theorem swrite_NIL:
  (swrite fd s []).result = NONE
Proof
  simp[swrite_def, asyncLevel1Theory.map_def, emit_needs_snapshot]
QED

Theorem sread_NIL:
  (sread fd []).result = NONE
Proof
  simp[sread_def, asyncLevel1Theory.map_def, emit_needs_snapshot]
QED

Theorem wf_swrite:
  wf (swrite fd s)
Proof
  simp[swrite_def, asyncLevel1Theory.wf_map, asyncLevel1Theory.wf_emit]
QED

Theorem wf_sread:
  wf (sread fd)
Proof
  simp[sread_def, asyncLevel1Theory.wf_map, asyncLevel1Theory.wf_emit]
QED

(* ------------------------------------------------------------------------
   The code
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  fun swrite fd s =
    async_map (fn r => ()) (Async.emit (Write fd (String.implode s)));

  fun sread fd =
    async_map (fn r => case r of Got ro =>
                         (case ro of Some s => Some (String.explode s)
                                   | None => None)
                       | _ => None)
              (Async.emit (Read fd 4096));
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

Theorem swrite_spec:
  NUM fd fdv ∧ fd < dimword(:64) ∧ LIST_TYPE CHAR s sv ⇒
  app (p:'ffi ffi_proj) swrite_v [fdv; sv] emp
    (POSTv v. &COMP p SACT UNIT_TYPE SSNAP (swrite fd s) v)
Proof
  strip_tac >> irule app_COMP_of_approxd >> simp[] >> gen_tac >>
  xcf_with_def (fetch "-" "swrite_v_def") >>
  xlet ‘POSTv tv. &STRING_TYPE (implode s) tv’ >- (xapp >> metis_tac[]) >>
  xlet ‘POSTv av. &SACT (Write (n2w fd) (MAP (n2w o ORD) s)) av’
  >- (xcon >> xsimpl >> gs[SACT_def, bytes_str_chars]) >>
  xlet ‘POSTv ev. &COMP p SACT SRESP SSNAP
                     (emit (Write (n2w fd) (MAP (n2w o ORD) s))) ev’
  >- (xapp_spec Async_emit_spec >> simp[]) >> xfun ‘f’ >>
  ‘app p async_map_v [f; ev] emp
     (POSTv v. &COMPd p SACT UNIT_TYPE SSNAP n (swrite fd s) v)’
    by (simp[swrite_def] >> irule async_map_spec_d >> simp[asyncLevel1Theory.wf_emit] >>
        qexists_tac ‘SRESP’ >> simp[COMP_IMP_COMPd] >> rpt strip_tac >>
        simp[returns_def] >>
        qpat_x_assum ‘curried _ _ f ∧ _’ (irule o CONJUNCT2) >>
        xcon >> xsimpl) >>
  qpat_x_assum ‘app _ async_map_v _ _ _’ xapp_spec >> xsimpl
QED

Theorem sread_spec:
  NUM fd fdv ∧ fd < dimword(:64) ⇒
  app (p:'ffi ffi_proj) sread_v [fdv] emp
    (POSTv v. &COMP p SACT (OPTION_TYPE (LIST_TYPE CHAR)) SSNAP (sread fd) v)
Proof
  strip_tac >> irule app_COMP_of_approxd >> simp[] >> gen_tac >>
  xcf_with_def (fetch "-" "sread_v_def") >>
  xlet ‘POSTv av. &SACT (Read (n2w fd) bufsz) av’
  >- (xcon >> xsimpl >> gs[SACT_def, bufsz_def, NUM_def, INT_def]) >>
  xlet ‘POSTv ev. &COMP p SACT SRESP SSNAP (emit (Read (n2w fd) bufsz)) ev’
  >- (xapp_spec Async_emit_spec >> simp[]) >> xfun ‘f’ >>
  ‘app p async_map_v [f; ev] emp
     (POSTv v. &COMPd p SACT (OPTION_TYPE (LIST_TYPE CHAR)) SSNAP n (sread fd) v)’
    by (simp[sread_def] >> irule async_map_spec_d >> simp[asyncLevel1Theory.wf_emit] >>
        qexists_tac ‘SRESP’ >> simp[COMP_IMP_COMPd] >> rpt strip_tac >>
        simp[returns_def] >>
        qpat_x_assum ‘curried _ _ f ∧ _’ (irule o CONJUNCT2) >>
        Cases_on ‘x’ >> gvs[SRESP_def] >> xmatch
        >- (xcon >> xsimpl >> simp[OPTION_TYPE_def])
        >- (rename1 ‘OPTION_MAP _ ro’ >> Cases_on ‘ro’ >>
            gvs[OPTION_TYPE_def] >> xmatch
            >- (xcon >> xsimpl >> simp[OPTION_TYPE_def]) >>
            xlet ‘POSTv cv. &LIST_TYPE CHAR (MAP (CHR o w2n) x) cv’
            >- (xapp >> xsimpl >> first_assum (irule_at Any) >>
                simp[mlstringTheory.explode_implode]) >>
            xcon >> xsimpl >> simp[OPTION_TYPE_def]) >>
        xcon >> xsimpl >> simp[OPTION_TYPE_def]) >>
  qpat_x_assum ‘app _ async_map_v _ _ _’ xapp_spec >> xsimpl
QED

(* ------------------------------------------------------------------------
   The guarded bind for Async.bind
   ------------------------------------------------------------------------ *)

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
