(*
  CF specs of the bodies HTTP server (asyncHttpSockProgB): it implements
  srelabel (http_server_b files lfd).  asyncHttpSockSpecH with the bodies
  parser and brespond; the skeleton's spec (sserver_with_spec) is reused.
*)
Theory asyncHttpSockSpecB
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncServer asyncCfActModel
  asyncCfActProg asyncM4Approx asyncM3World asyncM3Prog asyncM3Loop
  asyncM4Relabel asyncM4RelabelDist asyncM4SockModel asyncM4SockApprox
  asyncM4SockServer asyncServerWith HttpSpec HttpSpecHeaders HttpSpecBodies
  asyncHttpParse asyncHttpParseH asyncHttpParseB asyncHttpServerB asyncHttpImplProg asyncHttpSockModel
  asyncHttpSockModelB asyncHttpSockProg asyncHttpSockSpec asyncHttpSockProgH
  asyncHttpSockProgB
  ml_translator mlstring std_prelude
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncHttpSockProgB"

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
   The HTTP handler
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

(* MAIN (helper): the CakeML HTTP handler implements the socket-vocabulary
   handler up to any depth n, for every buffer *)
Theorem shttp_handler_b_spec_d:
  ∀n buf bufv fd fdv.
    FILES files filesv ∧ NUM fd fdv ∧ fd < dimword(:64) ∧ LIST_TYPE CHAR buf bufv ⇒
    app (p:'ffi ffi_proj) asyncHttpSockProgB$http_handler_b_v [filesv; fdv; bufv] emp
      (POSTv v. &COMPd p SACT UNIT_TYPE SSNAP n
                  (srelabel (http_handler_b files (fd, buf))) v)
Proof
  completeInduct_on ‘n’ >> rpt strip_tac >>
  xcf_with_def asyncHttpSockProgBTheory.http_handler_b_v_def >>
  xlet ‘POSTv rv. &ASYNCHTTPPARSEB_BPARSE_RESULT_TYPE (parse_brequest buf) rv’
  >- (xapp >> simp[]) >>
  simp_tac std_ss [Once shttp_handler_b_unfold] >>
  Cases_on ‘parse_brequest buf’ >>
  gvs[ASYNCHTTPPARSEB_BPARSE_RESULT_TYPE_def]
  >- ((* Complete (Get path) rest: write the response, then the handler on rest *)
      qmatch_goalsub_rename_tac ‘bhandle files req’ >>
      Cases_on ‘req’ >> gvs[HTTPSPECBODIES_BREQUEST_TYPE_def] >> xmatch >>
      simp_tac std_ss [GSYM brespond_thm] >>
      qmatch_goalsub_rename_tac ‘brespond files mth path body’ >>
      qmatch_goalsub_rename_tac ‘http_handler_b files (fd, rest)’ >>
      xfun ‘k1’ >>
      xlet ‘POSTv sv. &LIST_TYPE CHAR (brespond files mth path body) sv’
      >- (xapp >> fs[]) >>
      xlet ‘POSTv tv. &STRING_TYPE (implode (brespond files mth path body)) tv’
      >- (xapp >> simp[]) >>
      qabbrev_tac ‘bs = MAP ((n2w : num -> word8) o ORD) (brespond files mth path body)’ >>
      xlet ‘POSTv av. &SACT (Write (n2w fd) bs) av’
      >- (xcon >> xsimpl >> gs[SACT_def, Abbr ‘bs’, bytes_str_chars]) >>
      xlet ‘POSTv ev. &COMP p SACT SRESP SSNAP (emit (Write (n2w fd) bs)) ev’
      >- emit_tac “Write (n2w fd) bs” >>
      ‘app p Async_bind_v [ev; k1] emp
         (POSTv v. &COMPd p SACT UNIT_TYPE SSNAP n
                     (bind (emit (Write (n2w fd) bs))
                           (λw. srelabel (http_handler_b files (fd, rest)))) v)’
        by (irule Async_bind_guarded_spec_any >>
            simp[wf_emit, emit_needs_snapshot] >>
            qexists_tac ‘SRESP’ >> rpt strip_tac >> simp[returns_def] >>
            qpat_x_assum ‘curried _ _ k1 ∧ _’ (irule o CONJUNCT2) >>
            first_x_assum (qspec_then ‘n - 1’ mp_tac) >> simp[] >>
            strip_tac >> xapp >> simp[]) >>
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
                      >- (xapp >> simp[])
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
                      >- (xapp >> simp[] >> metis_tac[]) >>
                      xapp >> simp[]) >>
                  (* any other response: the handler on buf again *)
                  xmatch >> xapp >> simp[]) >>
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

(* MAIN: the CakeML HTTP handler implements the model's handler, in the
   socket vocabulary *)
Theorem shttp_handler_b_spec:
  FILES files filesv ∧ NUM fd fdv ∧ fd < dimword(:64) ∧ LIST_TYPE CHAR buf bufv ⇒
  app (p:'ffi ffi_proj) asyncHttpSockProgB$http_handler_b_v [filesv; fdv; bufv] emp
    (POSTv v. &COMP p SACT UNIT_TYPE SSNAP (srelabel (http_handler_b files (fd, buf))) v)
Proof
  strip_tac >> irule app_COMP_of_approxd >> simp[shttp_handler_b_spec_d]
QED

(* MAIN: the CakeML HTTP server implements the model's http_server, in the
   socket vocabulary: the instance of sserver_with_spec for the HTTP
   handler *)
Theorem shttp_server_b_spec:
  FILES files filesv ∧ NUM lfd lfdv ∧ lfd < dimword(:64) ⇒
  app (p:'ffi ffi_proj) asyncHttpSockProgB$http_server_b_v [filesv; lfdv] emp
    (POSTv v. &COMP p SACT UNIT_TYPE SSNAP (srelabel (http_server_b files lfd)) v)
Proof
  rpt strip_tac >> xcf_with_def asyncHttpSockProgBTheory.http_server_b_v_def >> xfun ‘h’ >>
  simp[http_server_b_def] >> xapp_spec sserver_with_spec >>
  simp[SHANDLER_def, wf_http_handler_b] >> rpt strip_tac >>
  qpat_x_assum ‘curried _ _ h ∧ _’ (irule o CONJUNCT2) >>
  xlet ‘POSTv bv. &LIST_TYPE CHAR "" bv’
  >- (xcon >> xsimpl >> simp[LIST_TYPE_def]) >>
  xapp_spec shttp_handler_b_spec >> simp[]
QED
