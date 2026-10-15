(*
  The CakeML server skeleton, the HTTP handler and the HTTP server implement
  the model's server_with, http_handler and http_server.

  The technique is asyncM4ServerSpec's: for every depth n, prove that the
  CakeML value implements the model up to depth n, by induction on n
  (bind_guarded_spec_d at the guarded bind, where the induction hypothesis
  is used; bind_spec_d, both_spec_d and map_spec_d elsewhere), and then take
  the limit with app_COMP_of_approxd.

  server_with_spec is proved once, for any handler that has a COMP spec;
  the echo server (server_with_handler_spec) and the HTTP server
  (http_server_spec) are instances.
*)
Theory asyncHttpImplSpec
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncServer asyncCfActModel
  asyncCfActProg asyncCfActSpec asyncCfActBoth asyncM4Approx
  asyncM4ServerProg asyncM4ServerSpec asyncServerWith HttpSpec
  asyncHttpParse asyncHttpServer asyncHttpImplProg ml_translator
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncHttpImplProg"

Theorem readable_NIL[local]:
  (readable fd []).result = NONE
Proof
  simp[readable_def, wait_needs_snapshot]
QED

Theorem wf_readable[local]:
  wf (readable fd)
Proof
  simp[readable_def, wf_wait]
QED

(* ------------------------------------------------------------------------
   The generic server skeleton
   ------------------------------------------------------------------------ *)

(* HANDLER h hv: the CakeML value hv implements the model handler h on
   every connection *)
Definition HANDLER_def:
  HANDLER (p:'ffi ffi_proj) h hv ⇔
    (∀fd. wf (h fd)) ∧
    ∀fd fdv. NUM fd fdv ⇒
      app p hv [fdv] emp (POSTv v. &COMP p ACTION UNIT_TYPE SNAP (h fd) v)
End

(* The skeleton's code up to the outer bind *)
val server_with_prelude =
  rpt strip_tac >> xcf_with_def server_with_v_def >>
  simp_tac std_ss [Once server_with_unfold] >>
  xfun ‘k1’ >>
  xlet ‘POSTv r. &COMP p ACTION UNIT_TYPE SNAP (readable lfd) r’
  >- (xapp_spec readable_spec >> simp[]) >>
  qmatch_goalsub_abbrev_tac ‘bind (readable lfd) G’;

(* MAIN (helper): the CakeML skeleton implements the model's server_with h
   up to any depth n, for any handler with a spec *)
Theorem server_with_spec_d:
  ∀n lfd lfdv.
    HANDLER p h hv ∧ NUM lfd lfdv ⇒
    app (p:'ffi ffi_proj) server_with_v [hv; lfdv] emp
      (POSTv v. &COMPd p ACTION UNIT_TYPE SNAP n (server_with h lfd) v)
Proof
  Induct
  >- (server_with_prelude >>
      ‘app p bind_v [r; k1] emp
         (POSTv v. &COMPd p ACTION UNIT_TYPE SNAP 0 (bind (readable lfd) G) v)’
        by (irule bind_guarded_spec_0 >> simp[readable_NIL] >>
            metis_tac[COMP_IMP_COMPd]) >>
      qpat_x_assum ‘app _ bind_v _ _ _’ xapp_spec >> xsimpl) >>
  server_with_prelude >>
  (* the continuation after readable: emit (Accept lfd), then G2 *)
  ‘∀x xv. UNIT_TYPE x xv ⇒
          returns p k1 [xv] (COMPd p ACTION UNIT_TYPE SNAP n (G x))’
    by (rpt strip_tac >> simp[returns_def, Abbr ‘G’] >>
        qpat_x_assum ‘curried _ _ k1 ∧ _’ (irule o CONJUNCT2) >>
        xfun ‘k2’ >>
        xlet ‘POSTv av. &ACTION (Accept lfd) av’
        >- (xcon >> xsimpl >> simp[ASYNCSERVER_ACTION_TYPE_def]) >>
        xlet ‘POSTv ev. &COMP p ACTION RESPONSE SNAP (emit (Accept lfd)) ev’
        >- (xapp_spec emit_spec >> simp[]) >>
        qmatch_goalsub_abbrev_tac ‘bind (emit _) G2’ >>
        ‘∀res resv. RESPONSE res resv ⇒
           returns p k2 [resv] (COMPd p ACTION UNIT_TYPE SNAP n (G2 res))’
          by (rpt strip_tac >> simp[returns_def, Abbr ‘G2’] >>
              qpat_x_assum ‘curried _ _ k2 ∧ _’ (irule o CONJUNCT2) >>
              Cases_on ‘res’ >> gvs[ASYNCSERVER_RESPONSE_TYPE_def] >>
              xmatch
              >~ [‘both (h _) _’]
              >- ((* Accepted fd: the handler alongside the rest *)
                  qmatch_goalsub_rename_tac ‘h cfd’ >>
                  qmatch_asmsub_rename_tac ‘NUM cfd cfdv’ >>
                  ‘∀fd. wf (h fd)’ by fs[HANDLER_def] >>
                  xlet ‘POSTv sv. &COMPd p ACTION UNIT_TYPE SNAP n
                                    (server_with h lfd) sv’
                  >- (xapp >> simp[]) >>
                  xlet ‘POSTv hv'. &COMP p ACTION UNIT_TYPE SNAP (h cfd) hv'’
                  >- (‘app p hv [cfdv] emp
                         (POSTv v. &COMP p ACTION UNIT_TYPE SNAP (h cfd) v)’
                        by gvs[HANDLER_def] >>
                      qpat_x_assum ‘app _ hv _ _ _’ xapp_spec >> xsimpl) >>
                  ‘app p both_v [hv'; sv] emp
                     (POSTv v. &COMPd p ACTION (PAIR_TYPE UNIT_TYPE UNIT_TYPE)
                                 SNAP n (both (h cfd) (server_with h lfd)) v)’
                    by (irule both_spec_d >> simp[wf_server_with, COMP_IMP_COMPd]) >>
                  xlet ‘POSTv bv. &COMPd p ACTION (PAIR_TYPE UNIT_TYPE UNIT_TYPE)
                                    SNAP n (both (h cfd) (server_with h lfd)) bv’
                  >- (qpat_x_assum ‘app _ both_v _ _ _’ xapp_spec >> xsimpl) >>
                  xfun ‘f’ >>
                  ‘app p map_v [f; bv] emp
                     (POSTv v. &COMPd p ACTION UNIT_TYPE SNAP n
                                 (map (λp. ()) (both (h cfd) (server_with h lfd))) v)’
                    by (irule map_spec_d >>
                        simp[wf_both, wf_server_with] >>
                        qexists_tac ‘PAIR_TYPE UNIT_TYPE UNIT_TYPE’ >> simp[] >>
                        rpt strip_tac >> simp[returns_def] >>
                        qpat_x_assum ‘curried _ _ f ∧ _’ (irule o CONJUNCT2) >>
                        xcon >> xsimpl) >>
                  qpat_x_assum ‘app _ map_v _ _ _’ xapp_spec >> xsimpl) >>
              (* any other response: the skeleton again *)
              xapp >> simp[]) >>
        ‘app p bind_v [ev; k2] emp
           (POSTv v. &COMPd p ACTION UNIT_TYPE SNAP n
                       (bind (emit (Accept lfd)) G2) v)’
          by (irule bind_spec_d >> simp[wf_emit] >> qexists_tac ‘RESPONSE’ >>
              simp[COMP_IMP_COMPd] >> metis_tac[]) >>
        qpat_x_assum ‘app _ bind_v _ _ _’ xapp_spec >> xsimpl) >>
  ‘app p bind_v [r; k1] emp
     (POSTv v. &COMPd p ACTION UNIT_TYPE SNAP (SUC n) (bind (readable lfd) G) v)’
    by (irule bind_guarded_spec_d >> simp[wf_readable, readable_NIL] >>
        qexists_tac ‘UNIT_TYPE’ >> simp[COMP_IMP_COMPd] >> metis_tac[]) >>
  qpat_x_assum ‘app _ bind_v _ _ _’ xapp_spec >> xsimpl
QED

(* MAIN: for any handler value hv implementing a model handler h, the
   CakeML skeleton server_with hv implements the model's server_with h *)
Theorem server_with_spec:
  HANDLER p h hv ∧ NUM lfd lfdv ⇒
  app (p:'ffi ffi_proj) server_with_v [hv; lfdv] emp
    (POSTv v. &COMP p ACTION UNIT_TYPE SNAP (server_with h lfd) v)
Proof
  strip_tac >> irule app_COMP_of_approxd >> simp[] >>
  metis_tac[server_with_spec_d]
QED

(* MAIN: the echo server is an instance: server_with applied to the CakeML
   echo handler implements the model's echo server *)
Theorem server_with_handler_spec:
  NUM lfd lfdv ⇒
  app (p:'ffi ffi_proj) server_with_v [handler_v; lfdv] emp
    (POSTv v. &COMP p ACTION UNIT_TYPE SNAP (server lfd) v)
Proof
  strip_tac >> simp[GSYM server_with_handler] >> irule server_with_spec >>
  simp[HANDLER_def, wf_handler, handler_spec]
QED

(* ------------------------------------------------------------------------
   The HTTP handler
   ------------------------------------------------------------------------ *)

(* The file map, as the translator represents it *)
Overload FILES = “LIST_TYPE (PAIR_TYPE (LIST_TYPE CHAR) (LIST_TYPE CHAR))”

(* A guarded bind, at any depth n: bind_guarded_spec_0 for n = 0 (the
   continuation is not needed), bind_guarded_spec_d otherwise (the
   continuation is needed one level less deep). *)
Theorem bind_guarded_spec_any[local]:
  wf m ∧ (m []).result = NONE ∧ COMP p ACT A (SNAPSHOT READY R) m mv ∧
  (0 < n ⇒
   ∀x xv. A x xv ⇒
     returns p gv [xv]
       (COMPd p ACT B (SNAPSHOT READY (R : 'r -> v -> bool)) (n - 1) (g x))) ⇒
  app (p:'ffi ffi_proj) bind_v [mv; gv] emp
    (POSTv v. &COMPd p (ACT : 'act -> v -> bool) B (SNAPSHOT READY R) n
                (bind m g) v)
Proof
  Cases_on ‘n’ >> rpt strip_tac
  >- (irule bind_guarded_spec_0 >> simp[] >> metis_tac[COMP_IMP_COMPd])
  >> irule bind_guarded_spec_d >> gs[] >> qexists_tac ‘A’ >>
  simp[COMP_IMP_COMPd]
QED

(* return (), at any depth *)
val return_unit_tac =
  xlet ‘POSTv uv. &UNIT_TYPE () uv’ >- (xcon >> xsimpl) >>
  ‘app p return_v [uv] emp
     (POSTv v. &COMP p ACTION UNIT_TYPE SNAP (return ()) v)’
    by (irule return_spec >> simp[]) >>
  qpat_x_assum ‘app _ return_v _ _ _’ xapp_spec >> xsimpl >>
  simp[COMP_IMP_COMPd];

(* MAIN (helper): the CakeML HTTP handler implements the model's handler
   up to any depth n, for every buffer *)
Theorem http_handler_spec_d:
  ∀n buf bufv fd fdv.
    FILES files filesv ∧ NUM fd fdv ∧ LIST_TYPE CHAR buf bufv ⇒
    app (p:'ffi ffi_proj) http_handler_v [filesv; fdv; bufv] emp
      (POSTv v. &COMPd p ACTION UNIT_TYPE SNAP n (http_handler files (fd, buf)) v)
Proof
  completeInduct_on ‘n’ >> rpt strip_tac >>
  xcf_with_def http_handler_v_def >>
  xlet ‘POSTv rv. &ASYNCHTTPPARSE_PARSE_RESULT_TYPE (parse_request buf) rv’
  >- (xapp >> simp[]) >>
  simp_tac std_ss [Once http_handler_unfold] >>
  Cases_on ‘parse_request buf’ >>
  gvs[ASYNCHTTPPARSE_PARSE_RESULT_TYPE_def]
  >- ((* Complete (Get path) rest: write the response, then the handler on rest *)
      qmatch_goalsub_rename_tac ‘handle files req’ >>
      Cases_on ‘req’ >> gvs[HTTPSPEC_REQUEST_TYPE_def] >> xmatch >>
      simp_tac std_ss [GSYM respond_thm] >>
      qmatch_goalsub_rename_tac ‘respond files path’ >>
      qmatch_goalsub_rename_tac ‘http_handler files (fd, rest)’ >>
      xfun ‘k1’ >>
      xlet ‘POSTv sv. &LIST_TYPE CHAR (respond files path) sv’
      >- (xapp >> qexists_tac ‘LIST_TYPE CHAR’ >>
          simp[EqualityType_LIST_TYPE, EqualityType_NUM_BOOL]) >>
      xlet ‘POSTv av. &ACTION (Write fd (respond files path)) av’
      >- (xcon >> xsimpl >> simp[ASYNCSERVER_ACTION_TYPE_def]) >>
      xlet ‘POSTv ev. &COMP p ACTION RESPONSE SNAP
                        (emit (Write fd (respond files path))) ev’
      >- (xapp_spec emit_spec >> simp[]) >>
      ‘app p bind_v [ev; k1] emp
         (POSTv v. &COMPd p ACTION UNIT_TYPE SNAP n
                     (bind (emit (Write fd (respond files path)))
                           (λw. http_handler files (fd, rest))) v)’
        by (irule bind_guarded_spec_any >>
            simp[wf_emit, emit_needs_snapshot] >>
            qexists_tac ‘RESPONSE’ >> rpt strip_tac >> simp[returns_def] >>
            qpat_x_assum ‘curried _ _ k1 ∧ _’ (irule o CONJUNCT2) >>
            first_x_assum (qspec_then ‘n - 1’ mp_tac) >> simp[] >>
            strip_tac >> xapp >> simp[]) >>
      qpat_x_assum ‘app _ bind_v _ _ _’ xapp_spec >> xsimpl)
  >- ((* Incomplete: wait for fd to be readable, read, and continue *)
      xmatch >> xfun ‘k1’ >>
      xlet ‘POSTv r. &COMP p ACTION UNIT_TYPE SNAP (readable fd) r’
      >- (xapp_spec readable_spec >> simp[]) >>
      qmatch_goalsub_abbrev_tac ‘bind (readable fd) G’ >>
      ‘0 < n ⇒ ∀x xv. UNIT_TYPE x xv ⇒
         returns p k1 [xv] (COMPd p ACTION UNIT_TYPE SNAP (n - 1) (G x))’
        by (rpt strip_tac >> simp[returns_def, Abbr ‘G’] >>
            first_x_assum (qspec_then ‘n - 1’ mp_tac) >> simp[] >> strip_tac >>
            qpat_x_assum ‘curried _ _ k1 ∧ _’ (irule o CONJUNCT2) >>
            xfun ‘k2’ >>
            xlet ‘POSTv av. &ACTION (Read fd) av’
            >- (xcon >> xsimpl >> simp[ASYNCSERVER_ACTION_TYPE_def]) >>
            xlet ‘POSTv ev. &COMP p ACTION RESPONSE SNAP (emit (Read fd)) ev’
            >- (xapp_spec emit_spec >> simp[]) >>
            qmatch_goalsub_abbrev_tac ‘bind (emit _) G2’ >>
            ‘∀res resv. RESPONSE res resv ⇒
               returns p k2 [resv]
                 (COMPd p ACTION UNIT_TYPE SNAP (n - 1) (G2 res))’
              by (rpt strip_tac >> simp[returns_def, Abbr ‘G2’] >>
                  qpat_x_assum ‘curried _ _ k2 ∧ _’ (irule o CONJUNCT2) >>
                  Cases_on ‘res’ >> gvs[ASYNCSERVER_RESPONSE_TYPE_def] >>
                  xmatch
                  >~ [‘buf ++ d’]
                  >- ((* Data d: the handler on buf ++ d *)
                      xlet ‘POSTv bv. &LIST_TYPE CHAR (buf ++ d) bv’
                      >- (xapp >> simp[] >> metis_tac[]) >>
                      xapp >> simp[])
                  >~ [‘return ()’]
                  >- return_unit_tac >>
                  (* any other response: the handler on buf again *)
                  xapp >> simp[]) >>
            ‘app p bind_v [ev; k2] emp
               (POSTv v. &COMPd p ACTION UNIT_TYPE SNAP (n - 1)
                           (bind (emit (Read fd)) G2) v)’
              by (irule bind_spec_d >> simp[wf_emit] >> qexists_tac ‘RESPONSE’ >>
                  simp[COMP_IMP_COMPd] >> metis_tac[]) >>
            qpat_x_assum ‘app _ bind_v _ _ _’ xapp_spec >> xsimpl) >>
      ‘app p bind_v [r; k1] emp
         (POSTv v. &COMPd p ACTION UNIT_TYPE SNAP n (bind (readable fd) G) v)’
        by (irule bind_guarded_spec_any >> simp[wf_readable, readable_NIL] >>
            metis_tac[]) >>
      qpat_x_assum ‘app _ bind_v _ _ _’ xapp_spec >> xsimpl) >>
  (* Invalid: stop *)
  xmatch >> return_unit_tac
QED

(* MAIN: the CakeML HTTP handler implements the model's handler: for a
   connection fd and a buffer buf, http_handler files fd buf returns a
   computation value that, round by round, emits exactly the model's actions
   (Write fd response, Read fd) and finishes exactly when the model's
   http_handler files (fd, buf) does. *)
Theorem http_handler_spec:
  FILES files filesv ∧ NUM fd fdv ∧ LIST_TYPE CHAR buf bufv ⇒
  app (p:'ffi ffi_proj) http_handler_v [filesv; fdv; bufv] emp
    (POSTv v. &COMP p ACTION UNIT_TYPE SNAP (http_handler files (fd, buf)) v)
Proof
  strip_tac >> irule app_COMP_of_approxd >> simp[http_handler_spec_d]
QED

(* ------------------------------------------------------------------------
   The HTTP server
   ------------------------------------------------------------------------ *)

(* MAIN: the CakeML HTTP server implements the model's http_server: for a
   file map and a listener lfd, http_server files lfd returns a computation
   value that, round by round, emits exactly the model's actions (Accept
   lfd, and the actions of every accepted connection's HTTP handler) and
   never finishes, exactly as the model's http_server files lfd.  It is the
   instance of server_with_spec for the HTTP handler. *)
Theorem http_server_spec:
  FILES files filesv ∧ NUM lfd lfdv ⇒
  app (p:'ffi ffi_proj) http_server_v [filesv; lfdv] emp
    (POSTv v. &COMP p ACTION UNIT_TYPE SNAP (http_server files lfd) v)
Proof
  rpt strip_tac >> xcf_with_def http_server_v_def >> xfun ‘h’ >>
  simp[http_server_def] >> xapp_spec server_with_spec >>
  simp[HANDLER_def, wf_http_handler] >> rpt strip_tac >>
  qpat_x_assum ‘curried _ _ h ∧ _’ (irule o CONJUNCT2) >>
  xlet ‘POSTv bv. &LIST_TYPE CHAR "" bv’
  >- (xcon >> xsimpl >> simp[LIST_TYPE_def]) >>
  xapp_spec http_handler_spec >> simp[]
QED
