(*
  The CakeML echo handler and server implement the model's handler and
  server (async/model/asyncServerScript.sml).

  The model defines both with fix; the CakeML code is ordinary recursion.
  The bridge is the model's unfolding equation (handler_unfold,
  server_unfold) plus the depth-indexed specs of asyncM4Approx: for every
  depth n we prove that the CakeML value implements the model up to depth
  n, by induction on n.  The step uses
   - bind_guarded_spec_d at the outer bind (the first part, readable,
     cannot finish before a poll, so the continuation is needed one level
     less deep: this is where the induction hypothesis is used), and
   - bind_spec_d, both_spec_d and map_spec_d inside (they preserve depth).
  The limit lemma app_COMP_of_approxd then gives the real predicate COMP.
*)
Theory asyncM4ServerSpec
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncServer asyncCfActModel
  asyncCfActProg asyncCfActSpec asyncCfActBoth asyncM4Approx
  asyncM4ServerProg ml_translator
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncM4ServerProg"

(* The relations used throughout: model actions and responses as the
   CakeML datatypes of asyncM4ServerProg, snapshots whose ready set is a
   list of events. *)
Overload ACTION = “ASYNCSERVER_ACTION_TYPE”
Overload RESPONSE = “ASYNCSERVER_RESPONSE_TYPE”
Overload SNAP = “SNAPSHOT EVENTS ASYNCSERVER_RESPONSE_TYPE”

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
   The handler
   ------------------------------------------------------------------------ *)

(* The handler's code up to the outer bind: compute readable fd, then
   bind it with the continuation k1 (Abbrev G is the model continuation). *)
val handler_prelude =
  rpt strip_tac >> xcf_with_def handler_v_def >>
  simp_tac std_ss [Once handler_unfold] >>
  simp_tac std_ss [handler_body_def] >>
  xfun ‘k1’ >>
  xlet ‘POSTv r. &COMP p ACTION UNIT_TYPE SNAP (readable fd) r’
  >- (xapp_spec readable_spec >> simp[]) >>
  qmatch_goalsub_abbrev_tac ‘bind (readable fd) G’;

(* MAIN (helper): the CakeML handler implements the model's handler up to
   any depth n *)
Theorem handler_spec_d:
  ∀n fd fdv.
    NUM fd fdv ⇒
    app (p:'ffi ffi_proj) handler_v [fdv] emp
      (POSTv v. &COMPd p ACTION UNIT_TYPE SNAP n (handler fd) v)
Proof
  Induct
  >- (handler_prelude >>
      ‘app p bind_v [r; k1] emp
         (POSTv v. &COMPd p ACTION UNIT_TYPE SNAP 0 (bind (readable fd) G) v)’
        by (irule bind_guarded_spec_0 >> simp[readable_NIL] >>
            metis_tac[COMP_IMP_COMPd]) >>
      qpat_x_assum ‘app _ bind_v _ _ _’ xapp_spec >> xsimpl) >>
  handler_prelude >>
  (* the continuation after readable: emit (Read fd), then G2 *)
  ‘∀x xv. UNIT_TYPE x xv ⇒
          returns p k1 [xv] (COMPd p ACTION UNIT_TYPE SNAP n (G x))’
    by (rpt strip_tac >> simp[returns_def, Abbr ‘G’] >>
        qpat_x_assum ‘curried _ _ k1 ∧ _’ (irule o CONJUNCT2) >>
        xfun ‘k2’ >>
        xlet ‘POSTv av. &ACTION (Read fd) av’
        >- (xcon >> xsimpl >> simp[ASYNCSERVER_ACTION_TYPE_def]) >>
        xlet ‘POSTv ev. &COMP p ACTION RESPONSE SNAP (emit (Read fd)) ev’
        >- (xapp_spec emit_spec >> simp[]) >>
        qmatch_goalsub_abbrev_tac ‘bind (emit _) G2’ >>
        ‘∀res resv. RESPONSE res resv ⇒
           returns p k2 [resv] (COMPd p ACTION UNIT_TYPE SNAP n (G2 res))’
          by (rpt strip_tac >> simp[returns_def, Abbr ‘G2’] >>
              qpat_x_assum ‘curried _ _ k2 ∧ _’ (irule o CONJUNCT2) >>
              Cases_on ‘res’ >> gvs[ASYNCSERVER_RESPONSE_TYPE_def] >>
              xmatch
              >~ [‘bind (emit (Write _ _)) _’]
              >- ((* Data d: emit (Write fd d), then the handler again *)
                  xfun ‘k3’ >>
                  xlet ‘POSTv av2. &ACTION (Write fd s) av2’
                  >- (xcon >> xsimpl >> simp[ASYNCSERVER_ACTION_TYPE_def]) >>
                  xlet ‘POSTv ev2. &COMP p ACTION RESPONSE SNAP
                                    (emit (Write fd s)) ev2’
                  >- (xapp_spec emit_spec >> simp[]) >>
                  ‘∀w wv. RESPONSE w wv ⇒
                     returns p k3 [wv]
                       (COMPd p ACTION UNIT_TYPE SNAP n ((λw. handler fd) w))’
                    by (rpt strip_tac >> simp[returns_def] >>
                        qpat_x_assum ‘curried _ _ k3 ∧ _’ (irule o CONJUNCT2) >>
                        xapp >> simp[]) >>
                  ‘app p bind_v [ev2; k3] emp
                     (POSTv v. &COMPd p ACTION UNIT_TYPE SNAP n
                                 (bind (emit (Write fd s)) (λw. handler fd)) v)’
                    by (irule bind_spec_d >> simp[wf_emit] >> qexists_tac ‘RESPONSE’ >>
                        simp[COMP_IMP_COMPd] >> metis_tac[]) >>
                  qpat_x_assum ‘app _ bind_v _ _ _’ xapp_spec >> xsimpl)
              >~ [‘return ()’]
              >- ((* Eof: return () *)
                  xlet ‘POSTv uv. &UNIT_TYPE () uv’ >- (xcon >> xsimpl) >>
                  ‘app p return_v [uv] emp
                     (POSTv v. &COMP p ACTION UNIT_TYPE SNAP (return ()) v)’
                    by (irule return_spec >> simp[]) >>
                  qpat_x_assum ‘app _ return_v _ _ _’ xapp_spec >> xsimpl >>
                  simp[COMP_IMP_COMPd]) >>
              (* any other response: the handler again *)
              xapp >> simp[]) >>
        ‘app p bind_v [ev; k2] emp
           (POSTv v. &COMPd p ACTION UNIT_TYPE SNAP n
                       (bind (emit (Read fd)) G2) v)’
          by (irule bind_spec_d >> simp[wf_emit] >> qexists_tac ‘RESPONSE’ >>
              simp[COMP_IMP_COMPd] >> metis_tac[]) >>
        qpat_x_assum ‘app _ bind_v _ _ _’ xapp_spec >> xsimpl) >>
  ‘app p bind_v [r; k1] emp
     (POSTv v. &COMPd p ACTION UNIT_TYPE SNAP (SUC n) (bind (readable fd) G) v)’
    by (irule bind_guarded_spec_d >> simp[wf_readable, readable_NIL] >>
        qexists_tac ‘UNIT_TYPE’ >>
        simp[COMP_IMP_COMPd] >> metis_tac[]) >>
  qpat_x_assum ‘app _ bind_v _ _ _’ xapp_spec >> xsimpl
QED

(* MAIN: the CakeML echo handler implements the model's handler: for a
   connection fd, handler fd returns a computation value that, round by
   round, emits exactly the model's actions (Read fd, Write fd d, ...) and
   finishes exactly when the model's handler fd does. *)
Theorem handler_spec:
  NUM fd fdv ⇒
  app (p:'ffi ffi_proj) handler_v [fdv] emp
    (POSTv v. &COMP p ACTION UNIT_TYPE SNAP (handler fd) v)
Proof
  strip_tac >> irule app_COMP_of_approxd >> simp[handler_spec_d]
QED

(* ------------------------------------------------------------------------
   The server
   ------------------------------------------------------------------------ *)

(* The server's code up to the outer bind, as for the handler *)
val server_prelude =
  rpt strip_tac >> xcf_with_def server_v_def >>
  simp_tac std_ss [Once server_unfold] >>
  xfun ‘k1’ >>
  xlet ‘POSTv r. &COMP p ACTION UNIT_TYPE SNAP (readable lfd) r’
  >- (xapp_spec readable_spec >> simp[]) >>
  qmatch_goalsub_abbrev_tac ‘bind (readable lfd) G’;

(* MAIN (helper): the CakeML server implements the model's server up to
   any depth n *)
Theorem server_spec_d:
  ∀n lfd lfdv.
    NUM lfd lfdv ⇒
    app (p:'ffi ffi_proj) server_v [lfdv] emp
      (POSTv v. &COMPd p ACTION UNIT_TYPE SNAP n (server lfd) v)
Proof
  Induct
  >- (server_prelude >>
      ‘app p bind_v [r; k1] emp
         (POSTv v. &COMPd p ACTION UNIT_TYPE SNAP 0 (bind (readable lfd) G) v)’
        by (irule bind_guarded_spec_0 >> simp[readable_NIL] >>
            metis_tac[COMP_IMP_COMPd]) >>
      qpat_x_assum ‘app _ bind_v _ _ _’ xapp_spec >> xsimpl) >>
  server_prelude >>
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
              >~ [‘both (handler _) _’]
              >- ((* Accepted fd: the handler alongside the rest *)
                  qmatch_goalsub_rename_tac ‘handler cfd’ >>
                  xlet ‘POSTv sv. &COMPd p ACTION UNIT_TYPE SNAP n
                                    (server lfd) sv’
                  >- (xapp >> simp[]) >>
                  xlet ‘POSTv hv. &COMP p ACTION UNIT_TYPE SNAP (handler cfd) hv’
                  >- (xapp_spec handler_spec >> simp[]) >>
                  ‘app p both_v [hv; sv] emp
                     (POSTv v. &COMPd p ACTION (PAIR_TYPE UNIT_TYPE UNIT_TYPE)
                                 SNAP n (both (handler cfd) (server lfd)) v)’
                    by (irule both_spec_d >> gs[wf_handler, wf_server] >>
                        metis_tac[COMP_IMP_COMPd]) >>
                  xlet ‘POSTv bv. &COMPd p ACTION (PAIR_TYPE UNIT_TYPE UNIT_TYPE)
                                    SNAP n (both (handler cfd) (server lfd)) bv’
                  >- (qpat_x_assum ‘app _ both_v _ _ _’ xapp_spec >> xsimpl) >>
                  xfun ‘f’ >>
                  ‘app p map_v [f; bv] emp
                     (POSTv v. &COMPd p ACTION UNIT_TYPE SNAP n
                                 (map (λp. ()) (both (handler cfd) (server lfd))) v)’
                    by (irule map_spec_d >>
                        simp[wf_both, wf_handler, wf_server] >>
                        qexists_tac ‘PAIR_TYPE UNIT_TYPE UNIT_TYPE’ >> simp[] >>
                        rpt strip_tac >> simp[returns_def] >>
                        qpat_x_assum ‘curried _ _ f ∧ _’ (irule o CONJUNCT2) >>
                        xcon >> xsimpl) >>
                  qpat_x_assum ‘app _ map_v _ _ _’ xapp_spec >> xsimpl) >>
              (* any other response: the server again *)
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

(* MAIN: the CakeML concurrent echo server implements the model's server:
   for a listener lfd, server lfd returns a computation value that, round
   by round, emits exactly the model's actions (Accept lfd, and the
   actions of every accepted connection's handler) and never finishes,
   exactly as the model's server lfd. *)
Theorem server_spec:
  NUM lfd lfdv ⇒
  app (p:'ffi ffi_proj) server_v [lfdv] emp
    (POSTv v. &COMP p ACTION UNIT_TYPE SNAP (server lfd) v)
Proof
  strip_tac >> irule app_COMP_of_approxd >> simp[server_spec_d]
QED
