(*
  The concurrent echo server in CakeML, in the socket vocabulary of M3's
  event loop, and its CF specs.

     fun handler fd =
       Async.bind (sreadable fd) (fn u =>
       Async.bind (Async.emit (Read fd 4096)) (fn r =>
         case r of
           Got (Some s) =>
             if s = "" then Async.return ()
             else Async.bind (Async.emit (Write fd s)) (fn w => handler fd)
         | _ => handler fd));

     fun server lfd =
       Async.bind (sreadable lfd) (fn u =>
       Async.bind (Async.emit (Accept lfd)) (fn r =>
         case r of
           Accepted (Some c) =>
             async_map (fn p => ()) (async_both (handler c) (server lfd))
         | _ => server lfd));

  This is the code of asyncM4ServerProg (spike/m4-server) with the
  socket actions and responses of asyncM3Loop in place of the model's.
  It implements  relabel sfa sfs (handler fd)  and
  relabel sfa sfs (server lfd)  (asyncM4SockModel): the model's handler
  and server, translated to the socket vocabulary.  The proofs are those
  of asyncM4ServerSpec: induction on the depth, with the guarded bind at
  the outer bind, then the limit lemma.
*)
Theory asyncM4SockServer
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncServer asyncCfActModel
  asyncCfActProg asyncM4Approx asyncM3World asyncM3Prog asyncM3Loop
  asyncM4Relabel asyncM4RelabelDist asyncM4SockModel asyncM4SockApprox
  ml_translator mlstring std_prelude
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncM4SockApprox"

Quote add_cakeml:
  fun has_fd fd l =
    case l of
      [] => False
    | x :: rest => if x = fd then True else has_fd fd rest;

  fun sreadable fd =
    Async.wait (fn w => case w of (rdy, t, res) =>
      if has_fd fd rdy then Some () else None);

  fun handler fd =
    Async.bind (sreadable fd) (fn u =>
    Async.bind (Async.emit (Read fd 4096)) (fn r =>
      case r of
        Got (Some s) =>
          if s = "" then Async.return ()
          else Async.bind (Async.emit (Write fd s)) (fn w => handler fd)
      | _ => handler fd));

  fun server lfd =
    Async.bind (sreadable lfd) (fn u =>
    Async.bind (Async.emit (Accept lfd)) (fn r =>
      case r of
        Accepted (Some c) =>
          async_map (fn p => ()) (async_both (handler c) (server lfd))
      | _ => server lfd));
End

(* The relations: socket actions and responses, snapshots whose ready set
   is a list of fds (asyncM3Loop) *)
Overload SSNAP = “SNAPSHOT SREADY SRESP”

val eq_num_v_thm =
  MATCH_MP (DISCH_ALL (fetch "mlbasicsProg" "eq_v_thm"))
           (EqualityType_NUM_BOOL |> CONJUNCT1);

val eq_string_v_thm =
  MATCH_MP (DISCH_ALL (fetch "mlbasicsProg" "eq_v_thm"))
           (EqualityType_NUM_BOOL |> CONJUNCTS |> el 6);

Theorem has_fd_spec:
  ∀ns v fd fdv. NUM fd fdv ∧ LIST_TYPE NUM ns v ⇒
    app (p:'ffi ffi_proj) has_fd_v [fdv; v] emp (POSTv b. &BOOL (MEM fd ns) b)
Proof
  Induct >> rpt strip_tac >> xcf_with_def (fetch "-" "has_fd_v_def") >>
  gvs[LIST_TYPE_def] >> xmatch
  >- (xcon >> xsimpl >> EVAL_TAC)
  >- (xlet ‘POSTv bv. &BOOL (h = fd) bv’
      >- (xapp_spec eq_num_v_thm >> xsimpl >> metis_tac[]) >>
      xif
      >- (xcon >> xsimpl >> EVAL_TAC)
      >- (xapp >> simp[] >> metis_tac[]))
QED

Theorem MEM_MAP_w2n[local]:
  MEM fd (MAP w2n (fds:word64 list)) ⇔ ∃c. MEM c fds ∧ w2n c = fd
Proof
  simp[MEM_MAP] >> metis_tac[]
QED

(* sreadable fd implements the model's sreadable fd *)
Theorem sreadable_spec:
  NUM fd fdv ⇒
  app (p:'ffi ffi_proj) sreadable_v [fdv] emp
    (POSTv v. &COMP p SACT UNIT_TYPE SSNAP (sreadable fd) v)
Proof
  rpt strip_tac >> xcf_with_def (fetch "-" "sreadable_v_def") >> xfun ‘f’ >>
  simp[sreadable_def] >>
  ‘∀w wv. SSNAP w wv ⇒
     returns p f [wv]
       (OPTION_TYPE UNIT_TYPE
          (if ∃c. c ∈ w.ready ∧ w2n c = fd then SOME () else NONE))’
    by (rpt strip_tac >> simp[returns_def] >>
        qpat_x_assum ‘curried _ _ f ∧ _’ (irule o CONJUNCT2) >>
        gvs[SNAPSHOT_def, SREADY_def] >> xmatch >>
        xlet ‘POSTv bv. &BOOL (MEM fd (MAP w2n fds)) bv’
        >- (xapp >> metis_tac[]) >>
        xif >> rpt (xlet_auto >- (xcon >> xsimpl)) >> xcon >> xsimpl >>
        gvs[MEM_MAP_w2n] >> rw[OPTION_TYPE_def] >> fs[UNIT_TYPE_def] >>
        metis_tac[]) >>
  ‘app p Async_wait_v [f] emp
     (POSTv v. &COMP p SACT UNIT_TYPE SSNAP
        (wait (λs. if ∃c. c ∈ s.ready ∧ w2n c = fd then SOME () else NONE)) v)’
    by (irule Async_wait_spec >> simp[]) >>
  qpat_x_assum ‘app _ Async_wait_v _ _ _’ xapp_spec >> xsimpl
QED

Theorem NUM_w2n_n2w[local]:
  fd < dimword(:64) ⇒ (NUM (w2n (n2w fd : word64)) v ⇔ NUM fd v)
Proof
  simp[]
QED

(* ------------------------------------------------------------------------
   The handler
   ------------------------------------------------------------------------ *)

val handler_prelude =
  rpt strip_tac >> xcf_with_def (fetch "-" "handler_v_def") >>
  simp_tac std_ss [Once shandler_unfold] >>
  xfun ‘k1’ >>
  xlet ‘POSTv r. &COMP p SACT UNIT_TYPE SSNAP (sreadable fd) r’
  >- (xapp_spec sreadable_spec >> simp[]) >>
  qmatch_goalsub_abbrev_tac ‘bind (sreadable fd) G’;

(* MAIN (helper): the CakeML handler implements the socket-vocabulary
   handler up to any depth n *)
Theorem shandler_spec_d:
  ∀n fd fdv.
    NUM fd fdv ∧ fd < dimword(:64) ⇒
    app (p:'ffi ffi_proj) handler_v [fdv] emp
      (POSTv v. &COMPd p SACT UNIT_TYPE SSNAP n (srelabel (handler fd)) v)
Proof
  Induct
  >- (handler_prelude >>
      ‘app p Async_bind_v [r; k1] emp
         (POSTv v. &COMPd p SACT UNIT_TYPE SSNAP 0 (bind (sreadable fd) G) v)’
        by (irule Async_bind_guarded_spec_0 >> simp[sreadable_NIL] >>
            metis_tac[COMP_IMP_COMPd]) >>
      qpat_x_assum ‘app _ Async_bind_v _ _ _’ xapp_spec >> xsimpl) >>
  handler_prelude >>
  ‘∀x xv. UNIT_TYPE x xv ⇒
          returns p k1 [xv] (COMPd p SACT UNIT_TYPE SSNAP n (G x))’
    by (rpt strip_tac >> simp[returns_def, Abbr ‘G’] >>
        qpat_x_assum ‘curried _ _ k1 ∧ _’ (irule o CONJUNCT2) >>
        xfun ‘k2’ >>
        xlet ‘POSTv av. &SACT (Read (n2w fd) bufsz) av’
        >- (xcon >> xsimpl >> gs[SACT_def, bufsz_def, NUM_def, INT_def]) >>
        xlet ‘POSTv ev. &COMP p SACT SRESP SSNAP (emit (Read (n2w fd) bufsz)) ev’
        >- (‘app p Async_emit_v [av] emp
               (POSTv v. &COMP p SACT SRESP SSNAP (emit (Read (n2w fd) bufsz)) v)’
              by (irule Async_emit_spec >> simp[]) >>
            qpat_x_assum ‘app _ Async_emit_v _ _ _’ xapp_spec >> xsimpl) >>
        qmatch_goalsub_abbrev_tac ‘bind (emit _) G2’ >>
        ‘∀res resv. SRESP res resv ⇒
           returns p k2 [resv] (COMPd p SACT UNIT_TYPE SSNAP n (G2 res))’
          by (rpt strip_tac >> simp[returns_def, Abbr ‘G2’] >>
              qpat_x_assum ‘curried _ _ k2 ∧ _’ (irule o CONJUNCT2) >>
              Cases_on ‘res’ >> gvs[SRESP_def]
              >~ [‘TypeStamp «Got» _’]
              >- (rename1 ‘OPTION_MAP _ ro’ >> Cases_on ‘ro’ >> gvs[OPTION_TYPE_def] >> xmatch
                  >- (xapp >> simp[])
                  >> rename1 ‘STRING_TYPE (bytes_str bs) sv’ >>
                  xlet ‘POSTv bv. &BOOL (bs = []) bv’
                  >- (xapp_spec eq_string_v_thm >> xsimpl >>
                      qexists_tac ‘bytes_str bs’ >> simp[] >>
                      Cases_on ‘bs’ >> simp[]) >>
                  xif
                  >- ((* EOF: return () *)
                      gvs[] >>
                      xlet ‘POSTv uv. &UNIT_TYPE () uv’ >- (xcon >> xsimpl) >>
                      ‘app p Async_return_v [uv] emp
                         (POSTv v. &COMP p SACT UNIT_TYPE SSNAP (return ()) v)’
                        by (irule Async_return_spec >> simp[]) >>
                      qpat_x_assum ‘app _ Async_return_v _ _ _’ xapp_spec >>
                      xsimpl >> simp[COMP_IMP_COMPd]) >>
                  (* data bs: write it back, then the handler again *)
                  gs[] >>
                  xfun ‘k3’ >>
                  xlet ‘POSTv av2. &SACT (Write (n2w fd) bs) av2’
                  >- (xcon >> xsimpl >> gs[SACT_def]) >>
                  xlet ‘POSTv ev2. &COMP p SACT SRESP SSNAP
                                     (emit (Write (n2w fd) bs)) ev2’
                  >- (‘app p Async_emit_v [av2] emp
                         (POSTv v. &COMP p SACT SRESP SSNAP
                                     (emit (Write (n2w fd) bs)) v)’
                        by (irule Async_emit_spec >> simp[]) >>
                      qpat_x_assum ‘app _ Async_emit_v _ _ _’ xapp_spec >>
                      xsimpl) >>
                  ‘∀w wv. SRESP w wv ⇒
                     returns p k3 [wv]
                       (COMPd p SACT UNIT_TYPE SSNAP n (srelabel (handler fd)))’
                    by (rpt strip_tac >> simp[returns_def] >>
                        qpat_x_assum ‘curried _ _ k3 ∧ _’ (irule o CONJUNCT2) >>
                        xapp >> simp[]) >>
                  ‘app p Async_bind_v [ev2; k3] emp
                     (POSTv v. &COMPd p SACT UNIT_TYPE SSNAP n
                                 (bind (emit (Write (n2w fd) bs))
                                       (λw. srelabel (handler fd))) v)’
                    by (irule Async_bind_spec_d >> simp[wf_emit] >>
                        qexists_tac ‘SRESP’ >> simp[COMP_IMP_COMPd] >>
                        metis_tac[]) >>
                  qpat_x_assum ‘app _ Async_bind_v _ _ _’ xapp_spec >> xsimpl) >>
              xmatch >> xapp >> simp[]) >>
        ‘app p Async_bind_v [ev; k2] emp
           (POSTv v. &COMPd p SACT UNIT_TYPE SSNAP n
                       (bind (emit (Read (n2w fd) bufsz)) G2) v)’
          by (irule Async_bind_spec_d >> simp[wf_emit] >>
              qexists_tac ‘SRESP’ >> simp[COMP_IMP_COMPd] >> metis_tac[]) >>
        qpat_x_assum ‘app _ Async_bind_v _ _ _’ xapp_spec >> xsimpl) >>
  ‘app p Async_bind_v [r; k1] emp
     (POSTv v. &COMPd p SACT UNIT_TYPE SSNAP (SUC n) (bind (sreadable fd) G) v)’
    by (irule Async_bind_guarded_spec_d >> simp[wf_sreadable, sreadable_NIL] >>
        qexists_tac ‘UNIT_TYPE’ >> simp[COMP_IMP_COMPd] >> metis_tac[]) >>
  qpat_x_assum ‘app _ Async_bind_v _ _ _’ xapp_spec >> xsimpl
QED

(* MAIN: the CakeML echo handler implements the model's handler, in the
   socket vocabulary *)
Theorem shandler_spec:
  NUM fd fdv ∧ fd < dimword(:64) ⇒
  app (p:'ffi ffi_proj) handler_v [fdv] emp
    (POSTv v. &COMP p SACT UNIT_TYPE SSNAP (srelabel (handler fd)) v)
Proof
  strip_tac >> irule app_COMP_of_approxd >> simp[shandler_spec_d]
QED

(* ------------------------------------------------------------------------
   The server
   ------------------------------------------------------------------------ *)

val server_prelude =
  rpt strip_tac >> xcf_with_def (fetch "-" "server_v_def") >>
  simp_tac std_ss [Once sserver_unfold] >>
  xfun ‘k1’ >>
  xlet ‘POSTv r. &COMP p SACT UNIT_TYPE SSNAP (sreadable lfd) r’
  >- (xapp_spec sreadable_spec >> simp[]) >>
  qmatch_goalsub_abbrev_tac ‘bind (sreadable lfd) G’;

(* MAIN (helper): the CakeML server implements the socket-vocabulary
   server up to any depth n *)
Theorem sserver_spec_d:
  ∀n lfd lfdv.
    NUM lfd lfdv ∧ lfd < dimword(:64) ⇒
    app (p:'ffi ffi_proj) server_v [lfdv] emp
      (POSTv v. &COMPd p SACT UNIT_TYPE SSNAP n (srelabel (server lfd)) v)
Proof
  Induct
  >- (server_prelude >>
      ‘app p Async_bind_v [r; k1] emp
         (POSTv v. &COMPd p SACT UNIT_TYPE SSNAP 0 (bind (sreadable lfd) G) v)’
        by (irule Async_bind_guarded_spec_0 >> simp[sreadable_NIL] >>
            metis_tac[COMP_IMP_COMPd]) >>
      qpat_x_assum ‘app _ Async_bind_v _ _ _’ xapp_spec >> xsimpl) >>
  server_prelude >>
  ‘∀x xv. UNIT_TYPE x xv ⇒
          returns p k1 [xv] (COMPd p SACT UNIT_TYPE SSNAP n (G x))’
    by (rpt strip_tac >> simp[returns_def, Abbr ‘G’] >>
        qpat_x_assum ‘curried _ _ k1 ∧ _’ (irule o CONJUNCT2) >>
        xfun ‘k2’ >>
        xlet ‘POSTv av. &SACT (Accept (n2w lfd)) av’
        >- (xcon >> xsimpl >> gs[SACT_def]) >>
        xlet ‘POSTv ev. &COMP p SACT SRESP SSNAP (emit (Accept (n2w lfd))) ev’
        >- (‘app p Async_emit_v [av] emp
               (POSTv v. &COMP p SACT SRESP SSNAP (emit (Accept (n2w lfd))) v)’
              by (irule Async_emit_spec >> simp[]) >>
            qpat_x_assum ‘app _ Async_emit_v _ _ _’ xapp_spec >> xsimpl) >>
        qmatch_goalsub_abbrev_tac ‘bind (emit _) G2’ >>
        ‘∀res resv. SRESP res resv ⇒
           returns p k2 [resv] (COMPd p SACT UNIT_TYPE SSNAP n (G2 res))’
          by (rpt strip_tac >> simp[returns_def, Abbr ‘G2’] >>
              qpat_x_assum ‘curried _ _ k2 ∧ _’ (irule o CONJUNCT2) >>
              Cases_on ‘res’ >> gvs[SRESP_def]
              >~ [‘TypeStamp «Accepted» _’]
              >- (rename1 ‘OPTION_MAP _ ro’ >> Cases_on ‘ro’ >> gvs[OPTION_TYPE_def] >> xmatch
                  >- (xapp >> simp[])
                  >> rename1 ‘NUM (w2n c) cv’ >>
                  xlet ‘POSTv sv. &COMPd p SACT UNIT_TYPE SSNAP n
                                    (srelabel (server lfd)) sv’
                  >- (xapp >> simp[]) >>
                  xlet ‘POSTv hv. &COMP p SACT UNIT_TYPE SSNAP
                                    (srelabel (handler (w2n c))) hv’
                  >- (xapp_spec shandler_spec >> simp[w2n_lt]) >>
                  ‘app p async_both_v [hv; sv] emp
                     (POSTv v. &COMPd p SACT (PAIR_TYPE UNIT_TYPE UNIT_TYPE)
                                 SSNAP n (both (srelabel (handler (w2n c)))
                                               (srelabel (server lfd))) v)’
                    by (irule async_both_spec_d >>
                        gs[wf_shandler, wf_sserver] >>
                        metis_tac[COMP_IMP_COMPd]) >>
                  xlet ‘POSTv bv. &COMPd p SACT (PAIR_TYPE UNIT_TYPE UNIT_TYPE)
                                    SSNAP n (both (srelabel (handler (w2n c)))
                                                  (srelabel (server lfd))) bv’
                  >- (qpat_x_assum ‘app _ async_both_v _ _ _’ xapp_spec >>
                      xsimpl) >>
                  xfun ‘f’ >>
                  ‘app p async_map_v [f; bv] emp
                     (POSTv v. &COMPd p SACT UNIT_TYPE SSNAP n
                                 (map (λp. ()) (both (srelabel (handler (w2n c)))
                                                     (srelabel (server lfd)))) v)’
                    by (irule async_map_spec_d >>
                        simp[wf_both, wf_shandler, wf_sserver] >>
                        qexists_tac ‘PAIR_TYPE UNIT_TYPE UNIT_TYPE’ >> simp[] >>
                        rpt strip_tac >> simp[returns_def] >>
                        qpat_x_assum ‘curried _ _ f ∧ _’ (irule o CONJUNCT2) >>
                        xcon >> xsimpl) >>
                  qpat_x_assum ‘app _ async_map_v _ _ _’ xapp_spec >> xsimpl) >>
              xmatch >> xapp >> simp[]) >>
        ‘app p Async_bind_v [ev; k2] emp
           (POSTv v. &COMPd p SACT UNIT_TYPE SSNAP n
                       (bind (emit (Accept (n2w lfd))) G2) v)’
          by (irule Async_bind_spec_d >> simp[wf_emit] >>
              qexists_tac ‘SRESP’ >> simp[COMP_IMP_COMPd] >> metis_tac[]) >>
        qpat_x_assum ‘app _ Async_bind_v _ _ _’ xapp_spec >> xsimpl) >>
  ‘app p Async_bind_v [r; k1] emp
     (POSTv v. &COMPd p SACT UNIT_TYPE SSNAP (SUC n) (bind (sreadable lfd) G) v)’
    by (irule Async_bind_guarded_spec_d >> simp[wf_sreadable, sreadable_NIL] >>
        qexists_tac ‘UNIT_TYPE’ >> simp[COMP_IMP_COMPd] >> metis_tac[]) >>
  qpat_x_assum ‘app _ Async_bind_v _ _ _’ xapp_spec >> xsimpl
QED

(* MAIN: the CakeML concurrent echo server implements the model's server,
   in the socket vocabulary of M3's event loop *)
Theorem sserver_spec:
  NUM lfd lfdv ∧ lfd < dimword(:64) ⇒
  app (p:'ffi ffi_proj) server_v [lfdv] emp
    (POSTv v. &COMP p SACT UNIT_TYPE SSNAP (srelabel (server lfd)) v)
Proof
  strip_tac >> irule app_COMP_of_approxd >> simp[sserver_spec_d]
QED
