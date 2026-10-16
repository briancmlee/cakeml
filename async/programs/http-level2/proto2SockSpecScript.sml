(*
  CF specs of the Level 2 protocol server (proto2SockProg), option C,
  design/33 §2.2: the CakeML handler and skeleton implement the socket
  vocabulary versions (srelabel2) of the model's proto_handler_v2 and
  server_v2, for the HTTP instance (identity vocabulary, no queries), given
  the protocol's parser and responder (PROTO_IMPL, as at Level 1).  The
  proofs follow cf-actions' protoSockSpec, with
  the Level 2 library's depth-indexed specs (lib2SockApprox).
*)
Theory proto2SockSpec
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncLevel2 asyncLoop2 echoServer
  libModel libProg loopPollWorld loopPoll relabel
  relabelDist echoSockModel echoSockServer skeletonV
  protoInterface protoV proto2 protoProg protoSockSpec
  lib2SockModel lib2SockProg lib2SockSpec lib2SockApprox relabel2
  proto2SockModel proto2SockProg ml_translator mlstring std_prelude ListProg
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "proto2SockProg"

val eq_string_v_thm =
  MATCH_MP (DISCH_ALL (fetch "mlbasicsProg" "eq_v_thm"))
           (EqualityType_NUM_BOOL |> CONJUNCTS |> el 6);

Theorem bytes_str_chars[local]:
  bytes_str (MAP (n2w o ORD) s : word8 list) = implode s
Proof
  AP_TERM_TAC >> Induct_on ‘s’ >> simp[] >> rpt strip_tac >>
  ‘ORD h < 256’ by simp[ORD_BOUND] >> simp[CHR_ORD]
QED

(* The CakeML relations of the socket program at Level 2 *)
Overload SCOMPI = “COMPI p SACT”
Overload SCOMPId = “COMPId p SACT”

(* return2 (), at any depth *)
val return_unit_tac =
  xlet ‘POSTv uv. &UNIT_TYPE () uv’ >- (xcon >> xsimpl) >>
  ‘app p return2_v [uv] emp
     (POSTv v. &COMPI p SACT UNIT_TYPE SEV SSNAP (return2 ()) v)’
    by (irule return2_specI >> simp[]) >>
  qpat_x_assum ‘app _ return2_v _ _ _’ xapp_spec >> xsimpl >>
  simp[COMPI_IMP_COMPId];

(* emit2 a, for a CakeML action value av *)
fun emit_tac a =
  ‘app p emit2_v [av] emp
     (POSTv v. &COMPI p SACT SRESP SEV SSNAP (emit2 ^a) v)’
    by (irule emit2_specI >> simp[]) >>
  qpat_x_assum ‘app _ emit2_v _ _ _’ xapp_spec >> xsimpl;

Theorem emit2_running[local]:
  wf (emit2 a).run ∧ ((emit2 a).run []).result = NONE
Proof
  simp[emit2_def, wf_emit, emit_def]
QED

Theorem wait_on_running[local]:
  wf (wait_on e q).run ∧ ((wait_on e q).run []).result = NONE
Proof
  simp[wait_on_def, wf_wait, wait_def, first_some_def]
QED

(* A guarded bind2, at any depth n *)
Theorem bind2_guarded_spec_any[local]:
  wf c.run ∧ (c.run []).result = NONE ∧
  COMPI p ACT A EV (SNAPSHOT READY R) c cv ∧
  (0 < n ⇒
   ∀x xv. A x xv ⇒
     returns p gv [xv]
       (COMPId p ACT B EV (SNAPSHOT READY (R : 'r -> v -> bool)) (n - 1) (g x))) ⇒
  app (p:'ffi ffi_proj) bind2_v [cv; gv] emp
    (POSTv v. &COMPId p (ACT : 'act -> v -> bool) B EV (SNAPSHOT READY R) n
                (bind2 c g) v)
Proof
  Cases_on ‘n’ >> rpt strip_tac
  >- (irule bind2_guarded_spec_0 >> simp[] >> metis_tac[COMPI_IMP_COMPId])
  >> irule bind2_guarded_spec_d >> gs[] >> qexists_tac ‘A’ >>
  simp[COMPI_IMP_COMPId]
QED

(* ------------------------------------------------------------------------
   The handler
   ------------------------------------------------------------------------ *)

(* MAIN (helper): the CakeML handler implements the socket-vocabulary Level
   2 handler up to any depth n, for every buffer *)
Theorem sproto_handler2_spec_d:
  ∀n buf bufv fd fdv.
    PROTO_IMPL R P resp parsev respv ∧
    NUM fd fdv ∧ fd < dimword(:64) ∧ LIST_TYPE CHAR buf bufv ⇒
    app (p:'ffi ffi_proj) proto_handler2_v [parsev; respv; fdv; bufv] emp
      (POSTv v. &COMPId p SACT UNIT_TYPE SEV SSNAP n
                  (srelabel2 (hproto2 P resp (fd, buf))) v)
Proof
  completeInduct_on ‘n’ >> rpt strip_tac >>
  gvs[PROTO_IMPL_def] >>
  xcf_with_def proto2SockProgTheory.proto_handler2_v_def >>
  xlet ‘POSTv rv. &PROTOINTERFACE_PRESULT_TYPE R (P.parse buf) rv’
  >- (qpat_assum ‘(_ --> _) P.parse _’ xapp_spec >> simp[]) >>
  ‘fd < dimword(:64)’ by simp[] >>
  pop_assum (fn th =>
    simp_tac std_ss [Once (MATCH_MP sproto_handler2_unfold th)]) >>
  Cases_on ‘P.parse buf’ >>
  gvs[PROTOINTERFACE_PRESULT_TYPE_def]
  >- ((* a complete request: write the response, then the handler on rest *)
      xmatch >>
      qmatch_goalsub_rename_tac ‘resp req’ >>
      qmatch_goalsub_rename_tac ‘hproto2 P resp (fd, rest)’ >>
      xfun ‘k1’ >>
      xlet ‘POSTv sv. &LIST_TYPE CHAR (resp req) sv’
      >- (qpat_assum ‘(_ --> _) resp _’ xapp_spec >> simp[] >> metis_tac[]) >>
      xlet ‘POSTv tv. &STRING_TYPE (implode (resp req)) tv’
      >- (xapp >> simp[]) >>
      qabbrev_tac ‘bs = MAP ((n2w : num -> word8) o ORD) (resp req)’ >>
      xlet ‘POSTv av. &SACT (Write (n2w fd) bs) av’
      >- (xcon >> xsimpl >> gs[SACT_def, Abbr ‘bs’, bytes_str_chars]) >>
      xlet ‘POSTv ev. &COMPI p SACT SRESP SEV SSNAP (emit2 (Write (n2w fd) bs)) ev’
      >- emit_tac “Write (n2w fd) bs” >>
      ‘app p bind2_v [ev; k1] emp
         (POSTv v. &COMPId p SACT UNIT_TYPE SEV SSNAP n
                     (bind2 (emit2 (Write (n2w fd) bs))
                            (λw. srelabel2 (hproto2 P resp (fd, rest)))) v)’
        by (irule bind2_guarded_spec_any >>
            simp[emit2_running] >>
            qexists_tac ‘SRESP’ >> rpt strip_tac >> simp[returns_def] >>
            qpat_x_assum ‘curried _ _ k1 ∧ _’ (irule o CONJUNCT2) >>
            first_x_assum (qspec_then ‘n - 1’ mp_tac) >> simp[] >>
            strip_tac >> xapp >> simp[PROTO_IMPL_def]) >>
      qpat_x_assum ‘app _ bind2_v _ _ _’ xapp_spec >> xsimpl >>
      simp[Abbr ‘bs’])
  >- ((* Incomplete: wait for fd to be readable, read, and continue *)
      xmatch >> xfun ‘k1’ >>
      xlet ‘POSTv r. &COMPI p SACT UNIT_TYPE SEV SSNAP
                       (wait_on (n2w fd) (λs. SOME ())) r’
      >- (xapp_spec sreadable2_spec >> simp[]) >>
      qmatch_goalsub_abbrev_tac ‘bind2 (wait_on _ _) G’ >>
      ‘0 < n ⇒ ∀x xv. UNIT_TYPE x xv ⇒
         returns p k1 [xv] (COMPId p SACT UNIT_TYPE SEV SSNAP (n - 1) (G x))’
        by (rpt strip_tac >> simp[returns_def, Abbr ‘G’] >>
            first_x_assum (qspec_then ‘n - 1’ mp_tac) >> simp[] >> strip_tac >>
            qpat_x_assum ‘curried _ _ k1 ∧ _’ (irule o CONJUNCT2) >>
            xfun ‘k2’ >>
            xlet ‘POSTv av. &SACT (Read (n2w fd) bufsz) av’
            >- (xcon >> xsimpl >> gs[SACT_def, bufsz_def, NUM_def, INT_def]) >>
            xlet ‘POSTv ev. &COMPI p SACT SRESP SEV SSNAP
                              (emit2 (Read (n2w fd) bufsz)) ev’
            >- emit_tac “Read (n2w fd) bufsz” >>
            qmatch_goalsub_abbrev_tac ‘bind2 (emit2 _) G2’ >>
            ‘∀res resv. SRESP res resv ⇒
               returns p k2 [resv]
                 (COMPId p SACT UNIT_TYPE SEV SSNAP (n - 1) (G2 res))’
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
                      gs[] >>
                      xlet ‘POSTv cv. &LIST_TYPE CHAR (MAP (CHR o w2n) bs) cv’
                      >- (xapp >> xsimpl >> qexists_tac ‘bytes_str bs’ >>
                          gs[mlstringTheory.explode_implode]) >>
                      xlet ‘POSTv bv2. &LIST_TYPE CHAR (buf ++ MAP (CHR o w2n) bs) bv2’
                      >- (xapp >> simp[] >> metis_tac[]) >>
                      xapp >> simp[PROTO_IMPL_def]) >>
                  xmatch >> xapp >> simp[PROTO_IMPL_def]) >>
            ‘app p bind2_v [ev; k2] emp
               (POSTv v. &COMPId p SACT UNIT_TYPE SEV SSNAP (n - 1)
                           (bind2 (emit2 (Read (n2w fd) bufsz)) G2) v)’
              by (irule bind2_spec_d >> simp[emit2_running] >>
                  qexists_tac ‘SRESP’ >> simp[COMPI_IMP_COMPId] >> metis_tac[]) >>
            qpat_x_assum ‘app _ bind2_v _ _ _’ xapp_spec >> xsimpl) >>
      ‘app p bind2_v [r; k1] emp
         (POSTv v. &COMPId p SACT UNIT_TYPE SEV SSNAP n
                     (bind2 (wait_on (n2w fd) (λs. SOME ())) G) v)’
        by (irule bind2_guarded_spec_any >> simp[wait_on_running] >>
            metis_tac[]) >>
      qpat_x_assum ‘app _ bind2_v _ _ _’ xapp_spec >> xsimpl) >>
  xmatch >> return_unit_tac
QED

(* MAIN: the CakeML handler implements the model's Level 2 handler, in the
   socket vocabulary, for every protocol *)
Theorem sproto_handler2_spec:
  PROTO_IMPL R P resp parsev respv ∧
  NUM fd fdv ∧ fd < dimword(:64) ∧ LIST_TYPE CHAR buf bufv ⇒
  app (p:'ffi ffi_proj) proto_handler2_v [parsev; respv; fdv; bufv] emp
    (POSTv v. &COMPI p SACT UNIT_TYPE SEV SSNAP
                (srelabel2 (hproto2 P resp (fd, buf))) v)
Proof
  strip_tac >> irule app_COMPI_of_approxd >> simp[] >> gen_tac >>
  metis_tac[sproto_handler2_spec_d]
QED

(* ------------------------------------------------------------------------
   The skeleton
   ------------------------------------------------------------------------ *)

Theorem wf_relabel2_run[local]:
  wf c.run ⇒ wf (relabel2 fa fe fr ie c).run
Proof
  simp[relabel2_def, wf_relabel]
QED

(* SHANDLER2 p h2 hv: the CakeML value hv implements the Level 2 model
   handler h2, in the socket vocabulary, on every connection *)
Definition SHANDLER2_def:
  SHANDLER2 (p:'ffi ffi_proj) h2 hv ⇔
    (∀fd. wf2 (h2 fd)) ∧
    ∀fd fdv. NUM fd fdv ∧ fd < dimword(:64) ⇒
      app p hv [fdv] emp
        (POSTv v. &COMPI p SACT UNIT_TYPE SEV SSNAP (srelabel2 (h2 fd)) v)
End

val sserver2_prelude =
  rpt strip_tac >> xcf_with_def proto2SockProgTheory.sserver2_v_def >>
  ‘lfd < dimword(:64)’ by simp[] >>
  pop_assum (fn th => assume_tac th >>
    simp_tac std_ss [Once (MATCH_MP sserver_v2_unfold th)]) >>
  xfun ‘k1’ >>
  xlet ‘POSTv r. &COMPI p SACT UNIT_TYPE SEV SSNAP
                   (wait_on (n2w lfd) (λs. SOME ())) r’
  >- (xapp_spec sreadable2_spec >> simp[]) >>
  qmatch_goalsub_abbrev_tac ‘bind2 (wait_on _ _) G’;

(* MAIN (helper): the CakeML skeleton implements srelabel2 (server_v2 idV h2
   lfd) up to any depth n, for any handler with a spec *)
Theorem sserver2_spec_d:
  ∀n lfd lfdv.
    SHANDLER2 p h2 hv ∧ NUM lfd lfdv ∧ lfd < dimword(:64) ⇒
    app (p:'ffi ffi_proj) sserver2_v [hv; lfdv] emp
      (POSTv v. &COMPId p SACT UNIT_TYPE SEV SSNAP n
                  (srelabel2 (server_v2 idVu h2 lfd)) v)
Proof
  Induct
  >- (sserver2_prelude >>
      ‘app p bind2_v [r; k1] emp
         (POSTv v. &COMPId p SACT UNIT_TYPE SEV SSNAP 0
                     (bind2 (wait_on (n2w lfd) (λs. SOME ())) G) v)’
        by (irule bind2_guarded_spec_0 >> simp[wait_on_running] >>
            metis_tac[COMPI_IMP_COMPId]) >>
      qpat_x_assum ‘app _ bind2_v _ _ _’ xapp_spec >> xsimpl) >>
  sserver2_prelude >>
  ‘∀fd. wf2 (h2 fd)’ by fs[SHANDLER2_def] >>
  ‘∀x xv. UNIT_TYPE x xv ⇒
          returns p k1 [xv] (COMPId p SACT UNIT_TYPE SEV SSNAP n (G x))’
    by (rpt strip_tac >> simp[returns_def, Abbr ‘G’] >>
        qpat_x_assum ‘curried _ _ k1 ∧ _’ (irule o CONJUNCT2) >>
        xfun ‘k2’ >>
        xlet ‘POSTv av. &SACT (Accept (n2w lfd)) av’
        >- (xcon >> xsimpl >> gs[SACT_def]) >>
        xlet ‘POSTv ev. &COMPI p SACT SRESP SEV SSNAP
                          (emit2 (Accept (n2w lfd))) ev’
        >- emit_tac “Accept (n2w lfd)” >>
        qmatch_goalsub_abbrev_tac ‘bind2 (emit2 _) G2’ >>
        ‘∀res resv. SRESP res resv ⇒
           returns p k2 [resv] (COMPId p SACT UNIT_TYPE SEV SSNAP n (G2 res))’
          by (rpt strip_tac >> simp[returns_def, Abbr ‘G2’] >>
              qpat_x_assum ‘curried _ _ k2 ∧ _’ (irule o CONJUNCT2) >>
              Cases_on ‘res’ >> gvs[SRESP_def]
              >~ [‘TypeStamp «Accepted» _’]
              >- (rename1 ‘OPTION_MAP _ ro’ >> Cases_on ‘ro’ >>
                  gvs[OPTION_TYPE_def] >> xmatch
                  >- (xapp >> simp[])
                  >> rename1 ‘NUM (w2n c) cv’ >>
                  xlet ‘POSTv sv. &COMPId p SACT UNIT_TYPE SEV SSNAP n
                                    (srelabel2 (server_v2 idVu h2 lfd)) sv’
                  >- (xapp >> simp[]) >>
                  xlet ‘POSTv hv'. &COMPI p SACT UNIT_TYPE SEV SSNAP
                                     (srelabel2 (h2 (w2n c))) hv'’
                  >- (‘app p hv [cv] emp
                         (POSTv v. &COMPI p SACT UNIT_TYPE SEV SSNAP
                                     (srelabel2 (h2 (w2n c))) v)’
                        by (gvs[SHANDLER2_def] >> first_x_assum irule >> simp[] >>
                            qspec_then ‘c’ assume_tac w2n_lt >> fs[]) >>
                      qpat_x_assum ‘app _ hv _ _ _’ xapp_spec >> xsimpl) >>
                  ‘app p both2_v [hv'; sv] emp
                     (POSTv v. &COMPId p SACT (PAIR_TYPE UNIT_TYPE UNIT_TYPE) SEV
                                 SSNAP n (both2 (srelabel2 (h2 (w2n c)))
                                                (srelabel2 (server_v2 idVu h2 lfd))) v)’
                    by (irule both2_spec_d >>
                        simp[COMPI_IMP_COMPId] >>
                        ‘wf2 (server_v2 idVu h2 lfd)’ by simp[wf2_server_v2] >>
                        fs[wf2_def, relabel2_def, wf_relabel]) >>
                  xlet ‘POSTv bv. &COMPId p SACT (PAIR_TYPE UNIT_TYPE UNIT_TYPE) SEV
                                    SSNAP n (both2 (srelabel2 (h2 (w2n c)))
                                                   (srelabel2 (server_v2 idVu h2 lfd))) bv’
                  >- (qpat_x_assum ‘app _ both2_v _ _ _’ xapp_spec >> xsimpl) >>
                  xfun ‘f’ >>
                  ‘app p map2_v [f; bv] emp
                     (POSTv v. &COMPId p SACT UNIT_TYPE SEV SSNAP n
                                 (map2 (λp. ()) (both2 (srelabel2 (h2 (w2n c)))
                                                  (srelabel2 (server_v2 idVu h2 lfd)))) v)’
                    by (irule map2_spec_d >>
                        qexists_tac ‘PAIR_TYPE UNIT_TYPE UNIT_TYPE’ >> simp[] >>
                        rpt strip_tac >> simp[returns_def] >>
                        qpat_x_assum ‘curried _ _ f ∧ _’ (irule o CONJUNCT2) >>
                        xcon >> xsimpl) >>
                  qpat_x_assum ‘app _ map2_v _ _ _’ xapp_spec >> xsimpl) >>
              xmatch >> xapp >> simp[]) >>
        ‘app p bind2_v [ev; k2] emp
           (POSTv v. &COMPId p SACT UNIT_TYPE SEV SSNAP n
                       (bind2 (emit2 (Accept (n2w lfd))) G2) v)’
          by (irule bind2_spec_d >> simp[emit2_running] >>
              qexists_tac ‘SRESP’ >> simp[COMPI_IMP_COMPId] >> metis_tac[]) >>
        qpat_x_assum ‘app _ bind2_v _ _ _’ xapp_spec >> xsimpl) >>
  ‘app p bind2_v [r; k1] emp
     (POSTv v. &COMPId p SACT UNIT_TYPE SEV SSNAP (SUC n)
                 (bind2 (wait_on (n2w lfd) (λs. SOME ())) G) v)’
    by (irule bind2_guarded_spec_d >> simp[wait_on_running] >>
        qexists_tac ‘UNIT_TYPE’ >> simp[COMPI_IMP_COMPId] >> metis_tac[]) >>
  qpat_x_assum ‘app _ bind2_v _ _ _’ xapp_spec >> xsimpl
QED

(* MAIN: for any handler value implementing a Level 2 model handler, the
   CakeML skeleton implements srelabel2 (server_v2 idV h2 lfd) *)
Theorem sserver2_spec:
  SHANDLER2 p h2 hv ∧ NUM lfd lfdv ∧ lfd < dimword(:64) ⇒
  app (p:'ffi ffi_proj) sserver2_v [hv; lfdv] emp
    (POSTv v. &COMPI p SACT UNIT_TYPE SEV SSNAP (srelabel2 (server_v2 idVu h2 lfd)) v)
Proof
  strip_tac >> irule app_COMPI_of_approxd >> simp[] >>
  metis_tac[sserver2_spec_d]
QED

(* MAIN: the Level 2 protocol server in CakeML implements the model's
   (HTTP instance), in the socket vocabulary *)
Theorem sproto_server2_spec:
  PROTO_IMPL R P resp parsev respv ∧ NUM lfd lfdv ∧ lfd < dimword(:64) ⇒
  app (p:'ffi ffi_proj) proto_server2_v [parsev; respv; lfdv] emp
    (POSTv v. &COMPI p SACT UNIT_TYPE SEV SSNAP
                (srelabel2 (proto_server_v2 idVu P (K (NONE : unit option))
                              (λr (k : unit option). resp r) lfd)) v)
Proof
  rpt strip_tac >> xcf_with_def proto2SockProgTheory.proto_server2_v_def >>
  xfun ‘h’ >> simp[proto_server_v2_def] >>
  xapp_spec sserver2_spec >>
  simp[SHANDLER2_def, wf2_proto_handler_v2] >> rpt strip_tac >>
  qpat_x_assum ‘curried _ _ h ∧ _’ (irule o CONJUNCT2) >>
  xlet ‘POSTv bv. &LIST_TYPE CHAR "" bv’
  >- (xcon >> xsimpl >> simp[LIST_TYPE_def]) >>
  xapp_spec sproto_handler2_spec >> simp[] >> metis_tac[]
QED
