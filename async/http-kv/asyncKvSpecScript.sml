(*
  CF specs of the key-value server (asyncKvProg): kv_server implements
  srelabel (kv_server lfd).

  - the store: kv_delta_al_DELTA (the translated association-list step
    implements kv_delta), for asyncWithStoreSpec's generic with_store_spec;
  - the skeleton and the handler, in the vocabulary Sock sact | Kv query
    (asyncHttpSockSpec / asyncHttpSockSpecB, with the tags);
  - kv_server_spec: the instance.
*)
Theory asyncKvSpec
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncServer asyncCfActModel
  asyncCfActProg asyncM4Approx asyncM3World asyncM3Prog asyncM3Loop
  asyncM4Relabel asyncM4RelabelDist asyncM4SockModel asyncM4SockApprox
  asyncM4SockServer HttpSpec HttpSpecHeaders HttpSpecBodies HttpKvSpec
  asyncHttpParse asyncHttpParseH asyncHttpParseB asyncHttpImplProg
  asyncHttpSockProg asyncHttpSockProgH asyncHttpSockProgB asyncWithStore
  asyncWithStoreStep asyncServerWithK asyncKvHandler asyncKvModel
  asyncKvSockModel asyncKvProg asyncWithStoreSpec ml_translator mlstring std_prelude
Libs
  preamble basis ml_translatorLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncWithStoreSpec"

val eq_string_v_thm =
  MATCH_MP (DISCH_ALL (fetch "mlbasicsProg" "eq_v_thm"))
           (EqualityType_NUM_BOOL |> CONJUNCTS |> el 6);

(* ------------------------------------------------------------------------
   The store
   ------------------------------------------------------------------------ *)

Overload KVAL = “LIST_TYPE (PAIR_TYPE (LIST_TYPE CHAR) (LIST_TYPE CHAR))”

Definition STORE_AL_def:
  STORE_AL st v ⇔ ∃al. al_store st al ∧ KVAL al v
End

(* MAIN: the translated association-list step implements kv_delta *)
Theorem kv_delta_al_DELTA:
  DELTA (p:'ffi ffi_proj) kv_delta STORE_AL KQRY KANS kv_delta_al_v
Proof
  rw[DELTA_def, STORE_AL_def] >>
  xapp_spec (fetch "asyncKvProg" "kv_delta_al_v_thm") >> xsimpl >>
  qexistsl_tac [‘q’, ‘al’] >> simp[] >> rpt strip_tac >>
  Cases_on ‘kv_delta_al al q’ >> gvs[PAIR_TYPE_def] >>
  drule (fetch "asyncKvProg" "kv_delta_al_thm") >> disch_then (qspec_then ‘q’ mp_tac) >>
  simp[] >> strip_tac >> gvs[] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The skeleton and the handler, in the vocabulary of with_store
   ------------------------------------------------------------------------ *)

(* return (), at any depth *)
val return_unit_tac =
  xlet ‘POSTv uv. &UNIT_TYPE () uv’ >- (xcon >> xsimpl) >>
  ‘app p Async_return_v [uv] emp
     (POSTv v. &COMP p KSACT UNIT_TYPE KSSNAP (return ()) v)’
    by (irule Async_return_spec >> simp[]) >>
  qpat_x_assum ‘app _ Async_return_v _ _ _’ xapp_spec >> xsimpl >>
  simp[COMP_IMP_COMPd];

(* emit a, for a CakeML action value av *)
fun emit_tac a av =
  ‘app p Async_emit_v [^av] emp
     (POSTv v. &COMP p KSACT KSRESP KSSNAP (emit ^a) v)’
    by (irule Async_emit_spec >> simp[]) >>
  qpat_x_assum ‘app _ Async_emit_v _ _ _’ xapp_spec >> xsimpl;

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

Theorem bytes_str_chars[local]:
  bytes_str (MAP (n2w o ORD) s : word8 list) = implode s
Proof
  AP_TERM_TAC >> Induct_on ‘s’ >> simp[] >> rpt strip_tac >>
  ‘ORD h < 256’ by simp[ORD_BOUND] >> simp[CHR_ORD]
QED

(* KHANDLER p h hv: hv implements the handler h, on every connection *)
Definition KHANDLER_def:
  KHANDLER (p:'ffi ffi_proj) h hv ⇔
    (∀fd. wf (h fd)) ∧
    ∀fd fdv. NUM fd fdv ∧ fd < dimword(:64) ⇒
      app p hv [fdv] emp (POSTv v. &COMP p KSACT UNIT_TYPE KSSNAP (krelabel (h fd)) v)
End

(* MAIN (helper): the skeleton, up to depth n *)
Theorem kserver_with_k_spec_d:
  ∀n lfd lfdv.
    KHANDLER p h hv ∧ NUM lfd lfdv ∧ lfd < dimword(:64) ⇒
    app (p:'ffi ffi_proj) sserver_with_k_v [hv; lfdv] emp
      (POSTv v. &COMPd p KSACT UNIT_TYPE KSSNAP n (krelabel (server_with_k h lfd)) v)
Proof
  Induct >> rpt strip_tac >> xcf_with_def (fetch "asyncKvProg" "sserver_with_k_v_def") >>
  simp_tac std_ss [Once kserver_with_k_unfold] >>
  xfun ‘k1’ >>
  xlet ‘POSTv r. &COMP p KSACT UNIT_TYPE KSSNAP (sreadable lfd) r’ >>
  TRY (xapp_spec ksreadable_spec >> simp[] >> NO_TAC) >>
  qmatch_goalsub_abbrev_tac ‘bind (sreadable lfd) G’
  >- (‘app p Async_bind_v [r; k1] emp
         (POSTv v. &COMPd p KSACT UNIT_TYPE KSSNAP 0 (bind (sreadable lfd) G) v)’
        by (irule Async_bind_guarded_spec_0 >> simp[sreadable_NIL] >>
            metis_tac[COMP_IMP_COMPd]) >>
      qpat_x_assum ‘app _ Async_bind_v _ _ _’ xapp_spec >> xsimpl) >>
  ‘∀x xv. UNIT_TYPE x xv ⇒
          returns p k1 [xv] (COMPd p KSACT UNIT_TYPE KSSNAP n (G x))’
    by (rpt strip_tac >> simp[returns_def, Abbr ‘G’] >>
        qpat_x_assum ‘curried _ _ k1 ∧ _’ (irule o CONJUNCT2) >>
        xfun ‘k2’ >>
        xlet ‘POSTv av0. &SACT (Accept (n2w lfd)) av0’
        >- (xcon >> xsimpl >> gs[SACT_def]) >>
        xlet ‘POSTv av. &KSACT (Sock (Accept (n2w lfd))) av’
        >- (xcon >> xsimpl >> simp[KACT_def]) >>
        xlet ‘POSTv ev. &COMP p KSACT KSRESP KSSNAP (emit (Sock (Accept (n2w lfd)))) ev’
        >- emit_tac “Sock (Accept (n2w lfd)) : (sact, num # brequest) kact” “av : v” >>
        qmatch_goalsub_abbrev_tac ‘bind (emit _) G2’ >>
        ‘∀res resv. KSRESP res resv ⇒
           returns p k2 [resv] (COMPd p KSACT UNIT_TYPE KSSNAP n (G2 res))’
          by (rpt strip_tac >> simp[returns_def, Abbr ‘G2’] >>
              qpat_x_assum ‘curried _ _ k2 ∧ _’ (irule o CONJUNCT2) >>
              Cases_on ‘res’ >> gvs[KRES_def]
              >- (rename1 ‘SRESP r0 rv’ >>
                  Cases_on ‘r0’ >> gvs[SRESP_def]
                  >~ [‘TypeStamp «Accepted» _’]
                  >- (rename1 ‘OPTION_MAP _ ro’ >> Cases_on ‘ro’ >>
                      gvs[OPTION_TYPE_def] >> xmatch
                      >- (xapp >> simp[])
                      >> rename1 ‘NUM (w2n c) cv’ >>
                      ‘∀fd. wf (h fd)’ by fs[KHANDLER_def] >>
                      xlet ‘POSTv sv. &COMPd p KSACT UNIT_TYPE KSSNAP n
                                        (krelabel (server_with_k h lfd)) sv’
                      >- (xapp >> simp[]) >>
                      xlet ‘POSTv hv'. &COMP p KSACT UNIT_TYPE KSSNAP
                                         (krelabel (h (w2n c))) hv'’
                      >- (‘app p hv [cv] emp
                             (POSTv v. &COMP p KSACT UNIT_TYPE KSSNAP (krelabel (h (w2n c))) v)’
                            by (gvs[KHANDLER_def] >> first_x_assum irule >> simp[] >>
                                qspec_then ‘c’ assume_tac w2n_lt >> fs[]) >>
                          qpat_x_assum ‘app _ hv _ _ _’ xapp_spec >> xsimpl) >>
                      ‘app p async_both_v [hv'; sv] emp
                         (POSTv v. &COMPd p KSACT (PAIR_TYPE UNIT_TYPE UNIT_TYPE)
                                     KSSNAP n (both (krelabel (h (w2n c)))
                                                    (krelabel (server_with_k h lfd))) v)’
                        by (irule async_both_spec_d >>
                            simp[wf_relabel, wf_server_with_k, COMP_IMP_COMPd]) >>
                      xlet ‘POSTv bv. &COMPd p KSACT (PAIR_TYPE UNIT_TYPE UNIT_TYPE)
                                        KSSNAP n (both (krelabel (h (w2n c)))
                                                       (krelabel (server_with_k h lfd))) bv’
                      >- (qpat_x_assum ‘app _ async_both_v _ _ _’ xapp_spec >> xsimpl) >>
                      xfun ‘f’ >>
                      ‘app p async_map_v [f; bv] emp
                         (POSTv v. &COMPd p KSACT UNIT_TYPE KSSNAP n
                                     (map (λp. ()) (both (krelabel (h (w2n c)))
                                                         (krelabel (server_with_k h lfd)))) v)’
                        by (irule async_map_spec_d >>
                            simp[wf_both, wf_relabel, wf_server_with_k] >>
                            qexists_tac ‘PAIR_TYPE UNIT_TYPE UNIT_TYPE’ >> simp[] >>
                            rpt strip_tac >> simp[returns_def] >>
                            qpat_x_assum ‘curried _ _ f ∧ _’ (irule o CONJUNCT2) >>
                            xcon >> xsimpl) >>
                      qpat_x_assum ‘app _ async_map_v _ _ _’ xapp_spec >> xsimpl) >>
                  xmatch >> xapp >> simp[]) >>
              xmatch >> xapp >> simp[]) >>
        ‘app p Async_bind_v [ev; k2] emp
           (POSTv v. &COMPd p KSACT UNIT_TYPE KSSNAP n
                       (bind (emit (Sock (Accept (n2w lfd)))) G2) v)’
          by (irule Async_bind_spec_d >> simp[wf_emit] >>
              qexists_tac ‘KSRESP’ >> simp[COMP_IMP_COMPd] >> metis_tac[]) >>
        qpat_x_assum ‘app _ Async_bind_v _ _ _’ xapp_spec >> xsimpl) >>
  ‘app p Async_bind_v [r; k1] emp
     (POSTv v. &COMPd p KSACT UNIT_TYPE KSSNAP (SUC n) (bind (sreadable lfd) G) v)’
    by (irule Async_bind_guarded_spec_d >> simp[wf_sreadable, sreadable_NIL] >>
        qexists_tac ‘UNIT_TYPE’ >> simp[COMP_IMP_COMPd] >> metis_tac[]) >>
  qpat_x_assum ‘app _ Async_bind_v _ _ _’ xapp_spec >> xsimpl
QED

Theorem kserver_with_k_spec:
  KHANDLER p h hv ∧ NUM lfd lfdv ∧ lfd < dimword(:64) ⇒
  app (p:'ffi ffi_proj) sserver_with_k_v [hv; lfdv] emp
    (POSTv v. &COMP p KSACT UNIT_TYPE KSSNAP (krelabel (server_with_k h lfd)) v)
Proof
  strip_tac >> irule app_COMP_of_approxd >> simp[] >>
  metis_tac[kserver_with_k_spec_d]
QED

(* MAIN (helper): the handler, up to depth n *)
Theorem kkv_handler_spec_d:
  ∀n buf bufv fd fdv.
    NUM fd fdv ∧ fd < dimword(:64) ∧ LIST_TYPE CHAR buf bufv ⇒
    app (p:'ffi ffi_proj) kv_handler_v [fdv; bufv] emp
      (POSTv v. &COMPd p KSACT UNIT_TYPE KSSNAP n (krelabel (kv_handler (fd, buf))) v)
Proof
  completeInduct_on ‘n’ >> rpt strip_tac >>
  xcf_with_def (fetch "asyncKvProg" "kv_handler_v_def") >>
  xlet ‘POSTv rv. &ASYNCHTTPPARSEB_BPARSE_RESULT_TYPE (parse_brequest buf) rv’
  >- (xapp >> simp[]) >>
  simp_tac std_ss [Once kkv_handler_unfold] >>
  Cases_on ‘parse_brequest buf’ >>
  gvs[ASYNCHTTPPARSEB_BPARSE_RESULT_TYPE_def]
  >- ((* a complete request: query the store, write the printed answer *)
      rename1 ‘BComplete req rest’ >> xmatch >>
      xfun ‘k1’ >>
      xlet ‘POSTv qv. &KQRY (fd, req) qv’
      >- (xcon >> xsimpl >> simp[PAIR_TYPE_def]) >>
      xlet ‘POSTv av. &KSACT (Kv (fd, req)) av’
      >- (xcon >> xsimpl >> simp[KACT_def]) >>
      xlet ‘POSTv ev. &COMP p KSACT KSRESP KSSNAP (emit (Kv (fd, req))) ev’
      >- emit_tac “Kv (fd, req) : (sact, num # brequest) kact” “av : v” >>
      qmatch_goalsub_abbrev_tac ‘bind (emit _) G’ >>
      ‘app p Async_bind_v [ev; k1] emp
         (POSTv v. &COMPd p KSACT UNIT_TYPE KSSNAP n (bind (emit (Kv (fd, req))) G) v)’
        by (irule Async_bind_guarded_spec_any >>
            simp[wf_emit, emit_needs_snapshot] >>
            qexists_tac ‘KSRESP’ >> rpt strip_tac >> simp[returns_def, Abbr ‘G’] >>
            qpat_x_assum ‘curried _ _ k1 ∧ _’ (irule o CONJUNCT2) >>
            Cases_on ‘x’ >> gvs[KRES_def] >> xmatch
            >- return_unit_tac >>
            rename1 ‘KANS ans ansv’ >>
            xfun ‘k2’ >>
            xlet ‘POSTv sv. &LIST_TYPE CHAR (sprint_response ans) sv’
            >- (xapp >> simp[]) >>
            xlet ‘POSTv tv. &STRING_TYPE (implode (sprint_response ans)) tv’
            >- (xapp >> simp[]) >>
            qabbrev_tac ‘bs = MAP ((n2w : num -> word8) o ORD) (print_response ans)’ >>
            xlet ‘POSTv av0. &SACT (Write (n2w fd) bs) av0’
            >- (xcon >> xsimpl >> gs[SACT_def, Abbr ‘bs’, bytes_str_chars,
                                     sprint_response_thm]) >>
            xlet ‘POSTv aw. &KSACT (Sock (Write (n2w fd) bs)) aw’
            >- (xcon >> xsimpl >> simp[KACT_def]) >>
            xlet ‘POSTv ev2. &COMP p KSACT KSRESP KSSNAP (emit (Sock (Write (n2w fd) bs))) ev2’
            >- emit_tac “Sock (Write (n2w fd) bs) : (sact, num # brequest) kact” “aw : v” >>
            ‘app p Async_bind_v [ev2; k2] emp
               (POSTv v. &COMPd p KSACT UNIT_TYPE KSSNAP (n - 1)
                   (bind (emit (Sock (Write (n2w fd) bs)))
                         (λw. krelabel (kv_handler (fd, rest)))) v)’
              by (irule Async_bind_guarded_spec_any >> simp[wf_emit, emit_needs_snapshot] >>
                  qexists_tac ‘KSRESP’ >> rpt strip_tac >> simp[returns_def] >>
                  qpat_x_assum ‘curried _ _ k2 ∧ _’ (irule o CONJUNCT2) >>
                  first_x_assum (qspec_then ‘n - 1 - 1’ mp_tac) >> simp[] >>
                  strip_tac >> xapp >> simp[]) >>
            qpat_x_assum ‘app _ Async_bind_v [ev2; _] _ _’ xapp_spec >> xsimpl >>
            simp[Abbr ‘bs’]) >>
      qpat_x_assum ‘app _ Async_bind_v _ _ _’ xapp_spec >> xsimpl)
  >- ((* incomplete: wait for fd to be readable, read, and continue *)
      xmatch >> xfun ‘k1’ >>
      xlet ‘POSTv r. &COMP p KSACT UNIT_TYPE KSSNAP (sreadable fd) r’
      >- (xapp_spec ksreadable_spec >> simp[]) >>
      qmatch_goalsub_abbrev_tac ‘bind (sreadable fd) G’ >>
      ‘0 < n ⇒ ∀x xv. UNIT_TYPE x xv ⇒
         returns p k1 [xv] (COMPd p KSACT UNIT_TYPE KSSNAP (n - 1) (G x))’
        by (rpt strip_tac >> simp[returns_def, Abbr ‘G’] >>
            first_x_assum (qspec_then ‘n - 1’ mp_tac) >> simp[] >> strip_tac >>
            qpat_x_assum ‘curried _ _ k1 ∧ _’ (irule o CONJUNCT2) >>
            xfun ‘k2’ >>
            xlet ‘POSTv av0. &SACT (Read (n2w fd) bufsz) av0’
            >- (xcon >> xsimpl >> gs[SACT_def, bufsz_def, NUM_def, INT_def]) >>
            xlet ‘POSTv av. &KSACT (Sock (Read (n2w fd) bufsz)) av’
            >- (xcon >> xsimpl >> simp[KACT_def]) >>
            xlet ‘POSTv ev. &COMP p KSACT KSRESP KSSNAP (emit (Sock (Read (n2w fd) bufsz))) ev’
            >- emit_tac “Sock (Read (n2w fd) bufsz) : (sact, num # brequest) kact” “av : v” >>
            qmatch_goalsub_abbrev_tac ‘bind (emit _) G2’ >>
            ‘∀res resv. KSRESP res resv ⇒
               returns p k2 [resv]
                 (COMPd p KSACT UNIT_TYPE KSSNAP (n - 1) (G2 res))’
              by (rpt strip_tac >> simp[returns_def, Abbr ‘G2’] >>
                  qpat_x_assum ‘curried _ _ k2 ∧ _’ (irule o CONJUNCT2) >>
                  Cases_on ‘res’ >> gvs[KRES_def]
                  >- (rename1 ‘SRESP r0 rv’ >> Cases_on ‘r0’ >> gvs[SRESP_def]
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
                          gs[] >>
                          xlet ‘POSTv cv. &LIST_TYPE CHAR (MAP (CHR o w2n) bs) cv’
                          >- (xapp >> xsimpl >> qexists_tac ‘bytes_str bs’ >>
                              gs[mlstringTheory.explode_implode]) >>
                          xlet ‘POSTv bv2. &LIST_TYPE CHAR (buf ++ MAP (CHR o w2n) bs) bv2’
                          >- (xapp >> simp[] >> metis_tac[]) >>
                          xapp >> simp[]) >>
                      xmatch >> xapp >> simp[]) >>
                  xmatch >> xapp >> simp[]) >>
            ‘app p Async_bind_v [ev; k2] emp
               (POSTv v. &COMPd p KSACT UNIT_TYPE KSSNAP (n - 1)
                           (bind (emit (Sock (Read (n2w fd) bufsz))) G2) v)’
              by (irule Async_bind_spec_d >> simp[wf_emit] >>
                  qexists_tac ‘KSRESP’ >> simp[COMP_IMP_COMPd] >> metis_tac[]) >>
            qpat_x_assum ‘app _ Async_bind_v _ _ _’ xapp_spec >> xsimpl) >>
      ‘app p Async_bind_v [r; k1] emp
         (POSTv v. &COMPd p KSACT UNIT_TYPE KSSNAP n (bind (sreadable fd) G) v)’
        by (irule Async_bind_guarded_spec_any >> simp[wf_sreadable, sreadable_NIL] >>
            metis_tac[]) >>
      qpat_x_assum ‘app _ Async_bind_v _ _ _’ xapp_spec >> xsimpl) >>
  (* invalid: stop *)
  xmatch >> return_unit_tac
QED

Theorem kkv_handler_spec:
  NUM fd fdv ∧ fd < dimword(:64) ∧ LIST_TYPE CHAR buf bufv ⇒
  app (p:'ffi ffi_proj) kv_handler_v [fdv; bufv] emp
    (POSTv v. &COMP p KSACT UNIT_TYPE KSSNAP (krelabel (kv_handler (fd, buf))) v)
Proof
  strip_tac >> irule app_COMP_of_approxd >> simp[kkv_handler_spec_d]
QED

(* MAIN: the inner server *)
Theorem kkv_inner_spec:
  NUM lfd lfdv ∧ lfd < dimword(:64) ⇒
  app (p:'ffi ffi_proj) kv_inner_v [lfdv] emp
    (POSTv v. &COMP p KSACT UNIT_TYPE KSSNAP (krelabel (kv_inner lfd)) v)
Proof
  rpt strip_tac >> xcf_with_def (fetch "asyncKvProg" "kv_inner_v_def") >> xfun ‘h’ >>
  simp[kv_inner_def] >> xapp_spec kserver_with_k_spec >>
  simp[KHANDLER_def, wf_kv_handler] >> rpt strip_tac >>
  qpat_x_assum ‘curried _ _ h ∧ _’ (irule o CONJUNCT2) >>
  xlet ‘POSTv bv. &LIST_TYPE CHAR "" bv’
  >- (xcon >> xsimpl >> simp[LIST_TYPE_def]) >>
  xapp_spec kkv_handler_spec >> simp[]
QED

(* MAIN: the key-value server implements the model's kv_server, in the
   socket vocabulary *)
Theorem kv_server_spec:
  NUM lfd lfdv ∧ lfd < dimword(:64) ⇒
  app (p:'ffi ffi_proj) kv_server_v [lfdv] emp
    (POSTv v. &COMP p SACT UNIT_TYPE SSNAP (srelabel (kv_server lfd)) v)
Proof
  rpt strip_tac >> xcf_with_def (fetch "asyncKvProg" "kv_server_v_def") >>
  simp[srelabel_kv_server] >>
  xlet ‘POSTv cv. &COMP p KSACT UNIT_TYPE KSSNAP (krelabel (kv_inner lfd)) cv’
  >- (xapp_spec kkv_inner_spec >> simp[]) >>
  xlet ‘POSTv sv. &KVAL [] sv’
  >- (xcon >> xsimpl >> simp[LIST_TYPE_def]) >>
  xapp_spec with_store_spec >> simp[wf_kkv_inner] >>
  qexistsl [‘KANS’, ‘KQRY’, ‘STORE_AL’] >>
  simp[kv_delta_al_DELTA, STORE_AL_def, al_store_def] >>
  qexists_tac ‘[]’ >> simp[]
QED
