(*
  HttpSpec to its peer form, for fd-disciplined programs: the ⇒
  direction of the disciplined http_peer_equiv (peerV1Http has ⇐).
  An instance of peerV1ConvRun via peerV1ReqConv: liveness is
  per request list, for Rel rs y = bresponses files rs ≼ y; safety per fd
  is the peer safety per renamed fd (v1_sym_safe_gen).
*)
Theory peerV1HttpConv
Ancestors
  llist ffi semantics EchoSpec HttpGetSpec HttpHeadersSpec HttpSpec EchoEpisodesSpec
  peerSpecForms peerInstances peerServers peerBufferKv
  peerBufferHttp peerV1Sim peerV1Run peerV1Inst peerV1Conv
  peerV1Http peerV1ConvRun peerV1ReqConv
Libs
  preamble

(* HttpSpec, over the version-1 server worlds connecting at most M
   clients (peerV1Http's http_spec_of_peer_disc concludes this) *)
Definition http_spec_le_def:
  http_spec_le lfd files prog ⇔
    ∀sk M. server_world lfd sk ∧ sched_connects_le M sk.sched ∧ M + 3 < dimword (:64) ⇒
           ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog (Diverge io) ∧
                http_safe files io ∧ http_live files sk io
End

(* A request that must be answered *)
Theorem valid_get_root[local]:
  valid_brequest (Req "GET" "/" "1.1" [] "")
Proof
  EVAL_TAC
QED

Theorem bresponses_nonempty[local]:
  bresponses files [r] ≠ []
Proof
  simp[bresponses_def, HttpGetSpecTheory.bytes_def, print_response_nonempty]
QED

(* MAIN: for an fd-disciplined program, HttpSpec over the version-1
   server worlds connecting at most M clients implies the peer HTTP
   spec with version 1's calls, in every world leaving room for one more
   client *)
Theorem peer_of_http_spec_le:
  v1_disciplined lfd prog ∧ http_spec_le lfd files prog ⇒
  rg_spec (λw. ep_server_world v1_calls lfd a w ∧ no_backpressure w ∧ open_loop w ∧
               nonsat1 lfd a w)
    (ep_http_guar files) prog
Proof
  rw[rg_spec_def] >>
  ‘∀sk N. lifetime_world lfd sk ∧ (∀n. nconn sk n ≤ N) ∧
          LENGTH sk.reserved + N + 3 < dimword (:64) ⇒
          ∃io. semantics_prog (init_state (socket_ffi (v1of2 lfd sk))) init_env prog
                 (Diverge io) ∧ http_safe files io ∧
               acc_live (λx y. ∀rs. EVERY valid_brequest rs ∧ brequests rs ≼ x ⇒
                                    bresponses files rs ≼ y) sk io’
    by (mp_tac (Q.INST [‘Rel’ |-> ‘λrs y. bresponses files rs ≼ y’,
                        ‘Sf’ |-> ‘http_safe files’,
                        ‘r0’ |-> ‘Req "GET" "/" "1.1" [] ""’] req_acc_live) >>
        simp[valid_get_root, bresponses_nonempty] >>
        impl_tac
        >- (rpt conj_tac >>
            TRY (rpt strip_tac >> irule IS_PREFIX_TRANS >> qexists_tac ‘bresponses files rs’ >>
                 simp[bresponses_mono] >> NO_TAC) >>
            TRY (rpt strip_tac >> irule IS_PREFIX_TRANS >> qexists_tac ‘y’ >> simp[] >> NO_TAC) >>
            rpt strip_tac >>
            ‘LENGTH sk.reserved + N + 3 < dimword (:64)’ by fs[] >>
            drule_all v1of2_props >> strip_tac >>
            qpat_x_assum ‘http_spec_le _ _ _’ (mp_tac o REWRITE_RULE [http_spec_le_def]) >>
            disch_then (qspecl_then [‘v1of2 lfd sk’, ‘N’] mp_tac) >>
            impl_tac >- (fs[sched_connects_le_conns] >> decide_tac) >> strip_tac >>
            qexists_tac ‘io’ >> fs[http_live_def] >> metis_tac[]) >>
        simp[]) >>
  drule_at (Pos (el 2)) peer_of_v1_live >> simp[] >>
  disch_then drule_all >> strip_tac >> qexists_tac ‘io’ >>
  simp[ep_http_guar_def] >>
  mp_tac (Q.INST [‘R’ |-> ‘λr w. ∀rs rest. EVERY valid_brequest rs ∧ r = brequests rs ++ rest ∧
                                            no_full_brequest rest ⇒ w ≼ bresponses files rs’]
            v1_sym_safe_gen) >>
  simp[] >>
  impl_tac >- (fs[http_safe_def] >> metis_tac[]) >>
  rw[sym_safe_def, always_def, http_safe_def, LPREFIX_fromList, from_toList] >>
  metis_tac[]
QED

(* MAIN: the disciplined http_peer_equiv *)
Theorem http_peer_equiv_disc_thm:
  ∀lfd a files prog.
    v1_disciplined lfd prog ⇒
    (rg_spec (λw. ep_server_world v1_calls lfd a w ∧ no_backpressure w ∧ open_loop w)
       (ep_http_guar files) prog ⇒ http_spec_le lfd files prog) ∧
    (http_spec_le lfd files prog ⇒
     rg_spec (λw. ep_server_world v1_calls lfd a w ∧ no_backpressure w ∧ open_loop w ∧
                  nonsat1 lfd a w)
       (ep_http_guar files) prog)
Proof
  rpt strip_tac
  >- (REWRITE_TAC[http_spec_le_def] >> rpt strip_tac >>
      drule_all http_spec_of_peer_disc >> simp[])
  >> metis_tac[peer_of_http_spec_le]
QED
