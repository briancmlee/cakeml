(*
  HttpSpec from its peer form, for fd-disciplined programs: the
  useful direction of http_peer_equiv, restricted as v1_instance_disc is.
  An instance of peerV1Disc: safety from the renamed trace (v1_bytes),
  liveness for the responses-to-requests relation (v1_live).
*)
Theory peerV1Http
Ancestors
  llist ffi semantics EchoSpec HttpGetSpec HttpSpec peerSpecForms
  peerInstances peerServers peerBufferKv peerV1Inst peerV1Disc
Libs
  preamble

(* MAIN: a disciplined program meeting the peer HTTP spec with version
   1's calls meets HttpSpec in every version-1 server world that
   connects at most M clients *)
Theorem http_spec_of_peer_disc:
  v1_disciplined lfd prog ∧
  rg_spec (λw. ep_server_world v1_calls lfd a w ∧ no_backpressure w ∧ open_loop w)
    (ep_http_guar files) prog ∧
  server_world lfd sk ∧ sched_connects_le M sk.sched ∧ M + 3 < dimword (:64) ⇒
  ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog (Diverge io) ∧
       http_safe files io ∧ http_live files sk io
Proof
  strip_tac >> drule_all v1_peer_run >> strip_tac >>
  qexists_tac ‘io’ >> fs[ep_http_guar_def] >> conj_tac
  >- (rw[http_safe_def] >> drule_all v1_bytes >> strip_tac >>
      reverse (Cases_on ‘MEM c (opened_fds evs)’) >- simp[] >>
      first_x_assum drule >> strip_tac >>
      fs[sym_safe_def, always_def] >>
      first_x_assum (qspec_then ‘evs’ mp_tac) >> simp[http_safe_def] >>
      disch_then (qspecl_then [‘ren_evs 0 [] evs’, ‘n2w j’, ‘rs’, ‘rest’] mp_tac) >>
      simp[]) >>
  rw[http_live_def] >>
  mp_tac (BETA_RULE (Q.INST [‘P’ |-> ‘λx y. ∀rs. EVERY valid_brequest rs ∧ brequests rs ≼ x ⇒
                                                 bresponses files rs ≼ y’] v1_live)) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
      >- (rpt strip_tac >> irule IS_PREFIX_TRANS >> qexists_tac ‘y’ >> simp[] >>
          qpat_x_assum ‘∀rs. _ ⇒ bresponses files rs ≼ y’ irule >> simp[] >>
          irule IS_PREFIX_TRANS >> qexists_tac ‘x’ >> simp[]) >>
      rpt strip_tac >> ‘rs' = []’ by fs[brequests_nil] >>
      simp[bresponses_def, HttpGetSpecTheory.bytes_def]) >>
  disch_then (qspecl_then [‘c’, ‘n’] strip_assume_tac) >>
  qexists_tac ‘evs’ >> simp[]
QED
