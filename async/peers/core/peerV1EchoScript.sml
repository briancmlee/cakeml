(*
  EchoSpec from its peer form, for fd-disciplined programs: the
  useful direction of echo_peer_equiv, restricted as v1_instance_disc is.
  An instance of peerV1Disc: safety from the renamed trace (v1_bytes),
  liveness for P = (≼) (v1_live).
*)
Theory peerV1Echo
Ancestors
  llist ffi semantics EchoSpec peerSpecForms peerInstances
  peerServers peerV1Inst peerV1Disc
Libs
  preamble

(* MAIN: a disciplined program meeting the peer echo spec with version
   1's calls meets EchoSpec in every version-1 server world that connects
   at most M clients *)
Theorem echo_spec_of_peer_disc:
  v1_disciplined lfd prog ∧
  rg_spec (λw. ep_server_world v1_calls lfd a w ∧ no_backpressure w ∧ open_loop w)
    ep_echo_guar prog ∧
  server_world lfd sk ∧ sched_connects_le M sk.sched ∧ M + 3 < dimword (:64) ⇒
  ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog (Diverge io) ∧
       echo_safe io ∧ echo_live sk io
Proof
  strip_tac >> drule_all v1_endpoint_run >> strip_tac >>
  qexists_tac ‘io’ >> fs[ep_echo_guar_def] >> conj_tac
  >- (rw[echo_safe_def] >> drule_all v1_bytes >> strip_tac >>
      reverse (Cases_on ‘MEM c (opened_fds evs)’) >- simp[] >>
      first_x_assum drule >> strip_tac >>
      fs[sym_safe_def, always_def] >>
      first_x_assum (qspec_then ‘evs’ mp_tac) >> simp[echo_safe_def] >>
      disch_then (qspecl_then [‘ren_evs 0 [] evs’, ‘n2w j’] mp_tac) >> simp[]) >>
  rw[echo_live_def] >>
  mp_tac (BETA_RULE (Q.INST [‘P’ |-> ‘λx y. x ≼ y’] v1_live)) >>
  impl_tac >- (simp[] >> metis_tac[IS_PREFIX_TRANS]) >> simp[]
QED
