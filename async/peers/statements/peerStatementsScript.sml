(*
  L2 (peers): the headline claims, and their proofs (layer L2-04).

  Each server's peer-world spec, over the SIMPLE CLASS of peer worlds:
  server worlds offering the calls cs on listener 3w, without backpressure
  (no_backpressure), open loop (open_loop), and not filling the fd space
  (nonsat1: reserved + M + 4 < 2^64 connections in all; user-approved).  Over all peer worlds they are false for our
  servers (a full «sock_write» under backpressure is a misuse); backpressure,
  fd limits and errors are L3's job.

  All four are PROVED below:
  - peer_echo_episodes_spec: echo_episodes_peer_equiv_thm's converse (under
    nonsat, implied by nonsat1) and L1's echo_episodes_prog_spec;
  - peer_echo_prog_spec, peer_http_prog_spec, peer_kv_prog_spec: L2-03's
    converses peer_of_*_spec_le, with the programs' fd discipline
    (fdDisciplinePrograms) and the L0 headlines.

*)
Theory peerStatements
Ancestors
  llist ffi semantics ml_prog EchoSpec EchoEpisodesSpec HttpSpec KvSpec
  peerWorld peerFair peerSpecForms peerServers
  peerInstances peerEchoEpisodesConv peerV1ConvRun peerV1EchoConv
  peerV1HttpConv peerV1KvConv echoMain echoEpisodesMain echoHeadline
  httpSemantics kvHeadline echoEpisodesHeadline fdDisciplinePrograms
Libs
  preamble

(* nonsat1 is close-v2's, imported from peerV1ConvRun *)

(* The simple class, for version 1's or version 2's calls.  nonsat1 is used
   UNIFORMLY (also for the echo with close, whose converse needs only
   nonsat; nonsat1 is stronger, so that claim still follows) *)
Definition simple_class_def:
  simple_class cs lfd a w ⇔
    ep_server_world cs lfd a w ∧ no_backpressure w ∧ open_loop w ∧ nonsat1 lfd a w
End

(* The echo server (L0's echo_prog), in the peer world *)
Definition peer_echo_prog_claim_def:
  peer_echo_prog_claim ⇔ ∀a. rg_spec (simple_class v1_calls 3w a) ep_echo_guar echo_prog
End

(* The HTTP server; the series' instance is (demo_files, http_prog) *)
Definition peer_http_prog_claim_def:
  peer_http_prog_claim files prog ⇔
    ∀a. rg_spec (simple_class v1_calls 3w a) (ep_http_guar files) prog
End

(* The key-value server; the series' instance is kv_prog *)
Definition peer_kv_prog_claim_def:
  peer_kv_prog_claim prog ⇔ ∀a. rg_spec (simple_class v1_calls 3w a) ep_kv_guar prog
End

(* The echo server with close and fd reuse (L1's echo_episodes_prog) *)
Definition peer_echo_episodes_claim_def:
  peer_echo_episodes_claim ⇔
    ∀a. rg_spec (simple_class v2_calls 3w a) ep_echo2_guar echo_episodes_prog
End

(* ------------------------------------------------------------------------
   The proofs
   ------------------------------------------------------------------------ *)

Theorem simple_class_eta[local]:
  simple_class cs lfd a =
  (λw. ep_server_world cs lfd a w ∧ no_backpressure w ∧ open_loop w ∧ nonsat1 lfd a w)
Proof
  simp[FUN_EQ_THM, simple_class_def]
QED

Theorem nonsat1_nonsat[local]:
  nonsat1 lfd a w ⇒ nonsat lfd a w
Proof
  rw[nonsat1_def, nonsat_def] >> qexists_tac ‘M’ >> simp[]
QED

(* MAIN: the echo server with close and fd reuse, in the peer world *)
Theorem peer_echo_episodes_spec:
  peer_echo_episodes_claim
Proof
  rw[peer_echo_episodes_claim_def] >> irule rg_spec_mono >>
  qexists_tac ‘λw. ep_server_world v2_calls 3w a w ∧ no_backpressure w ∧ open_loop w ∧
                   nonsat 3w a w’ >>
  conj_tac >- (rw[simple_class_def] >> metis_tac[nonsat1_nonsat]) >>
  metis_tac[echo_episodes_peer_equiv_thm, echo_episodes_prog_spec]
QED

(* MAIN: the core echo server, in the peer world *)
Theorem peer_echo_prog_spec:
  peer_echo_prog_claim
Proof
  rw[peer_echo_prog_claim_def, simple_class_eta] >>
  irule peer_of_echo_spec_le >> simp[echo_prog_disciplined] >>
  rw[echo_spec_le_def] >> metis_tac[echo_prog_spec, echo_spec_def]
QED

(* MAIN: the HTTP server, in the peer world *)
Theorem peer_http_prog_spec:
  peer_http_prog_claim demo_files http_prog
Proof
  rw[peer_http_prog_claim_def, simple_class_eta] >>
  irule peer_of_http_spec_le >> simp[http_prog_disciplined] >>
  rw[http_spec_le_def] >> metis_tac[http_prog_spec, http_spec_def]
QED

(* MAIN: the key-value server, in the peer world *)
Theorem peer_kv_prog_spec:
  peer_kv_prog_claim kv_prog
Proof
  rw[peer_kv_prog_claim_def, simple_class_eta] >>
  irule peer_of_kv_spec_le >> simp[kv_prog_disciplined] >>
  rw[kv_spec_le_def] >> metis_tac[kv_prog_spec, kv_spec_def]
QED
