(*
  The series' core-level programs are fd-disciplined: in every core server
  world, the run touches only the listener and the fds it has accepted
  (v1_disciplined, peerInstances).  This is the hypothesis under which the
  core specs and their peer forms are equivalent (L2-03's *_peer_equiv_disc
  theorems).

  Each proof is rounds_disciplined (fdDiscipline: the trace of a uses_ok
  server, run by the polling loop, is fd-disciplined) applied to the
  program's semantics theorem and the server's uses_ok fact.
*)
Theory fdDisciplinePrograms
Ancestors
  EchoSpec socketWorld echoSemantics echoSafeHeadline skeletonRunOk skeletonLive
  protoServer protoLive httpProto httpSemantics kvModel kvSemantics
  peerInstances fdDiscipline
Libs
  preamble

Theorem echo_prog_disciplined:
  v1_disciplined 3w echo_prog
Proof
  rw[v1_disciplined_def, server_world_def, socket_ffi_socket_only_ffi] >>
  drule echo_semantics_prog >> strip_tac >>
  qexists_tac ‘echo_trace sk’ >> simp[] >>
  qspecl_then [‘3’, ‘server 3’, ‘sk’] mp_tac
    (Q.GENL [‘lfdn’, ‘m’, ‘s0’] rounds_disciplined) >>
  simp[uses_ok_server]
QED

Theorem http_prog_disciplined:
  v1_disciplined 3w http_prog
Proof
  rw[v1_disciplined_def, server_world_def, socket_ffi_socket_only_ffi] >>
  drule_all http_semantics_prog_pb >> strip_tac >>
  qexists_tac ‘proto_trace P_b resp_b sk’ >> simp[] >>
  qspecl_then [‘3’, ‘proto_server P_b resp_b 3’, ‘sk’] mp_tac
    (Q.GENL [‘lfdn’, ‘m’, ‘s0’] rounds_disciplined) >>
  simp[proto_server_def] >> disch_then irule >>
  irule uses_ok_sw >> irule hok_proto >> simp[proto_ok_b]
QED

Theorem kv_prog_disciplined:
  v1_disciplined 3w kv_prog
Proof
  rw[v1_disciplined_def, server_world_def, socket_ffi_socket_only_ffi] >>
  drule kv_semantics_prog >> strip_tac >>
  qexists_tac ‘kv_trace sk’ >> simp[] >>
  qspecl_then [‘3’, ‘kv_server 3’, ‘sk’] mp_tac
    (Q.GENL [‘lfdn’, ‘m’, ‘s0’] rounds_disciplined) >>
  simp[kv_server_uses_ok]
QED
