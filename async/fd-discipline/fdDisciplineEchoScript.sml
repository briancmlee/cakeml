(*
  The verified echo server (EchoSpec's echo_prog) is fd-disciplined in every
  version-1 server world: it polls, accepts, reads and writes only the
  listener and the connections it has accepted.  So version 1's
  idealisation (a connection's fd is usable before it is accepted) does not
  matter for it.
*)
Theory fdDisciplineEcho
Ancestors
  EchoSpec ffiSpikeSocketFFI asyncEchoSemantics asyncM4EchoSpecSafe asyncRunOkGen
  endpointInstances fdDiscipline
Libs
  preamble

(* MAIN *)
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
