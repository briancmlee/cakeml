(*
  The verified HTTP server with request bodies (HttpSpecBodies'
  http_prog_b) is fd-disciplined in every version-1 server world.
*)
Theory fdDisciplineHttp
Ancestors
  EchoSpec HttpSpecBodies asyncHttpLiveB asyncHttpSemanticsB asyncHeadline
  endpointInstances fdDiscipline
Libs
  preamble

(* MAIN *)
Theorem http_prog_b_disciplined:
  v1_disciplined 3w http_prog_b
Proof
  rw[v1_disciplined_def, server_world_def, GSYM socket_only_ffi_eq] >>
  mp_tac (Q.INST [‘s0’ |-> ‘sk’] http_semantics_prog_bodies) >>
  simp[] >> strip_tac >>
  qexists_tac ‘http_trace_b sk’ >> simp[] >>
  qspecl_then [‘3’, ‘http_server_b demo_files 3’, ‘sk’] mp_tac
    (Q.GENL [‘lfdn’, ‘m’, ‘s0’] rounds_disciplined) >>
  simp[uses_ok_http_b]
QED
