(*
  The bodies HTTP program meets HttpSpecBodies' whole
  specification, safety and liveness, with no extra hypotheses:

     http_prog_b_spec : http_spec_b 3w demo_files http_prog_b

  Safety and divergence are cf-actions' (http_semantics_prog_bodies,
  spike/http-headers); liveness is asyncHttpLiveB's http_live_b_rounds on
  the same trace.  The proof follows spike/m4-liveness's echo_prog_spec.
*)
Theory asyncHttpSpecB
Ancestors
  EchoSpec HttpSpec HttpSpecHeaders HttpSpecBodies asyncHttpLiveB asyncHttpSemanticsB
  asyncHeadline asyncHeadlineB
Libs
  preamble

(* MAIN: in every server world for listener 3w, the bodies HTTP
   program runs forever, never writes anything but the responses to the
   complete requests it has read, and eventually writes the responses to
   all complete requests each client sends *)
Theorem http_prog_b_spec:
  http_spec_b 3w demo_files http_prog_b
Proof
  rw[http_spec_b_def, server_world_def, GSYM socket_only_ffi_eq] >>
  mp_tac (Q.INST [‘s0’ |-> ‘sk’] http_semantics_prog_bodies) >>
  simp[] >> strip_tac >>
  qexists_tac ‘http_trace_b sk’ >> simp[] >>
  mp_tac (Q.INST [‘s0’ |-> ‘sk’, ‘lfdn’ |-> ‘3’, ‘files’ |-> ‘demo_files’]
            http_live_b_rounds) >>
  simp[]
QED
