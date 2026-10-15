(*
  The header-tolerant HTTP program meets HttpSpecHeaders' whole
  specification, safety and liveness, with no extra hypotheses:

     http_prog_h_spec : http_spec_h 3w demo_files http_prog_h

  Safety and divergence are cf-actions' (http_semantics_prog_headers,
  spike/http-headers); liveness is asyncHttpLiveH's http_live_h_rounds on
  the same trace.  The proof follows spike/m4-liveness's echo_prog_spec.
*)
Theory asyncHttpSpecH
Ancestors
  EchoSpec HttpSpec HttpSpecHeaders asyncHttpLiveH asyncHttpSemanticsH
  asyncHeadline asyncHeadlineH
Libs
  preamble

(* MAIN: in every server world for listener 3w, the header-tolerant HTTP
   program runs forever, never writes anything but the responses to the
   complete requests it has read, and eventually writes the responses to
   all complete requests each client sends *)
Theorem http_prog_h_spec:
  http_spec_h 3w demo_files http_prog_h
Proof
  rw[http_spec_h_def, server_world_def, GSYM socket_only_ffi_eq] >>
  mp_tac (Q.INST [‘s0’ |-> ‘sk’] http_semantics_prog_headers) >>
  simp[] >> strip_tac >>
  qexists_tac ‘http_trace_h sk’ >> simp[] >>
  mp_tac (Q.INST [‘s0’ |-> ‘sk’, ‘lfdn’ |-> ‘3’, ‘files’ |-> ‘demo_files’]
            http_live_h_rounds) >>
  simp[]
QED
