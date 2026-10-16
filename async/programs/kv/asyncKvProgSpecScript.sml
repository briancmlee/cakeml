(*
  The key-value program meets HttpKvSpec's whole specification, safety
  and liveness, with no extra hypotheses:
     kv_prog_spec : kv_spec 3w kv_prog
  Safety and divergence are asyncKvSemantics' kv_semantics_prog (the order
  construction is asyncKvSafe's kv_comp_safe); liveness is asyncKvLive's
  kv_live_rounds on the same trace.  The proof follows asyncHttpSpecB's
  http_prog_b_spec.
*)
Theory asyncKvProgSpec
Ancestors
  EchoSpec HttpSpec HttpSpecBodies HttpKvSpec asyncM4EchoSpecSafe asyncKvMain
  asyncKvSemantics asyncKvLive
Libs
  preamble

(* MAIN: in every server world for listener 3w, the key-value program runs
   forever; at every point there is one order of all the complete requests
   read so far, respecting each connection's order and real time, such that
   what it has written to each connection is a prefix of the responses that
   running the requests in that order on one store gives; and it eventually
   writes the responses to all complete requests each client sends *)
Theorem kv_prog_spec:
  kv_spec 3w kv_prog
Proof
  rw[kv_spec_def, server_world_def, socket_ffi_socket_only_ffi] >>
  mp_tac (Q.INST [‘s0’ |-> ‘sk’] kv_semantics_prog) >>
  simp[] >> strip_tac >>
  qexists_tac ‘kv_trace sk’ >> simp[] >>
  mp_tac (Q.INST [‘s0’ |-> ‘sk’, ‘lfdn’ |-> ‘3’] kv_live_rounds) >>
  simp[]
QED
