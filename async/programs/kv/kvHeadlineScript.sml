(*
  The key-value program meets KvSpec's whole specification, safety
  and liveness, with no extra hypotheses:
     kv_prog_spec : kv_spec 3w kv_prog
  kv_prog_safe: safety alone.  Safety and divergence are
  kvSemantics' kv_semantics_prog (the order
  construction is kvSafe's kv_comp_safe); liveness is kvLive's
  kv_live_rounds on the same trace.  The proof follows asyncHttpSpecB's
  http_prog_b_spec.
*)
Theory kvHeadline
Ancestors
  EchoSpec HttpGetSpec HttpSpec KvSpec echoSafeHeadline kvMain
  kvSemantics kvLive
Libs
  preamble

(* MAIN: the key-value program satisfies the safety half of
   kv_spec 3w kv_prog: in every fair world with one listener 3w, it runs
   forever, and its I/O trace is linearizable (kv_safe): at every point
   there is one order of all complete requests, respecting each
   connection's order and real time, whose sequential run on one store
   gives every connection a prefix of what the server wrote to it. *)
Theorem kv_prog_safe:
  ∀sk. server_world 3w sk ⇒
       ∃io. semantics_prog (init_state (socket_ffi sk)) init_env kv_prog
              (Diverge io) ∧
            kv_safe io
Proof
  rw[server_world_def] >>
  qspec_then ‘sk’ mp_tac (Q.GEN ‘s0’ kv_semantics_prog) >>
  simp[GSYM socket_ffi_socket_only_ffi] >> metis_tac[]
QED


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
