(*
  The key-value program, in spec/HttpKvSpec's own terms.
*)
Theory asyncKvHeadline
Ancestors
  EchoSpec HttpSpec HttpSpecBodies HttpKvSpec asyncM4EchoSpecSafe asyncKvMain
  asyncKvSemantics
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
