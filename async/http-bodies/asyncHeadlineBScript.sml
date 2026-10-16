(*
  The bodies HTTP program, stated in spec/HttpSpecBodies' own
  terms (as headline/asyncHeadline does for HttpSpec).
*)
Theory asyncHeadlineB
Ancestors
  EchoSpec HttpSpec HttpSpecHeaders HttpSpecBodies asyncHeadline asyncHttpMainB
  asyncHttpSemanticsB
Libs
  preamble

(* MAIN: the bodies HTTP program satisfies the safety half of
   HttpSpecBodies' http_spec_b 3w demo_files: in every fair world with one
   listener 3w, it runs forever, and at every point of its I/O trace, on
   every connection, if the bytes read are complete valid requests rs (with
   framed bodies) followed by a rest without a full request, the bytes written
   are a prefix of the responses to rs. *)
Theorem http_prog_b_safe:
  ∀sk. server_world 3w sk ⇒
       ∃io. semantics_prog (init_state (socket_ffi sk)) init_env http_prog_b
              (Diverge io) ∧
            http_safe_b demo_files io
Proof
  rw[server_world_def] >>
  qspec_then ‘sk’ mp_tac (Q.GEN ‘s0’ http_semantics_prog_bodies) >>
  simp[socket_only_ffi_eq] >> metis_tac[]
QED
