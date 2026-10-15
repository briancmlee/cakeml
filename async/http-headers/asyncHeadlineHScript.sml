(*
  The header-tolerant HTTP program, stated in spec/HttpSpecHeaders' own
  terms (as headline/asyncHeadline does for HttpSpec).
*)
Theory asyncHeadlineH
Ancestors
  EchoSpec HttpSpec HttpSpecHeaders asyncHeadline asyncHttpMainH
  asyncHttpSemanticsH
Libs
  preamble

(* MAIN: the header-tolerant HTTP program satisfies the safety half of
   HttpSpecHeaders' http_spec_h 3w demo_files: in every fair world with one
   listener 3w, it runs forever, and at every point of its I/O trace, on
   every connection, if the bytes read are complete valid requests rs (with
   any headers) followed by a rest without a full request, the bytes written
   are a prefix of the responses to rs. *)
Theorem http_prog_h_safe:
  ∀sk. server_world 3w sk ⇒
       ∃io. semantics_prog (init_state (socket_ffi sk)) init_env http_prog_h
              (Diverge io) ∧
            http_safe_h demo_files io
Proof
  rw[server_world_def] >>
  qspec_then ‘sk’ mp_tac (Q.GEN ‘s0’ http_semantics_prog_headers) >>
  simp[socket_only_ffi_eq] >> metis_tac[]
QED
