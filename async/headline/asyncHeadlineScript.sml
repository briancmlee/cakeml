(*
  The headline theorems, stated in the trusted specs' own terms
  (spec/EchoSpecScript.sml, spec/HttpSpecScript.sml).

  echo_spec lfd prog and http_spec lfd files prog say: in every fair world
  with one listener lfd, prog runs forever, and its I/O trace is safe and
  live.  Proved here: the SAFETY half of each, for the verified programs,
  in exactly the spec's world (socket_ffi sk, server_world 3w sk).  The
  liveness halves (echo_live, http_live) are pending.

  The only new fact is that the sockets-only FFI used by the proofs
  (ffiSpikeSocketDiv's socket_only_ffi) is EchoSpec's socket_ffi.
*)
Theory asyncHeadline
Ancestors
  EchoSpec HttpSpec ffiSpikeSocketFFI ffiSpikeSocketWorld ffiSpikeSocketDiv
  asyncEchoMain asyncEchoSemantics asyncHttpMain asyncHttpSemantics
Libs
  preamble

(* The proofs' sockets-only oracle and FFI are the spec's *)
Theorem socket_only_oracle_eq:
  socket_only_oracle = socket_oracle
Proof
  simp[FUN_EQ_THM] >> Cases >>
  rw[socket_only_oracle_def, socket_oracle_def, socket_name_def, socket_fn_def,
     socket_call_def, sockets_ffi_part_def, socket_names_def] >>
  gvs[]
QED

Theorem socket_only_ffi_eq:
  socket_only_ffi = socket_ffi
Proof
  simp[FUN_EQ_THM, socket_only_ffi_def, socket_ffi_def, socket_only_oracle_eq]
QED

(* MAIN: the echo program satisfies the safety half of EchoSpec's
   echo_spec 3w: in every fair world with one listener 3w (nothing pending,
   no connections), it runs forever, and at every point of its I/O trace,
   on every connection, the bytes it has written are a prefix of the bytes
   it has read. *)
Theorem echo_prog_safe:
  ∀sk. server_world 3w sk ⇒
       ∃io. semantics_prog (init_state (socket_ffi sk)) init_env echo_prog
              (Diverge io) ∧
            echo_safe io
Proof
  rw[server_world_def] >>
  qspec_then ‘sk’ mp_tac (Q.GEN ‘s0’ echo_semantics_prog) >>
  simp[socket_only_ffi_eq] >> metis_tac[]
QED

(* MAIN: the HTTP program satisfies the safety half of HttpSpec's
   http_spec 3w demo_files: in every fair world with one listener 3w, it
   runs forever, and at every point of its I/O trace, on every connection,
   if the bytes read are complete valid requests rs followed by a rest
   without a full request, the bytes written are a prefix of the responses
   to rs. *)
Theorem http_prog_safe:
  ∀sk. server_world 3w sk ⇒
       ∃io. semantics_prog (init_state (socket_ffi sk)) init_env http_prog
              (Diverge io) ∧
            http_safe demo_files io
Proof
  rw[server_world_def] >>
  qspec_then ‘sk’ mp_tac (Q.GEN ‘s0’ http_semantics_prog) >>
  simp[socket_only_ffi_eq] >> metis_tac[]
QED
