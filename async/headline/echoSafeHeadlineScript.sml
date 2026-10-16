(*
  The safety half of EchoSpec for the verified echo program, in EchoSpec's
  own form.

  The program is echo_prog of echoMain (spike/runnable): the basis,
  the Socket module, the Async library, M4's dynamic-interest event loop
  and the socket-vocabulary echo server, then main () =
  run_i ([3], server 3).  Its divergence and safety in the sockets-only
  world are echo_semantics_prog (echoSemantics, spike/machine-code).
  What is added here:
   - EchoSpec's oracle socket_ffi is that sockets-only world
     (socket_ffi_socket_only_ffi);
   - EchoSpec's server_world gives the initial world shape the theorem
     needs (one listener 3w, nothing pending, no connections).
*)
Theory echoSafeHeadline
Ancestors
  EchoSpec socketWorld composedWorld socketDiv
  echoMain echoSemantics
Libs
  preamble

(* EchoSpec's oracle is the socket worker's sockets-only oracle *)
Theorem socket_ffi_socket_only_ffi:
  socket_ffi sk = socket_only_ffi sk
Proof
  simp[socket_ffi_def, socket_only_ffi_def, FUN_EQ_THM] >> Cases >>
  simp[socket_oracle_def, socket_only_oracle_def, socket_name_def] >>
  rw[socket_fn_def, socket_call_def, sockets_ffi_part_def, socket_names_def] >>
  gvs[]
QED

(* MAIN: the safety half of EchoSpec for the verified echo program: in
   every server world for listener 3w, the program runs forever, and at
   every point of the run and on every connection, the bytes it has
   written are a prefix of the bytes it has read. *)
Theorem echo_prog_safe:
  server_world 3w sk ⇒
  ∃io. semantics_prog (init_state (socket_ffi sk)) init_env echo_prog
         (Diverge io) ∧ echo_safe io
Proof
  rw[server_world_def, socket_ffi_socket_only_ffi] >>
  drule_all echo_semantics_prog >> metis_tac[]
QED
