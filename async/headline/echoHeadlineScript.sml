(*
  EchoSpec, in full, for the verified echo program.

  The program is echo_prog (echoMain): main () = run_i ([3], server 3),
  M4's dynamic-interest event loop running the socket-vocabulary echo
  server on listener 3w.  In the sockets-only world its I/O is the
  server's run, echo_trace s0 (echo_semantics_prog, echoSemantics),
  which is safe (echo_prog_safe's ingredients) and live
  (echo_live_rounds, echoLive).
*)
Theory echoHeadline
Ancestors
  EchoSpec socketWorld echoMain echoSemantics
  echoSafeHeadline echoLiveReadSoon echoLive
Libs
  preamble

(* MAIN: the verified echo program meets EchoSpec on listener 3w: in every
   server world it runs forever, never writes on a connection more than it
   has read from it, and eventually echoes everything every client sends *)
Theorem echo_prog_spec:
  echo_spec 3w echo_prog
Proof
  rw[echo_spec_def, server_world_def, socket_ffi_socket_only_ffi]
  >> drule echo_semantics_prog >> strip_tac
  >> qexists_tac ‘echo_trace sk’ >> simp[]
  >> qspecl_then [‘sk’, ‘3’] mp_tac (Q.GENL [‘s0’, ‘lfdn’] echo_live_rounds)
  >> simp[]
QED
