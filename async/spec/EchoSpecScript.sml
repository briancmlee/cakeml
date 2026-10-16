(*
  EchoSpec: the final statement of what the verified echo server does.

  This file is the TRUSTED SURFACE: to believe the final theorem, a reader
  needs to read this file (and the socket model it imports), nothing
  else.  In particular, the async library's model, its CF refinement
  layer (STEPA), the event loop and the scheduler do NOT appear here.

  What is trusted, in order:
   1. CakeML's source semantics (semantics_prog) and its I/O events
      (ffi$io_event): imported from CakeML.
   2. The socket world (socketWorld, imported): listeners,
      connections, a schedule of future arrivals, and the byte-level FFI
      functions «sock_poll», «sock_accept», «sock_read», «sock_write».
      (Trust base: the C implementation of these four FFI calls behaves
      like this model.)
   3. The fairness assumption on schedules, sched_wf (socketFair,
      imported): the world never drops an arrival.
   4. Below: the sockets-only FFI oracle, the per-connection projections
      of raw I/O events, the data a client sends, and the statement.

  Nothing here is proved; echo_spec is a definition (a proposition about
  a program).  The theorem to prove is  echo_spec 3w echo_prog.
  EchoSpecBiteScript.sml shows that the statement rules out plausible
  bugs and that its assumptions are satisfiable.
*)
Theory EchoSpec
Ancestors
  semantics ffi llist ml_prog socketWorld socketFair
Libs
  preamble

(* ------------------------------------------------------------------------
   The world: a sockets-only FFI, driven by the socket model
   ------------------------------------------------------------------------ *)

(* The model's FFI function for each of the four socket calls *)
Definition socket_fn_def:
  socket_fn n =
    if n = «sock_poll» then SOME ffi_sock_poll
    else if n = «sock_accept» then SOME ffi_sock_accept
    else if n = «sock_read» then SOME ffi_sock_read
    else if n = «sock_write» then SOME ffi_sock_write
    else NONE
End

(* The oracle: a socket call runs the model's function on the world's state;
   anything else (or a failing call) ends the program with an FFI failure. *)
Definition socket_oracle_def:
  socket_oracle (ExtCall n) (sk:sockets) conf bytes =
    (case socket_fn n of
     | SOME f =>
         (case f conf bytes sk of
          | SOME (FFIreturn bytes' sk') => Oracle_return sk' bytes'
          | _ => Oracle_final FFI_failed)
     | NONE => Oracle_final FFI_failed) ∧
  socket_oracle _ sk conf bytes = Oracle_final FFI_failed
End

(* The initial FFI state: world sk, no I/O yet *)
Definition socket_ffi_def:
  socket_ffi sk = <| oracle := socket_oracle; ffi_state := sk; io_events := [] |>
End

(* The worlds the servers are run in: one listener lfd with nothing
   pending, no connections yet, and a fair schedule. *)
Definition server_world_def:
  server_world lfd sk ⇔
    sk.listeners = [(lfd, [])] ∧ sk.conns = [] ∧ sched_wf sk
End

(* ------------------------------------------------------------------------
   Per-connection projections of raw I/O events
   ------------------------------------------------------------------------ *)

(* The bytes a «sock_read» event on connection c returned: the buffer came
   back as status 0 (data), an 8-byte length k, then k data bytes. *)
Definition event_read_def:
  event_read c (IO_event (ExtCall n) conf bytes) =
    (let out = MAP SND bytes in
     if n = «sock_read» ∧ LENGTH conf = 8 ∧ bytes_fd conf = c ∧
        9 ≤ LENGTH out ∧ HD out = 0w
     then TAKE (w82n (TAKE 8 (TL out))) (DROP 9 out)
     else []) ∧
  event_read c _ = []
End

(* The bytes a «sock_write» event sent on connection c: the config is the
   8-byte connection followed by the data. *)
Definition event_written_def:
  event_written c (IO_event (ExtCall n) conf bytes) =
    (if n = «sock_write» ∧ 8 ≤ LENGTH conf ∧ bytes_fd (TAKE 8 conf) = c
     then DROP 8 conf else []) ∧
  event_written c _ = []
End

(* Everything the program read from / wrote to connection c in a finite
   trace, in order *)
Definition bytes_read_from_def:
  bytes_read_from c evs = FLAT (MAP (event_read c) evs)
End

Definition bytes_written_to_def:
  bytes_written_to c evs = FLAT (MAP (event_written c) evs)
End

(* ------------------------------------------------------------------------
   What the clients send
   ------------------------------------------------------------------------ *)

(* The arrivals of the first n steps of a schedule *)
Definition arrivals_upto_def:
  arrivals_upto 0 sched = [] ∧
  arrivals_upto (SUC n) sched =
    case LHD sched of
    | NONE => []
    | SOME step => step ++ arrivals_upto n (THE (LTL sched))
End

(* The data the client of connection c sends in the first n steps *)
Definition sent_upto_def:
  sent_upto c n sk =
    FLAT (MAP (λa. case a of Data c' bs => if c' = c then bs else [] | _ => [])
              (arrivals_upto n sk.sched))
End

(* ------------------------------------------------------------------------
   The specification
   ------------------------------------------------------------------------ *)

(* Safety: at every point of the run, on every connection, the server has
   written back a prefix of what it has read. *)
Definition echo_safe_def:
  echo_safe io ⇔
    ∀evs c. LPREFIX (fromList evs) io ⇒
            bytes_written_to c evs ≼ bytes_read_from c evs
End

(* Liveness: everything a client sends is eventually written back to it. *)
Definition echo_live_def:
  echo_live sk io ⇔
    ∀c n. ∃evs. LPREFIX (fromList evs) io ∧
                sent_upto c n sk ≼ bytes_written_to c evs
End

(* THE STATEMENT (to be proved for the echo server's program, with lfd = 3w):
   in every fair world with one listener lfd, the program runs forever, and
   its I/O trace is safe and live on every connection. *)
Definition echo_spec_def:
  echo_spec lfd (prog : dec list) ⇔
    ∀sk. server_world lfd sk ⇒
         ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog
                (Diverge io) ∧
              echo_safe io ∧ echo_live sk io
End
