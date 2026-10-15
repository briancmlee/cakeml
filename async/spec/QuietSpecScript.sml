(*
  QuietSpec: what the BLOCKING servers must do, CPU included.  A companion
  to EchoSpec and HttpSpecHeaders, which are unchanged.

  EchoSpec and HttpSpecHeaders say nothing about waiting: a server that
  polls in a busy loop meets them.  Here the world also offers a blocking
  call, «sock_select», and the statement adds QUIESCENCE:

    in every fair world in which only finitely many things ever arrive,
    the program's run is FINITE: it ends blocked forever in select
    (CakeML's FFI_diverged outcome of «sock_select»), having answered
    everything that arrived.

  A program that busy-polls, or that spins in select on an fd it never
  reads, runs forever in such a world (Diverge), so it fails.  A program
  that goes to sleep too early fails liveness.  In worlds where arrivals
  never stop, the program must still be safe and live, whether it runs
  forever or not.

  What it does not say (on purpose):
  - nothing about CPU while arrivals keep coming: a fair world can keep
    the server busy forever;
  - nothing about HOW SOON the program sleeps: a run that busy-polls for
    a long but finite time and then sleeps meets it.  Quiescence is
    qualitative; a quantitative version would bound the rounds between
    the last arrival and the final select.

  What is trusted, beyond EchoSpec: the select call's model below
  (sel_wait, ffi_select: block until a poll of the given fds would
  report one ready; forever if none ever will be), which the C side's
  sock_select (a poll(2) with no timeout) must implement.

  Nothing here is proved; the statements are definitions.
  QuietSpecBiteScript.sml shows that they bite and are not vacuous.
*)
Theory QuietSpec
Ancestors
  semantics ffi llist ml_prog ffiSpikeSocketFFI ffiSpikeSocketFair
  EchoSpec HttpSpec HttpSpecHeaders
Libs
  preamble

(* ------------------------------------------------------------------------
   The world: EchoSpec's sockets, plus a blocking select
   ------------------------------------------------------------------------ *)

(* select on fds: the number of rounds of the schedule that pass before one
   of fds is ready (it is ready after one more round), or NONE: none of
   fds ever becomes ready, and select blocks forever *)
Definition sel_wait_def:
  sel_wait fds s =
    if ∃n. EXISTS (is_ready (ticks (SUC n) s)) fds then
      SOME (LEAST n. EXISTS (is_ready (ticks (SUC n) s)) fds)
    else NONE
End

(* «sock_select»: conf is a list of fds (8 bytes each, as for «sock_poll»);
   the buffer is empty and nothing is returned in it.  The «sock_poll» that
   follows reports which fds are ready. *)
Definition ffi_select_def:
  ffi_select (conf:word8 list) (bytes:word8 list) s =
    if bytes = [] then
      case sel_wait (bytes_fds conf) s of
      | NONE => SOME FFIdiverge
      | SOME k => SOME (FFIreturn [] (ticks k s))
    else NONE
End

(* The model's function for each call: EchoSpec's four, and select *)
Definition sel_fn_def:
  sel_fn n = if n = «sock_select» then SOME ffi_select else socket_fn n
End

(* The oracle: as EchoSpec's socket_oracle, and a select that blocks
   forever ends the program with FFI_diverged *)
Definition sel_oracle_def:
  sel_oracle (ExtCall n) (sk:sockets) conf bytes =
    (case sel_fn n of
     | SOME f =>
         (case f conf bytes sk of
          | SOME (FFIreturn bytes' sk') => Oracle_return sk' bytes'
          | SOME FFIdiverge => Oracle_final FFI_diverged
          | NONE => Oracle_final FFI_failed)
     | NONE => Oracle_final FFI_failed) ∧
  sel_oracle _ sk conf bytes = Oracle_final FFI_failed
End

Definition select_ffi_def:
  select_ffi sk = <| oracle := sel_oracle; ffi_state := sk; io_events := [] |>
End

(* ------------------------------------------------------------------------
   Quiet worlds and sleeping programs
   ------------------------------------------------------------------------ *)

(* Only finitely many things ever arrive: from some step on, nothing *)
Definition arrivals_finite_def:
  arrivals_finite sk ⇔
    ∃N. ∀m. N ≤ m ⇒ arrivals_upto m sk.sched = arrivals_upto N sk.sched
End

(* The program ended blocked forever in select, after the I/O io *)
Definition asleep_def:
  asleep b io ⇔
    ∃conf. b = Terminate (FFI_outcome (Final_event (ExtCall «sock_select») conf []
                                        FFI_diverged)) io
End

(* ------------------------------------------------------------------------
   The statements
   ------------------------------------------------------------------------ *)

(* THE ECHO STATEMENT: in every fair world with one listener lfd, the
   program either runs forever or ends asleep in select; either way its
   I/O is safe and live (EchoSpec's echo_safe, echo_live); and if only
   finitely many things arrive, it ends asleep. *)
Definition echo_quiet_def:
  echo_quiet lfd (prog : dec list) ⇔
    ∀sk. server_world lfd sk ⇒
         ∃b. semantics_prog (init_state (select_ffi sk)) init_env prog b ∧
             ((∃io. b = Diverge io ∧ echo_safe io ∧ echo_live sk io) ∨
              (∃io. asleep b io ∧
                    echo_safe (fromList io) ∧ echo_live sk (fromList io))) ∧
             (arrivals_finite sk ⇒ ∃io. asleep b io)
End

(* THE HTTP STATEMENT: the same, with HttpSpecHeaders' http_safe_h and
   http_live_h *)
Definition http_quiet_def:
  http_quiet lfd files (prog : dec list) ⇔
    ∀sk. server_world lfd sk ⇒
         ∃b. semantics_prog (init_state (select_ffi sk)) init_env prog b ∧
             ((∃io. b = Diverge io ∧
                    http_safe_h files io ∧ http_live_h files sk io) ∨
              (∃io. asleep b io ∧
                    http_safe_h files (fromList io) ∧
                    http_live_h files sk (fromList io))) ∧
             (arrivals_finite sk ⇒ ∃io. asleep b io)
End
