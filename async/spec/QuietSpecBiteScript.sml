(*
  QuietSpec bites, and is not vacuous.

  - Quiet worlds exist, also with a connection that is closed
    (hello_world, close_world) and with an invalid HTTP request followed
    by a close (body_then_close).
  - broken_runs_forever(_h): a program that runs forever in a quiet world
    fails.  This covers a polling server, a server that spins in select
    after a disconnect (#27), and one that spins after an invalid request
    whose client closes (#56): in hello_world / body_then_close they run
    forever.
  - broken_sleeps_early: a program that goes to sleep before echoing what
    arrived fails, in particular one that blocks in select at once.
  - select_non_socket_fails, select_stdin_fails: selecting on an fd that
    is not a socket of the model fails the FFI call; it never puts the
    program to sleep (asleep needs FFI_diverged).  Without that rule the
    model would sleep forever on fd 0, which is never ready
    (stdin_never_ready).
  - ideal_quiet / ideal_quiet_h / ideal_quiet_b: an ideal sleeping run
    meets every clause of the statement in a quiet world.
*)
Theory QuietSpecBite
Ancestors
  QuietSpec EchoSpec EchoSpecBite HttpSpec HttpSpecBite HttpSpecHeaders
  HttpSpecHeadersBite HttpSpecBodies HttpSpecBodiesBite
  ffiSpikeSocketFFI ffiSpikeSocketFair llist
Libs
  preamble

(* ------------------------------------------------------------------------
   Quiet worlds
   ------------------------------------------------------------------------ *)

Theorem arrivals_upto_LNIL[local]:
  ∀k. arrivals_upto k [||] = []
Proof
  Cases >> simp[arrivals_upto_def]
QED

(* A schedule of one step is quiet *)
Theorem arrivals_finite_one_step:
  sk.sched = [|step|] ⇒ arrivals_finite sk
Proof
  rw[arrivals_finite_def] >> qexists_tac ‘1’ >> rpt strip_tac >>
  Cases_on ‘m’ >> gvs[] >>
  simp[arrivals_upto_def, arrivals_upto_LNIL] >>
  REWRITE_TAC[ONE, arrivals_upto_def] >> simp[arrivals_upto_LNIL]
QED

(* NON-VACUITY: a fair, quiet world in which a client connects, sends a
   line, and closes *)
Theorem hello_world_quiet:
  server_world 3w hello_world ∧ arrivals_finite hello_world
Proof
  simp[server_world_exists] >> irule arrivals_finite_one_step >>
  simp[hello_world_def]
QED

(* A client connects, sends bs, and closes *)
Definition close_world_def:
  close_world bs =
    <| listeners := [(3w, [])]; conns := [];
       sched := [|[Connect 3w 4w; Data 4w bs; Eof 4w]|] |>
End

Theorem ticks_quiet[local]:
  ∀n. s.sched = [||] ⇒ ticks n s = s
Proof
  Induct >> simp[ticks_def, tick_def]
QED

Theorem close_world_quiet:
  server_world 3w (close_world bs) ∧ arrivals_finite (close_world bs)
Proof
  conj_tac
  >- (simp[server_world_def, close_world_def, sched_wf_def] >> Cases
      >- simp[ticks_def, next_step_def, step_ok_def, arrival_ok_def, deliver1_def,
              is_listener_def, is_conn_def, AFUPDKEY_def, empty_conn_def]
      >> ‘(tick (close_world bs)).sched = [||]’ by simp[tick_def, close_world_def]
      >> fs[close_world_def]
      >> simp[ticks_def, ticks_quiet, next_step_def, step_ok_def])
  >> irule arrivals_finite_one_step >> simp[close_world_def]
QED

(* An HTTP request with a body (Content-Length), then a close: the world of
   #56's busy-polling caveat *)
Overload body_then_close = “close_world (bytes "POST / HTTP/1.1\r\nContent-Length: 5\r\n\r\nhello")”

(* ------------------------------------------------------------------------
   Bite
   ------------------------------------------------------------------------ *)

(* BITE: a program that runs forever in a quiet world fails (a polling
   server; a server that spins in select) *)
Theorem broken_runs_forever:
  server_world lfd sk ∧ arrivals_finite sk ∧
  (∀b. semantics_prog (init_state (select_ffi sk)) init_env prog b ⇒
       ∃io. b = Diverge io) ⇒
  ¬echo_quiet lfd prog
Proof
  rw[echo_quiet_def] >> qexists_tac ‘sk’ >> rw[] >>
  Cases_on ‘semantics_prog (init_state (select_ffi sk)) init_env prog b’ >> simp[] >>
  first_x_assum drule >> rw[] >> simp[asleep_def]
QED

Theorem broken_runs_forever_h:
  server_world lfd sk ∧ arrivals_finite sk ∧
  (∀b. semantics_prog (init_state (select_ffi sk)) init_env prog b ⇒
       ∃io. b = Diverge io) ⇒
  ¬http_quiet lfd files prog
Proof
  rw[http_quiet_def] >> qexists_tac ‘sk’ >> rw[] >>
  Cases_on ‘semantics_prog (init_state (select_ffi sk)) init_env prog b’ >> simp[] >>
  first_x_assum drule >> rw[] >> simp[asleep_def]
QED

Theorem broken_runs_forever_b:
  server_world lfd sk ∧ arrivals_finite sk ∧
  (∀b. semantics_prog (init_state (select_ffi sk)) init_env prog b ⇒
       ∃io. b = Diverge io) ⇒
  ¬http_quiet_b lfd files prog
Proof
  rw[http_quiet_b_def] >> qexists_tac ‘sk’ >> rw[] >>
  Cases_on ‘semantics_prog (init_state (select_ffi sk)) init_env prog b’ >> simp[] >>
  first_x_assum drule >> rw[] >> simp[asleep_def]
QED

(* The worlds of the two spinning servers are quiet: running forever there
   fails the statement *)
Theorem spin_worlds_quiet:
  (server_world 3w hello_world ∧ arrivals_finite hello_world) ∧
  (server_world 3w body_then_close ∧ arrivals_finite body_then_close)
Proof
  simp[hello_world_quiet, close_world_quiet]
QED

(* BITE: a program that goes to sleep before echoing what arrived fails;
   in particular one that blocks in select at once *)
Theorem broken_sleeps_early:
  (∀b. semantics_prog (init_state (select_ffi hello_world)) init_env prog b ⇒
       ∃io. asleep b io ∧ ∀evs. evs ≼ io ⇒ bytes_written_to 4w evs = []) ⇒
  ¬echo_quiet 3w prog
Proof
  rw[echo_quiet_def] >> qexists_tac ‘hello_world’ >> simp[server_world_exists] >>
  rw[] >>
  Cases_on ‘semantics_prog (init_state (select_ffi hello_world)) init_env prog b’ >>
  simp[] >> first_x_assum drule >> strip_tac >>
  gvs[asleep_def] >> rw[] >>
  disj2_tac >> irule broken_never_echoes >> rpt strip_tac >>
  first_x_assum irule >> gvs[LPREFIX_fromList, from_toList]
QED

(* BITE: select on an fd that is not a socket of the model fails; it does
   not block, so it cannot end the run asleep *)
Theorem select_non_socket_fails:
  MEM fd (bytes_fds conf) ∧ ¬is_listener sk fd ∧ ¬is_conn sk fd ⇒
  sel_oracle (ExtCall «sock_select») sk conf bs = Oracle_final FFI_failed
Proof
  rw[sel_oracle_def, sel_fn_def, ffi_select_def, sel_ok_def, EVERY_MEM] >>
  metis_tac[]
QED

(* fd 0 in hello_world: never ready, so the old rule would block forever *)
Theorem stdin_never_ready:
  sel_wait [0w] hello_world = NONE
Proof
  ‘(tick hello_world).sched = [||]’ by simp[tick_def, hello_world_def] >>
  ‘∀n. ticks (SUC n) hello_world = tick hello_world’
    by simp[ticks_def, ticks_quiet] >>
  simp[sel_wait_def] >>
  simp[tick_def, hello_world_def, deliver_def, deliver1_def, is_ready_def,
       is_listener_def, is_conn_def, AFUPDKEY_def, empty_conn_def]
QED

Theorem select_stdin_fails:
  sel_oracle (ExtCall «sock_select») hello_world (fds_bytes [0w]) [] =
  Oracle_final FFI_failed
Proof
  irule select_non_socket_fails >> qexists_tac ‘0w’ >>
  simp[hello_world_def, is_listener_def, is_conn_def]
QED

(* ------------------------------------------------------------------------
   Non-vacuity
   ------------------------------------------------------------------------ *)

(* NON-VACUITY: a run that reads the line, echoes it, and sleeps in select
   meets every clause of echo_quiet in hello_world *)
Theorem ideal_quiet:
  let b = Terminate (FFI_outcome (Final_event (ExtCall «sock_select») conf []
                                   FFI_diverged))
                    [rd 4w [104w; 105w; 10w] 100; wr 4w [104w; 105w; 10w]] in
  ((∃io. b = Diverge io ∧ echo_safe io ∧ echo_live hello_world io) ∨
   (∃io. asleep b io ∧
         echo_safe (fromList io) ∧ echo_live hello_world (fromList io))) ∧
  (arrivals_finite hello_world ⇒ ∃io. asleep b io)
Proof
  simp[asleep_def] >> assume_tac ideal_trace_safe_and_live >> fs[]
QED

(* NON-VACUITY (HTTP): a run that reads a request, answers it, and sleeps
   in select meets every clause of http_quiet in a quiet world *)
Theorem ideal_quiet_h:
  let b = Terminate (FFI_outcome (Final_event (ExtCall «sock_select») conf []
                                   FFI_diverged)) ideal_h in
  server_world 3w (one_client (hrequests [ra])) ∧
  arrivals_finite (one_client (hrequests [ra])) ∧
  ((∃io. b = Diverge io ∧ http_safe_h site io ∧
         http_live_h site (one_client (hrequests [ra])) io) ∨
   (∃io. asleep b io ∧ http_safe_h site (fromList io) ∧
         http_live_h site (one_client (hrequests [ra])) (fromList io))) ∧
  (arrivals_finite (one_client (hrequests [ra])) ⇒ ∃io. asleep b io)
Proof
  ‘arrivals_finite (one_client (hrequests [ra]))’
    by (irule arrivals_finite_one_step >> simp[one_client_def]) >>
  simp[asleep_def] >> assume_tac ideal_h_trace_safe_and_live >> fs[]
QED

(* NON-VACUITY (HTTP bodies, the headline): a run that reads a POST /echo
   with a body, answers it, and sleeps in select meets every clause of
   http_quiet_b in a quiet world *)
Theorem ideal_quiet_b:
  let b = Terminate (FFI_outcome (Final_event (ExtCall «sock_select») conf []
                                   FFI_diverged)) ideal_b in
  server_world 3w (one_client (brequests [rp])) ∧
  arrivals_finite (one_client (brequests [rp])) ∧
  ((∃io. b = Diverge io ∧ http_safe_b site io ∧
         http_live_b site (one_client (brequests [rp])) io) ∨
   (∃io. asleep b io ∧ http_safe_b site (fromList io) ∧
         http_live_b site (one_client (brequests [rp])) (fromList io))) ∧
  (arrivals_finite (one_client (brequests [rp])) ⇒ ∃io. asleep b io)
Proof
  ‘arrivals_finite (one_client (brequests [rp]))’
    by (irule arrivals_finite_one_step >> simp[one_client_def]) >>
  simp[asleep_def] >> assume_tac ideal_b_trace_safe_and_live >> fs[]
QED

