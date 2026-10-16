(*
  Version 1's and version 2's server worlds are endpoint worlds (for the
  user's review).

  Two FFI states answer the same (endpointSemantics' same_answers) if, for
  every sequence of calls, they give the same sequence of answers.  Then any
  program has the same behaviours in both (same_answers_semantics, proved
  here from endpointSemantics).  The instance claims say that
  - every version-1 server world answers as some endpoint server world
    offering version 1's calls, without backpressure, whose rely holds; and
    conversely (so specs over the two classes coincide);
  - likewise version 2's worlds, with version 2's calls.
*)
Theory endpointInstances
Ancestors
  llist ffi semantics ffiSpikeSocketFFI ffiSpikeSocketFair EchoSpec socketV2FFI socketV2Fair
  EchoSpec2 endpointWorld endpointFair endpointSpecForms endpointSemantics
Libs
  preamble

(* MAIN: a program's behaviours depend only on the answers (any two FFI
   state types, e.g. version 1's or version 2's sockets and the endpoint
   world) *)
Theorem same_answers_semantics:
  same_answers f1 f2 ∧ f1.io_events = f2.io_events ⇒
  (semantics_prog (init_state f1) init_env prog b ⇔
   semantics_prog (init_state f2) init_env prog b)
Proof
  strip_tac >>
  ‘init_state f2 = init_state f1 with ffi := f2’
    by simp[ml_progTheory.init_state_def, semanticPrimitivesTheory.state_component_equality] >>
  pop_assum SUBST1_TAC >>
  ‘ffi_rel (init_state f1).ffi f2’ by simp[ml_progTheory.init_state_def, ffi_rel_def] >>
  drule semantics_prog_same_answers >> disch_then (fn th => simp[th])
QED

(* The original claim, REFUTED below (not_v1_instance): version 1's server
   worlds are the endpoint server worlds with version 1's calls and no
   backpressure *)
Definition v1_instance_def:
  v1_instance ⇔
    (∀lfd sk. server_world lfd sk ⇒
              ∃a w. ep_server_world v1_calls lfd a w ∧ no_backpressure w ∧ ep_rely w ∧
                    same_answers (socket_ffi sk) (ep_ffi w)) ∧
    (∀lfd a w. ep_server_world v1_calls lfd a w ∧ no_backpressure w ∧ ep_rely w ⇒
               ∃sk. server_world lfd sk ∧ same_answers (socket_ffi sk) (ep_ffi w))
End

(* CLAIM (proved in endpointV2Sim): version 2's server worlds are the
   endpoint server worlds with version 2's calls, no backpressure and a
   fixed schedule *)
Definition v2_instance_def:
  v2_instance ⇔
    (∀lfd sk. server_world2 lfd sk ⇒
              ∃a w. ep_server_world v2_calls lfd a w ∧ no_backpressure w ∧ open_loop w ∧
                    ep_rely w ∧ same_answers (socket2_ffi sk) (ep_ffi w)) ∧
    (∀lfd a w. ep_server_world v2_calls lfd a w ∧ no_backpressure w ∧ open_loop w ∧
               ep_rely w ⇒
               ∃sk. server_world2 lfd sk ∧ same_answers (socket2_ffi sk) (ep_ffi w))
End

(* ------------------------------------------------------------------------
   Version 1 is NOT an exact instance: its connections are usable before
   they are accepted
   ------------------------------------------------------------------------ *)

(* In version 1, «Connect l c» makes c a connection at once, so a program
   may read c before accepting it.  In the endpoint world (as in POSIX and
   version 2) an fd exists only once accepted. *)

Theorem ep_deliver_open_fds[local]:
  ∀as w. (FOLDL ep_deliver w as).open_fds = w.open_fds
Proof
  Induct >> simp[] >> Cases >> rw[ep_deliver_def, upd_chan_def] >>
  every_case_tac >> simp[] >> pairarg_tac >> simp[]
QED

Theorem ep_tick_open_fds[local]:
  (ep_tick w).open_fds = w.open_fds
Proof
  simp[ep_tick_def, ep_deliver_open_fds, settle_def]
QED

Theorem ticks_LNIL[local]:
  ∀n s. s.sched = [||] ⇒ ticks n s = s
Proof
  Induct >> simp[ffiSpikeSocketFairTheory.ticks_def, tick_def]
QED

Definition v1_early_world_def:
  v1_early_world =
    <| listeners := [(3w, [])]; conns := [];
       sched := fromList [[Connect 3w 5w; Data 5w [1w]]] |>
End

Theorem v1_early_world_ok[local]:
  server_world 3w v1_early_world
Proof
  simp[server_world_def, v1_early_world_def, sched_wf_def] >> Cases
  >- simp[ffiSpikeSocketFairTheory.ticks_def, ffiSpikeSocketFairTheory.next_step_def, ffiSpikeSocketFairTheory.step_ok_def, ffiSpikeSocketFairTheory.arrival_ok_def, deliver1_def,
          is_listener_def, is_conn_def, AFUPDKEY_def, empty_conn_def] >>
  simp[ffiSpikeSocketFairTheory.ticks_def] >>
  qmatch_goalsub_abbrev_tac ‘ticks n s’ >>
  ‘s.sched = [||]’
    by simp[Abbr ‘s’, tick_def, deliver_def, deliver1_def, is_listener_def,
            is_conn_def, AFUPDKEY_def] >>
  simp[ticks_LNIL, ffiSpikeSocketFairTheory.next_step_def, ffiSpikeSocketFairTheory.step_ok_def]
QED

(* The calls: poll (the connection arrives), then read it unaccepted *)
Definition early_calls_def:
  early_calls = [(ExtCall «sock_poll», [], []);
                 (ExtCall «sock_read», fd_bytes 5w, REPLICATE 10 (0w:word8))]
End

Theorem bytes_fds_nil[local]:
  bytes_fds [] = []
Proof
  simp[Once bytes_fds_def]
QED

Theorem not_v1_instance:
  ¬v1_instance
Proof
  simp[v1_instance_def] >> disj1_tac >>
  qexistsl_tac [‘3w’, ‘v1_early_world’] >> simp[v1_early_world_ok] >>
  CCONTR_TAC >> fs[same_answers_def] >>
  first_x_assum (qspec_then ‘early_calls’ mp_tac) >>
  ‘∃x. run_calls (socket_ffi v1_early_world) early_calls = [INL []; INL x]’
    by simp[early_calls_def, run_calls_def, socket_ffi_def, socket_oracle_def,
            socket_fn_def, ffi_sock_poll_def, bytes_fds_nil, ffi_sock_read_def,
            sock_read_def, tick_def, v1_early_world_def, deliver_def, deliver1_def,
            is_listener_def, is_conn_def, AFUPDKEY_def, empty_conn_def] >>
  ‘run_calls (ep_ffi w) early_calls = [INL []; INR FFI_failed]’
    suffices_by (strip_tac >> ASM_REWRITE_TAC[] >> simp[]) >>
  gvs[ep_server_world_def] >>
  simp[early_calls_def, run_calls_def, ep_ffi_def, ep_oracle_def, ep_ffi_fn_def,
       ep_call_def, v1_calls_def, bytes_fds_nil] >>
  simp[ep_conn_err_def, ep_read_def, ep_chan_of_def, ep_tick_open_fds]
QED

(* ------------------------------------------------------------------------
   DRAFT (pending user decision): version 1 for fd-disciplined programs
   ------------------------------------------------------------------------ *)

(* The fds a socket event names *)
Definition event_fds_def:
  event_fds (IO_event (ExtCall n) conf bytes) =
    (if n = «sock_poll» ∨ n = «sock_select» then bytes_fds conf
     else if n = «sock_write» ∨ n = «sock_send» then [bytes_fd (TAKE 8 conf)]
     else if n = «sock_connect» then []
     else [bytes_fd conf]) ∧
  event_fds _ = []
End

(* The fds open after some events (given newest first): opened and not
   closed since *)
Definition open_now_def:
  open_now [] = [] ∧
  open_now (ev :: evs) =
    (case event_opened ev of
     | SOME f => f :: open_now evs
     | NONE => case event_closed ev of
               | SOME f => FILTER ((≠) f) (open_now evs)
               | NONE => open_now evs)
End

(* A trace is fd-disciplined: every socket event names only the listener
   lfd or an fd an earlier event opened (accepted or connected) and no event
   has closed since.  A trace property, not a syntactic one. *)
Definition fd_disciplined_def:
  fd_disciplined lfd io ⇔
    always (λevs. ∀pre ev. evs = pre ++ [ev] ⇒
                    EVERY (λf. f = lfd ∨ MEM f (open_now (REVERSE pre))) (event_fds ev)) io
End

(* A program is fd-disciplined in version 1's worlds *)
Definition v1_disciplined_def:
  v1_disciplined lfd prog ⇔
    ∀sk. server_world lfd sk ⇒
         ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog (Diverge io) ∧
              fd_disciplined lfd io
End

(* The non-saturation hypothesis (approved 2026-10-16): the schedule
   connects at most M clients in all *)
Definition sched_connects_le_def:
  sched_connects_le M ll ⇔
    ∀n. LENGTH (FILTER (λa. ∃l c. a = Connect l c) (arrivals_upto n ll)) ≤ M
End

(* CLAIM (approved 2026-10-16; PROVED as endpointV1Inst's
   v1_instance_disc_thm): for an fd-disciplined program, a version-1 server
   world that connects at most M clients (M + 3 < 2^64: otherwise the
   endpoint world runs out of fds where version 1 never does) and an
   endpoint server world with version 1's calls, no backpressure and the
   same fixed schedule (alloc giving each channel the fd version 1's
   schedule chose) have the same behaviours *)
Definition v1_instance_disc_def:
  v1_instance_disc ⇔
    ∀lfd sk prog M.
      server_world lfd sk ∧ sched_connects_le M sk.sched ∧ M + 3 < dimword (:64) ∧
      v1_disciplined lfd prog ⇒
      ∃a w. ep_server_world v1_calls lfd a w ∧ no_backpressure w ∧ open_loop w ∧
            ep_rely w ∧
            ∀b. semantics_prog (init_state (socket_ffi sk)) init_env prog b ⇔
                semantics_prog (init_state (ep_ffi w)) init_env prog b
End
