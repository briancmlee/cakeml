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
  llist ffi semantics ffiSpikeSocketFFI EchoSpec socketV2FFI socketV2Fair
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

(* CLAIM: version 1's server worlds are the endpoint server worlds with
   version 1's calls and no backpressure *)
Definition v1_instance_def:
  v1_instance ⇔
    (∀lfd sk. server_world lfd sk ⇒
              ∃a w. ep_server_world v1_calls lfd a w ∧ no_backpressure w ∧ ep_rely w ∧
                    same_answers (socket_ffi sk) (ep_ffi w)) ∧
    (∀lfd a w. ep_server_world v1_calls lfd a w ∧ no_backpressure w ∧ ep_rely w ⇒
               ∃sk. server_world lfd sk ∧ same_answers (socket_ffi sk) (ep_ffi w))
End

(* CLAIM: version 2's server worlds are the endpoint server worlds with
   version 2's calls and no backpressure *)
Definition v2_instance_def:
  v2_instance ⇔
    (∀lfd sk. server_world2 lfd sk ⇒
              ∃a w. ep_server_world v2_calls lfd a w ∧ no_backpressure w ∧ ep_rely w ∧
                    same_answers (socket2_ffi sk) (ep_ffi w)) ∧
    (∀lfd a w. ep_server_world v2_calls lfd a w ∧ no_backpressure w ∧ ep_rely w ⇒
               ∃sk. server_world2 lfd sk ∧ same_answers (socket2_ffi sk) (ep_ffi w))
End
