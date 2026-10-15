(*
  Version 1's and version 2's server worlds are endpoint worlds (for the
  user's review; statements only, proofs after review).

  Two FFI states answer the same if, for every sequence of calls (each a
  name, a config and a buffer), they give the same sequence of answers
  (until the first failure).  Then any program has the same behaviours in
  both (same_answers_semantics).  The instance claims say that
  - every version-1 server world answers as some endpoint server world
    offering version 1's calls, without backpressure, whose rely holds; and
    conversely (so specs over the two classes coincide);
  - likewise version 2's worlds, with version 2's calls.
*)
Theory endpointInstances
Ancestors
  llist ffi semantics ffiSpikeSocketFFI EchoSpec socketV2FFI socketV2Fair
  EchoSpec2 endpointWorld endpointFair endpointSpecForms
Libs
  preamble

(* The answers to a sequence of calls; NONE at the first failure *)
Definition run_calls_def:
  run_calls (f : 'a ffi_state) [] = [] ∧
  run_calls f ((n, conf, bytes) :: cs) =
    case f.oracle (ExtCall n) f.ffi_state conf bytes of
    | Oracle_return st' bytes' => SOME bytes' :: run_calls (f with ffi_state := st') cs
    | Oracle_final _ => [NONE]
End

Definition same_answers_def:
  same_answers (f1 : 'a ffi_state) (f2 : 'b ffi_state) ⇔ ∀cs. run_calls f1 cs = run_calls f2 cs
End

(* CLAIM: a program's behaviours depend only on the answers *)
Definition same_answers_semantics_def:
  same_answers_semantics ⇔
    ∀(f1 : sockets ffi_state) (f2 : eworld ffi_state) prog b.
      same_answers f1 f2 ∧ f1.io_events = [] ∧ f2.io_events = [] ⇒
      (semantics_prog (init_state f1) init_env prog b ⇔
       semantics_prog (init_state f2) init_env prog b)
End

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

Definition same_answers2_semantics_def:
  same_answers2_semantics ⇔
    ∀(f1 : sockets2 ffi_state) (f2 : eworld ffi_state) prog b.
      same_answers f1 f2 ∧ f1.io_events = [] ∧ f2.io_events = [] ⇒
      (semantics_prog (init_state f1) init_env prog b ⇔
       semantics_prog (init_state f2) init_env prog b)
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
