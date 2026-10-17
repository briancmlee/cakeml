(*
  asyncProtoLiveViaB: liveness of the existing server http_server_b,
  for the loop's trace, derived from the generic proto_live_rounds
  (asyncProtoLive) through http_live_b_proto and http_server_b_proto.
  design/32 phase 3b.
*)
Theory asyncProtoLiveViaB
Ancestors
  words llist asyncCore asyncServer asyncM4Relabel asyncM4GRounds
  ffiSpikeSocketFFI ffiSpikeSocketFair asyncM4Loop
  asyncProto asyncProtoServer asyncProtoLive asyncProtoB asyncProtoViaB
Libs
  preamble

(* MAIN: the existing server's trace is live (the trusted http_live_b),
   through the generic pipeline *)
Theorem http_live_b_via_proto:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ⇒
  http_live_b files s0
    (LFLATTEN (LGENLIST
       (λi. fromList (grounds_events (EI lfdn) (srelabel (http_server_b files lfdn)) s0 i))
       NONE))
Proof
  rw[http_live_b_proto, http_server_b_proto] >>
  irule proto_live_rounds >> simp[proto_ok_b]
QED
