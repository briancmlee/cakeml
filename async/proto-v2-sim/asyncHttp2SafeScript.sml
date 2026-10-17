(*
  HttpSpecBodies2's safety (per episode) for the HTTP server with request
  bodies on the version-2 handle layer (http2_safe):

     http_safe_b2 files (gtrace2 (http_server_b files lfdn) lfdn s2)

  for a fresh one-listener s2 with alloc_ok and sched_wf2, and the same
  for a loop polling any ifds_sub interest lists (D26: e.g. live lists),
  http2_safe_if.  The HTTP twin of asyncKv2Safe's kv2_safe(_if), for
  design/46's P4 (gap 1).

  No new proof: http_server_b is the generic proto_server for P_b
  (asyncProtoViaB), http_safe_b2 is proto_safe2 P_b (by unfolding, as
  asyncProto2's http_spec_b2_proto), and asyncProto2Model's
  proto2_safe_if is the generic version-2 safety.
*)
Theory asyncHttp2Safe
Ancestors
  llist words asyncCore asyncM4GRounds EchoSpec EchoSpec2 HttpSpecBodies
  HttpSpecBodies2 asyncHttpServerB asyncProto asyncProtoB asyncProtoViaB
  socketV2FFI asyncHLModel asyncHLSimRunGen asyncProto2 asyncProto2Model
Libs
  preamble

(* The approved safety is the generic one, for P_b *)
Theorem http_safe_b2_proto:
  http_safe_b2 files io ⇔ proto_safe2 P_b (print_response o bhandle files) io
Proof
  simp[http_safe_b2_def, brequests_def, bresponses_def, no_full_brequest_def,
       proto_safe2_def, preqs_def, presps_def, no_full_def, P_b_def]
QED

(* MAIN: per-episode safety for the HTTP server on the handle layer, in
   every fair version-2 world with one listener, for a loop polling any
   ifds_sub interest lists *)
Theorem http2_safe_if:
  ifds_sub (n2w lfdn) ifds ∧
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ⇒
  http_safe_b2 files (gtrace2i (http_server_b files lfdn) lfdn ifds s2)
Proof
  strip_tac >> REWRITE_TAC[http_safe_b2_proto, http_server_b_proto] >>
  irule proto2_safe_if >> simp[proto_ok_b]
QED

(* MAIN: the same for the interest lists EI *)
Theorem http2_safe:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ⇒
  http_safe_b2 files (gtrace2 (http_server_b files lfdn) lfdn s2)
Proof
  strip_tac >> irule http2_safe_if >> simp[]
QED
