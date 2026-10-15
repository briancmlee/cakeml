(*
  asyncProtoViaB: the existing server http_server_b (asyncHttpServerB) IS the
  generic proto_server for P_b, and its trace-level safety
  (http_comp_safe_b) follows from the generic proto_comp_safe.

  The existing theorem and its proof are untouched; this is its twin,
  proved through the generic pipeline (design/32 §2.2, §2.8.3).
*)
Theory asyncProtoViaB
Ancestors
  words llist asyncCore asyncServer asyncM4Relabel asyncM4GRounds
  HttpSpecBodies asyncHttpServerB asyncProto asyncProtoServer asyncProtoSafe asyncProtoB
Libs
  preamble

Theorem http_body_b_proto[local]:
  http_body_b files r p = proto_body P_b (print_response o bhandle files) r p
Proof
  PairCases_on ‘p’ >> simp[http_body_b_def, proto_body_def, P_b_def] >>
  Cases_on ‘parse_brequest p1’ >> simp[b_presult_def]
QED

(* MAIN: the existing handler and server are the generic ones *)
Theorem http_handler_b_proto:
  http_handler_b files = proto_handler P_b (print_response o bhandle files)
Proof
  simp[http_handler_b_def] >> irule proto_handler_fix >>
  simp[http_body_b_proto]
QED

Theorem http_server_b_proto:
  http_server_b files lfd = proto_server P_b (print_response o bhandle files) lfd
Proof
  simp[http_server_b_def, proto_server_def, http_handler_b_proto]
QED

(* The trusted safety and liveness are the generic ones, for P_b *)
Theorem http_safe_b_proto:
  http_safe_b files io ⇔ proto_safe P_b (print_response o bhandle files) io
Proof
  simp[http_safe_b_def, proto_safe_def, brequests_def, bresponses_def, no_full_brequest_def,
       preqs_def, presps_def, no_full_def, P_b_def]
QED

Theorem http_live_b_proto:
  http_live_b files sk io ⇔ proto_live P_b (print_response o bhandle files) sk io
Proof
  simp[http_live_b_def, proto_live_def, brequests_def, bresponses_def, no_full_brequest_def,
       preqs_def, presps_def, P_b_def]
QED

(* MAIN: http_comp_safe_b, re-derived through the generic pipeline *)
Theorem http_comp_safe_b_via_proto:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  http_safe_b files (LFLATTEN (LGENLIST
    (λi. fromList (grounds_events ifds (srelabel (http_server_b files lfdn)) s0 i))
    NONE))
Proof
  rw[http_safe_b_proto, http_server_b_proto] >>
  irule proto_comp_safe >> simp[proto_ok_b]
QED
