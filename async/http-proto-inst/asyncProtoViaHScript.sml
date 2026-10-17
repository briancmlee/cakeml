(*
  asyncProtoViaH: the existing server http_server_h (asyncHttpServerH) IS the
  generic proto_server for P_h, and its trace-level safety
  (http_comp_safe_h) follows from the generic proto_comp_safe.

  The existing theorem and its proof are untouched; this is its twin,
  proved through the generic pipeline (design/32 §2.2, §2.8.3).
*)
Theory asyncProtoViaH
Ancestors
  words llist asyncCore asyncServer asyncM4Relabel asyncM4GRounds
  HttpSpecHeaders asyncHttpServerH asyncProto asyncProtoServer asyncProtoSafe asyncProtoH
Libs
  preamble

Theorem http_body_h_proto[local]:
  http_body_h files r p = proto_body P_h (print_response o handle files o hpath) r p
Proof
  PairCases_on ‘p’ >> simp[http_body_h_def, proto_body_def, P_h_def] >>
  Cases_on ‘parse_hrequest p1’ >> simp[h_presult_def]
QED

(* MAIN: the existing handler and server are the generic ones *)
Theorem http_handler_h_proto:
  http_handler_h files = proto_handler P_h (print_response o handle files o hpath)
Proof
  simp[http_handler_h_def] >> irule proto_handler_fix >>
  simp[http_body_h_proto]
QED

Theorem http_server_h_proto:
  http_server_h files lfd = proto_server P_h (print_response o handle files o hpath) lfd
Proof
  simp[http_server_h_def, proto_server_def, http_handler_h_proto]
QED

(* The trusted safety and liveness are the generic ones, for P_h *)
Theorem http_safe_h_proto:
  http_safe_h files io ⇔ proto_safe P_h (print_response o handle files o hpath) io
Proof
  simp[http_safe_h_def, proto_safe_def, hrequests_def, hresponses_def, no_full_hrequest_def,
       preqs_def, presps_def, no_full_def, P_h_def]
QED

Theorem http_live_h_proto:
  http_live_h files sk io ⇔ proto_live P_h (print_response o handle files o hpath) sk io
Proof
  simp[http_live_h_def, proto_live_def, hrequests_def, hresponses_def, no_full_hrequest_def,
       preqs_def, presps_def, P_h_def]
QED

(* MAIN: http_comp_safe_h, re-derived through the generic pipeline *)
Theorem http_comp_safe_h_via_proto:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  http_safe_h files (LFLATTEN (LGENLIST
    (λi. fromList (grounds_events ifds (srelabel (http_server_h files lfdn)) s0 i))
    NONE))
Proof
  rw[http_safe_h_proto, http_server_h_proto] >>
  irule proto_comp_safe >> simp[proto_ok_h]
QED
