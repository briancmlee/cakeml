(*
  asyncProtoViaStrict: the existing server http_server (asyncHttpServer) IS the
  generic proto_server for P_strict, and its trace-level safety
  (http_comp_safe) follows from the generic proto_comp_safe.

  The existing theorem and its proof are untouched; this is its twin,
  proved through the generic pipeline (design/32 §2.2, §2.8.3).
*)
Theory asyncProtoViaStrict
Ancestors
  words llist asyncCore asyncServer asyncM4Relabel asyncM4GRounds
  HttpSpec asyncHttpServer asyncProto asyncProtoServer asyncProtoSafe asyncProtoStrict
Libs
  preamble

Theorem http_body_proto[local]:
  http_body files r p = proto_body P_strict (print_response o handle files) r p
Proof
  PairCases_on ‘p’ >> simp[http_body_def, proto_body_def, P_strict_def] >>
  Cases_on ‘parse_request p1’ >> simp[strict_presult_def]
QED

(* MAIN: the existing handler and server are the generic ones *)
Theorem http_handler_proto:
  http_handler files = proto_handler P_strict (print_response o handle files)
Proof
  simp[http_handler_def] >> irule proto_handler_fix >>
  simp[http_body_proto]
QED

Theorem http_server_proto:
  http_server files lfd = proto_server P_strict (print_response o handle files) lfd
Proof
  simp[http_server_def, proto_server_def, http_handler_proto]
QED

(* The trusted safety and liveness are the generic ones, for P_strict *)
Theorem http_safe_proto:
  http_safe files io ⇔ proto_safe P_strict (print_response o handle files) io
Proof
  simp[http_safe_def, proto_safe_def, requests_def, responses_def, no_full_request_def,
       preqs_def, presps_def, no_full_def, P_strict_def]
QED

Theorem http_live_proto:
  http_live files sk io ⇔ proto_live P_strict (print_response o handle files) sk io
Proof
  simp[http_live_def, proto_live_def, requests_def, responses_def, no_full_request_def,
       preqs_def, presps_def, P_strict_def]
QED

(* MAIN: http_comp_safe, re-derived through the generic pipeline *)
Theorem http_comp_safe_via_proto:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  http_safe files (LFLATTEN (LGENLIST
    (λi. fromList (grounds_events ifds (srelabel (http_server files lfdn)) s0 i))
    NONE))
Proof
  rw[http_safe_proto, http_server_proto] >>
  irule proto_comp_safe >> simp[proto_ok_strict]
QED
