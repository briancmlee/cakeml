(*
  httpGetProto: the strict parser (httpGetParse) against HttpGetSpec, as an instance of the generic protocol interface
  (protoInterface, design/32 phase 1).

  P_strict packages the parser; proto_ok_strict discharges P1-P4 from the
  parser's existing theorems (parse_print, parse_complete, parse_invalid); http_get_spec_proto
  states the trusted spec as proto_spec, by unfolding.
*)
Theory httpGetProto
Ancestors
  protoInterface HttpGetSpec httpGetParse
Libs
  preamble

(* The parser's result, in the interface's type *)
Definition strict_presult_def:
  strict_presult (Complete r rest) = PComplete r rest ∧
  strict_presult Incomplete = PIncomplete ∧
  strict_presult Invalid = PInvalid
End

Definition P_strict_def:
  P_strict = <| valid := valid_request; print := print_request;
             parse := strict_presult o parse_request |>
End

Theorem strict_presult_eqs[simp,local]:
  (strict_presult v = PComplete r rest ⇔ v = Complete r rest) ∧
  (strict_presult v = PInvalid ⇔ v = Invalid)
Proof
  Cases_on ‘v’ >> simp[strict_presult_def]
QED

(* MAIN: the parser meets the interface *)
Theorem proto_ok_strict:
  proto_ok P_strict
Proof
  rw[proto_ok_def, P_strict_def]
  >- simp[parse_print, strict_presult_def]
  >- metis_tac[parse_complete]
  >- metis_tac[parse_complete]
  >- metis_tac[parse_invalid]
  >> Cases_on ‘r’ >> simp[print_request_def]
QED

(* MAIN: the trusted spec is the generic one, for this protocol *)
Theorem http_get_spec_proto:
  http_get_spec lfd files prog ⇔ proto_spec P_strict (print_response o handle files) lfd prog
Proof
  simp[http_get_spec_def, http_get_safe_def, http_get_live_def, requests_def, responses_def, no_full_request_def,
       proto_spec_def, proto_safe_def, proto_live_def, preqs_def, presps_def,
       no_full_def, P_strict_def]
QED
