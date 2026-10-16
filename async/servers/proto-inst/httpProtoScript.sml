(*
  httpProto: the bodies parser (httpParse) against HttpSpec, as an instance of the generic protocol interface
  (protoInterface, design/32 phase 1).

  P_b packages the parser; proto_ok_b discharges P1-P4 from the
  parser's existing theorems (parse_bprint, parse_bcomplete, parse_binvalid); http_spec_proto
  states the trusted spec as proto_spec, by unfolding.
*)
Theory httpProto
Ancestors
  protoInterface HttpSpec httpParse httpParseExt
Libs
  preamble

(* The parser's result, in the interface's type *)
Definition b_presult_def:
  b_presult (BComplete r rest) = PComplete r rest ∧
  b_presult BIncomplete = PIncomplete ∧
  b_presult BInvalid = PInvalid
End

Definition P_b_def:
  P_b = <| valid := valid_brequest; print := print_brequest;
             parse := b_presult o parse_brequest |>
End

Theorem b_presult_eqs[simp,local]:
  (b_presult v = PComplete r rest ⇔ v = BComplete r rest) ∧
  (b_presult v = PInvalid ⇔ v = BInvalid)
Proof
  Cases_on ‘v’ >> simp[b_presult_def]
QED

(* MAIN: the parser meets the interface *)
Theorem proto_ok_b:
  proto_ok P_b
Proof
  rw[proto_ok_def, P_b_def]
  >- simp[parse_bprint, b_presult_def]
  >- metis_tac[parse_bcomplete]
  >- metis_tac[parse_bcomplete]
  >- metis_tac[parse_binvalid]
  >> Cases_on ‘r’ >> simp[print_brequest_def]
QED

(* MAIN: the trusted spec is the generic one, for this protocol *)
Theorem http_spec_proto:
  http_spec lfd files prog ⇔ proto_spec P_b (print_response o bhandle files) lfd prog
Proof
  simp[http_spec_def, http_safe_def, http_live_def, brequests_def, bresponses_def, no_full_brequest_def,
       proto_spec_def, proto_safe_def, proto_live_def, preqs_def, presps_def,
       no_full_def, P_b_def]
QED
