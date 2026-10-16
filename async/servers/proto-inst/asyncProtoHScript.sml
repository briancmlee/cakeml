(*
  asyncProtoH: the header-tolerant parser (asyncHttpParseH) against HttpSpecHeaders, as an instance of the generic protocol interface
  (asyncProto, design/32 phase 1).

  P_h packages the parser; proto_ok_h discharges P1-P4 from the
  parser's existing theorems (parse_hprint, parse_hcomplete, parse_hinvalid); http_spec_h_proto
  states the trusted spec as proto_spec, by unfolding.
*)
Theory asyncProtoH
Ancestors
  asyncProto HttpSpecHeaders asyncHttpParseH asyncHttpParseHExt
Libs
  preamble

(* The parser's result, in the interface's type *)
Definition h_presult_def:
  h_presult (HComplete r rest) = PComplete r rest ∧
  h_presult HIncomplete = PIncomplete ∧
  h_presult HInvalid = PInvalid
End

Definition P_h_def:
  P_h = <| valid := valid_hrequest; print := print_hrequest;
             parse := h_presult o parse_hrequest |>
End

Theorem h_presult_eqs[simp,local]:
  (h_presult v = PComplete r rest ⇔ v = HComplete r rest) ∧
  (h_presult v = PInvalid ⇔ v = HInvalid)
Proof
  Cases_on ‘v’ >> simp[h_presult_def]
QED

(* MAIN: the parser meets the interface *)
Theorem proto_ok_h:
  proto_ok P_h
Proof
  rw[proto_ok_def, P_h_def]
  >- simp[parse_hprint, h_presult_def]
  >- metis_tac[parse_hcomplete]
  >- metis_tac[parse_hcomplete]
  >- metis_tac[parse_hinvalid]
  >> Cases_on ‘r’ >> simp[print_hrequest_def]
QED

(* MAIN: the trusted spec is the generic one, for this protocol *)
Theorem http_spec_h_proto:
  http_spec_h lfd files prog ⇔ proto_spec P_h (print_response o handle files o hpath) lfd prog
Proof
  simp[http_spec_h_def, http_safe_h_def, http_live_h_def, hrequests_def, hresponses_def, no_full_hrequest_def,
       proto_spec_def, proto_safe_def, proto_live_def, preqs_def, presps_def,
       no_full_def, P_h_def]
QED
