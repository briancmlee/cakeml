(*
  The generic version-2 spec vocabulary, for a protocol P answered by
  resp: asyncProto's proto_safe and proto_live per EPISODE (EchoSpec2's
  projections), and EchoSpec2's closing clause.  Not trusted: each
  trusted spec is an instance by an equality lemma (HttpSpecBodies2's
  http_spec_b2 is proto_spec2 P_b, http_spec_b2_proto).
*)
Theory asyncProto2
Ancestors
  asyncProto EchoSpec EchoSpec2 HttpSpecBodies HttpSpecBodies2 asyncProtoB
Libs
  preamble

Definition proto_safe2_def:
  proto_safe2 P resp io ⇔
    ∀evs j rs rest.
      LPREFIX (fromList evs) io ∧ EVERY P.valid rs ∧
      ep_read j evs = preqs P rs ++ rest ∧ no_full P rest ⇒
      ep_written j evs ≼ presps resp rs
End

Definition proto_live2_def:
  proto_live2 P resp sk io ⇔
    ∀j n rs.
      EVERY P.valid rs ∧ preqs P rs ≼ sent2_upto j n sk ⇒
      ∃evs. LPREFIX (fromList evs) io ∧ presps resp rs ≼ ep_written j evs
End

Definition proto_spec2_def:
  proto_spec2 P resp lfd (prog : dec list) ⇔
    ∀sk. server_world2 lfd sk ⇒
         ∃io. semantics_prog (init_state (socket2_ffi sk)) init_env prog
                (Diverge io) ∧
              proto_safe2 P resp io ∧ proto_live2 P resp sk io ∧
              echo_closes2 io
End

(* MAIN: the approved HTTP spec is the generic one, for P_b *)
Theorem http_spec_b2_proto:
  http_spec_b2 lfd files prog ⇔
  proto_spec2 P_b (print_response o bhandle files) lfd prog
Proof
  simp[http_spec_b2_def, http_safe_b2_def, http_live_b2_def, http_closes_b2_def,
       brequests_def, bresponses_def, no_full_brequest_def,
       proto_spec2_def, proto_safe2_def, proto_live2_def, preqs_def, presps_def,
       no_full_def, P_b_def]
QED
