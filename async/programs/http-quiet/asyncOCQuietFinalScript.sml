(*
  Option C, headline: the HTTP-bodies program on the select-on-interest
  loop meets QuietSpec, unconditionally.

  asyncOCQuietB proves http_q_quiet_b under PROTO_STABLE (the server's
  stability after the last arrival); cf-actions' proto_stable
  (asyncProtoStable) proves it, for every protocol.

  MAIN: proto_stable_holds, http_q_quiet.
*)
Theory asyncOCQuietFinal
Ancestors
  asyncProtoStable asyncOCQuietB
Libs
  preamble

Theorem proto_stable_holds:
  PROTO_STABLE P resp
Proof
  rw[PROTO_STABLE_def] >> irule proto_stable >> simp[]
QED

(* MAIN: ⊢ the HTTP-bodies program on the select-on-interest loop meets
   QuietSpec's HTTP statement *)
Theorem http_q_quiet:
  http_quiet_b 3w demo_files (SNOC (main_call «main») http_q_prog)
Proof
  irule http_q_quiet_b >> simp[proto_stable_holds]
QED
