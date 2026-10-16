(*
  Option C, headline: the HTTP-bodies program on the select-on-interest
  loop meets QuietSpec, unconditionally.

  httpQuietStable proves http_blocking_quiet_stable under PROTO_STABLE (the server's
  stability after the last arrival); cf-actions' proto_stable
  (protoStable) proves it, for every protocol.

  MAIN: proto_stable_holds, http_blocking_quiet.
*)
Theory httpQuietHeadline
Ancestors
  protoStable httpQuietStable
Libs
  preamble

Theorem proto_stable_holds:
  PROTO_STABLE P resp
Proof
  rw[PROTO_STABLE_def] >> irule proto_stable >> simp[]
QED

(* MAIN: ⊢ the HTTP-bodies program on the select-on-interest loop meets
   QuietSpec's HTTP statement *)
Theorem http_blocking_quiet:
  http_quiet 3w demo_files (SNOC (main_call «main») http_blocking_prog)
Proof
  irule http_blocking_quiet_stable >> simp[proto_stable_holds]
QED
