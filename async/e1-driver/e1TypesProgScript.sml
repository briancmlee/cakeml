(*
  The E1 driver's translator types: the endpoint handle layer's actions and
  responses, and E1's L1 state (honestL1EPModel), registered on top of the
  prefetching L1's translation (honestL1PFProg).

  The programs the driver runs (the moonshot client and proxy) translate
  their fold steps on top of this theory, and later on top of e1DriverProg
  (the driver's code), which extends this one.
*)
Theory e1TypesProg
Ancestors
  ml_translator endpointHLModel honestL1PFModel honestL1EPModel honestL1PFProg
Libs
  preamble ml_translatorLib ml_progLib

val _ = translation_extends "honestL1PFProg";

val _ = register_type “:eact”;
val _ = register_type “:eresp”;
val _ = register_type “:cstat”;
val _ = register_type “:l1e”;

(* The proxy's and the client's pause policy (never pause; design/45 Q1) *)
val r = translate pol_never_def;
