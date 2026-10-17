(*
  Moonshot step 12, the headline: moonshot_safe_stmt holds outright, its
  only hypotheses being the three per-program claims (l0_client_claim,
  proxy_claim_safe, kv_claim_safe) inside the statement.  From
  moonshotStep12's moonshot_safe and m4-server's b2_iso_stmt_holds.
*)
Theory moonshotHeadline
Ancestors
  moonshotStep12 moonshotB2Iso moonshotStep12Stmts
Libs
  preamble

Theorem moonshot_safe_holds:
  moonshot_safe_stmt kt hw cprog pprog kprog
Proof
  irule moonshotStep12Theory.moonshot_safe >>
  ACCEPT_TAC moonshotB2IsoTheory.b2_iso_stmt_holds
QED
