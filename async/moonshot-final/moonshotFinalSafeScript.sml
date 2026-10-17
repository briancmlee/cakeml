(*
  The moonshot's safety headline at the concrete client binary: from
  moonshot_safe_holds and close-v2's client_prog_l0_claim.  The proxy and
  KV claims (proxy_claim_safe, kv_claim_safe) stay hypotheses; each becomes
  a one-line discharge once its program's claim lands (m4-server's
  l0_proxy_claim; KV's P4 with e1-driver).

  MAIN: moonshot_safe_client.
*)
Theory moonshotFinalSafe
Ancestors
  moonshotHeadline moonshotStep12Stmts moonshotClientL0
Libs
  preamble

Theorem moonshot_safe_client:
  proxy_claim_safe kt hw pprog ∧ kv_claim_safe kprog ⇒
  ∀a b c N rqs rs.
    a < 65536 ∧ b < 65536 ∧ c < 65536 ∧ a ≠ b ∧ c ≠ a ∧ c ≠ b ∧
    2 ≤ N ∧ N < 2 ** 63 ∧ (∀i. EVERY valid_brequest (rqs i)) ∧
    l0sys_iso_run (moonshot_sys client_prog pprog kprog a b c N rqs) a b rs ⇒
    kv_client_safe (conn_only l0_ep_sent) (conn_only l0_ep_recvd)
                   (fromList (proc_events client_ix rs))
Proof
  strip_tac >>
  mp_tac (INST [mk_var ("cprog", type_of “client_prog”) |-> “client_prog”]
            moonshotHeadlineTheory.moonshot_safe_holds) >>
  rewrite_tac[moonshot_safe_stmt_def] >>
  impl_tac
  >- (rpt conj_tac >>
      FIRST [ACCEPT_TAC moonshotClientL0Theory.client_prog_l0_claim, first_assum ACCEPT_TAC]) >>
  disch_then ACCEPT_TAC
QED
