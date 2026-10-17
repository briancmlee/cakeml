(*
  The proxy's liveness parts of l0_proxy_claim (proxyL0Stmts, rev 10),
  STATED over m4-server's run (proxyL0Run): from the start proxy_start
  and E1's rounds never failing (totality), on the proxy's whole trace
  proxy_run_io and its pairing proxy_pr, under the claim's live-block
  hypotheses (F1_io, F2, accepts_below):
   - proxy_live_run: proxy_live_l0 (relay, conditional on draining);
   - proxy_pairs_run: proxy_pairs_l0 (every front gets a backend);
   - conn_live_run: under accepts_lt (2 ** 62) (plain prefix form, as
     moonshot-live's accepts_lt_lift concludes), conn_live_l0.
  K is L1's write timeout pf_sendwait (D23), as l0_proxy_claim's header
  has it.  Statements only; proofs to come.
*)
Theory proxyLiveLift
Ancestors
  proxyL0Run proxyL0Stmts honestL1BStmts honestL1PFModel e1DriverLoop
Libs
  preamble

(* The run and the live block's hypotheses *)
Definition proxy_live_hyps_def:
  proxy_live_hyps a b hw w0 pre w4 k ⇔
    a < 65536 ∧ b < 65536 ∧ proxy_start a w0 pre w4 k ∧
    (∀n. erounds (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4, einit) n ≠ NONE) ∧
    F1_io (proxy_run_io b hw k w4 pre) ∧ F2 w0 ∧ accepts_below (proxy_run_io b hw k w4 pre)
End

Definition proxy_live_run_def:
  proxy_live_run ⇔
    ∀a b hw w0 pre w4 k.
      proxy_live_hyps a b hw w0 pre w4 k ⇒
      proxy_live_l0 pf_sendwait (proxy_pr a b hw k w4 (proxy_run_io b hw k w4 pre)) w0
                    (proxy_run_io b hw k w4 pre)
End

Definition proxy_pairs_run_def:
  proxy_pairs_run ⇔
    ∀a b hw w0 pre w4 k.
      proxy_live_hyps a b hw w0 pre w4 k ⇒
      proxy_pairs_l0 pf_sendwait (proxy_pr a b hw k w4 (proxy_run_io b hw k w4 pre))
                     (proxy_run_io b hw k w4 pre)
End

Definition conn_live_run_def:
  conn_live_run ⇔
    ∀a b hw w0 pre w4 k.
      proxy_live_hyps a b hw w0 pre w4 k ∧ accepts_lt (2 ** 62) (proxy_run_io b hw k w4 pre) ⇒
      conn_live_l0 w0 (proxy_run_io b hw k w4 pre)
End
