(*
  KV on the kernel, the accept clause of kv_live_claim (decision 8):
  conn_live_l0 for the PF KV m = srelabel (kv_server lfdn) polled through
  the live list (D26), on its trace io, from pf_conn_live with KV's S1
  (kv_S1), S2 (kv_S2) and F1 from F1_io; as honestEchoL0Live's
  echo_conn_live(_trace).

  MAIN: kv_conn_live, kv_conn_live_trace.
*)
Theory honestKvConnLive
Ancestors
  honestKvAsksEp honestKvReadSoonPF honestKvL0Obl honestL1PFConnTrace honestL1PFObl
  honestL1BConn honestL1PFConnRun honestL1PFConn honestL1PFLive honestL1PFRound
  honestL1BStmts asyncM4Loop
Libs
  preamble

(* MAIN: raw liveness for connections of the PF KV, on its trace *)
Theorem kv_conn_live:
  kv_run lfdn pol w0 ∧ linv (n2w lfdn) w0 ∧ lone (n2w lfdn) w0 ∧
  pftrace (n2w lfdn) pol KI KS w0 io ∧ F1_io io ⇒
  conn_live_l0 w0 io
Proof
  strip_tac >>
  ‘run_ok (n2w lfdn) pol KI KS w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0) ∧
   (∀n. SND (pcm (n2w lfdn) pol KI KS w0 n) + 1 < dimword (:64))’
    by fs[kv_run_def] >>
  ‘F1 (n2w lfdn) pol KI KS w0’ by metis_tac[F1_io_F1] >>
  ‘S1 (n2w lfdn) pol KI KS w0’ by (irule kv_S1 >> first_assum ACCEPT_TAC) >>
  ‘S2 (n2w lfdn) pol KI KS w0’ by (irule kv_S2 >> first_assum ACCEPT_TAC) >>
  metis_tac[pf_conn_live]
QED

(* MAIN (statement premises): the client bound comes from the trace's
   accepts_below *)
Theorem kv_conn_live_trace:
  run_ok (n2w lfdn) pol KI KS w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0) ∧
  lfdn < dimword (:64) ∧ linv (n2w lfdn) w0 ∧ lone (n2w lfdn) w0 ∧
  pftrace (n2w lfdn) pol KI KS w0 io ∧ F1_io io ∧ accepts_below io ⇒
  conn_live_l0 w0 io
Proof
  strip_tac >>
  ‘∀n. SND (pcm (n2w lfdn) pol KI KS w0 n) + 1 < dimword (:64)’
    by metis_tac[pcm_bound_accepts_below] >>
  ‘kv_run lfdn pol w0’
    by (PURE_REWRITE_TAC[kv_run_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  metis_tac[kv_conn_live]
QED
