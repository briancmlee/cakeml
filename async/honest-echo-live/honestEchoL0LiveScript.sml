(*
  The echo on the kernel, liveness (design/47), for the PF echo
  m = srelabel (server lfdn) polled through interest [n2w lfdn], on its
  trace io (pftrace):
   - echo_conn_live: conn_live_l0 (C), from pf_conn_live with the echo's
     S1 (honestL1PFObl), S2 (honestEchoL0Obl) and F1 from F1_io;
   - echo_live_l0: to come (D), with honest-ffi's flush_live.
*)
Theory honestEchoL0Live
Ancestors
  honestL1PFConnTrace honestEchoL0Obl honestL1PFObl honestL1BConn honestL1PFConnRun
  honestL1PFConn honestL1PFLive honestL1PFRound honestL1BStmts asyncM4Loop
Libs
  preamble

(* MAIN (C): raw liveness for connections of the PF echo, on its trace *)
Theorem echo_conn_live:
  echo_run lfdn pol w0 ∧ linv (n2w lfdn) w0 ∧ lone (n2w lfdn) w0 ∧
  pftrace (n2w lfdn) pol EI ES w0 io ∧ F1_io io ⇒
  conn_live_l0 w0 io
Proof
  strip_tac >> drule echo_run_hyp >> strip_tac >>
  ‘run_ok (n2w lfdn) pol EI ES w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0) ∧
   (∀n. SND (pcm (n2w lfdn) pol EI ES w0 n) + 1 < dimword (:64)) ∧ fds_lt w0’
    by fs[echo_run_def, run_hyp_def] >>
  ‘F1 (n2w lfdn) pol EI ES w0’ by metis_tac[F1_io_F1] >>
  ‘S1 (n2w lfdn) pol EI ES w0’ by (irule S1_interest >> simp[]) >>
  ‘S2 (n2w lfdn) pol EI ES w0’ by metis_tac[echo_S2] >>
  metis_tac[pf_conn_live]
QED

(* MAIN (C, statement premises): the client bound comes from the trace's
   accepts_below *)
Theorem echo_conn_live_trace:
  run_ok (n2w lfdn) pol EI ES w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0) ∧
  lfdn < dimword (:64) ∧ linv (n2w lfdn) w0 ∧ lone (n2w lfdn) w0 ∧
  pftrace (n2w lfdn) pol EI ES w0 io ∧ F1_io io ∧ accepts_below io ⇒
  conn_live_l0 w0 io
Proof
  strip_tac >>
  ‘∀n. SND (pcm (n2w lfdn) pol EI ES w0 n) + 1 < dimword (:64)’
    by metis_tac[pcm_bound_accepts_below] >>
  ‘echo_run lfdn pol w0’
    by (PURE_REWRITE_TAC[echo_run_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  metis_tac[echo_conn_live]
QED
