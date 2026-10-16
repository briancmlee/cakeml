(*
  Liveness of the echo server's I/O, against EchoSpec's echo_live.

  The event loop's I/O is the stream of its rounds' events (run_i_spec,
  asyncM4Loop):
     io = LFLATTEN (LGENLIST (λi. fromList (grounds_events (EI lfdn) (EM lfdn) s0 i)) NONE)
  For every connection c and every n, the data c's client sends in the
  first n steps of the schedule is eventually echoed on c:
   - if c is not a connection after n rounds, nothing was sent on it
     (grounds_acct);
   - otherwise c is eventually handed out to the server (conn_accepted),
     after which everything sent so far is written back (accepted_live).
*)
Theory asyncM4EchoLive
Ancestors
  pair list rich_list arithmetic option llist alist words
  ffiSpikeSocketFFI ffiSpikeSocketFair EchoSpec asyncM3World asyncM4GRounds
  asyncM4SockInv asyncM4GTrans asyncM4EchoRunOk asyncM4Sched asyncM4Account
  asyncM4ReadSoon asyncM4Drain asyncM4Queue asyncM4AcceptSoon
Libs
  preamble

(* MAIN: everything a client sends in the first n steps is eventually
   written back on its connection, within finitely many rounds *)
Theorem echo_comp_live:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ⇒
  ∃N. sent_upto c n s0 ≼
      bytes_written_to c (FLAT (GENLIST (grounds_events (EI lfdn) (EM lfdn) s0) N))
Proof
  strip_tac
  >> ‘grun_ok (EI lfdn) (EM lfdn) s0’ by (irule echo_grun_ok >> simp[])
  >> Cases_on ‘is_conn (gstate (EI lfdn) (EM lfdn) s0 n) c’
  (* a connection: it is handed out at some round N *)
  >- (qspecl_then [‘s0’, ‘lfdn’, ‘n’, ‘c’] mp_tac
        (Q.GENL [‘s0’, ‘lfdn’, ‘n’, ‘c’] conn_accepted)
      >> impl_tac >- fs[] >> strip_tac
      >> ‘MEM c (wacc (SP lfdn (EI lfdn) s0 (n + N)))’
           by (irule wacc_mono >> qexists_tac ‘N’ >> simp[])
      >> qspecl_then [‘s0’, ‘lfdn’, ‘c’, ‘n + N’] mp_tac
           (Q.GENL [‘s0’, ‘lfdn’, ‘c’, ‘n’] accepted_live)
      >> impl_tac >- fs[] >> strip_tac
      >> qexists_tac ‘SUC N'’ >> irule IS_PREFIX_TRANS
      >> qexists_tac ‘sent_upto c (n + N) s0’ >> simp[sent_upto_prefix])
  (* not a connection after n rounds: nothing was sent on it *)
  >> qexists_tac ‘0’
  >> qspecl_then [‘EI lfdn’, ‘EM lfdn’, ‘s0’, ‘c’] mp_tac
       (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘c’] grounds_acct)
  >> impl_tac >- fs[] >> disch_then (qspec_then ‘n’ mp_tac)
  >> gvs[acct_def, is_conn_def]
QED

(* MAIN: the event loop's I/O satisfies EchoSpec's liveness *)
Theorem echo_live_rounds:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ⇒
  echo_live s0
    (LFLATTEN (LGENLIST (λi. fromList (grounds_events (EI lfdn) (EM lfdn) s0 i)) NONE))
Proof
  rw[echo_live_def]
  >> qspecl_then [‘s0’, ‘lfdn’, ‘c’, ‘n’] mp_tac
       (Q.GENL [‘s0’, ‘lfdn’, ‘c’, ‘n’] echo_comp_live)
  >> impl_tac >- fs[] >> strip_tac
  >> qexists_tac ‘FLAT (GENLIST (grounds_events (EI lfdn) (EM lfdn) s0) N)’
  >> simp[rounds_LPREFIX]
QED
