(*
  Per-connection accounting in the socket world, along the event loop's run.

  For every connection c, after n rounds:
     sent_upto c n s0 = (bytes the program read from c) ++ c's unread data
     c's outgoing     = (bytes the program wrote to c)
  where "read" / "written" are over the performed (action, response) pairs
  gperf (asyncM4GTrans).  Before c exists, nothing has been sent on it,
  read from it or written to it.

  This uses that every arrival of the run is effective (asyncM4Sched,
  from sched_wf), that the socket operations only move data from a
  connection's incoming buffer to the program, and that a connection
  starts empty.
*)
Theory asyncM4Account
Ancestors
  pair list rich_list arithmetic option llist alist
  ffiSpikeSocketFFI ffiSpikeSocketFair EchoSpec asyncM3World asyncM4GRounds
  asyncM4GTrans asyncM4Sched
Libs
  preamble

(* What the program has read from / written to c, over performed pairs *)
Overload pread_all = “λc ps. FLAT (MAP (pread c) ps)”
Overload pwritten_all = “λc ps. FLAT (MAP (pwritten c) ps)”

(* The accounting for connection c, in world s, after performed pairs ps,
   with sent the data sent on c so far *)
Definition acct_def:
  acct c sent ps s ⇔
    case ALOOKUP s.conns c of
    | SOME cn => sent = pread_all c ps ++ cn.incoming ∧
                 cn.outgoing = pwritten_all c ps
    | NONE => sent = [] ∧ pread_all c ps = [] ∧ pwritten_all c ps = []
End

(* ------------------------------------------------------------------------
   The program's operations
   ------------------------------------------------------------------------ *)

Theorem sock_do_acct:
  sock_do s a = SOME (r, s') ∧ acct c sent ps s ⇒ acct c sent (ps ++ [(a, r)]) s'
Proof
  Cases_on ‘a’ >> rw[sock_do_def]
  >> gvs[sock_accept_def, sock_read_def, sock_write_def, AllCaseEqs(), acct_def,
         pread_def, pwritten_def, AFUPDKEY_ALOOKUP]
  >> rpt (CASE_TAC >> gvs[pread_def, pwritten_def]) >> rw[] >> gvs[]
QED

Theorem sock_acts_acct:
  ∀acts s ps rs evs s'.
    sock_acts s acts = SOME (rs, evs, s') ∧ acct c sent ps s ⇒
    acct c sent (ps ++ ZIP (acts, rs)) s'
Proof
  Induct >> rw[sock_acts_def] >> gvs[AllCaseEqs()]
  >> drule_all sock_do_acct >> strip_tac
  >> first_x_assum drule_all >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND]
QED

(* ------------------------------------------------------------------------
   Arrivals
   ------------------------------------------------------------------------ *)

Theorem deliver1_sched:
  deliver1 (s with sched := x) a = (deliver1 s a) with sched := x
Proof
  Cases_on ‘a’ >> rw[deliver1_def, is_listener_def, is_conn_def]
QED

Theorem step_ok_sched:
  ∀as s. step_ok (s with sched := x) as ⇔ step_ok s as
Proof
  Induct >> simp[step_ok_def, deliver1_sched]
  >> Cases >> simp[arrival_ok_def, is_listener_def, is_conn_def]
QED

Theorem acct_sched[simp]:
  acct c sent ps (s with sched := x) ⇔ acct c sent ps s
Proof
  simp[acct_def]
QED

(* An effective arrival: data for c is appended to c's unread data; a new
   connection starts empty *)
Theorem deliver1_acct:
  arrival_ok s a ∧ acct c sent ps s ⇒
  acct c (sent ++ sent_of c [a]) ps (deliver1 s a)
Proof
  Cases_on ‘a’
  >> rw[arrival_ok_def, deliver1_def, sent_of_def, acct_def, AFUPDKEY_ALOOKUP,
        is_conn_def, empty_conn_def]
  >> Cases_on ‘ALOOKUP s.conns c’ >> gvs[acct_def, AllCaseEqs()] >> rw[] >> gvs[]
QED

Theorem deliver_acct:
  ∀as s sent. step_ok s as ∧ acct c sent ps s ⇒
              acct c (sent ++ sent_of c as) ps (FOLDL deliver1 s as)
Proof
  Induct >> simp[sent_of_def] >> rw[step_ok_def]
  >> drule_all deliver1_acct >> strip_tac
  >> first_x_assum drule_all >> simp[sent_of_def]
QED

Theorem tick_acct:
  step_ok s (next_step s) ∧ acct c sent ps s ⇒
  acct c (sent ++ sent_of c (next_step s)) ps (tick s)
Proof
  rw[tick_def, next_step_def] >> CASE_TAC >> gvs[sent_of_def, deliver_def]
  >> irule (SIMP_RULE (srw_ss()) [sent_of_def] deliver_acct)
  >> simp[step_ok_sched]
QED

(* ------------------------------------------------------------------------
   Along the run
   ------------------------------------------------------------------------ *)

(* MAIN: the accounting holds after every round of the run, for every
   connection, in a world that starts with no connections *)
Theorem grounds_acct:
  s0.conns = [] ∧ sched_wf s0 ∧ grun_ok ifds m s0 ⇒
  ∀n. acct c (sent_upto c n s0) (gperf ifds m s0 n) (gstate ifds m s0 n)
Proof
  strip_tac >> Induct
  >- simp[acct_def, sent_upto_def, arrivals_upto_def, gperf_def, gstate_def,
          grounds_def]
  >> ONCE_REWRITE_TAC[sent_upto_SUC] >> simp[gperf_SUC, gstate_SUC]
  >> irule tick_acct >> conj_tac
  >- (qspecl_then [‘s0’, ‘m’, ‘ifds’] mp_tac (Q.GENL [‘s0’, ‘m’, ‘ifds’] grounds_step_ok)
      >> simp[])
  >> drule grun_ok_sock_acts >> disch_then (qspec_then ‘n’ strip_assume_tac)
  >> ‘gmid ifds m s0 n = s'’ by simp[gmid_def, sock_acts_tot_def]
  >> simp[] >> drule_all sock_acts_acct >> simp[]
QED
