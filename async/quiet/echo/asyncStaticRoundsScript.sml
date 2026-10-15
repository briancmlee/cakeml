(*
  The socket world after the last arrival (option C, design/33 §2.5).

  When a schedule delivers finitely many arrivals (QuietSpec's
  arrivals_finite), the event loop's run reaches a round N after which
  ticks deliver nothing (static_after).  In such a static round the world
  changes only by the program's own actions, and exactly:
  - the listener's queue shrinks by the connections accepted;
  - a connection's unread bytes shrink by the bytes read from it;
  - whether its peer has closed does not change.
  (static_round.)  These are the bookkeeping of the quiescence measure.

  MAIN: static_after, static_round.
*)
Theory asyncStaticRounds
Ancestors
  pair list rich_list arithmetic option llist alist
  ffiSpikeSocketFFI ffiSpikeSocketFair asyncM3World asyncM4GRounds
  asyncM4GTrans asyncM4Sched asyncM4Queue EchoSpec QuietSpec
Libs
  preamble

(* ------------------------------------------------------------------------
   What a round's performed actions take
   ------------------------------------------------------------------------ *)

(* The connections accepted from listener l *)
Definition nacc_ok_def:
  nacc_ok l (ps : (sact # sresp) list) =
    LENGTH (FILTER (λp. ∃c. p = (Accept l, Accepted (SOME c))) ps)
End

(* The bytes read from connection c *)
Definition rdbytes_def:
  rdbytes c (ps : (sact # sresp) list) =
    SUM (MAP (λp. case p of
                  | (Read c' k, Got (SOME d)) => if c' = c then LENGTH d else 0
                  | _ => 0) ps)
End

Theorem counts_NIL[simp]:
  nacc_ok l [] = 0 ∧ rdbytes c [] = 0
Proof
  simp[nacc_ok_def, rdbytes_def]
QED

Theorem counts_CONS:
  nacc_ok l (p :: ps) = nacc_ok l [p] + nacc_ok l ps ∧
  rdbytes c (p :: ps) = rdbytes c [p] + rdbytes c ps
Proof
  simp[nacc_ok_def, rdbytes_def] >> rw[]
QED

(* One action *)
Theorem sock_do_counts:
  sock_do s a = SOME (r, s') ⇒
  LENGTH (lq l s') + nacc_ok l [(a, r)] = LENGTH (lq l s) ∧
  (∀c. ALOOKUP s.conns c = NONE ⇒
       ALOOKUP s'.conns c = NONE ∧ rdbytes c [(a, r)] = 0) ∧
  ∀c cn. ALOOKUP s.conns c = SOME cn ⇒
         ∃cn'. ALOOKUP s'.conns c = SOME cn' ∧ cn'.peer_closed = cn.peer_closed ∧
               LENGTH cn'.incoming + rdbytes c [(a, r)] = LENGTH cn.incoming
Proof
  Cases_on ‘a’ >>
  rw[sock_do_def, sock_accept_def, sock_read_def, sock_write_def] >>
  gvs[AllCaseEqs(), nacc_ok_def, rdbytes_def, lq_def, AFUPDKEY_ALOOKUP] >>
  rw[] >> gvs[] >>
  TRY (Cases_on ‘ALOOKUP s.listeners l’ >> gvs[]) >>
  TRY (Cases_on ‘c' = c’ >> gvs[]) >> rw[LENGTH_TAKE_EQ]
QED

(* MAIN (the world): a round's actions *)
Theorem sock_acts_counts:
  ∀acts s rs evs s'.
    sock_acts s acts = SOME (rs, evs, s') ⇒
    LENGTH (lq l s') + nacc_ok l (ZIP (acts, rs)) = LENGTH (lq l s) ∧
    (∀c. ALOOKUP s.conns c = NONE ⇒
         ALOOKUP s'.conns c = NONE ∧ rdbytes c (ZIP (acts, rs)) = 0) ∧
    ∀c cn. ALOOKUP s.conns c = SOME cn ⇒
           ∃cn'. ALOOKUP s'.conns c = SOME cn' ∧ cn'.peer_closed = cn.peer_closed ∧
                 LENGTH cn'.incoming + rdbytes c (ZIP (acts, rs)) = LENGTH cn.incoming
Proof
  Induct >> simp[sock_acts_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> rename1 ‘sock_do s h = SOME (r, s1)’ >>
  drule sock_do_counts >> disch_then (qspec_then ‘l’ strip_assume_tac) >>
  last_x_assum drule >> strip_tac >>
  ONCE_REWRITE_TAC[counts_CONS] >> rpt conj_tac
  >- simp[]
  >- (rpt gen_tac >> strip_tac >> res_tac >> res_tac >> simp[])
  >> rpt strip_tac >>
  qpat_x_assum ‘∀c cn. ALOOKUP s.conns c = SOME cn ⇒ _’ drule >> strip_tac >>
  qpat_x_assum ‘∀c cn. ALOOKUP s1.conns c = SOME cn ⇒ _’ drule >> strip_tac >>
  simp[]
QED

(* ------------------------------------------------------------------------
   Static rounds
   ------------------------------------------------------------------------ *)

(* A tick that delivers nothing changes nothing but the schedule *)
Theorem tick_static:
  next_step s = [] ⇒ (tick s).listeners = s.listeners ∧ (tick s).conns = s.conns
Proof
  rw[tick_def, next_step_def] >> CASE_TAC >> gvs[deliver_def]
QED

Theorem arrivals_upto_one[local]:
  arrivals_upto 1 s.sched = next_step s
Proof
  REWRITE_TAC[ONE] >> simp[arrivals_upto_tick] >> simp[arrivals_upto_def]
QED

(* MAIN: after finitely many arrivals, every round is static *)
Theorem static_after:
  arrivals_finite s0 ⇒ ∃N. ∀n. N ≤ n ⇒ next_step (gstate ifds m s0 n) = []
Proof
  rw[arrivals_finite_def] >> qexists_tac ‘N’ >> rpt strip_tac >>
  qspecl_then [‘n’, ‘1’] mp_tac grounds_arrivals >>
  ‘arrivals_upto (n + 1) s0.sched = arrivals_upto N s0.sched ∧
   arrivals_upto n s0.sched = arrivals_upto N s0.sched’ by simp[] >>
  simp[arrivals_upto_one]
QED

(* MAIN (the run): in a static round, the queue shrinks by the accepts and
   each connection's unread bytes by the bytes read *)
Theorem static_round:
  grun_ok ifds m s0 ∧ next_step (gstate ifds m s0 n) = [] ⇒
  LENGTH (lq l (gstate ifds m s0 (SUC n))) +
    nacc_ok l (ZIP (gacts ifds m s0 n, gres ifds m s0 n)) =
  LENGTH (lq l (gstate ifds m s0 n)) ∧
  (∀c. ALOOKUP (gstate ifds m s0 n).conns c = NONE ⇒
       ALOOKUP (gstate ifds m s0 (SUC n)).conns c = NONE ∧
       rdbytes c (ZIP (gacts ifds m s0 n, gres ifds m s0 n)) = 0) ∧
  ∀c cn. ALOOKUP (gstate ifds m s0 n).conns c = SOME cn ⇒
         ∃cn'. ALOOKUP (gstate ifds m s0 (SUC n)).conns c = SOME cn' ∧
               cn'.peer_closed = cn.peer_closed ∧
               LENGTH cn'.incoming +
                 rdbytes c (ZIP (gacts ifds m s0 n, gres ifds m s0 n)) =
               LENGTH cn.incoming
Proof
  strip_tac >> drule grun_ok_sock_acts >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  ‘gmid ifds m s0 n = s'’ by simp[gmid_def, sock_acts_tot_def] >>
  ‘next_step (gmid ifds m s0 n) = []’ by gvs[next_step_def, gmid_sched] >>
  drule tick_static >> strip_tac >>
  drule sock_acts_counts >> strip_tac >>
  gvs[gstate_SUC, lq_def]
QED
