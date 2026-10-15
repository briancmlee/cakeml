(*
  The listener's queue, along the event loop's run (socket model).

   - grounds_known: every connection of the world has either been handed
     out to the program (an accept returned it) or waits in the listener's
     queue;
   - round_queued: a connection waiting in the queue stays there, behind
     no more connections than before, until it is handed out; each accept
     of the listener in a round moves it one place forward.
*)
Theory asyncM4Queue
Ancestors
  pair list rich_list arithmetic option llist alist
  ffiSpikeSocketFFI ffiSpikeSocketFair asyncM3World asyncM4GRounds
  asyncM4SockInv asyncM4GTrans asyncM4Sched
Libs
  preamble

(* The connections pending on listener l *)
Definition lq_def:
  lq l s = case ALOOKUP s.listeners l of SOME q => q | NONE => []
End

(* Connection c waits in l's queue, behind k connections *)
Definition queued_def:
  queued l c k s ⇔ ∃pre post. lq l s = pre ++ c :: post ∧ LENGTH pre = k
End

(* The accepts of l among a round's actions *)
Definition nacc_def:
  nacc l acts = LENGTH (FILTER (λa. a = Accept l) acts)
End

Theorem lq_AFUPDKEY:
  ALOOKUP s.listeners l' = SOME q ⇒
  lq l (s with listeners := AFUPDKEY l' f s.listeners) =
  if l = l' then f q else lq l s
Proof
  rw[lq_def, AFUPDKEY_ALOOKUP] >> CASE_TAC >> rw[]
QED

Theorem is_conn_AFUPDKEY_conns[local]:
  is_conn (s with conns := AFUPDKEY k f s.conns) c ⇔ is_conn s c
Proof
  simp[is_conn_def, AFUPDKEY_ALOOKUP] >> Cases_on ‘ALOOKUP s.conns c’ >> simp[]
QED

Theorem lq_conns[simp]:
  lq l (s with conns := x) = lq l s
Proof
  simp[lq_def]
QED

Theorem queued_ready:
  queued l c k s ⇒ is_ready s l
Proof
  rw[queued_def, lq_def, is_ready_def] >> every_case_tac >> gvs[]
QED

(* ------------------------------------------------------------------------
   Every connection is handed out or pending
   ------------------------------------------------------------------------ *)

Definition known_def:
  known l acc s ⇔ ∀c. is_conn s c ⇒ MEM c acc ∨ MEM c (lq l s)
End

Theorem sock_do_keys:
  sock_do s a = SOME (r, s') ⇒ MAP FST s'.listeners = MAP FST s.listeners
Proof
  Cases_on ‘a’ >> rw[sock_do_def, sock_accept_def, sock_read_def, sock_write_def]
  >> gvs[AllCaseEqs()]
QED

Theorem sock_acts_keys:
  ∀acts s rs evs s'.
    sock_acts s acts = SOME (rs, evs, s') ⇒ MAP FST s'.listeners = MAP FST s.listeners
Proof
  Induct >> rw[sock_acts_def] >> gvs[AllCaseEqs()]
  >> first_x_assum drule >> drule sock_do_keys >> simp[]
QED

Theorem sock_do_known:
  sock_do s a = SOME (r, s') ∧ known l acc s ⇒ known l (acc ++ wacc [(a, r)]) s'
Proof
  Cases_on ‘a’ >> rw[sock_do_def]
  >> gvs[sock_accept_def, sock_read_def, sock_write_def, AllCaseEqs(), wacc_def]
  >> gvs[known_def, is_conn_AFUPDKEY_conns]
  >> rpt strip_tac >> TRY (metis_tac[])
  >> rename1 ‘ALOOKUP s.listeners l' = SOME (h :: t)’
  >> gvs[is_conn_def] >> first_x_assum drule >> strip_tac >> simp[]
  >> drule lq_AFUPDKEY >> disch_then (qspecl_then [‘l’, ‘K t’] SUBST1_TAC)
  >> rw[] >> gvs[lq_def]
QED

Theorem sock_acts_known:
  ∀acts s rs evs s' acc.
    sock_acts s acts = SOME (rs, evs, s') ∧ known l acc s ⇒
    known l (acc ++ wacc (ZIP (acts, rs))) s'
Proof
  Induct >> rw[sock_acts_def] >> gvs[AllCaseEqs(), wacc_def]
  >> drule_all sock_do_known >> strip_tac
  >> first_x_assum drule_all >> simp[wacc_def]
QED

(* A new connection is queued on the listener, which is l *)
Theorem deliver1_known:
  MAP FST s.listeners = [l] ∧ known l acc s ⇒
  MAP FST (deliver1 s a).listeners = [l] ∧ known l acc (deliver1 s a)
Proof
  Cases_on ‘a’ >> rw[deliver1_def] >> gvs[known_def, is_conn_AFUPDKEY_conns]
  >> PairCases_on ‘x0’
  >> gvs[is_listener_def, AllCaseEqs(), AFUPDKEY_def, lq_def, is_conn_def]
  >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem tick_keys:
  MAP FST (tick s).listeners = MAP FST s.listeners
Proof
  simp[tick_def] >> CASE_TAC >> simp[deliver_def]
  >> ‘∀as s. MAP FST (FOLDL deliver1 s as).listeners = MAP FST s.listeners’
       suffices_by simp[]
  >> Induct >> simp[] >> Cases >> rw[deliver1_def]
QED

Theorem tick_known:
  MAP FST s.listeners = [l] ∧ known l acc s ⇒ known l acc (tick s)
Proof
  strip_tac >> simp[tick_def] >> CASE_TAC >> simp[deliver_def]
  >> ‘∀as s. MAP FST s.listeners = [l] ∧ known l acc s ⇒
             known l acc (FOLDL deliver1 s as)’
       by (Induct >> simp[] >> rpt strip_tac >> first_x_assum irule
           >> irule deliver1_known >> simp[])
  >> first_x_assum irule >> gvs[known_def, lq_def, is_conn_def]
QED

(* MAIN: every connection of the world, in every round, has been handed out
   to the program or is pending on the listener *)
Theorem grounds_known:
  s0.listeners = [(lfd, [])] ∧ s0.conns = [] ∧ grun_ok ifds m s0 ⇒
  ∀n. MAP FST (gstate ifds m s0 n).listeners = [lfd] ∧
      known lfd (wacc (gperf ifds m s0 n)) (gstate ifds m s0 n)
Proof
  strip_tac >> Induct
  >- simp[gstate_def, grounds_def, known_def, is_conn_def]
  >> drule grun_ok_sock_acts >> disch_then (qspec_then ‘n’ strip_assume_tac)
  >> ‘gmid ifds m s0 n = s'’ by simp[gmid_def, sock_acts_tot_def]
  >> qpat_x_assum ‘_ ∧ _’ strip_assume_tac
  >> drule_all sock_acts_known >> drule sock_acts_keys >> rpt strip_tac
  >> REWRITE_TAC[gstate_SUC, gperf_SUC, tick_keys, wacc_APPEND]
  >> TRY (irule tick_known) >> gvs[]
QED

(* ------------------------------------------------------------------------
   A pending connection moves forward
   ------------------------------------------------------------------------ *)

Theorem sock_do_queued:
  sock_do s a = SOME (r, s') ∧ queued l c k s ⇒
  (a = Accept l ∧ r = Accepted (SOME c)) ∨
  ∃k'. queued l c k' s' ∧ k' + nacc l [a] = k
Proof
  Cases_on ‘a’ >> rw[sock_do_def, nacc_def]
  >> gvs[sock_accept_def, sock_read_def, sock_write_def, AllCaseEqs()]
  >> gvs[queued_def] >> TRY (metis_tac[] >> NO_TAC) >> TRY (gvs[lq_def] >> NO_TAC)
  >> drule lq_AFUPDKEY >> disch_then (fn th => simp[th])
  >> TRY (qexistsl_tac [‘pre’, ‘post’] >> simp[] >> NO_TAC)
  (* an accept of l: c moves one place forward, or is the one accepted *)
  >> gvs[lq_def] >> Cases_on ‘pre’ >> gvs[]
  >> disj2_tac >> qexists_tac ‘LENGTH t’ >> simp[]
  >> qexistsl_tac [‘t’, ‘post’] >> simp[]
QED

Theorem sock_acts_queued:
  ∀acts s rs evs s' k.
    sock_acts s acts = SOME (rs, evs, s') ∧ queued l c k s ⇒
    MEM c (wacc (ZIP (acts, rs))) ∨ ∃k'. queued l c k' s' ∧ k' + nacc l acts = k
Proof
  Induct >- (rw[sock_acts_def, nacc_def] >> metis_tac[])
  >> rw[sock_acts_def] >> gvs[AllCaseEqs()]
  >> drule_all sock_do_queued >> strip_tac >> gvs[wacc_def]
  >> first_x_assum drule_all >> strip_tac >> gvs[wacc_def]
  >> disj2_tac >> qexists_tac ‘k''’ >> gvs[nacc_def] >> rw[]
QED

(* An arrival only appends to the queue *)
Theorem lq_deliver1:
  ∃x. lq l (deliver1 s a) = lq l s ++ x
Proof
  Cases_on ‘a’ >> rw[deliver1_def, lq_def, AFUPDKEY_ALOOKUP] >> every_case_tac >> gvs[]
QED

Theorem deliver1_queued:
  queued l c k s ⇒ queued l c k (deliver1 s a)
Proof
  rw[queued_def] >> qspecl_then [‘l’, ‘s’, ‘a’] strip_assume_tac
    (Q.GENL [‘l’, ‘s’, ‘a’] lq_deliver1)
  >> qexistsl_tac [‘pre’, ‘post ++ x’] >> simp[]
QED

Theorem tick_queued:
  queued l c k s ⇒ queued l c k (tick s)
Proof
  strip_tac >> simp[tick_def] >> CASE_TAC >> simp[deliver_def]
  >> ‘∀as s. queued l c k s ⇒ queued l c k (FOLDL deliver1 s as)’
       by (Induct >> simp[] >> rpt strip_tac >> first_x_assum irule
           >> irule deliver1_queued >> simp[])
  >> first_x_assum irule >> gvs[queued_def, lq_def] >> metis_tac[]
QED

(* MAIN: in one round, a pending connection is handed out, or stays
   pending and moves one place forward for each accept of the listener *)
Theorem round_queued:
  grun_ok ifds m s0 ∧ queued l c k (gstate ifds m s0 n) ⇒
  MEM c (wacc (gperf ifds m s0 (SUC n))) ∨
  ∃k'. queued l c k' (gstate ifds m s0 (SUC n)) ∧
       k' + nacc l (gacts ifds m s0 n) = k
Proof
  strip_tac >> drule grun_ok_sock_acts >> disch_then (qspec_then ‘n’ strip_assume_tac)
  >> ‘gmid ifds m s0 n = s'’ by simp[gmid_def, sock_acts_tot_def]
  >> drule_all sock_acts_queued >> strip_tac
  >- simp[gperf_SUC]
  >> disj2_tac >> qexists_tac ‘k'’ >> simp[gstate_SUC, tick_queued]
QED

Theorem rounds_queued:
  grun_ok ifds m s0 ⇒
  ∀d k. queued l c k (gstate ifds m s0 n) ⇒
        MEM c (wacc (gperf ifds m s0 (n + d))) ∨
        ∃k'. queued l c k' (gstate ifds m s0 (n + d)) ∧ k' ≤ k
Proof
  strip_tac >> Induct >- (simp[] >> metis_tac[LESS_EQ_REFL])
  >> rpt strip_tac >> first_x_assum drule >> strip_tac
  >> ‘n + SUC d = SUC (n + d)’ by simp[] >> pop_assum SUBST1_TAC
  >- gvs[gperf_SUC]
  >> drule_all round_queued >> strip_tac >> gvs[]
  >> disj2_tac >> qexists_tac ‘k''’ >> gvs[]
QED
