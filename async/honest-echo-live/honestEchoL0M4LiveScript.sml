(*
  D26 for the echo, at M4: the M4 echo's liveness (asyncM4EchoLive's
  echo_comp_live) for the loop polled through the live interest list
  (asyncM4LiveInterest).  The proofs are asyncM4AcceptSoon's
  queue_progress / conn_accepted, asyncM4Drain's drain_step / drain /
  accepted_live and asyncM4EchoLive's echo_comp_live, with cf-actions'
  live lemmas (asyncM4LiveSoon) for read_soon_s and accept_soon_s.  Their
  no-end-of-file premises:
   - accept_soon_live: the echo never reads its listener
     (echo_no_listener_read);
   - read_soon_live: c has unread data, and a read of c that returned
     end-of-file leaves it none for good (asyncM4LiveWorld's grounds_eof).

  MAIN: echo_comp_live_l.
*)
Theory honestEchoL0M4Live
Ancestors
  asyncM4LiveSoon asyncM4NoListenRead asyncM4LiveAcc asyncM4LiveInterest
  asyncM4EchoLive asyncM4Drain asyncM4AcceptSoon asyncM4Queue asyncM4ReadSoon
  asyncM4LiveWorld asyncM4LiveProg asyncM4Account asyncM4EchoSafe asyncM4EchoRunOk
  asyncM4Sched asyncM4GTrans asyncM4GRounds asyncM4SockInv asyncM4Loop asyncM3World
  EchoSpec ffiSpikeSocketFFI
Libs
  preamble

Overload LV = “λlfdn. asyncM4LiveInterest$live [n2w lfdn : word64] (log_of (srelabel (server lfdn)))”
Overload EM = “λlfdn. srelabel (server lfdn)”

(* Unread data on c: no read of c has returned end-of-file *)
Theorem incoming_noeof:
  grun_ok ifds m s0 ∧ ALOOKUP (gstate ifds m s0 n).conns c = SOME cn ∧ cn.incoming ≠ [] ⇒
  ∀k. ¬MEM (Read c k, Got (SOME [])) (gperf ifds m s0 n)
Proof
  rpt strip_tac >> drule_all grounds_eof >> strip_tac >> gvs[]
QED

(* ------------------------------------------------------------------------
   Queued connections are handed out (asyncM4AcceptSoon)
   ------------------------------------------------------------------------ *)

Theorem queue_progress_l:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ⇒
  ∀k n. queued (n2w lfdn) c k (gstate (LV lfdn) (EM lfdn) s0 n) ⇒
        ∃N. MEM c (wacc (SP lfdn (LV lfdn) s0 N))
Proof
  strip_tac
  >> ‘grun_ok (LV lfdn) (EM lfdn) s0’ by (irule echo_grun_ok >> simp[])
  >> completeInduct_on ‘k’ >> rpt strip_tac
  >> Cases_on ‘MEM c (wacc (SP lfdn (LV lfdn) s0 (n + 3)))’ >- metis_tac[]
  (* not handed out by round n + 3: still pending in rounds n .. n + 3 *)
  >> ‘∀d. d ≤ 3 ⇒ ∃k'. queued (n2w lfdn) c k' (gstate (LV lfdn) (EM lfdn) s0 (n + d)) ∧
                       k' ≤ k’
       by (rpt strip_tac
           >> qspecl_then [‘LV lfdn’, ‘EM lfdn’, ‘s0’, ‘n’, ‘n2w lfdn’, ‘c’] mp_tac
                (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘n’, ‘l’, ‘c’] rounds_queued)
           >> simp[] >> disch_then (qspecl_then [‘d’, ‘k’] mp_tac) >> simp[]
           >> strip_tac >- (‘MEM c (wacc (SP lfdn (LV lfdn) s0 (n + 3)))’
                              suffices_by metis_tac[]
                            >> irule wacc_mono >> qexists_tac ‘d + n’ >> simp[])
           >> metis_tac[])
  (* so the server accepts in round n + 1 or n + 2 *)
  >> qspecl_then [‘s0’, ‘lfdn’, ‘n’] mp_tac
       (Q.GENL [‘s0’, ‘lfdn’, ‘n’] accept_soon_live)
  >> impl_tac
  >- (simp[echo_no_listener_read] >> rpt strip_tac
      >> first_x_assum (qspec_then ‘j − n’ mp_tac) >> simp[] >> strip_tac
      >> ‘n + (j − n) = j’ by simp[] >> gvs[] >> metis_tac[queued_ready])
  >> strip_tac
  (* which moves c forward *)
  >> first_assum (qspec_then ‘i’ mp_tac) >> impl_tac >- simp[] >> strip_tac
  >> qspecl_then [‘LV lfdn’, ‘EM lfdn’, ‘s0’, ‘n2w lfdn’, ‘c’, ‘k'’, ‘n + i’] mp_tac
       (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘l’, ‘c’, ‘k’, ‘n’] round_queued)
  >> simp[] >> strip_tac >- metis_tac[]
  >> ‘0 < nacc (n2w lfdn) (SA lfdn (LV lfdn) s0 (i + n))’
       by (gvs[nacc_def, LENGTH_NON_NIL, FILTER_NEQ_NIL] >> metis_tac[])
  >> qpat_x_assum ‘∀m. m < k ⇒ _’ (qspec_then ‘k''’ mp_tac) >> impl_tac >- fs[]
  >> disch_then (qspec_then ‘SUC (i + n)’ mp_tac) >> fs[]
QED

Theorem conn_accepted_l:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  is_conn (gstate (LV lfdn) (EM lfdn) s0 n) c ⇒
  ∃N. MEM c (wacc (SP lfdn (LV lfdn) s0 N))
Proof
  strip_tac
  >> ‘grun_ok (LV lfdn) (EM lfdn) s0’ by (irule echo_grun_ok >> simp[])
  >> qspecl_then [‘LV lfdn’, ‘EM lfdn’, ‘s0’, ‘n2w lfdn’] mp_tac
       (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘lfd’] grounds_known)
  >> simp[] >> disch_then (qspec_then ‘n’ (strip_assume_tac o CONJUNCT2))
  >> fs[known_def] >> first_x_assum drule >> strip_tac >- metis_tac[]
  >> qpat_x_assum ‘MEM c (lq _ _)’ (strip_assume_tac o REWRITE_RULE[MEM_SPLIT])
  >> qspecl_then [‘s0’, ‘lfdn’, ‘c’] mp_tac (Q.GENL [‘s0’, ‘lfdn’, ‘c’] queue_progress_l)
  >> impl_tac >- fs[] >> disch_then irule
  >> qexistsl_tac [‘LENGTH l1’, ‘n’] >> simp[queued_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Draining (asyncM4Drain)
   ------------------------------------------------------------------------ *)

Overload RDL = “λlfdn s0 c k. pread_all c (SP lfdn (LV lfdn) s0 k)”

Theorem least_round[local]:
  P ((k:num) + i) ⇒ ∃j. k ≤ j ∧ j ≤ k + i ∧ P j ∧ ∀l. k ≤ l ∧ l < j ⇒ ¬P l
Proof
  strip_tac
  >> qspec_then ‘λx. P (k + x)’ mp_tac arithmeticTheory.WOP >> simp[]
  >> impl_tac >- metis_tac[] >> strip_tac
  >> ‘n ≤ i’ by (CCONTR_TAC >> gvs[NOT_LESS_EQUAL] >> res_tac)
  >> qexists_tac ‘k + n’ >> simp[] >> rpt strip_tac
  >> first_x_assum (qspec_then ‘l − k’ mp_tac) >> simp[]
QED

Theorem drain_step_l:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ sched_wf s0 ∧
  MEM c (wacc (SP lfdn (LV lfdn) s0 k)) ∧
  tgt ≼ sent_upto c k s0 ∧ ¬(tgt ≼ RDL lfdn s0 c k) ⇒
  ∃k'. k < k' ∧ k' ≤ k + 4 ∧ LENGTH (RDL lfdn s0 c k) < LENGTH (RDL lfdn s0 c k')
Proof
  rpt strip_tac >> ‘grun_ok (LV lfdn) (EM lfdn) s0’ by (irule echo_grun_ok >> simp[])
  (* c has unread data *)
  >> qspecl_then [‘s0’, ‘LV lfdn’, ‘EM lfdn’, ‘c’] mp_tac
       (Q.GENL [‘s0’, ‘ifds’, ‘m’, ‘c’] grounds_acct)
  >> impl_tac >- simp[] >> disch_then (qspec_then ‘k’ mp_tac)
  >> simp[acct_def] >> CASE_TAC >> strip_tac >> gvs[]
  >> ‘x.incoming ≠ []’ by (strip_tac >> gvs[])
  (* so the server reads c in some round j ≤ k + 3; take the first *)
  >> ‘∀kk. ¬MEM (Read c kk, Got (SOME [])) (SP lfdn (LV lfdn) s0 k)’
       by (irule incoming_noeof >> metis_tac[])
  >> qspecl_then [‘s0’, ‘lfdn’, ‘c’, ‘k’, ‘x’] mp_tac
       (Q.GENL [‘s0’, ‘lfdn’, ‘c’, ‘n’, ‘cn’] read_soon_live)
  >> impl_tac >- simp[] >> strip_tac
  >> qspecl_then [‘λj. reads_c c (SA lfdn (LV lfdn) s0 j)’, ‘k’, ‘i’] mp_tac
       (Q.GENL [‘P’, ‘k’, ‘i’] least_round)
  >> simp[] >> strip_tac
  (* until then c's data stays unread *)
  >> qspecl_then [‘LV lfdn’, ‘EM lfdn’, ‘s0’, ‘k’, ‘c’] mp_tac
       (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘n’, ‘c’] quiet_rounds_s)
  >> impl_tac >- simp[] >> disch_then (qspecl_then [‘j − k’, ‘x’] mp_tac)
  >> impl_tac >- (simp[] >> rpt strip_tac >> first_x_assum irule >> simp[])
  >> strip_tac
  >> ‘k + (j − k) = j’ by simp[] >> gvs[]
  >> ‘cn'.incoming ≠ []’ by (strip_tac >> gvs[])
  (* so that read reads something *)
  >> qspecl_then [‘LV lfdn’, ‘EM lfdn’, ‘s0’, ‘j’] mp_tac
       (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘n’] grun_ok_sock_acts)
  >> simp[] >> strip_tac
  >> drule_all sock_acts_read_nonempty >> strip_tac
  >> qexists_tac ‘SUC j’ >> simp[gperf_SUC]
  >> ‘RDL lfdn s0 c k ≼ RDL lfdn s0 c j’
       by (irule pread_all_prefix >> ‘j = k + (j − k)’ by simp[]
           >> pop_assum SUBST1_TAC >> simp[gperf_prefix])
  >> imp_res_tac IS_PREFIX_LENGTH
  >> Cases_on ‘pread_all c (ZIP (gacts (LV lfdn) (EM lfdn) s0 j,
                                 gres (LV lfdn) (EM lfdn) s0 j))’
  >> gvs[]
QED

Theorem RDL_sent:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ sched_wf s0 ⇒
  RDL lfdn s0 c k ≼ sent_upto c k s0
Proof
  strip_tac >> ‘grun_ok (LV lfdn) (EM lfdn) s0’ by (irule echo_grun_ok >> simp[])
  >> qspecl_then [‘s0’, ‘LV lfdn’, ‘EM lfdn’, ‘c’] mp_tac
       (Q.GENL [‘s0’, ‘ifds’, ‘m’, ‘c’] grounds_acct)
  >> impl_tac >- simp[] >> disch_then (qspec_then ‘k’ mp_tac)
  >> simp[acct_def] >> CASE_TAC >> simp[]
QED

Theorem drain_l:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ sched_wf s0 ⇒
  ∀m k. MEM c (wacc (SP lfdn (LV lfdn) s0 k)) ∧ tgt ≼ sent_upto c k s0 ∧
        LENGTH tgt ≤ LENGTH (RDL lfdn s0 c k) + m ⇒
        ∃N. k ≤ N ∧ tgt ≼ RDL lfdn s0 c N
Proof
  strip_tac >> Induct
  >- (rpt strip_tac >> qexists_tac ‘k’ >> simp[]
      >> qspecl_then [‘tgt’, ‘sent_upto c k s0’, ‘RDL lfdn s0 c k’] mp_tac
           (Q.GENL [‘a’, ‘x’, ‘b’] prefix_by_length)
      >> simp[RDL_sent])
  >> rpt strip_tac
  >> Cases_on ‘tgt ≼ RDL lfdn s0 c k’ >- (qexists_tac ‘k’ >> simp[])
  >> drule_all drain_step_l >> strip_tac
  >> first_x_assum (qspec_then ‘k'’ mp_tac) >> impl_tac
  >- (rpt conj_tac
      >- (irule wacc_prefix >> qexists_tac ‘SP lfdn (LV lfdn) s0 k’ >> simp[]
          >> ‘k' = k + (k' − k)’ by simp[] >> pop_assum SUBST1_TAC >> simp[gperf_prefix])
      >- (irule IS_PREFIX_TRANS >> qexists_tac ‘sent_upto c k s0’ >> simp[]
          >> ‘k' = k + (k' − k)’ by simp[] >> pop_assum SUBST1_TAC
          >> simp[sent_upto_prefix])
      >> simp[])
  >> strip_tac >> qexists_tac ‘N’ >> simp[]
QED

Theorem accepted_live_l:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ sched_wf s0 ∧
  MEM c (wacc (SP lfdn (LV lfdn) s0 n)) ⇒
  ∃N. sent_upto c n s0 ≼
      bytes_written_to c (FLAT (GENLIST (grounds_events (LV lfdn) (EM lfdn) s0) (SUC N)))
Proof
  strip_tac >> ‘grun_ok (LV lfdn) (EM lfdn) s0’ by (irule echo_grun_ok >> simp[])
  >> qspecl_then [‘s0’, ‘lfdn’, ‘c’, ‘sent_upto c n s0’] mp_tac
       (Q.GENL [‘s0’, ‘lfdn’, ‘c’, ‘tgt’] drain_l)
  >> impl_tac >- simp[]
  >> disch_then (qspecl_then [‘LENGTH (sent_upto c n s0)’, ‘n’] mp_tac)
  >> simp[] >> strip_tac >> qexists_tac ‘N’
  >> simp[echo_rounds_written_read, bytes_read_from_rounds]
QED

(* ------------------------------------------------------------------------
   MAIN (asyncM4EchoLive)
   ------------------------------------------------------------------------ *)

Theorem echo_comp_live_l:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ⇒
  ∃N. sent_upto c n s0 ≼
      bytes_written_to c (FLAT (GENLIST (grounds_events (LV lfdn) (EM lfdn) s0) N))
Proof
  strip_tac
  >> ‘grun_ok (LV lfdn) (EM lfdn) s0’ by (irule echo_grun_ok >> simp[])
  >> Cases_on ‘is_conn (gstate (LV lfdn) (EM lfdn) s0 n) c’
  (* a connection: it is handed out at some round N *)
  >- (qspecl_then [‘s0’, ‘lfdn’, ‘n’, ‘c’] mp_tac
        (Q.GENL [‘s0’, ‘lfdn’, ‘n’, ‘c’] conn_accepted_l)
      >> impl_tac >- fs[] >> strip_tac
      >> ‘MEM c (wacc (SP lfdn (LV lfdn) s0 (n + N)))’
           by (irule wacc_mono >> qexists_tac ‘N’ >> simp[])
      >> qspecl_then [‘s0’, ‘lfdn’, ‘c’, ‘n + N’] mp_tac
           (Q.GENL [‘s0’, ‘lfdn’, ‘c’, ‘n’] accepted_live_l)
      >> impl_tac >- fs[] >> strip_tac
      >> qexists_tac ‘SUC N'’ >> irule IS_PREFIX_TRANS
      >> qexists_tac ‘sent_upto c (n + N) s0’ >> simp[sent_upto_prefix])
  (* not a connection after n rounds: nothing was sent on it *)
  >> qexists_tac ‘0’
  >> qspecl_then [‘LV lfdn’, ‘EM lfdn’, ‘s0’, ‘c’] mp_tac
       (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘c’] grounds_acct)
  >> impl_tac >- fs[] >> disch_then (qspec_then ‘n’ mp_tac)
  >> gvs[acct_def, is_conn_def]
QED
