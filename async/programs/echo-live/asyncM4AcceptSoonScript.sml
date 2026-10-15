(*
  Accepts, at the socket level: while connections are pending, the echo
  server accepts within two rounds (accept_soon_s), so every pending
  connection, and hence every connection of the world, is eventually
  handed out to the server (queue_progress, conn_accepted).

  As for reads (asyncM4ReadSoon): the listener is always in the interest
  list, a non-empty queue makes it readable, and the program-level
  progress theorem server_accept_progress makes the server accept.  Each
  accept moves a pending connection one place forward (asyncM4Queue).
*)
Theory asyncM4AcceptSoon
Ancestors
  pair list rich_list arithmetic option pred_set llist alist words
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncProgress ffiSpikeSocketFFI asyncM3World asyncM4GRounds asyncM4Relabel
  asyncM4RelabelDist asyncM4SockModel asyncM4SockInv asyncM4GTrans asyncM4Loop
  asyncM4EchoRunOk asyncM4Sched asyncM4LiveProg asyncM4ReadSoon asyncM4Queue
Libs
  preamble

(* If the server's accepts of lfd grew between rounds i and i + d, it
   emitted an accept of lfd in one of the rounds i+1 .. i+d *)
Theorem naccepts_step:
  ∀d. naccepts lfd (server lfd (TAKE i h)).actions <
      naccepts lfd (server lfd (TAKE (i + d) h)).actions ⇒
      ∃k. i < k ∧ k ≤ i + d ∧
          MEM (Accept lfd) (new_actions (log_of (server lfd)) (TAKE k h))
Proof
  Induct >- simp[] >> rpt strip_tac
  >> Cases_on ‘naccepts lfd (server lfd (TAKE i h)).actions <
               naccepts lfd (server lfd (TAKE (i + d) h)).actions’
  >- (first_x_assum drule >> strip_tac >> qexists_tac ‘k’ >> simp[])
  >> qexists_tac ‘i + SUC d’ >> simp[]
  >> ‘i + SUC d ≤ LENGTH h’
       by (CCONTR_TAC
           >> ‘TAKE (i + SUC d) h = h ∧ TAKE (i + d) h = h’ by simp[TAKE_LENGTH_TOO_LONG]
           >> gvs[])
  >> ‘TAKE (i + SUC d) h = TAKE (i + d) h ++ [EL (i + d) h]’
       by (‘i + SUC d = SUC (i + d)’ by simp[] >> pop_assum SUBST1_TAC
           >> simp[GSYM SNOC_EL_TAKE, SNOC_APPEND])
  >> pop_assum SUBST_ALL_TAC
  >> ‘(server lfd (TAKE (i + d) h ++ [EL (i + d) h])).actions =
      (server lfd (TAKE (i + d) h)).actions ++
      new_actions (log_of (server lfd)) (TAKE (i + d) h ++ [EL (i + d) h])’
       by (qspecl_then [‘log_of (server lfd)’, ‘TAKE (i + d) h’, ‘EL (i + d) h’] mp_tac
             (Q.GENL [‘acts’, ‘h’, ‘s’] new_actions_prefix)
           >> simp[log_of_def, wf_SNOC_actions, wf_server])
  >> gvs[naccepts_def, asyncProgressTheory.count_def, FILTER_APPEND_DISTRIB] >> CCONTR_TAC
  >> ‘FILTER (λa. a = Accept lfd)
        (new_actions (log_of (server lfd)) (TAKE (i + d) h ++ [EL (i + d) h])) = []’
       by simp[FILTER_EQ_NIL, EVERY_MEM]
  >> gvs[]
QED

Theorem wacc_mono:
  n1 ≤ n2 ∧ MEM c (wacc (gperf ifds m s0 n1)) ⇒ MEM c (wacc (gperf ifds m s0 n2))
Proof
  rw[] >> irule wacc_prefix >> qexists_tac ‘gperf ifds m s0 n1’ >> simp[]
  >> ‘n2 = n1 + (n2 − n1)’ by simp[] >> pop_assum SUBST1_TAC
  >> REWRITE_TAC[gperf_prefix]
QED

(* MAIN: while connections are pending (the listener is ready), the server
   accepts in one of the next two rounds *)
Theorem accept_soon_s:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  (∀j. n < j ∧ j ≤ n + 2 ⇒
       is_ready (gstate (EI lfdn) (EM lfdn) s0 j) (n2w lfdn)) ⇒
  ∃i. 1 ≤ i ∧ i ≤ 2 ∧
      MEM (asyncM3World$Accept (n2w lfdn)) (SA lfdn (EI lfdn) s0 (n + i))
Proof
  rpt strip_tac
  >> ‘grun_ok (EI lfdn) (EM lfdn) s0’ by (irule echo_grun_ok >> simp[])
  (* the model server sees the listener readable in snapshots n, n + 1 *)
  >> ‘∀j. n ≤ j ∧ j < n + 2 ⇒
          Readable lfdn ∈ (EL j (MAP sfs (ghist (EI lfdn) (EM lfdn) s0 (n + 2)))).ready’
       by (rpt strip_tac >> simp[EL_MAP, snap_map_def, sfe_def, ready_EL_ghist, MEM_FILTER]
           >> qexists_tac ‘n2w lfdn’ >> simp[]
           (* the listener is in the interest list *)
           >> irule interest_accepted >> simp[])
  >> qspecl_then [‘MAP sfs (ghist (EI lfdn) (EM lfdn) s0 (n + 2))’, ‘n’] mp_tac
       (Q.INST [‘lfd’ |-> ‘lfdn’] server_accept_progress)
  >> impl_tac >- simp[prompt_ghist]
  >> ‘∀k. k ≤ n + 2 ⇒ TAKE k (MAP sfs (ghist (EI lfdn) (EM lfdn) s0 (n + 2))) =
                       MAP sfs (ghist (EI lfdn) (EM lfdn) s0 k)’
       by simp[GSYM MAP_TAKE, ghist_TAKE]
  >> strip_tac
  >> qspecl_then [‘2’] mp_tac
       (Q.INST [‘lfd’ |-> ‘lfdn’, ‘i’ |-> ‘n’,
                ‘h’ |-> ‘MAP sfs (ghist (EI lfdn) (EM lfdn) s0 (n + 2))’] naccepts_step)
  >> impl_tac >- simp[] >> strip_tac
  (* an accept of the model server is an accept of the socket program *)
  >> qexists_tac ‘k − n’ >> simp[]
  >> gvs[gacts_def, new_actions_relabel, MEM_MAP]
  >> qexists_tac ‘Accept lfdn’ >> simp[sfa_def]
QED

(* MAIN: a pending connection is eventually handed out to the server *)
Theorem queue_progress:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ⇒
  ∀k n. queued (n2w lfdn) c k (gstate (EI lfdn) (EM lfdn) s0 n) ⇒
        ∃N. MEM c (wacc (SP lfdn (EI lfdn) s0 N))
Proof
  strip_tac
  >> ‘grun_ok (EI lfdn) (EM lfdn) s0’ by (irule echo_grun_ok >> simp[])
  >> completeInduct_on ‘k’ >> rpt strip_tac
  >> Cases_on ‘MEM c (wacc (SP lfdn (EI lfdn) s0 (n + 3)))’ >- metis_tac[]
  (* not handed out by round n + 3: still pending in rounds n .. n + 3 *)
  >> ‘∀d. d ≤ 3 ⇒ ∃k'. queued (n2w lfdn) c k' (gstate (EI lfdn) (EM lfdn) s0 (n + d)) ∧
                       k' ≤ k’
       by (rpt strip_tac
           >> qspecl_then [‘EI lfdn’, ‘EM lfdn’, ‘s0’, ‘n’, ‘n2w lfdn’, ‘c’] mp_tac
                (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘n’, ‘l’, ‘c’] rounds_queued)
           >> simp[] >> disch_then (qspecl_then [‘d’, ‘k’] mp_tac) >> simp[]
           >> strip_tac >- (‘MEM c (wacc (SP lfdn (EI lfdn) s0 (n + 3)))’
                              suffices_by metis_tac[]
                            >> irule wacc_mono >> qexists_tac ‘d + n’ >> simp[])
           >> metis_tac[])
  (* so the server accepts in round n + 1 or n + 2 *)
  >> qspecl_then [‘s0’, ‘lfdn’, ‘n’] mp_tac
       (Q.GENL [‘s0’, ‘lfdn’, ‘n’] accept_soon_s)
  >> impl_tac
  >- (simp[] >> rpt strip_tac
      >> first_x_assum (qspec_then ‘j − n’ mp_tac) >> simp[] >> strip_tac
      >> ‘n + (j − n) = j’ by simp[] >> gvs[] >> metis_tac[queued_ready])
  >> strip_tac
  (* which moves c forward *)
  >> first_assum (qspec_then ‘i’ mp_tac) >> impl_tac >- simp[] >> strip_tac
  >> qspecl_then [‘EI lfdn’, ‘EM lfdn’, ‘s0’, ‘n2w lfdn’, ‘c’, ‘k'’, ‘n + i’] mp_tac
       (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘l’, ‘c’, ‘k’, ‘n’] round_queued)
  >> simp[] >> strip_tac >- metis_tac[]
  >> ‘0 < nacc (n2w lfdn) (SA lfdn (EI lfdn) s0 (i + n))’
       by (gvs[nacc_def, LENGTH_NON_NIL, FILTER_NEQ_NIL] >> metis_tac[])
  >> qpat_x_assum ‘∀m. m < k ⇒ _’ (qspec_then ‘k''’ mp_tac) >> impl_tac >- fs[]
  >> disch_then (qspec_then ‘SUC (i + n)’ mp_tac) >> fs[]
QED

(* MAIN: every connection of the world is eventually handed out to the
   server *)
Theorem conn_accepted:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  is_conn (gstate (EI lfdn) (EM lfdn) s0 n) c ⇒
  ∃N. MEM c (wacc (SP lfdn (EI lfdn) s0 N))
Proof
  strip_tac
  >> ‘grun_ok (EI lfdn) (EM lfdn) s0’ by (irule echo_grun_ok >> simp[])
  >> qspecl_then [‘EI lfdn’, ‘EM lfdn’, ‘s0’, ‘n2w lfdn’] mp_tac
       (Q.GENL [‘ifds’, ‘m’, ‘s0’, ‘lfd’] grounds_known)
  >> simp[] >> disch_then (qspec_then ‘n’ (strip_assume_tac o CONJUNCT2))
  >> fs[known_def] >> first_x_assum drule >> strip_tac >- metis_tac[]
  >> qpat_x_assum ‘MEM c (lq _ _)’ (strip_assume_tac o REWRITE_RULE[MEM_SPLIT])
  >> qspecl_then [‘s0’, ‘lfdn’, ‘c’] mp_tac (Q.GENL [‘s0’, ‘lfdn’, ‘c’] queue_progress)
  >> impl_tac >- fs[] >> disch_then irule
  >> qexistsl_tac [‘LENGTH l1’, ‘n’] >> simp[queued_def] >> metis_tac[]
QED
