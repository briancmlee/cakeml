(*
  The closed loop (asyncWorld) running the generic server  server_with hf lfd
  for a well-behaved handler hf (hok): the world stays consistent with what
  the server has done, and the per-connection, per-round facts of
  asyncLiveness.  These are asyncClosedLoop's / asyncLiveness's proofs for
  the echo server, with server_echoes replaced by server_with_isolates.
*)
Theory asyncSWClosedLoop
Ancestors
  pair list rich_list arithmetic option pred_set string alist
  asyncCore asyncLevel1 asyncLoop asyncTranscript asyncServer asyncServerSafety
  asyncProgress asyncWorld asyncClosedLoop asyncLiveness asyncServerWith
  asyncSWProgress
Libs
  BasicProvers

(* MAIN: the world stays consistent with what the server has done, in every
   round of the closed loop *)
Theorem sw_consistent:
  hok hf ⇒
  ∀n h w perf.
    closed_loop (server_with hf lfd) (start_world lfd sch) n = (h, w, perf) ⇒
    consistent lfd w perf
Proof
  strip_tac >> Induct >- simp[closed_loop_def, consistent_start]
  >> rpt gen_tac >> simp[closed_loop_def]
  >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[]
  >> irule consistent_tick >> irule consistent_perform_all >> simp[]
  >> reverse conj_tac >- metis_tac[]
  (* the server only writes to connections it has accepted *)
  >> rpt strip_tac
  >> drule (Q.GEN ‘m’ trans_closed_loop) >> strip_tac
  >> ‘fresh (trans (server_with hf lfd) h')’
       by gvs[fresh_def, accepted_pending, consistent_def, ALL_DISTINCT_APPEND,
              sperf_def]
  >> ‘∀fd hh. EVERY (on_fd fd) (trans (hf fd) hh)’ by metis_tac[hok_own]
  >> drule server_with_isolates >> disch_then drule >> strip_tac
  >> first_x_assum (qspec_then ‘c’ mp_tac)
  >> impl_tac
  >- (simp[EXISTS_MEM, MEM_MAP] >> qexists_tac ‘(Write c d, NONE)’
      >> simp[on_fd_def])
  >> simp[accepted_pending, sperf_def]
QED

(* The server's transcript in the closed loop hands out distinct connections *)
Theorem sw_fresh:
  hok hf ∧ closed_loop (server_with hf lfd) (start_world lfd sch) n = (h, w, perf) ⇒
  fresh (trans (server_with hf lfd) h) ∧
  trans (server_with hf lfd) h =
    sperf perf ++ MAP (λa. (a, NONE)) (new_actions (log_of (server_with hf lfd)) h)
Proof
  strip_tac >> ‘consistent lfd w perf’ by metis_tac[sw_consistent] >>
  pop_assum mp_tac >> simp[consistent_def] >> strip_tac
  >> drule (Q.GEN ‘m’ trans_closed_loop) >> strip_tac
  >> gvs[fresh_def, accepted_pending, ALL_DISTINCT_APPEND, sperf_def]
QED

(* In one round of the closed loop, for a known connection c:
   - what has arrived on c only grows;
   - unless the server read c, its unread data only grows;
   - once c's peer has closed and everything is read, it stays that way;
   - if the server read c, everything that had arrived has now been read *)
Theorem sw_round_conn:
  hok hf ∧ closed_loop (server_with hf lfd) (start_world lfd sch) n = (h, w, perf) ∧
  closed_loop (server_with hf lfd) (start_world lfd sch) (n + 1) = (h', w', perf') ∧
  ALOOKUP w.conns c = SOME cn ⇒
  ∃cn'. ALOOKUP w'.conns c = SOME cn' ∧
        cn.received ≼ cn'.received ∧
        (¬MEM (Read c) (new_actions (log_of (server_with hf lfd)) h) ⇒
         cn.incoming ≼ cn'.incoming) ∧
        (cn.peer_closed ∧ cn.incoming = "" ⇒ cn'.peer_closed ∧ cn'.incoming = "") ∧
        (MEM (Read c) (new_actions (log_of (server_with hf lfd)) h) ⇒
         cn.received = FLAT (read c (sperf perf')))
Proof
  strip_tac
  >> ‘consistent lfd w' perf'’ by metis_tac[sw_consistent]
  >> drule_all closed_loop_step >> strip_tac >> gvs[]
  >> drule_all perform_all_conn >> strip_tac
  >> drule tick_conn >> strip_tac >> simp[]
  >> conj_tac
  >- (rw[] >> Cases_on ‘MEM (Read c) (new_actions (log_of (server_with hf lfd)) h)’ >> gvs[])
  >> strip_tac >> gvs[consistent_def] >> first_x_assum drule >> simp[]
QED

(* Once the server has seen end-of-file on c, c's peer has closed and there
   is nothing left to read *)
Theorem sw_eof:
  ∀n h w perf.
    hok hf ∧ closed_loop (server_with hf lfd) (start_world lfd sch) n = (h, w, perf) ∧
    MEM (Read c, Eof) perf ⇒
    ∃cn. ALOOKUP w.conns c = SOME cn ∧ cn.peer_closed ∧ cn.incoming = ""
Proof
  Induct >- simp[closed_loop_def]
  >> rpt strip_tac
  >> Cases_on ‘closed_loop (server_with hf lfd) (start_world lfd sch) n’ >> PairCases_on ‘r’
  >> qspecl_then [‘server_with hf lfd’, ‘start_world lfd sch’, ‘n’, ‘q’, ‘r0’, ‘r1’,
                  ‘h’, ‘w’, ‘perf’] mp_tac
       (Q.GENL [‘m’, ‘w0’, ‘n’, ‘h’, ‘w’, ‘perf’, ‘h'’, ‘w'’, ‘perf'’] closed_loop_step)
  >> gvs[ADD1] >> strip_tac >> gvs[]
  >> ‘∃cn1. ALOOKUP w1.conns c = SOME cn1 ∧ cn1.peer_closed ∧ cn1.incoming = ""’
       suffices_by (strip_tac >> drule tick_conn >> strip_tac >> gvs[])
  (* end-of-file was seen before: it stays that way *)
  >- (drule_all perform_all_conn >> strip_tac >> simp[]
      >> Cases_on ‘MEM (Read c) (new_actions (log_of (server_with hf lfd)) q)’ >> gvs[])
  (* it is seen in this round: the peer had closed, and the read took all *)
  >> Cases_on ‘ALOOKUP r0.conns c’
  >- (drule_all perform_all_unknown >> simp[])
  >> drule_all perform_all_conn >> strip_tac >> simp[]
  >> drule perform_all_length >> strip_tac
  >> qpat_x_assum ‘MEM (Read c,Eof) (ZIP _)’ mp_tac >> simp[MEM_ZIP]
  >> metis_tac[MEM_EL]
QED

(* What has arrived on a connection only grows *)
Theorem sw_received_later:
  ∀d h' w' perf'.
    hok hf ∧ closed_loop (server_with hf lfd) (start_world lfd sch) n = (h, w, perf) ∧
    ALOOKUP w.conns c = SOME cn ∧
    closed_loop (server_with hf lfd) (start_world lfd sch) (n + d) = (h', w', perf') ⇒
    ∃cn'. ALOOKUP w'.conns c = SOME cn' ∧ cn.received ≼ cn'.received
Proof
  Induct >- (rw[] >> gvs[])
  >> rpt strip_tac
  >> Cases_on ‘closed_loop (server_with hf lfd) (start_world lfd sch) (n + d)’
  >> PairCases_on ‘r’
  >> first_x_assum (qspecl_then [‘q’, ‘r0’, ‘r1’] mp_tac) >> simp[] >> strip_tac
  >> qspecl_then [‘n + d’, ‘q’, ‘r0’, ‘r1’, ‘h'’, ‘w'’, ‘perf'’, ‘cn'’] mp_tac
       (Q.GENL [‘n’, ‘h’, ‘w’, ‘perf’, ‘h'’, ‘w'’, ‘perf'’, ‘cn’] sw_round_conn)
  >> gvs[ADD1] >> strip_tac >> metis_tac[IS_PREFIX_TRANS]
QED

(* While the server does not read c, c's unread data only grows, and no
   read of c is performed *)
Theorem sw_quiet_rounds:
  ∀d h' w' perf'.
    hok hf ∧ closed_loop (server_with hf lfd) (start_world lfd sch) n = (h, w, perf) ∧
    ALOOKUP w.conns c = SOME cn ∧
    closed_loop (server_with hf lfd) (start_world lfd sch) (n + d) = (h', w', perf') ∧
    (∀i hi wi pi. i < d ∧
                  closed_loop (server_with hf lfd) (start_world lfd sch) (n + i) = (hi, wi, pi) ⇒
                  ¬MEM (Read c) (new_actions (log_of (server_with hf lfd)) hi)) ⇒
    ∃cn'. ALOOKUP w'.conns c = SOME cn' ∧ cn.incoming ≼ cn'.incoming ∧
          ∀r. MEM (Read c, r) perf' ⇒ MEM (Read c, r) perf
Proof
  Induct >- (rw[] >> gvs[])
  >> rpt strip_tac
  >> Cases_on ‘closed_loop (server_with hf lfd) (start_world lfd sch) (n + d)’
  >> PairCases_on ‘r’
  >> first_x_assum (qspecl_then [‘q’, ‘r0’, ‘r1’] mp_tac) >> simp[]
  >> impl_tac
  >- (rpt strip_tac >> first_x_assum (qspecl_then [‘i’, ‘hi’, ‘wi’, ‘pi’] mp_tac)
      >> gvs[])
  >> strip_tac
  >> ‘¬MEM (Read c) (new_actions (log_of (server_with hf lfd)) q)’
       by (first_x_assum (qspecl_then [‘d’, ‘q’, ‘r0’, ‘r1’] mp_tac) >> simp[])
  >> qspecl_then [‘n + d’, ‘q’, ‘r0’, ‘r1’, ‘h'’, ‘w'’, ‘perf'’, ‘cn'’] mp_tac
       (Q.GENL [‘n’, ‘h’, ‘w’, ‘perf’, ‘h'’, ‘w'’, ‘perf'’, ‘cn’] sw_round_conn)
  >> gvs[ADD1] >> strip_tac >> qexists_tac ‘cn''’ >> simp[]
  >> conj_tac >- metis_tac[IS_PREFIX_TRANS]
  >> qspecl_then [‘server_with hf lfd’, ‘start_world lfd sch’, ‘n + d’, ‘q’, ‘r0’, ‘r1’,
                  ‘h'’, ‘w'’, ‘perf'’] mp_tac
       (Q.GENL [‘m’, ‘w0’, ‘n’, ‘h’, ‘w’, ‘perf’, ‘h'’, ‘w'’, ‘perf'’] closed_loop_step)
  >> simp[] >> strip_tac >> gvs[]
  >> rpt strip_tac >- metis_tac[]
  >> qpat_x_assum ‘MEM _ (ZIP _)’ mp_tac >> drule perform_all_length
  >> simp[MEM_ZIP] >> metis_tac[MEM_EL]
QED

Theorem sw_actions_SNOC[local]:
  hok hf ⇒
  (server_with hf lfd (h ++ [s])).actions =
  (server_with hf lfd h).actions ++ new_actions (log_of (server_with hf lfd)) (h ++ [s])
Proof
  strip_tac >> qspecl_then [‘log_of (server_with hf lfd)’, ‘h’, ‘s’] mp_tac
    (Q.GENL [‘acts’, ‘h’, ‘s’] new_actions_prefix)
  >> gs[log_of_def, wf_SNOC_actions, hok_wf_server_with]
QED

(* If the server reads c in none of the rounds n+1 .. n+d, its reads of c
   stay the same *)
Theorem sw_nreads_quiet:
  ∀d h' w' perf'.
    hok hf ∧ closed_loop (server_with hf lfd) (start_world lfd sch) n = (h, w, perf) ∧
    closed_loop (server_with hf lfd) (start_world lfd sch) (n + d) = (h', w', perf') ∧
    (∀i hi wi pi. 0 < i ∧ i ≤ d ∧
                  closed_loop (server_with hf lfd) (start_world lfd sch) (n + i) = (hi, wi, pi) ⇒
                  ¬MEM (Read c) (new_actions (log_of (server_with hf lfd)) hi)) ⇒
    nreads c (server_with hf lfd h').actions = nreads c (server_with hf lfd h).actions
Proof
  Induct >- (rw[] >> gvs[])
  >> rpt strip_tac
  >> Cases_on ‘closed_loop (server_with hf lfd) (start_world lfd sch) (n + d)’
  >> PairCases_on ‘r’
  >> first_x_assum (qspecl_then [‘q’, ‘r0’, ‘r1’] mp_tac) >> simp[]
  >> impl_tac
  >- (rpt strip_tac >> first_x_assum (qspecl_then [‘i’, ‘hi’, ‘wi’, ‘pi’] mp_tac)
      >> gvs[])
  >> strip_tac
  >> ‘¬MEM (Read c) (new_actions (log_of (server_with hf lfd)) h')’
       by (first_x_assum (qspecl_then [‘SUC d’, ‘h'’, ‘w'’, ‘perf'’] mp_tac) >> simp[])
  >> qspecl_then [‘server_with hf lfd’, ‘start_world lfd sch’, ‘n + d’, ‘q’, ‘r0’, ‘r1’,
                  ‘h'’, ‘w'’, ‘perf'’] mp_tac
       (Q.GENL [‘m’, ‘w0’, ‘n’, ‘h’, ‘w’, ‘perf’, ‘h'’, ‘w'’, ‘perf'’] closed_loop_step)
  >> gvs[ADD1] >> strip_tac >> gvs[sw_actions_SNOC]
  >> gvs[nreads_def, FILTER_EQ_NIL, EVERY_MEM, FILTER_APPEND_DISTRIB]
  >> rw[] >> metis_tac[]
QED
