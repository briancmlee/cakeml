(*
  Liveness of the echo server in the closed loop (M4 in the model).

  In the closed-loop world every byte that arrives on a connection is
  written back to that connection within a bounded number of rounds:
   - closed_loop_echo_accepted: on an accepted connection, everything that
     has arrived by round n is written back by round n + 5;
   - queue_progress: a pending connection with p connections ahead of it
     in the listener's queue is handed out within 3 (p + 1) rounds;
   - closed_loop_liveness: so on every connection, everything that has
     arrived by round n is written back by round n + 3 q + 5, where q is
     the number of pending connections at round n.

  The world is fair by construction (design/09-closed-loop.md): it answers
  every action in the next snapshot, a read returns all available data, a
  write always completes, and arrivals are delivered when scheduled.  So
  no further assumption is needed.  The proof combines the program-level
  progress theorems (echoProgress) with how the world evolves.
*)
Theory echoClosedLive
Ancestors
  pair list rich_list arithmetic option pred_set string alist llist
  asyncCore asyncLevel1 asyncTranscript echoServer echoServerSafety
  closedWorld echoClosedLoop echoProgress
Libs
  BasicProvers

(* ------------------------------------------------------------------------
   One connection, as the world changes
   ------------------------------------------------------------------------ *)

(* Performing an action: a read of c takes all of c's incoming data (end
   of file is reported only when the peer has closed); nothing else changes
   what has arrived on c, or whether c's peer has closed *)
Theorem perform_conn:
  ALOOKUP w.conns c = SOME cn ∧ perform a w = (r, w') ⇒
  ∃cn'. ALOOKUP w'.conns c = SOME cn' ∧
        cn'.received = cn.received ∧ cn'.peer_closed = cn.peer_closed ∧
        (a = Read c ⇒ cn'.incoming = "" ∧ (r = Eof ⇒ cn.peer_closed)) ∧
        (a ≠ Read c ⇒ cn'.incoming = cn.incoming)
Proof
  Cases_on ‘a’ >> simp[perform_def] >> rpt strip_tac
  >> gvs[AllCaseEqs(), AFUPDKEY_ALOOKUP] >> Cases_on ‘c = n’ >> gvs[]
QED

Theorem perform_all_conn:
  ∀acts w cn rs w'.
    ALOOKUP w.conns c = SOME cn ∧ perform_all acts w = (rs, w') ⇒
    ∃cn'. ALOOKUP w'.conns c = SOME cn' ∧
          cn'.received = cn.received ∧ cn'.peer_closed = cn.peer_closed ∧
          (MEM (Read c) acts ⇒ cn'.incoming = "") ∧
          (¬MEM (Read c) acts ⇒ cn'.incoming = cn.incoming) ∧
          (MEM (Read c, Eof) (ZIP (acts, rs)) ⇒ cn.peer_closed)
Proof
  Induct >> simp[perform_all_def] >> rpt gen_tac
  >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[]
  >> drule_all perform_conn >> strip_tac
  >> first_x_assum drule_all >> strip_tac >> simp[]
  >> Cases_on ‘h = Read c’ >> gvs[] >> metis_tac[]
QED

Theorem deliver1_conn:
  ALOOKUP w.conns c = SOME cn ⇒
  ∃cn' x. ALOOKUP (deliver1 w a).conns c = SOME cn' ∧
          cn'.received = cn.received ++ x ∧ cn'.incoming = cn.incoming ++ x ∧
          (cn.peer_closed ⇒ cn'.peer_closed ∧ x = "")
Proof
  Cases_on ‘a’ >> simp[deliver1_def] >> strip_tac
  >- (rw[] >> gvs[is_conn_def] >> rw[] >> gvs[])
  >> simp[AFUPDKEY_ALOOKUP] >> rw[] >> simp[]
QED

Theorem deliver_conn:
  ∀as w cn.
    ALOOKUP w.conns c = SOME cn ⇒
    ∃cn' x. ALOOKUP (FOLDL deliver1 w as).conns c = SOME cn' ∧
            cn'.received = cn.received ++ x ∧ cn'.incoming = cn.incoming ++ x ∧
            (cn.peer_closed ⇒ cn'.peer_closed ∧ x = "")
Proof
  Induct >> simp[]
  >> rpt strip_tac >> drule deliver1_conn >> disch_then (qspec_then ‘h’ strip_assume_tac)
  >> first_x_assum drule >> strip_tac >> simp[]
  >> qexists_tac ‘x ++ x'’ >> simp[] >> rw[] >> gvs[]
QED

(* Time passing: data may arrive on c (it is both received and incoming);
   once c's peer has closed, nothing more arrives *)
Theorem tick_conn:
  ALOOKUP w.conns c = SOME cn ⇒
  ∃cn' x. ALOOKUP (tick w).conns c = SOME cn' ∧
          cn'.received = cn.received ++ x ∧ cn'.incoming = cn.incoming ++ x ∧
          (cn.peer_closed ⇒ cn'.peer_closed ∧ x = "")
Proof
  rw[tick_def] >> CASE_TAC >> simp[deliver_def]
  >> irule deliver_conn >> simp[]
QED

(* ------------------------------------------------------------------------
   The closed loop, round by round
   ------------------------------------------------------------------------ *)

(* One round: the world performs the round's actions, then time passes *)
Theorem closed_loop_step:
  closed_loop m w0 n = (h, w, perf) ∧ closed_loop m w0 (n + 1) = (h', w', perf') ⇒
  ∃rs w1. perform_all (new_actions (log_of m) h) w = (rs, w1) ∧ w' = tick w1 ∧
          perf' = perf ++ ZIP (new_actions (log_of m) h, rs) ∧
          h' = h ++ [snapshot_of w' (n + 1) rs]
Proof
  rw[GSYM ADD1] >> Cases_on ‘perform_all (new_actions (log_of m) h) w’
  >> drule_all closed_loop_SUC >> gvs[]
QED

Theorem closed_loop_length:
  closed_loop m w0 n = (h, w, perf) ⇒ LENGTH h = n
Proof
  metis_tac[trans_closed_loop]
QED

(* Earlier rounds are prefixes of later ones *)
Theorem closed_loop_prefix:
  ∀d h w perf h' w' perf'.
    closed_loop m w0 n = (h, w, perf) ∧
    closed_loop m w0 (n + d) = (h', w', perf') ⇒
    h = TAKE n h' ∧ perf ≼ perf'
Proof
  Induct
  >- (rw[] >> gvs[] >> drule closed_loop_length >> simp[TAKE_LENGTH_ID_rwt])
  >> rpt gen_tac >> strip_tac
  >> Cases_on ‘closed_loop m w0 (n + d)’ >> PairCases_on ‘r’
  >> first_x_assum (qspecl_then [‘h’, ‘w’, ‘perf’, ‘q’, ‘r0’, ‘r1’] mp_tac)
  >> simp[] >> strip_tac
  >> ‘n + SUC d = (n + d) + 1’ by simp[] >> gvs[]
  >> qspecl_then [‘d + n’, ‘q’, ‘r0’, ‘r1’, ‘h'’, ‘w'’, ‘perf'’] mp_tac
       (Q.GENL [‘n’, ‘h’, ‘w’, ‘perf’, ‘h'’, ‘w'’, ‘perf'’] closed_loop_step)
  >> simp[] >> strip_tac >> gvs[]
  >> qpat_x_assum ‘closed_loop _ _ (d + n) = _’ (assume_tac o MATCH_MP closed_loop_length)
  >> simp[TAKE_APPEND1] >> metis_tac[IS_PREFIX_APPEND, APPEND_ASSOC, IS_PREFIX_TRANS]
QED

(* Snapshot j reports the fds ready in the world after round j + 1 *)
Theorem closed_loop_snapshot:
  closed_loop m w0 n = (h, w, perf) ∧ j < n ∧
  closed_loop m w0 (j + 1) = (h1, w1, perf1) ⇒
  (EL j h).ready = set (MAP Readable (ready_fds w1))
Proof
  strip_tac
  >> qspecl_then [‘n - (j + 1)’, ‘h1’, ‘w1’, ‘perf1’, ‘h’, ‘w’, ‘perf’] mp_tac
       (Q.GEN ‘n’ closed_loop_prefix |> Q.SPEC ‘j + 1’)
  >> simp[] >> strip_tac
  >> ‘EL j h = EL j h1’ by (qpat_x_assum ‘h1 = TAKE _ _’ SUBST1_TAC >> simp[EL_TAKE])
  >> pop_assum SUBST1_TAC
  >> Cases_on ‘closed_loop m w0 j’ >> PairCases_on ‘r’
  >> qspecl_then [‘j’, ‘q’, ‘r0’, ‘r1’, ‘h1’, ‘w1’, ‘perf1’] mp_tac
       (Q.GENL [‘n’, ‘h’, ‘w’, ‘perf’, ‘h'’, ‘w'’, ‘perf'’] closed_loop_step)
  >> simp[] >> strip_tac
  >> qpat_x_assum ‘closed_loop _ _ j = _’ (assume_tac o MATCH_MP closed_loop_length)
  >> simp[EL_APPEND2, snapshot_of_def]
QED

(* The world answers every action in the next snapshot *)
Theorem closed_loop_prompt:
  ∀n h w perf. closed_loop m w0 n = (h, w, perf) ⇒ prompt m h
Proof
  Induct >- simp[closed_loop_def, prompt_def]
  >> rpt strip_tac
  >> Cases_on ‘closed_loop m w0 n’ >> PairCases_on ‘r’
  >> qspecl_then [‘n’, ‘q’, ‘r0’, ‘r1’, ‘h’, ‘w’, ‘perf’] mp_tac
       (Q.GENL [‘n’, ‘h’, ‘w’, ‘perf’, ‘h'’, ‘w'’, ‘perf'’] closed_loop_step)
  >> gvs[ADD1] >> strip_tac >> gvs[]
  >> qpat_x_assum ‘closed_loop _ _ n = _’ (assume_tac o MATCH_MP closed_loop_length)
  >> drule perform_all_length >> rw[prompt_def] >> Cases_on ‘i < LENGTH q’
  >- (gvs[prompt_def] >> first_x_assum drule
      >> simp[TAKE_APPEND1, responses_at_def, EL_APPEND1])
  >> ‘i = LENGTH q’ by simp[]
  >> gvs[TAKE_LENGTH_APPEND, responses_at_def, EL_APPEND2, snapshot_of_def]
QED

(* The server's transcript in the closed loop hands out distinct connections *)
Theorem closed_loop_fresh:
  closed_loop (server lfd) (start_world lfd sch) n = (h, w, perf) ⇒
  fresh (trans (server lfd) h) ∧
  trans (server lfd) h =
    sperf perf ++ MAP (λa. (a, NONE)) (new_actions (log_of (server lfd)) h)
Proof
  strip_tac >> drule closed_loop_consistent >> simp[consistent_def] >> strip_tac
  >> drule (Q.GEN ‘m’ trans_closed_loop) >> strip_tac
  >> gvs[fresh_def, accepted_pending, ALL_DISTINCT_APPEND, sperf_def]
QED

(* ------------------------------------------------------------------------
   One connection, round by round
   ------------------------------------------------------------------------ *)

Theorem perform_unknown:
  ALOOKUP w.conns c = NONE ∧ perform a w = (r, w') ⇒
  ALOOKUP w'.conns c = NONE ∧ (a = Read c ⇒ r ≠ Eof)
Proof
  Cases_on ‘a’ >> simp[perform_def] >> rpt strip_tac
  >> gvs[AllCaseEqs(), AFUPDKEY_ALOOKUP]
QED

Theorem perform_all_unknown:
  ∀acts w rs w'.
    ALOOKUP w.conns c = NONE ∧ perform_all acts w = (rs, w') ⇒
    ¬MEM (Read c, Eof) (ZIP (acts, rs))
Proof
  Induct >> simp[perform_all_def] >> rpt gen_tac
  >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[]
  >> drule_all perform_unknown >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem written_ZIP:
  ∀acts rs. LENGTH rs = LENGTH acts ⇒
            written c (sperf (ZIP (acts, rs))) =
            written c (MAP (λa. (a, NONE : response option)) acts)
Proof
  Induct >> simp[] >> rpt strip_tac >> Cases_on ‘rs’ >> gvs[]
  >> Cases_on ‘h’ >> gvs[sperf_def]
QED

(* In one round of the closed loop, for a known connection c:
   - what has arrived on c only grows;
   - unless the server read c, its unread data only grows;
   - once c's peer has closed and everything is read, it stays that way;
   - if the server read c, everything that had arrived has now been read *)
Theorem round_conn:
  closed_loop (server lfd) (start_world lfd sch) n = (h, w, perf) ∧
  closed_loop (server lfd) (start_world lfd sch) (n + 1) = (h', w', perf') ∧
  ALOOKUP w.conns c = SOME cn ⇒
  ∃cn'. ALOOKUP w'.conns c = SOME cn' ∧
        cn.received ≼ cn'.received ∧
        (¬MEM (Read c) (new_actions (log_of (server lfd)) h) ⇒
         cn.incoming ≼ cn'.incoming) ∧
        (cn.peer_closed ∧ cn.incoming = "" ⇒ cn'.peer_closed ∧ cn'.incoming = "") ∧
        (MEM (Read c) (new_actions (log_of (server lfd)) h) ⇒
         cn.received = FLAT (read c (sperf perf')))
Proof
  strip_tac
  >> qpat_assum ‘closed_loop _ _ (n + 1) = _’ (assume_tac o MATCH_MP closed_loop_consistent)
  >> drule_all closed_loop_step >> strip_tac >> gvs[]
  >> drule_all perform_all_conn >> strip_tac
  >> drule tick_conn >> strip_tac >> simp[]
  >> conj_tac
  >- (rw[] >> Cases_on ‘MEM (Read c) (new_actions (log_of (server lfd)) h)’ >> gvs[])
  >> strip_tac >> gvs[consistent_def] >> first_x_assum drule >> simp[]
QED

(* Everything the server has read from c by round n has been written back
   to c by round n + 1 *)
Theorem echo_next:
  closed_loop (server lfd) (start_world lfd sch) n = (h, w, perf) ∧
  closed_loop (server lfd) (start_world lfd sch) (n + 1) = (h', w', perf') ∧
  ALOOKUP w'.conns c = SOME cn' ⇒
  cn'.outgoing = FLAT (read c (sperf perf))
Proof
  strip_tac
  >> qpat_assum ‘closed_loop _ _ (n + 1) = _’ (assume_tac o MATCH_MP closed_loop_consistent)
  >> qpat_assum ‘closed_loop _ _ n = _’ (assume_tac o MATCH_MP closed_loop_fresh)
  >> drule_all closed_loop_step >> strip_tac >> gvs[]
  >> drule perform_all_length >> strip_tac
  >> gvs[consistent_def] >> first_x_assum drule >> strip_tac
  >> simp[written_ZIP]
  >> ‘written c (trans (server lfd) h) = read c (trans (server lfd) h)’
       by metis_tac[echo_server_safety]
  >> qpat_x_assum ‘written c _ = _’ mp_tac >> ASM_REWRITE_TAC[] >> simp[read_pending]
  >> disch_then (SUBST1_TAC o GSYM) >> simp[FLAT_APPEND]
QED

(* Once the server has seen end-of-file on c, c's peer has closed and there
   is nothing left to read *)
Theorem closed_loop_eof:
  ∀n h w perf.
    closed_loop (server lfd) (start_world lfd sch) n = (h, w, perf) ∧
    MEM (Read c, Eof) perf ⇒
    ∃cn. ALOOKUP w.conns c = SOME cn ∧ cn.peer_closed ∧ cn.incoming = ""
Proof
  Induct >- simp[closed_loop_def]
  >> rpt strip_tac
  >> Cases_on ‘closed_loop (server lfd) (start_world lfd sch) n’ >> PairCases_on ‘r’
  >> qspecl_then [‘server lfd’, ‘start_world lfd sch’, ‘n’, ‘q’, ‘r0’, ‘r1’,
                  ‘h’, ‘w’, ‘perf’] mp_tac
       (Q.GENL [‘m’, ‘w0’, ‘n’, ‘h’, ‘w’, ‘perf’, ‘h'’, ‘w'’, ‘perf'’] closed_loop_step)
  >> gvs[ADD1] >> strip_tac >> gvs[]
  >> ‘∃cn1. ALOOKUP w1.conns c = SOME cn1 ∧ cn1.peer_closed ∧ cn1.incoming = ""’
       suffices_by (strip_tac >> drule tick_conn >> strip_tac >> gvs[])
  (* end-of-file was seen before: it stays that way *)
  >- (drule_all perform_all_conn >> strip_tac >> simp[]
      >> Cases_on ‘MEM (Read c) (new_actions (log_of (server lfd)) q)’ >> gvs[])
  (* it is seen in this round: the peer had closed, and the read took all *)
  >> Cases_on ‘ALOOKUP r0.conns c’
  >- (drule_all perform_all_unknown >> simp[])
  >> drule_all perform_all_conn >> strip_tac >> simp[]
  >> drule perform_all_length >> strip_tac
  >> qpat_x_assum ‘MEM (Read c,Eof) (ZIP _)’ mp_tac >> simp[MEM_ZIP]
  >> metis_tac[MEM_EL]
QED

(* A connection with unread data is reported readable *)
Theorem incoming_ready:
  ALOOKUP w.conns c = SOME cn ∧ cn.incoming ≠ "" ⇒
  Readable c ∈ set (MAP Readable (ready_fds w))
Proof
  rw[ready_fds_def, MEM_MAP, MEM_FILTER, is_ready_def]
  >> imp_res_tac ALOOKUP_MEM >> disj2_tac >> qexists_tac ‘(c, cn)’ >> simp[]
QED

(* ------------------------------------------------------------------------
   Several rounds
   ------------------------------------------------------------------------ *)

(* What has arrived on a connection only grows *)
Theorem received_later:
  ∀d h' w' perf'.
    closed_loop (server lfd) (start_world lfd sch) n = (h, w, perf) ∧
    ALOOKUP w.conns c = SOME cn ∧
    closed_loop (server lfd) (start_world lfd sch) (n + d) = (h', w', perf') ⇒
    ∃cn'. ALOOKUP w'.conns c = SOME cn' ∧ cn.received ≼ cn'.received
Proof
  Induct >- (rw[] >> gvs[])
  >> rpt strip_tac
  >> Cases_on ‘closed_loop (server lfd) (start_world lfd sch) (n + d)’
  >> PairCases_on ‘r’
  >> first_x_assum (qspecl_then [‘q’, ‘r0’, ‘r1’] mp_tac) >> simp[] >> strip_tac
  >> qspecl_then [‘n + d’, ‘q’, ‘r0’, ‘r1’, ‘h'’, ‘w'’, ‘perf'’, ‘cn'’] mp_tac
       (Q.GENL [‘n’, ‘h’, ‘w’, ‘perf’, ‘h'’, ‘w'’, ‘perf'’, ‘cn’] round_conn)
  >> gvs[ADD1] >> strip_tac >> metis_tac[IS_PREFIX_TRANS]
QED

(* While the server does not read c, c's unread data only grows, and no
   read of c is performed *)
Theorem quiet_rounds:
  ∀d h' w' perf'.
    closed_loop (server lfd) (start_world lfd sch) n = (h, w, perf) ∧
    ALOOKUP w.conns c = SOME cn ∧
    closed_loop (server lfd) (start_world lfd sch) (n + d) = (h', w', perf') ∧
    (∀i hi wi pi. i < d ∧
                  closed_loop (server lfd) (start_world lfd sch) (n + i) = (hi, wi, pi) ⇒
                  ¬MEM (Read c) (new_actions (log_of (server lfd)) hi)) ⇒
    ∃cn'. ALOOKUP w'.conns c = SOME cn' ∧ cn.incoming ≼ cn'.incoming ∧
          ∀r. MEM (Read c, r) perf' ⇒ MEM (Read c, r) perf
Proof
  Induct >- (rw[] >> gvs[])
  >> rpt strip_tac
  >> Cases_on ‘closed_loop (server lfd) (start_world lfd sch) (n + d)’
  >> PairCases_on ‘r’
  >> first_x_assum (qspecl_then [‘q’, ‘r0’, ‘r1’] mp_tac) >> simp[]
  >> impl_tac
  >- (rpt strip_tac >> first_x_assum (qspecl_then [‘i’, ‘hi’, ‘wi’, ‘pi’] mp_tac)
      >> gvs[])
  >> strip_tac
  >> ‘¬MEM (Read c) (new_actions (log_of (server lfd)) q)’
       by (first_x_assum (qspecl_then [‘d’, ‘q’, ‘r0’, ‘r1’] mp_tac) >> simp[])
  >> qspecl_then [‘n + d’, ‘q’, ‘r0’, ‘r1’, ‘h'’, ‘w'’, ‘perf'’, ‘cn'’] mp_tac
       (Q.GENL [‘n’, ‘h’, ‘w’, ‘perf’, ‘h'’, ‘w'’, ‘perf'’, ‘cn’] round_conn)
  >> gvs[ADD1] >> strip_tac >> qexists_tac ‘cn''’ >> simp[]
  >> conj_tac >- metis_tac[IS_PREFIX_TRANS]
  >> qspecl_then [‘server lfd’, ‘start_world lfd sch’, ‘n + d’, ‘q’, ‘r0’, ‘r1’,
                  ‘h'’, ‘w'’, ‘perf'’] mp_tac
       (Q.GENL [‘m’, ‘w0’, ‘n’, ‘h’, ‘w’, ‘perf’, ‘h'’, ‘w'’, ‘perf'’] closed_loop_step)
  >> simp[] >> strip_tac >> gvs[]
  >> rpt strip_tac >- metis_tac[]
  >> qpat_x_assum ‘MEM _ (ZIP _)’ mp_tac >> drule perform_all_length
  >> simp[MEM_ZIP] >> metis_tac[MEM_EL]
QED

Theorem actions_SNOC[local]:
  (server lfd (h ++ [s])).actions =
  (server lfd h).actions ++ new_actions (log_of (server lfd)) (h ++ [s])
Proof
  qspecl_then [‘log_of (server lfd)’, ‘h’, ‘s’] mp_tac
    (Q.GENL [‘acts’, ‘h’, ‘s’] new_actions_prefix)
  >> simp[log_of_def, wf_SNOC_actions, wf_server]
QED

(* If the server reads c in none of the rounds n+1 .. n+d, its reads of c
   stay the same *)
Theorem nreads_quiet:
  ∀d h' w' perf'.
    closed_loop (server lfd) (start_world lfd sch) n = (h, w, perf) ∧
    closed_loop (server lfd) (start_world lfd sch) (n + d) = (h', w', perf') ∧
    (∀i hi wi pi. 0 < i ∧ i ≤ d ∧
                  closed_loop (server lfd) (start_world lfd sch) (n + i) = (hi, wi, pi) ⇒
                  ¬MEM (Read c) (new_actions (log_of (server lfd)) hi)) ⇒
    nreads c (server lfd h').actions = nreads c (server lfd h).actions
Proof
  Induct >- (rw[] >> gvs[])
  >> rpt strip_tac
  >> Cases_on ‘closed_loop (server lfd) (start_world lfd sch) (n + d)’
  >> PairCases_on ‘r’
  >> first_x_assum (qspecl_then [‘q’, ‘r0’, ‘r1’] mp_tac) >> simp[]
  >> impl_tac
  >- (rpt strip_tac >> first_x_assum (qspecl_then [‘i’, ‘hi’, ‘wi’, ‘pi’] mp_tac)
      >> gvs[])
  >> strip_tac
  >> ‘¬MEM (Read c) (new_actions (log_of (server lfd)) h')’
       by (first_x_assum (qspecl_then [‘SUC d’, ‘h'’, ‘w'’, ‘perf'’] mp_tac) >> simp[])
  >> qspecl_then [‘server lfd’, ‘start_world lfd sch’, ‘n + d’, ‘q’, ‘r0’, ‘r1’,
                  ‘h'’, ‘w'’, ‘perf'’] mp_tac
       (Q.GENL [‘m’, ‘w0’, ‘n’, ‘h’, ‘w’, ‘perf’, ‘h'’, ‘w'’, ‘perf'’] closed_loop_step)
  >> gvs[ADD1] >> strip_tac >> gvs[actions_SNOC]
  >> gvs[nreads_def, FILTER_EQ_NIL, EVERY_MEM, FILTER_APPEND_DISTRIB]
  >> rw[] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Liveness
   ------------------------------------------------------------------------ *)

Theorem MEM_accepted_prefix[local]:
  p ≼ p' ∧ MEM c (accepted (sperf p)) ⇒ MEM c (accepted (sperf p'))
Proof
  rw[IS_PREFIX_APPEND] >> simp[]
QED

(* On an accepted connection with unread data, the server reads it in one
   of the next four rounds (n .. n + 3).  The proof: if not, the data stays
   unread, so the connection is readable in three snapshots in a row, and
   then by handler_progress its handler, and so the server, reads it. *)
Theorem read_soon:
  closed_loop (server lfd) (start_world lfd sch) n = (h, w, perf) ∧
  ALOOKUP w.conns c = SOME cn ∧ cn.incoming ≠ "" ∧
  MEM c (accepted (sperf perf)) ⇒
  ∃i hi wi pi. i ≤ 3 ∧
     closed_loop (server lfd) (start_world lfd sch) (n + i) = (hi, wi, pi) ∧
     MEM (Read c) (new_actions (log_of (server lfd)) hi)
Proof
  rpt strip_tac >> CCONTR_TAC
  >> ‘∀i hi wi pi. i ≤ 3 ∧
        closed_loop (server lfd) (start_world lfd sch) (n + i) = (hi, wi, pi) ⇒
        ¬MEM (Read c) (new_actions (log_of (server lfd)) hi)’ by metis_tac[]
  >> qpat_x_assum ‘¬∃i. _’ kall_tac
  (* no read of c is performed in these rounds, so c's data stays unread *)
  >> ‘∀d hd wd pd.
        d ≤ 3 ∧ closed_loop (server lfd) (start_world lfd sch) (n + d) = (hd, wd, pd) ⇒
        ∃cn'. ALOOKUP wd.conns c = SOME cn' ∧ cn.incoming ≼ cn'.incoming ∧
              ∀r. MEM (Read c, r) pd ⇒ MEM (Read c, r) perf’
       by (rpt strip_tac
           >> qspecl_then [‘d’, ‘hd’, ‘wd’, ‘pd’] mp_tac quiet_rounds
           >> impl_tac
           >- (simp[] >> rpt strip_tac
               >> first_x_assum (qspecl_then [‘i’, ‘hi’, ‘wi’, ‘pi’] mp_tac) >> simp[])
           >> simp[])
  >> Cases_on ‘closed_loop (server lfd) (start_world lfd sch) (n + 3)’
  >> PairCases_on ‘r’ >> rename1 ‘_ = (h3, w3, p3)’
  (* so c stays readable *)
  >> ‘∀j. n ≤ j ∧ j < n + 3 ⇒ Readable c ∈ (EL j h3).ready’
       by (rpt strip_tac
           >> Cases_on ‘closed_loop (server lfd) (start_world lfd sch) (j + 1)’
           >> PairCases_on ‘r’
           >> first_x_assum (qspecl_then [‘j + 1 − n’, ‘q’, ‘r0’, ‘r1’] mp_tac)
           >> simp[] >> strip_tac
           >> drule_all closed_loop_snapshot >> disch_then SUBST1_TAC
           >> irule incoming_ready >> qexists_tac ‘cn'’ >> simp[]
           >> strip_tac >> gvs[])
  (* the closed loop gives the server a fresh, prompt history *)
  >> qpat_assum ‘closed_loop _ _ (n + 3) = _’ (strip_assume_tac o MATCH_MP closed_loop_fresh)
  >> qpat_assum ‘closed_loop _ _ (n + 3) = _’ (assume_tac o MATCH_MP closed_loop_prompt)
  >> qpat_assum ‘closed_loop _ _ n = _’ (strip_assume_tac o MATCH_MP closed_loop_fresh)
  >> qspecl_then [‘server lfd’, ‘start_world lfd sch’, ‘n’, ‘3’, ‘h’, ‘w’, ‘perf’,
                  ‘h3’, ‘w3’, ‘p3’] mp_tac (Q.GENL [‘m’, ‘w0’, ‘n’] closed_loop_prefix)
  >> impl_tac >- simp[] >> strip_tac
  (* the handler of c, inside the server, started at round a ≤ n *)
  >> qspec_then ‘h3’ mp_tac (Q.INST [‘fd’ |-> ‘c’] server_handler_view)
  >> impl_tac >- (simp[accepted_pending] >> metis_tac[MEM_accepted_prefix])
  >> strip_tac
  >> qpat_assum ‘closed_loop _ _ (n + 3) = _’ (assume_tac o MATCH_MP closed_loop_length)
  >> ‘a ≤ n’ by (first_x_assum (qspec_then ‘n’ mp_tac)
                 >> qpat_x_assum ‘h = TAKE _ _’ (assume_tac o GSYM)
                 >> simp[accepted_pending])
  (* by handler_progress, it reads c in rounds n + 1 .. n + 3 *)
  >> qspecl_then [‘g’, ‘n − a’] mp_tac (Q.INST [‘fd’ |-> ‘c’] handler_progress)
  >> impl_tac
  >- (rpt conj_tac >- simp[] >- simp[]
      >- (rpt strip_tac >> first_x_assum (qspec_then ‘j’ mp_tac) >> simp[]
          >> disch_then SUBST1_TAC >> first_x_assum irule >> simp[])
      (* it has not seen end-of-file: c still has unread data *)
      >> qpat_x_assum ‘FILTER _ _ = trans (handler c) g’ (SUBST1_TAC o GSYM)
      >> simp[MEM_FILTER, sperf_def, MEM_MAP] >> rpt strip_tac
      >> PairCases_on ‘y’ >> gvs[]
      >> qpat_x_assum ‘∀d hd wd pd. _’ (qspecl_then [‘3’, ‘h3’, ‘w3’, ‘p3’] mp_tac)
      >> impl_tac >- simp[]
      >> strip_tac >> ‘MEM (Read c, Eof) perf’ by metis_tac[]
      >> qspecl_then [‘n’, ‘TAKE n h3’, ‘w’, ‘perf’] mp_tac closed_loop_eof
      >> impl_tac >- simp[] >> strip_tac >> gvs[])
  >> strip_tac >> qpat_assum ‘∀j. j ≤ LENGTH g ⇒ _’ (qspec_then ‘n − a’ mp_tac)
  >> qpat_x_assum ‘∀j. j ≤ LENGTH g ⇒ _’ (qspec_then ‘n − a + 3’ mp_tac)
  >> simp[TAKE_LENGTH_ID_rwt] >> rpt strip_tac
  >> ‘TAKE (n − a + 3) g = g’ by simp[TAKE_LENGTH_ID_rwt]
  (* but the server's reads of c did not change in those rounds *)
  >> qspecl_then [‘3’, ‘h3’, ‘w3’, ‘p3’] mp_tac nreads_quiet
  >> impl_tac
  >- (simp[] >> rpt strip_tac
      >> qpat_x_assum ‘∀i hi wi pi. _ ⇒ ¬MEM _ _’
           (qspecl_then [‘i’, ‘hi’, ‘wi’, ‘pi’] mp_tac)
      >> simp[])
  >> gvs[]
QED

Theorem read_prefix[local]:
  p ≼ p' ⇒ FLAT (read c (sperf p)) ≼ FLAT (read c (sperf p'))
Proof
  rw[IS_PREFIX_APPEND] >> simp[]
QED

(* MAIN: liveness for an accepted connection.  Everything that has arrived
   on it by round n has been written back to it by round n + 5. *)
Theorem closed_loop_echo_accepted:
  closed_loop (server lfd) (start_world lfd sch) n = (h, w, perf) ∧
  ALOOKUP w.conns c = SOME cn ∧ MEM c (accepted (sperf perf)) ∧
  closed_loop (server lfd) (start_world lfd sch) (n + 5) = (h5, w5, p5) ⇒
  ∃cn5. ALOOKUP w5.conns c = SOME cn5 ∧ cn.received ≼ cn5.outgoing
Proof
  strip_tac
  >> qspecl_then [‘5’, ‘h5’, ‘w5’, ‘p5’] mp_tac received_later
  >> impl_tac >- simp[] >> strip_tac >> qexists_tac ‘cn'’ >> simp[]
  (* by round n + 5, everything read by round n + 4 is written back *)
  >> Cases_on ‘closed_loop (server lfd) (start_world lfd sch) (n + 4)’
  >> PairCases_on ‘r’ >> rename1 ‘_ = (h4, w4, p4)’
  >> qspecl_then [‘n + 4’, ‘h4’, ‘w4’, ‘p4’, ‘h5’, ‘w5’, ‘p5’, ‘cn'’] mp_tac
       (Q.GENL [‘n’, ‘h’, ‘w’, ‘perf’, ‘h'’, ‘w'’, ‘perf'’, ‘cn'’] echo_next)
  >> impl_tac >- simp[] >> disch_then SUBST1_TAC
  >> qspecl_then [‘server lfd’, ‘start_world lfd sch’, ‘n’, ‘4’, ‘h’, ‘w’, ‘perf’,
                  ‘h4’, ‘w4’, ‘p4’] mp_tac (Q.GENL [‘m’, ‘w0’, ‘n’] closed_loop_prefix)
  >> impl_tac >- simp[] >> strip_tac
  >> Cases_on ‘cn.incoming = ""’
  (* nothing unread: everything has been read already *)
  >- (qpat_assum ‘closed_loop _ _ n = _’ (mp_tac o MATCH_MP closed_loop_consistent)
      >> simp[consistent_def] >> strip_tac >> first_x_assum drule >> strip_tac
      >> gvs[read_prefix])
  (* otherwise the server reads c in some round n + i, i ≤ 3 *)
  >> drule_all read_soon >> strip_tac
  >> Cases_on ‘closed_loop (server lfd) (start_world lfd sch) (n + i + 1)’
  >> PairCases_on ‘r’ >> rename1 ‘_ = (hj, wj, pj)’
  >> qspecl_then [‘i’, ‘hi’, ‘wi’, ‘pi’] mp_tac received_later
  >> impl_tac >- simp[] >> strip_tac
  >> qspecl_then [‘n + i’, ‘hi’, ‘wi’, ‘pi’, ‘hj’, ‘wj’, ‘pj’, ‘cn''’] mp_tac
       (Q.GENL [‘n’, ‘h’, ‘w’, ‘perf’, ‘h'’, ‘w'’, ‘perf'’, ‘cn’] round_conn)
  >> impl_tac >- simp[] >> strip_tac >> gvs[]
  >> qspecl_then [‘server lfd’, ‘start_world lfd sch’, ‘n + i + 1’, ‘3 − i’, ‘hj’, ‘wj’,
                  ‘pj’, ‘h4’, ‘w4’, ‘p4’] mp_tac (Q.GENL [‘m’, ‘w0’, ‘n’] closed_loop_prefix)
  >> impl_tac >- simp[] >> strip_tac
  >> metis_tac[IS_PREFIX_TRANS, read_prefix]
QED

(* ------------------------------------------------------------------------
   The listener's queue
   ------------------------------------------------------------------------ *)

(* Performing an action: an accept on the listener takes the connection at
   the front of its queue, and hands it out; nothing else changes the queue
   or which connections exist *)
Theorem perform_listener:
  w.listeners = [(lfd, q)] ∧ perform a w = (r, w') ⇒
  (∀c. ALOOKUP w'.conns c = NONE ⇔ ALOOKUP w.conns c = NONE) ∧
  ∃d q'. w'.listeners = [(lfd, q')] ∧ q = d ++ q' ∧
         accepted [(a, SOME r)] = d ∧ (a = Accept lfd ∧ q ≠ [] ⇒ d ≠ []) ∧
         (a ≠ Accept lfd ⇒ d = [])
Proof
  Cases_on ‘a’ >> simp[perform_def] >> strip_tac
  >> gvs[AllCaseEqs(), AFUPDKEY_ALOOKUP, AFUPDKEY_def] >> rw[]
  >> gvs[AllCaseEqs()]
QED

Theorem accepted_sperf_CONS[local]:
  accepted (sperf ((a, r) :: l)) = accepted [(a, SOME r)] ++ accepted (sperf l)
Proof
  ‘(a, r) :: l = [(a, r)] ++ l’ by simp[] >> pop_assum SUBST1_TAC
  >> REWRITE_TAC[sperf_APPEND, accepted_APPEND]
QED

Theorem perform_all_listener:
  ∀acts w rs w' q.
    w.listeners = [(lfd, q)] ∧ perform_all acts w = (rs, w') ⇒
    (∀c. ALOOKUP w'.conns c = NONE ⇔ ALOOKUP w.conns c = NONE) ∧
    ∃d q'. w'.listeners = [(lfd, q')] ∧ q = d ++ q' ∧
           accepted (sperf (ZIP (acts, rs))) = d ∧
           (MEM (Accept lfd) acts ∧ q ≠ [] ⇒ d ≠ []) ∧
           (¬MEM (Accept lfd) acts ⇒ d = [])
Proof
  Induct >> simp[perform_all_def] >> rpt gen_tac
  >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[]
  >> drule_all perform_listener >> strip_tac
  >> first_x_assum drule_all >> strip_tac
  >> simp[accepted_sperf_CONS] >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem deliver1_listener:
  w.listeners = [(lfd, q)] ⇒
  ∃x. (deliver1 w a).listeners = [(lfd, q ++ x)] ∧
      ∀c. ALOOKUP (deliver1 w a).conns c ≠ NONE ⇒ ALOOKUP w.conns c ≠ NONE ∨ MEM c x
Proof
  Cases_on ‘a’ >> simp[deliver1_def] >> strip_tac
  >- (rw[] >> gvs[is_listener_def, AllCaseEqs()]
      >> qexists_tac ‘[n0]’ >> simp[AFUPDKEY_def] >> metis_tac[])
  >> rw[AFUPDKEY_ALOOKUP] >> gvs[AllCaseEqs()]
QED

Theorem deliver_listener:
  ∀as w q.
    w.listeners = [(lfd, q)] ⇒
    ∃x. (FOLDL deliver1 w as).listeners = [(lfd, q ++ x)] ∧
        ∀c. ALOOKUP (FOLDL deliver1 w as).conns c ≠ NONE ⇒
            ALOOKUP w.conns c ≠ NONE ∨ MEM c x
Proof
  Induct >> simp[]
  >> rpt strip_tac >> drule deliver1_listener
  >> disch_then (qspec_then ‘h’ strip_assume_tac)
  >> first_x_assum drule >> strip_tac
  >> qexists_tac ‘x ++ x'’ >> simp[] >> metis_tac[MEM_APPEND]
QED

(* Time passing: new connections join the back of the queue; they are the
   only new connections *)
Theorem tick_listener:
  w.listeners = [(lfd, q)] ⇒
  ∃x. (tick w).listeners = [(lfd, q ++ x)] ∧
      ∀c. ALOOKUP (tick w).conns c ≠ NONE ⇒ ALOOKUP w.conns c ≠ NONE ∨ MEM c x
Proof
  rw[tick_def] >> CASE_TAC >> simp[deliver_def]
  >> qspecl_then [‘x’, ‘w with sched := THE (LTL w.sched)’, ‘q’] mp_tac deliver_listener
  >> simp[] >> metis_tac[]
QED

(* In one round: the accepts take connections d from the front of the
   queue, which are handed out; new connections x join the back *)
Theorem round_listener:
  closed_loop (server lfd) (start_world lfd sch) n = (h, w, perf) ∧
  closed_loop (server lfd) (start_world lfd sch) (n + 1) = (h', w', perf') ∧
  w.listeners = [(lfd, q)] ⇒
  ∃d q' x. w'.listeners = [(lfd, q' ++ x)] ∧ q = d ++ q' ∧
           accepted (sperf perf') = accepted (sperf perf) ++ d ∧
           (MEM (Accept lfd) (new_actions (log_of (server lfd)) h) ∧ q ≠ [] ⇒ d ≠ []) ∧
           (¬MEM (Accept lfd) (new_actions (log_of (server lfd)) h) ⇒ d = []) ∧
           ∀c. ALOOKUP w'.conns c ≠ NONE ⇒ ALOOKUP w.conns c ≠ NONE ∨ MEM c x
Proof
  strip_tac >> drule_all closed_loop_step >> strip_tac >> gvs[]
  >> drule_all perform_all_listener >> strip_tac
  >> drule tick_listener >> strip_tac
  >> qexistsl_tac [‘q'’, ‘x’] >> gvs[] >> metis_tac[]
QED

(* Every connection has been handed out, or is pending on the listener *)
Theorem conns_known:
  ∀n h w perf.
    closed_loop (server lfd) (start_world lfd sch) n = (h, w, perf) ⇒
    ∃q. w.listeners = [(lfd, q)] ∧
        ∀c. ALOOKUP w.conns c ≠ NONE ⇒ MEM c (accepted (sperf perf)) ∨ MEM c q
Proof
  Induct >- simp[closed_loop_def, start_world_def]
  >> rpt strip_tac
  >> Cases_on ‘closed_loop (server lfd) (start_world lfd sch) n’ >> PairCases_on ‘r’
  >> first_x_assum (qspecl_then [‘q’, ‘r0’, ‘r1’] mp_tac) >> simp[] >> strip_tac
  >> qspecl_then [‘n’, ‘q’, ‘r0’, ‘r1’, ‘h’, ‘w’, ‘perf’, ‘q'’] mp_tac
       (Q.GENL [‘n’, ‘h’, ‘w’, ‘perf’, ‘h'’, ‘w'’, ‘perf'’, ‘q’] round_listener)
  >> gvs[ADD1] >> strip_tac >> simp[] >> rpt strip_tac
  >> first_x_assum drule >> strip_tac >> gvs[]
  >> Cases_on ‘ALOOKUP r0.conns c = NONE’ >> gvs[] >> metis_tac[]
QED

(* A listener with pending connections is reported readable *)
Theorem listener_ready:
  w.listeners = [(lfd, q)] ∧ q ≠ [] ⇒
  Readable lfd ∈ set (MAP Readable (ready_fds w))
Proof
  rw[ready_fds_def, MEM_MAP, MEM_FILTER, is_ready_def]
  >> qexists_tac ‘lfd’ >> simp[]
QED

(* While the server does not accept, the queue only grows *)
Theorem quiet_listener:
  ∀d h' w' perf'.
    closed_loop (server lfd) (start_world lfd sch) n = (h, w, perf) ∧
    w.listeners = [(lfd, q)] ∧
    closed_loop (server lfd) (start_world lfd sch) (n + d) = (h', w', perf') ∧
    (∀i hi wi pi. i < d ∧
                  closed_loop (server lfd) (start_world lfd sch) (n + i) = (hi, wi, pi) ⇒
                  ¬MEM (Accept lfd) (new_actions (log_of (server lfd)) hi)) ⇒
    ∃y. w'.listeners = [(lfd, q ++ y)]
Proof
  Induct >- (rw[] >> gvs[])
  >> rpt strip_tac
  >> Cases_on ‘closed_loop (server lfd) (start_world lfd sch) (n + d)’
  >> PairCases_on ‘r’
  >> first_x_assum (qspecl_then [‘q'’, ‘r0’, ‘r1’] mp_tac) >> simp[]
  >> impl_tac
  >- (rpt strip_tac >> first_x_assum (qspecl_then [‘i’, ‘hi’, ‘wi’, ‘pi’] mp_tac)
      >> gvs[])
  >> strip_tac
  >> ‘¬MEM (Accept lfd) (new_actions (log_of (server lfd)) q')’
       by (first_x_assum (qspecl_then [‘d’, ‘q'’, ‘r0’, ‘r1’] mp_tac) >> simp[])
  >> qspecl_then [‘n + d’, ‘q'’, ‘r0’, ‘r1’, ‘h'’, ‘w'’, ‘perf'’, ‘q ++ y’] mp_tac
       (Q.GENL [‘n’, ‘h’, ‘w’, ‘perf’, ‘h'’, ‘w'’, ‘perf'’, ‘q’] round_listener)
  >> gvs[ADD1] >> strip_tac >> gvs[]
QED

(* If the server accepts in none of the rounds n+1 .. n+d, its accepts
   stay the same *)
Theorem naccepts_quiet:
  ∀d h' w' perf'.
    closed_loop (server lfd) (start_world lfd sch) n = (h, w, perf) ∧
    closed_loop (server lfd) (start_world lfd sch) (n + d) = (h', w', perf') ∧
    (∀i hi wi pi. 0 < i ∧ i ≤ d ∧
                  closed_loop (server lfd) (start_world lfd sch) (n + i) = (hi, wi, pi) ⇒
                  ¬MEM (Accept lfd) (new_actions (log_of (server lfd)) hi)) ⇒
    naccepts lfd (server lfd h').actions = naccepts lfd (server lfd h).actions
Proof
  Induct >- (rw[] >> gvs[])
  >> rpt strip_tac
  >> Cases_on ‘closed_loop (server lfd) (start_world lfd sch) (n + d)’
  >> PairCases_on ‘r’
  >> first_x_assum (qspecl_then [‘q’, ‘r0’, ‘r1’] mp_tac) >> simp[]
  >> impl_tac
  >- (rpt strip_tac >> first_x_assum (qspecl_then [‘i’, ‘hi’, ‘wi’, ‘pi’] mp_tac)
      >> gvs[])
  >> strip_tac
  >> ‘¬MEM (Accept lfd) (new_actions (log_of (server lfd)) h')’
       by (first_x_assum (qspecl_then [‘SUC d’, ‘h'’, ‘w'’, ‘perf'’] mp_tac) >> simp[])
  >> qspecl_then [‘server lfd’, ‘start_world lfd sch’, ‘n + d’, ‘q’, ‘r0’, ‘r1’,
                  ‘h'’, ‘w'’, ‘perf'’] mp_tac
       (Q.GENL [‘m’, ‘w0’, ‘n’, ‘h’, ‘w’, ‘perf’, ‘h'’, ‘w'’, ‘perf'’] closed_loop_step)
  >> gvs[ADD1] >> strip_tac >> gvs[actions_SNOC]
  >> gvs[naccepts_def, count_def, FILTER_EQ_NIL, EVERY_MEM, FILTER_APPEND_DISTRIB]
  >> rw[] >> metis_tac[]
QED

(* With connections pending, the server accepts in one of the next three
   rounds (n .. n + 2), by server_accept_progress *)
Theorem accept_soon:
  closed_loop (server lfd) (start_world lfd sch) n = (h, w, perf) ∧
  w.listeners = [(lfd, q)] ∧ q ≠ [] ⇒
  ∃i hi wi pi. i ≤ 2 ∧
     closed_loop (server lfd) (start_world lfd sch) (n + i) = (hi, wi, pi) ∧
     MEM (Accept lfd) (new_actions (log_of (server lfd)) hi)
Proof
  rpt strip_tac >> CCONTR_TAC
  >> ‘∀i hi wi pi. i ≤ 2 ∧
        closed_loop (server lfd) (start_world lfd sch) (n + i) = (hi, wi, pi) ⇒
        ¬MEM (Accept lfd) (new_actions (log_of (server lfd)) hi)’ by metis_tac[]
  >> qpat_x_assum ‘¬∃i. _’ kall_tac
  >> Cases_on ‘closed_loop (server lfd) (start_world lfd sch) (n + 2)’
  >> PairCases_on ‘r’ >> rename1 ‘_ = (h2, w2, p2)’
  (* the listener stays readable *)
  >> ‘∀j. n ≤ j ∧ j < n + 2 ⇒ Readable lfd ∈ (EL j h2).ready’
       by (rpt strip_tac
           >> Cases_on ‘closed_loop (server lfd) (start_world lfd sch) (j + 1)’
           >> PairCases_on ‘r’
           >> qspecl_then [‘j + 1 − n’, ‘q'’, ‘r0’, ‘r1’] mp_tac quiet_listener
           >> impl_tac
           >- (simp[] >> rpt strip_tac
               >> qpat_x_assum ‘∀i hi wi pi. _ ⇒ ¬MEM _ _’
                    (qspecl_then [‘i’, ‘hi’, ‘wi’, ‘pi’] mp_tac) >> simp[])
           >> strip_tac
           >> drule_all closed_loop_snapshot >> disch_then SUBST1_TAC
           >> irule listener_ready >> simp[])
  >> qpat_assum ‘closed_loop _ _ (n + 2) = _’ (assume_tac o MATCH_MP closed_loop_prompt)
  >> qpat_assum ‘closed_loop _ _ (n + 2) = _’ (assume_tac o MATCH_MP closed_loop_length)
  >> qspecl_then [‘server lfd’, ‘start_world lfd sch’, ‘n’, ‘2’, ‘h’, ‘w’, ‘perf’,
                  ‘h2’, ‘w2’, ‘p2’] mp_tac (Q.GENL [‘m’, ‘w0’, ‘n’] closed_loop_prefix)
  >> impl_tac >- simp[] >> strip_tac
  >> qspecl_then [‘h2’, ‘n’] mp_tac server_accept_progress
  >> impl_tac >- simp[]
  >> simp[TAKE_LENGTH_ID_rwt] >> qpat_x_assum ‘h = TAKE _ _’ (SUBST1_TAC o GSYM)
  >> qspecl_then [‘2’, ‘h2’, ‘w2’, ‘p2’] mp_tac naccepts_quiet
  >> impl_tac
  >- (simp[] >> rpt strip_tac
      >> qpat_x_assum ‘∀i hi wi pi. _ ⇒ ¬MEM _ _’
           (qspecl_then [‘i’, ‘hi’, ‘wi’, ‘pi’] mp_tac)
      >> simp[])
  >> simp[]
QED

(* A pending connection c, with pre ahead of it in the queue: after a round
   it has been handed out, or it has no more connections ahead of it (fewer,
   if the server accepted) *)
Theorem round_queue:
  closed_loop (server lfd) (start_world lfd sch) n = (h, w, perf) ∧
  closed_loop (server lfd) (start_world lfd sch) (n + 1) = (h', w', perf') ∧
  w.listeners = [(lfd, pre ++ c :: post)] ⇒
  MEM c (accepted (sperf perf')) ∨
  ∃pre' post'. w'.listeners = [(lfd, pre' ++ c :: post')] ∧
               LENGTH pre' ≤ LENGTH pre ∧
               (MEM (Accept lfd) (new_actions (log_of (server lfd)) h) ⇒
                LENGTH pre' < LENGTH pre)
Proof
  strip_tac >> drule_all round_listener >> strip_tac
  >> qpat_x_assum ‘_ = d ++ q'’ (strip_assume_tac o REWRITE_RULE[APPEND_EQ_APPEND])
  >> gvs[]
  >- (disj2_tac >> qexistsl_tac [‘l’, ‘post ++ x’] >> simp[]
      >> strip_tac >> gvs[] >> Cases_on ‘d’ >> gvs[])
  >> Cases_on ‘l’ >> gvs[]
  >> disj2_tac >> qexistsl_tac [‘[]’, ‘post ++ x’] >> simp[]
  >> strip_tac >> gvs[] >> Cases_on ‘pre’ >> gvs[]
QED

(* Connections handed out stay handed out *)
Theorem accepted_later:
  closed_loop (server lfd) (start_world lfd sch) m = (h, w, perf) ∧
  closed_loop (server lfd) (start_world lfd sch) N = (h', w', perf') ∧
  m ≤ N ∧ MEM c (accepted (sperf perf)) ⇒
  MEM c (accepted (sperf perf'))
Proof
  strip_tac
  >> qspecl_then [‘server lfd’, ‘start_world lfd sch’, ‘m’, ‘N − m’, ‘h’, ‘w’, ‘perf’,
                  ‘h'’, ‘w'’, ‘perf'’] mp_tac (Q.GENL [‘m’, ‘w0’, ‘n’] closed_loop_prefix)
  >> simp[] >> metis_tac[MEM_accepted_prefix]
QED

Theorem queue_later:
  ∀d h' w' perf'.
    closed_loop (server lfd) (start_world lfd sch) n = (h, w, perf) ∧
    w.listeners = [(lfd, pre ++ c :: post)] ∧
    closed_loop (server lfd) (start_world lfd sch) (n + d) = (h', w', perf') ⇒
    MEM c (accepted (sperf perf')) ∨
    ∃pre' post'. w'.listeners = [(lfd, pre' ++ c :: post')] ∧ LENGTH pre' ≤ LENGTH pre
Proof
  Induct >- (rw[] >> gvs[] >> metis_tac[LESS_EQ_REFL])
  >> rpt strip_tac
  >> Cases_on ‘closed_loop (server lfd) (start_world lfd sch) (n + d)’
  >> PairCases_on ‘r’
  >> qpat_x_assum ‘∀h' w' perf'. _’ (qspecl_then [‘q’, ‘r0’, ‘r1’] mp_tac)
  >> simp[] >> strip_tac
  >- (disj1_tac
      >> qspecl_then [‘n + d’, ‘q’, ‘r0’, ‘r1’, ‘n + SUC d’, ‘h'’, ‘w'’, ‘perf'’] mp_tac
           (Q.GENL [‘m’, ‘h’, ‘w’, ‘perf’, ‘N’, ‘h'’, ‘w'’, ‘perf'’] accepted_later)
      >> simp[])
  >> qspecl_then [‘n + d’, ‘q’, ‘r0’, ‘r1’, ‘h'’, ‘w'’, ‘perf'’, ‘pre'’, ‘post'’] mp_tac
       (Q.GENL [‘n’, ‘h’, ‘w’, ‘perf’, ‘h'’, ‘w'’, ‘perf'’, ‘pre’, ‘post’] round_queue)
  >> gvs[ADD1] >> strip_tac >> simp[] >> metis_tac[LESS_EQ_TRANS]
QED

(* MAIN: pending connections are accepted.  A connection with p connections
   ahead of it in the listener's queue is handed out within 3 (p + 1)
   rounds. *)
Theorem queue_progress:
  ∀p n h w perf pre post.
    closed_loop (server lfd) (start_world lfd sch) n = (h, w, perf) ∧
    w.listeners = [(lfd, pre ++ c :: post)] ∧ LENGTH pre ≤ p ⇒
    ∀N hN wN pN.
      n + 3 * (p + 1) ≤ N ∧
      closed_loop (server lfd) (start_world lfd sch) N = (hN, wN, pN) ⇒
      MEM c (accepted (sperf pN))
Proof
  completeInduct_on ‘p’ >> rpt strip_tac
  (* the server accepts in some round n + i, i ≤ 2 *)
  >> qspecl_then [‘n’, ‘h’, ‘w’, ‘perf’, ‘pre ++ c :: post’] mp_tac
       (Q.GENL [‘n’, ‘h’, ‘w’, ‘perf’, ‘q’] accept_soon)
  >> simp[] >> strip_tac
  (* until then, c does not lose its place *)
  >> qspecl_then [‘i’, ‘hi’, ‘wi’, ‘pi’] mp_tac queue_later
  >> impl_tac >- simp[] >> strip_tac
  >- (qspecl_then [‘n + i’, ‘hi’, ‘wi’, ‘pi’, ‘N’, ‘hN’, ‘wN’, ‘pN’] mp_tac
        (Q.GENL [‘m’, ‘h’, ‘w’, ‘perf’, ‘N’, ‘h'’, ‘w'’, ‘perf'’] accepted_later)
      >> simp[])
  (* in round n + i it gets handed out, or moves up the queue *)
  >> Cases_on ‘closed_loop (server lfd) (start_world lfd sch) (n + i + 1)’
  >> PairCases_on ‘r’ >> rename1 ‘_ = (hj, wj, pj)’
  >> qspecl_then [‘n + i’, ‘hi’, ‘wi’, ‘pi’, ‘hj’, ‘wj’, ‘pj’, ‘pre'’, ‘post'’] mp_tac
       (Q.GENL [‘n’, ‘h’, ‘w’, ‘perf’, ‘h'’, ‘w'’, ‘perf'’, ‘pre’, ‘post’] round_queue)
  >> simp[] >> strip_tac
  >- (qspecl_then [‘n + i + 1’, ‘hj’, ‘wj’, ‘pj’, ‘N’, ‘hN’, ‘wN’, ‘pN’] mp_tac
        (Q.GENL [‘m’, ‘h’, ‘w’, ‘perf’, ‘N’, ‘h'’, ‘w'’, ‘perf'’] accepted_later)
      >> simp[])
  (* then by induction, with fewer connections ahead of it *)
  >> first_x_assum (qspec_then ‘p − 1’ mp_tac) >> simp[]
  >> disch_then (qspecl_then [‘n + i + 1’, ‘hj’, ‘wj’, ‘pj’, ‘pre''’, ‘post''’] mp_tac)
  >> impl_tac >- simp[]
  >> disch_then (qspecl_then [‘N’, ‘hN’, ‘wN’, ‘pN’] mp_tac) >> simp[]
QED

(* What has been written to a connection only grows *)
Theorem outgoing_later:
  closed_loop (server lfd) (start_world lfd sch) m = (h, w, perf) ∧
  closed_loop (server lfd) (start_world lfd sch) N = (h', w', perf') ∧ m ≤ N ∧
  ALOOKUP w.conns c = SOME cn ∧ ALOOKUP w'.conns c = SOME cn' ⇒
  cn.outgoing ≼ cn'.outgoing
Proof
  strip_tac
  >> qspecl_then [‘server lfd’, ‘start_world lfd sch’, ‘m’, ‘N − m’, ‘h’, ‘w’, ‘perf’,
                  ‘h'’, ‘w'’, ‘perf'’] mp_tac (Q.GENL [‘m’, ‘w0’, ‘n’] closed_loop_prefix)
  >> simp[] >> strip_tac
  >> qpat_assum ‘closed_loop _ _ m = _’ (mp_tac o MATCH_MP closed_loop_consistent)
  >> qpat_assum ‘closed_loop _ _ N = _’ (mp_tac o MATCH_MP closed_loop_consistent)
  >> simp[consistent_def] >> rpt strip_tac
  >> res_tac >> simp[]
  >> qpat_x_assum ‘perf ≼ perf'’ (strip_assume_tac o REWRITE_RULE[IS_PREFIX_APPEND])
  >> simp[]
QED

(* Every connection known at round n has been handed out by round n + 3 q *)
Theorem handed_out_by:
  closed_loop (server lfd) (start_world lfd sch) n = (h, w, perf) ∧
  ALOOKUP w.conns c = SOME cn ∧ w.listeners = [(lfd, q)] ⇒
  ∃M hM wM pM. n ≤ M ∧ M ≤ n + 3 * LENGTH q ∧
     closed_loop (server lfd) (start_world lfd sch) M = (hM, wM, pM) ∧
     MEM c (accepted (sperf pM))
Proof
  strip_tac
  >> qpat_assum ‘closed_loop _ _ n = _’ (strip_assume_tac o MATCH_MP conns_known)
  >> gvs[] >> first_x_assum (qspec_then ‘c’ mp_tac) >> simp[] >> strip_tac
  (* already handed out *)
  >- (qexistsl_tac [‘n’, ‘h’, ‘w’, ‘perf’] >> simp[])
  (* pending, with l1 ahead of it *)
  >> qpat_x_assum ‘MEM c q’ (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >> gvs[]
  >> Cases_on ‘closed_loop (server lfd) (start_world lfd sch) (n + 3 * (LENGTH l1 + 1))’
  >> PairCases_on ‘r’ >> rename1 ‘_ = (hM, wM, pM)’
  >> qexistsl_tac [‘n + 3 * (LENGTH l1 + 1)’, ‘hM’, ‘wM’, ‘pM’] >> simp[]
  >> qspecl_then [‘LENGTH l1’, ‘n’, ‘h’, ‘w’, ‘perf’, ‘l1’, ‘l2’] mp_tac queue_progress
  >> impl_tac >- simp[]
  >> disch_then (qspecl_then [‘n + 3 * (LENGTH l1 + 1)’, ‘hM’, ‘wM’, ‘pM’] mp_tac)
  >> simp[]
QED

(* MAIN: liveness of the echo server in the closed loop.  On every
   connection, everything that has arrived by round n has been written back
   to it by round n + 3 q + 5, where q is the number of connections pending
   on the listener at round n.  No assumption is needed beyond the world
   model itself (see design/09-closed-loop.md). *)
Theorem closed_loop_liveness:
  closed_loop (server lfd) (start_world lfd sch) n = (h, w, perf) ∧
  ALOOKUP w.conns c = SOME cn ∧ w.listeners = [(lfd, q)] ∧
  n + 3 * LENGTH q + 5 ≤ N ∧
  closed_loop (server lfd) (start_world lfd sch) N = (hN, wN, pN) ⇒
  ∃cnN. ALOOKUP wN.conns c = SOME cnN ∧ cn.received ≼ cnN.outgoing
Proof
  strip_tac
  (* c is handed out by some round M ≤ n + 3 q *)
  >> drule_all handed_out_by >> strip_tac
  (* what had arrived by round n had arrived by round M *)
  >> qspecl_then [‘M − n’, ‘hM’, ‘wM’, ‘pM’] mp_tac received_later
  >> impl_tac >- simp[] >> strip_tac
  (* and is written back by round M + 5 *)
  >> Cases_on ‘closed_loop (server lfd) (start_world lfd sch) (M + 5)’
  >> PairCases_on ‘r’ >> rename1 ‘_ = (h5, w5, p5)’
  >> qspecl_then [‘M’, ‘hM’, ‘wM’, ‘pM’, ‘cn'’, ‘h5’, ‘w5’, ‘p5’] mp_tac
       (Q.GENL [‘n’, ‘h’, ‘w’, ‘perf’, ‘cn’, ‘h5’, ‘w5’, ‘p5’] closed_loop_echo_accepted)
  >> simp[] >> strip_tac
  (* so by round N *)
  >> qspecl_then [‘N − n’, ‘hN’, ‘wN’, ‘pN’] mp_tac received_later
  >> impl_tac >- simp[] >> strip_tac >> qexists_tac ‘cn''’ >> simp[]
  >> qspecl_then [‘M + 5’, ‘h5’, ‘w5’, ‘p5’, ‘N’, ‘hN’, ‘wN’, ‘pN’, ‘cn5’, ‘cn''’] mp_tac
       (Q.GENL [‘m’, ‘h’, ‘w’, ‘perf’, ‘N’, ‘h'’, ‘w'’, ‘perf'’, ‘cn’, ‘cn'’] outgoing_later)
  >> simp[] >> metis_tac[IS_PREFIX_TRANS]
QED

(* ------------------------------------------------------------------------
   From the clients' side
   ------------------------------------------------------------------------ *)

(* An arrival is effective: the world does not drop it.  This mirrors the
   socket model's arrival_ok (spike/socket-model, socketFair), whose
   sched_wf asks it of every arrival of the schedule. *)
Definition arrival_ok_def:
  (arrival_ok w (Connect l c) ⇔
     is_listener w l ∧ ¬is_listener w c ∧ ¬is_conn w c) ∧
  (arrival_ok w (Arrive c d) ⇔
     ∃cn. ALOOKUP w.conns c = SOME cn ∧ ¬cn.peer_closed) ∧
  (arrival_ok w (Hangup c) ⇔
     ∃cn. ALOOKUP w.conns c = SOME cn ∧ ¬cn.peer_closed)
End

(* Data a client sends, if effective, is recorded as received on its
   connection; closed_loop_liveness then says it is written back *)
Theorem arrive_received:
  arrival_ok w (Arrive c d) ⇒
  ∃cn cn'. ALOOKUP w.conns c = SOME cn ∧
           ALOOKUP (deliver1 w (Arrive c d)).conns c = SOME cn' ∧
           cn'.received = cn.received ++ d
Proof
  rw[arrival_ok_def, deliver1_def, AFUPDKEY_ALOOKUP] >> simp[]
QED

(* ------------------------------------------------------------------------
   Sanity check: two clients, interleaved, in the closed loop
   ------------------------------------------------------------------------ *)

(* Client 5 connects and sends "hi"; client 6 connects and sends "yo";
   client 5 sends "!!", then closes its side *)
Definition two_clients_sched_def:
  two_clients_sched =
    fromList [[Connect 0 5; Arrive 5 "hi"]; [Connect 0 6; Arrive 6 "yo"];
              [Arrive 5 "!!"]; [Hangup 5]]
End

(* After 9 rounds each client has got back exactly what it sent (fields:
   fd, received, outgoing, unread) *)
Theorem example_closed_loop:
  MAP (λ(c, cn). (c, cn.received, cn.outgoing, cn.incoming))
      (FST (SND (closed_loop (server 0) (start_world 0 two_clients_sched) 9))).conns =
  [(6, "yo", "yo", ""); (5, "hi!!", "hi!!", "")]
Proof
  EVAL_TAC
QED
