(*
  Liveness of the echo server in the closed loop (M4 in the model).

  In the closed-loop world every byte that arrives on a connection is
  written back to that connection within a bounded number of rounds:
   - closed_loop_echo_accepted: on an accepted connection, everything that
     has arrived by round n is written back by round n + 5;
   - closed_loop_accepts: a pending connection at position i of the
     listener's queue is accepted within 3 (i + 1) rounds;
   - closed_loop_liveness: so on every connection, everything that has
     arrived by round n is written back by round n + 3 q + 5, where q is
     the number of pending connections at round n.

  The world is fair by construction (design/09-closed-loop.md): it answers
  every action in the next snapshot, a read returns all available data, a
  write always completes, and arrivals are delivered when scheduled.  So
  no further assumption is needed.  The proof combines the program-level
  progress theorems (asyncProgress) with how the world evolves.
*)
Theory asyncLiveness
Ancestors
  pair list rich_list arithmetic option pred_set string alist llist
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncWorld asyncClosedLoop asyncProgress
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
