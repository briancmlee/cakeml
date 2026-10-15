(*
  The echo server in the closed loop with the world (M4 in the model).

  Safety, lifted: in the closed loop, every connection's outgoing data is a
  prefix of the data that has arrived on it: nothing is written that was
  not sent on that connection, and nothing out of order.
*)
Theory asyncClosedLoop
Ancestors
  pair list rich_list arithmetic option pred_set string alist llist
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety asyncWorld
Libs
  BasicProvers

(* ------------------------------------------------------------------------
   Transcripts in the closed loop
   ------------------------------------------------------------------------ *)

Theorem zipr_NIL_responses:
  ∀as. zipr as [] = MAP (λa. (a, NONE)) as
Proof
  Induct >> simp[zipr_def]
QED

Theorem zipr_same_length:
  ∀as rs. LENGTH rs = LENGTH as ⇒
          zipr as rs = MAP (λ(a, r). (a, SOME r)) (ZIP (as, rs))
Proof
  Induct >> simp[zipr_def] >> rpt strip_tac >> Cases_on ‘rs’ >> gvs[]
QED

(* The transcript after one more snapshot: the last round's actions get
   their responses, and the new round's actions have none yet *)
Theorem trans_SNOC:
  trans m (h ++ [s]) =
    FLAT (GENLIST (round_trans m h) (LENGTH h)) ++
    zipr (new_actions (log_of m) h) s.results ++
    MAP (λa. (a, NONE)) (new_actions (log_of m) (h ++ [s]))
Proof
  simp[trans_def, GENLIST, SNOC_APPEND]
  >> ‘LENGTH h + 1 = SUC (LENGTH h)’ by simp[] >> pop_assum SUBST1_TAC
  >> REWRITE_TAC[GENLIST, SNOC_APPEND, FLAT_APPEND, FLAT, APPEND_NIL,
                 GSYM APPEND_ASSOC]
  >> ‘GENLIST (round_trans m (h ++ [s])) (LENGTH h) =
      GENLIST (round_trans m h) (LENGTH h)’
       by simp[GENLIST_FUN_EQ, round_trans_def, responses_at_def, TAKE_APPEND1,
               EL_APPEND1]
  >> simp[round_trans_def, responses_at_def, TAKE_LENGTH_TOO_LONG,
          zipr_NIL_responses, EL_LENGTH_APPEND_0, TAKE_LENGTH_APPEND]
QED

Theorem trans_without_last:
  trans m h =
    FLAT (GENLIST (round_trans m h) (LENGTH h)) ++
    MAP (λa. (a, NONE)) (new_actions (log_of m) h)
Proof
  simp[trans_def, GENLIST, SNOC_APPEND, round_trans_def, responses_at_def,
       TAKE_LENGTH_ID, zipr_NIL_responses]
QED

Theorem perform_all_length:
  ∀as w rs w'. perform_all as w = (rs, w') ⇒ LENGTH rs = LENGTH as
Proof
  Induct >> simp[perform_all_def] >> rpt gen_tac
  >> Cases_on ‘perform h w’ >> simp[]
  >> Cases_on ‘perform_all as r’ >> simp[] >> strip_tac >> gvs[]
  >> metis_tac[]
QED

Theorem closed_loop_SUC:
  closed_loop m w0 n = (h, w, perf) ∧
  perform_all (new_actions (log_of m) h) w = (rs, w1) ⇒
  closed_loop m w0 (SUC n) =
    (h ++ [snapshot_of (tick w1) (SUC n) rs], tick w1,
     perf ++ ZIP (new_actions (log_of m) h, rs))
Proof
  simp[closed_loop_def]
QED

(* MAIN: in the closed loop, the program's transcript is the log of the
   actions the world performed, with their responses, followed by the
   current round's actions, whose responses have not arrived yet *)
Theorem trans_closed_loop:
  ∀n h w perf.
    closed_loop m w0 n = (h, w, perf) ⇒
    trans m h = MAP (λ(a, r). (a, SOME r)) perf ++
                MAP (λa. (a, NONE)) (new_actions (log_of m) h) ∧
    LENGTH h = n
Proof
  Induct
  >- simp[closed_loop_def, trans_without_last]
  >> rpt gen_tac
  >> Cases_on ‘closed_loop m w0 n’ >> PairCases_on ‘r’
  >> rename1 ‘closed_loop m w0 n = (h0, w1, p0)’
  >> Cases_on ‘perform_all (new_actions (log_of m) h0) w1’
  >> simp[closed_loop_def] >> strip_tac
  >> first_x_assum (qspecl_then [‘h0’, ‘w1’, ‘p0’] mp_tac) >> simp[] >> strip_tac
  >> drule perform_all_length >> strip_tac
  >> gvs[]
  >> ‘FLAT (GENLIST (round_trans m h0) (LENGTH h0)) = MAP (λ(a, r). (a, SOME r)) p0’
       by (qpat_x_assum ‘trans m h0 = _’ mp_tac >> simp[trans_without_last])
  >> simp[trans_SNOC, snapshot_of_def, zipr_same_length]
QED

(* ------------------------------------------------------------------------
   The world invariant for the server's closed loop
   ------------------------------------------------------------------------ *)

(* The performed log as a transcript (every response present) *)
Definition sperf_def:
  sperf perf = MAP (λ(a, r). (a, SOME r)) perf
End

Theorem sperf_APPEND[simp]:
  sperf (p1 ++ p2) = sperf p1 ++ sperf p2 ∧ sperf [] = [] ∧
  sperf [(a, r)] = [(a, SOME r)]
Proof
  simp[sperf_def]
QED

(* The world is consistent with what the server has done:
   - one listener, whose pending connections and the accepted ones are
     distinct known connections;
   - every known connection has received exactly what the server read from
     it, followed by what is still unread; and holds exactly what the server
     wrote to it;
   - unknown connections have not been read or written. *)
Definition consistent_def:
  consistent lfd w perf ⇔
    (∃q. w.listeners = [(lfd, q)] ∧
         ALL_DISTINCT (accepted (sperf perf) ++ q) ∧
         ∀c. MEM c (accepted (sperf perf) ++ q) ⇒ is_conn w c) ∧
    (∀c cn. ALOOKUP w.conns c = SOME cn ⇒
            cn.received = FLAT (read c (sperf perf)) ++ cn.incoming ∧
            cn.outgoing = FLAT (written c (sperf perf))) ∧
    (∀c. ALOOKUP w.conns c = NONE ⇒
         read c (sperf perf) = [] ∧ written c (sperf perf) = [])
End

Theorem consistent_start:
  consistent lfd (start_world lfd sch) []
Proof
  simp[consistent_def, start_world_def]
QED

(* One action, by the server: writes only go to accepted connections *)
Theorem consistent_perform:
  consistent lfd w perf ∧
  (∀c d. a = Write c d ⇒ MEM c (accepted (sperf perf))) ∧
  perform a w = (r, w') ⇒
  consistent lfd w' (perf ++ [(a, r)])
Proof
  Cases_on ‘a’ >> simp[perform_def]
  (* Read c *)
  >- (rename1 ‘Read c’ >> strip_tac >> Cases_on ‘ALOOKUP w.conns c’ >> gvs[]
      >- (gvs[consistent_def, AllCaseEqs()] >> metis_tac[])
      >> rename1 ‘_ = SOME cn’ >> Cases_on ‘cn.incoming = ""’ >> gvs[]
      >- (Cases_on ‘cn.peer_closed’ >> gvs[consistent_def, AllCaseEqs()]
          >> metis_tac[])
      >> gvs[consistent_def, is_conn_def, AFUPDKEY_ALOOKUP, AllCaseEqs()]
      >> conj_tac >- metis_tac[]
      >> rw[] >> gvs[] >> res_tac >> gvs[])
  (* Write c d: c is an accepted, hence known, connection *)
  >- (strip_tac >> gvs[]
      >> rename1 ‘Write c d’
      >> ‘∃cn. ALOOKUP w.conns c = SOME cn’
           by (fs[consistent_def, is_conn_def] >> Cases_on ‘ALOOKUP w.conns c’
               >> gvs[] >> metis_tac[])
      >> gvs[consistent_def, is_conn_def, AFUPDKEY_ALOOKUP, AllCaseEqs()]
      >> conj_tac >- metis_tac[]
      >> rw[] >> gvs[] >> res_tac >> gvs[])
  (* Accept l *)
  >> strip_tac >> qpat_x_assum ‘consistent _ _ _’ mp_tac
  >> simp[consistent_def] >> strip_tac
  >> gvs[AllCaseEqs()]
  >- metis_tac[]
  >> qexists_tac ‘q'’ >> simp[AFUPDKEY_def, is_conn_def] >> fs[is_conn_def]
  >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> simp[] >> metis_tac[]
QED

Theorem consistent_perform_all:
  ∀acts w perf rs w'.
    consistent lfd w perf ∧
    (∀c d. MEM (Write c d) acts ⇒ MEM c (accepted (sperf perf))) ∧
    perform_all acts w = (rs, w') ⇒
    consistent lfd w' (perf ++ ZIP (acts, rs))
Proof
  Induct >> simp[perform_all_def] >> rpt gen_tac
  >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[]
  >> ‘consistent lfd w1 (perf ++ [(h, r)])’
       by (irule consistent_perform >> simp[] >> metis_tac[])
  >> first_x_assum drule >> disch_then (qspecl_then [‘rs'’, ‘w'’] mp_tac)
  >> simp[sperf_APPEND] >> impl_tac >- metis_tac[]
  >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND]
QED

Theorem consistent_deliver1:
  consistent lfd w perf ⇒ consistent lfd (deliver1 w a) perf
Proof
  Cases_on ‘a’ >> simp[deliver1_def]
  (* a new connection: it is fresh, so nothing has been read or written *)
  >- (rw[] >> gvs[consistent_def, is_listener_def, is_conn_def]
      >> simp[AFUPDKEY_def, ALL_DISTINCT_APPEND] >> rw[]
      >> gvs[empty_conn_def, ALL_DISTINCT_APPEND] >> metis_tac[])
  (* data arrives, or the peer closes *)
  >> rw[consistent_def, is_conn_def, AFUPDKEY_ALOOKUP]
  >> gvs[consistent_def, is_conn_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem consistent_sched[local]:
  consistent lfd (w with sched := x) perf ⇔ consistent lfd w perf
Proof
  simp[consistent_def, is_conn_def]
QED

Theorem consistent_tick:
  consistent lfd w perf ⇒ consistent lfd (tick w) perf
Proof
  rw[tick_def] >> CASE_TAC >> simp[deliver_def]
  >> ‘∀as w. consistent lfd w perf ⇒ consistent lfd (FOLDL deliver1 w as) perf’
       suffices_by (disch_then irule >> simp[consistent_sched])
  >> Induct >> simp[consistent_deliver1]
QED

Theorem accepted_pending[local]:
  ∀as. accepted (MAP (λa. (a, NONE)) as) = []
Proof
  Induct >> simp[] >> Cases >> simp[]
QED

Theorem read_pending[local]:
  ∀as. read c (MAP (λa. (a, NONE)) as) = []
Proof
  Induct >> simp[] >> Cases >> simp[]
QED

(* MAIN: the world stays consistent with what the server has done, in every
   round of the closed loop *)
Theorem closed_loop_consistent:
  ∀n h w perf.
    closed_loop (server lfd) (start_world lfd sch) n = (h, w, perf) ⇒
    consistent lfd w perf
Proof
  Induct >- simp[closed_loop_def, consistent_start]
  >> rpt gen_tac >> simp[closed_loop_def]
  >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[]
  >> irule consistent_tick >> irule consistent_perform_all >> simp[]
  >> reverse conj_tac >- metis_tac[]
  (* the server only writes to connections it has accepted *)
  >> rpt strip_tac
  >> drule (Q.GEN ‘m’ trans_closed_loop) >> strip_tac
  >> ‘fresh (trans (server lfd) h')’
       by gvs[fresh_def, accepted_pending, consistent_def, ALL_DISTINCT_APPEND,
              sperf_def]
  >> drule server_echoes >> strip_tac
  >> first_x_assum (qspec_then ‘c’ mp_tac)
  >> impl_tac
  >- (simp[EXISTS_MEM, MEM_MAP] >> qexists_tac ‘(Write c d, NONE)’
      >> simp[on_fd_def])
  >> simp[accepted_pending, sperf_def]
QED

(* MAIN: the closed loop's accounting, per connection.  Everything that has
   arrived on c is: what the server has written back, then what it has read
   and is writing back this round, then what it has not read yet. *)
Theorem closed_loop_accounting:
  closed_loop (server lfd) (start_world lfd sch) n = (h, w, perf) ∧
  ALOOKUP w.conns c = SOME cn ⇒
  cn.received =
    cn.outgoing ++
    FLAT (written c (MAP (λa. (a, NONE : response option))
                         (new_actions (log_of (server lfd)) h))) ++
    cn.incoming
Proof
  strip_tac
  >> drule closed_loop_consistent >> simp[consistent_def] >> strip_tac
  >> first_x_assum drule >> strip_tac >> simp[]
  >> drule (Q.GEN ‘m’ trans_closed_loop) >> strip_tac
  >> ‘fresh (trans (server lfd) h)’
       by gvs[fresh_def, accepted_pending, ALL_DISTINCT_APPEND, sperf_def]
  >> drule echo_server_safety >> disch_then (qspec_then ‘c’ mp_tac)
  >> simp[read_pending, GSYM sperf_def] >> strip_tac
  >> qpat_x_assum ‘_ ++ _ = read c _’ (SUBST1_TAC o GSYM) >> simp[]
QED

(* MAIN: safety in the closed loop.  On every connection, what the server
   has written is a prefix of what has arrived on it: nothing is written that
   was not sent on that connection, and nothing out of order. *)
Theorem closed_loop_safety:
  closed_loop (server lfd) (start_world lfd sch) n = (h, w, perf) ∧
  ALOOKUP w.conns c = SOME cn ⇒
  cn.outgoing ≼ cn.received
Proof
  strip_tac >> drule_all closed_loop_accounting >> simp[IS_PREFIX_APPEND]
QED
