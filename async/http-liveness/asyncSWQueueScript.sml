(*
  Pending connections are accepted, for the generic server  server_with hf
  (any well-behaved handler, hok hf), in the closed loop.  These are
  asyncLiveness's proofs for the echo server (09), with server_with hf lfd
  replaced by server_with hf lfd and server_accept_progress by
  sw_accept_progress.  The main result: a connection with p connections
  ahead of it in the listener's queue is handed out within 3 (p + 1)
  rounds (sw_queue_progress), so a known connection is handed out by round
  n + 3 q (sw_handed_out_by).
*)
Theory asyncSWQueue
Ancestors
  pair list rich_list arithmetic option pred_set string alist
  asyncCore asyncLevel1 asyncLoop asyncTranscript asyncServer asyncServerSafety
  asyncProgress asyncWorld asyncClosedLoop asyncLiveness asyncServerWith
  asyncSWProgress asyncSWClosedLoop
Libs
  BasicProvers

Theorem sw_actions_SNOC[local]:
  hok hf ⇒
  (server_with hf lfd (h ++ [s])).actions =
  (server_with hf lfd h).actions ++ new_actions (log_of (server_with hf lfd)) (h ++ [s])
Proof
  strip_tac >>
  qspecl_then [‘log_of (server_with hf lfd)’, ‘h’, ‘s’] mp_tac
    (Q.GENL [‘acts’, ‘h’, ‘s’] new_actions_prefix) >>
  gs[log_of_def, wf_SNOC_actions, hok_wf_server_with]
QED

Theorem sw_MEM_accepted_prefix[local]:
  p ≼ p' ∧ MEM c (accepted (sperf p)) ⇒ MEM c (accepted (sperf p'))
Proof
  rw[IS_PREFIX_APPEND] >> simp[]
QED

(* In one round: the accepts take connections d from the front of the
   queue, which are handed out; new connections x join the back *)
Theorem sw_round_listener:
  closed_loop (server_with hf lfd) (start_world lfd sch) n = (h, w, perf) ∧
  closed_loop (server_with hf lfd) (start_world lfd sch) (n + 1) = (h', w', perf') ∧
  w.listeners = [(lfd, q)] ⇒
  ∃d q' x. w'.listeners = [(lfd, q' ++ x)] ∧ q = d ++ q' ∧
           accepted (sperf perf') = accepted (sperf perf) ++ d ∧
           (MEM (Accept lfd) (new_actions (log_of (server_with hf lfd)) h) ∧ q ≠ [] ⇒ d ≠ []) ∧
           (¬MEM (Accept lfd) (new_actions (log_of (server_with hf lfd)) h) ⇒ d = []) ∧
           ∀c. ALOOKUP w'.conns c ≠ NONE ⇒ ALOOKUP w.conns c ≠ NONE ∨ MEM c x
Proof
  strip_tac >> drule_all closed_loop_step >> strip_tac >> gvs[]
  >> drule_all perform_all_listener >> strip_tac
  >> drule tick_listener >> strip_tac
  >> qexistsl_tac [‘q'’, ‘x’] >> gvs[] >> metis_tac[]
QED

(* Every connection has been handed out, or is pending on the listener *)
Theorem sw_conns_known:
  ∀n h w perf.
    closed_loop (server_with hf lfd) (start_world lfd sch) n = (h, w, perf) ⇒
    ∃q. w.listeners = [(lfd, q)] ∧
        ∀c. ALOOKUP w.conns c ≠ NONE ⇒ MEM c (accepted (sperf perf)) ∨ MEM c q
Proof
  Induct >- simp[closed_loop_def, start_world_def]
  >> rpt strip_tac
  >> Cases_on ‘closed_loop (server_with hf lfd) (start_world lfd sch) n’ >> PairCases_on ‘r’
  >> first_x_assum (qspecl_then [‘q’, ‘r0’, ‘r1’] mp_tac) >> simp[] >> strip_tac
  >> qspecl_then [‘n’, ‘q’, ‘r0’, ‘r1’, ‘h’, ‘w’, ‘perf’, ‘q'’] mp_tac
       (Q.GENL [‘n’, ‘h’, ‘w’, ‘perf’, ‘h'’, ‘w'’, ‘perf'’, ‘q’] sw_round_listener)
  >> gvs[ADD1] >> strip_tac >> simp[] >> rpt strip_tac
  >> first_x_assum drule >> strip_tac >> gvs[]
  >> Cases_on ‘ALOOKUP r0.conns c = NONE’ >> gvs[] >> metis_tac[]
QED


(* While the server does not accept, the queue only grows *)
Theorem sw_quiet_listener:
  ∀d h' w' perf'.
    closed_loop (server_with hf lfd) (start_world lfd sch) n = (h, w, perf) ∧
    w.listeners = [(lfd, q)] ∧
    closed_loop (server_with hf lfd) (start_world lfd sch) (n + d) = (h', w', perf') ∧
    (∀i hi wi pi. i < d ∧
                  closed_loop (server_with hf lfd) (start_world lfd sch) (n + i) = (hi, wi, pi) ⇒
                  ¬MEM (Accept lfd) (new_actions (log_of (server_with hf lfd)) hi)) ⇒
    ∃y. w'.listeners = [(lfd, q ++ y)]
Proof
  Induct >- (rw[] >> gvs[])
  >> rpt strip_tac
  >> Cases_on ‘closed_loop (server_with hf lfd) (start_world lfd sch) (n + d)’
  >> PairCases_on ‘r’
  >> first_x_assum (qspecl_then [‘q'’, ‘r0’, ‘r1’] mp_tac) >> simp[]
  >> impl_tac
  >- (rpt strip_tac >> first_x_assum (qspecl_then [‘i’, ‘hi’, ‘wi’, ‘pi’] mp_tac)
      >> gvs[])
  >> strip_tac
  >> ‘¬MEM (Accept lfd) (new_actions (log_of (server_with hf lfd)) q')’
       by (first_x_assum (qspecl_then [‘d’, ‘q'’, ‘r0’, ‘r1’] mp_tac) >> simp[])
  >> qspecl_then [‘n + d’, ‘q'’, ‘r0’, ‘r1’, ‘h'’, ‘w'’, ‘perf'’, ‘q ++ y’] mp_tac
       (Q.GENL [‘n’, ‘h’, ‘w’, ‘perf’, ‘h'’, ‘w'’, ‘perf'’, ‘q’] sw_round_listener)
  >> gvs[ADD1] >> strip_tac >> gvs[]
QED

(* If the server accepts in none of the rounds n+1 .. n+d, its accepts
   stay the same *)
Theorem sw_naccepts_quiet:
  ∀d h' w' perf'.
    hok hf ∧ closed_loop (server_with hf lfd) (start_world lfd sch) n = (h, w, perf) ∧
    closed_loop (server_with hf lfd) (start_world lfd sch) (n + d) = (h', w', perf') ∧
    (∀i hi wi pi. 0 < i ∧ i ≤ d ∧
                  closed_loop (server_with hf lfd) (start_world lfd sch) (n + i) = (hi, wi, pi) ⇒
                  ¬MEM (Accept lfd) (new_actions (log_of (server_with hf lfd)) hi)) ⇒
    naccepts lfd (server_with hf lfd h').actions = naccepts lfd (server_with hf lfd h).actions
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
  >> ‘¬MEM (Accept lfd) (new_actions (log_of (server_with hf lfd)) h')’
       by (first_x_assum (qspecl_then [‘SUC d’, ‘h'’, ‘w'’, ‘perf'’] mp_tac) >> simp[])
  >> qspecl_then [‘server_with hf lfd’, ‘start_world lfd sch’, ‘n + d’, ‘q’, ‘r0’, ‘r1’,
                  ‘h'’, ‘w'’, ‘perf'’] mp_tac
       (Q.GENL [‘m’, ‘w0’, ‘n’, ‘h’, ‘w’, ‘perf’, ‘h'’, ‘w'’, ‘perf'’] closed_loop_step)
  >> gvs[ADD1] >> strip_tac >> gvs[sw_actions_SNOC]
  >> gvs[naccepts_def, count_def, FILTER_EQ_NIL, EVERY_MEM, FILTER_APPEND_DISTRIB]
  >> rw[] >> metis_tac[]
QED

(* With connections pending, the server accepts in one of the next three
   rounds (n .. n + 2), by sw_accept_progress *)
Theorem sw_accept_soon:
  hok hf ∧ closed_loop (server_with hf lfd) (start_world lfd sch) n = (h, w, perf) ∧
  w.listeners = [(lfd, q)] ∧ q ≠ [] ⇒
  ∃i hi wi pi. i ≤ 2 ∧
     closed_loop (server_with hf lfd) (start_world lfd sch) (n + i) = (hi, wi, pi) ∧
     MEM (Accept lfd) (new_actions (log_of (server_with hf lfd)) hi)
Proof
  rpt strip_tac >> CCONTR_TAC
  >> ‘∀i hi wi pi. i ≤ 2 ∧
        closed_loop (server_with hf lfd) (start_world lfd sch) (n + i) = (hi, wi, pi) ⇒
        ¬MEM (Accept lfd) (new_actions (log_of (server_with hf lfd)) hi)’ by metis_tac[]
  >> qpat_x_assum ‘¬∃i. _’ kall_tac
  >> Cases_on ‘closed_loop (server_with hf lfd) (start_world lfd sch) (n + 2)’
  >> PairCases_on ‘r’ >> rename1 ‘_ = (h2, w2, p2)’
  (* the listener stays readable *)
  >> ‘∀j. n ≤ j ∧ j < n + 2 ⇒ Readable lfd ∈ (EL j h2).ready’
       by (rpt strip_tac
           >> Cases_on ‘closed_loop (server_with hf lfd) (start_world lfd sch) (j + 1)’
           >> PairCases_on ‘r’
           >> qspecl_then [‘j + 1 − n’, ‘q'’, ‘r0’, ‘r1’] mp_tac sw_quiet_listener
           >> impl_tac
           >- (simp[] >> rpt strip_tac
               >> qpat_x_assum ‘∀i hi wi pi. _ ⇒ ¬MEM _ _’
                    (qspecl_then [‘i’, ‘hi’, ‘wi’, ‘pi’] mp_tac) >> simp[])
           >> strip_tac
           >> drule_all closed_loop_snapshot >> disch_then SUBST1_TAC
           >> irule listener_ready >> simp[])
  >> qpat_assum ‘closed_loop _ _ (n + 2) = _’ (assume_tac o MATCH_MP closed_loop_prompt)
  >> qpat_assum ‘closed_loop _ _ (n + 2) = _’ (assume_tac o MATCH_MP closed_loop_length)
  >> qspecl_then [‘server_with hf lfd’, ‘start_world lfd sch’, ‘n’, ‘2’, ‘h’, ‘w’, ‘perf’,
                  ‘h2’, ‘w2’, ‘p2’] mp_tac (Q.GENL [‘m’, ‘w0’, ‘n’] closed_loop_prefix)
  >> impl_tac >- gs[] >> strip_tac
  >> qspecl_then [‘h2’, ‘n’] mp_tac sw_accept_progress
  >> impl_tac >- gs[]
  >> simp[TAKE_LENGTH_ID_rwt] >> qpat_x_assum ‘h = TAKE _ _’ (SUBST1_TAC o GSYM)
  >> qspecl_then [‘2’, ‘h2’, ‘w2’, ‘p2’] mp_tac sw_naccepts_quiet
  >> impl_tac
  >- (gs[] >> rpt strip_tac
      >> qpat_x_assum ‘∀i hi wi pi. _ ⇒ ¬MEM _ _’
           (qspecl_then [‘i’, ‘hi’, ‘wi’, ‘pi’] mp_tac)
      >> simp[])
  >> simp[]
QED

(* A pending connection c, with pre ahead of it in the queue: after a round
   it has been handed out, or it has no more connections ahead of it (fewer,
   if the server accepted) *)
Theorem sw_round_queue:
  closed_loop (server_with hf lfd) (start_world lfd sch) n = (h, w, perf) ∧
  closed_loop (server_with hf lfd) (start_world lfd sch) (n + 1) = (h', w', perf') ∧
  w.listeners = [(lfd, pre ++ c :: post)] ⇒
  MEM c (accepted (sperf perf')) ∨
  ∃pre' post'. w'.listeners = [(lfd, pre' ++ c :: post')] ∧
               LENGTH pre' ≤ LENGTH pre ∧
               (MEM (Accept lfd) (new_actions (log_of (server_with hf lfd)) h) ⇒
                LENGTH pre' < LENGTH pre)
Proof
  strip_tac >> drule_all sw_round_listener >> strip_tac
  >> qpat_x_assum ‘_ = d ++ q'’ (strip_assume_tac o REWRITE_RULE[APPEND_EQ_APPEND])
  >> gvs[]
  >- (disj2_tac >> qexistsl_tac [‘l’, ‘post ++ x’] >> simp[]
      >> strip_tac >> gvs[] >> Cases_on ‘d’ >> gvs[])
  >> Cases_on ‘l’ >> gvs[]
  >> disj2_tac >> qexistsl_tac [‘[]’, ‘post ++ x’] >> simp[]
  >> strip_tac >> gvs[] >> Cases_on ‘pre’ >> gvs[]
QED

(* Connections handed out stay handed out *)
Theorem sw_accepted_later:
  closed_loop (server_with hf lfd) (start_world lfd sch) m = (h, w, perf) ∧
  closed_loop (server_with hf lfd) (start_world lfd sch) N = (h', w', perf') ∧
  m ≤ N ∧ MEM c (accepted (sperf perf)) ⇒
  MEM c (accepted (sperf perf'))
Proof
  strip_tac
  >> qspecl_then [‘server_with hf lfd’, ‘start_world lfd sch’, ‘m’, ‘N − m’, ‘h’, ‘w’, ‘perf’,
                  ‘h'’, ‘w'’, ‘perf'’] mp_tac (Q.GENL [‘m’, ‘w0’, ‘n’] closed_loop_prefix)
  >> simp[] >> metis_tac[sw_MEM_accepted_prefix]
QED

Theorem sw_queue_later:
  ∀d h' w' perf'.
    closed_loop (server_with hf lfd) (start_world lfd sch) n = (h, w, perf) ∧
    w.listeners = [(lfd, pre ++ c :: post)] ∧
    closed_loop (server_with hf lfd) (start_world lfd sch) (n + d) = (h', w', perf') ⇒
    MEM c (accepted (sperf perf')) ∨
    ∃pre' post'. w'.listeners = [(lfd, pre' ++ c :: post')] ∧ LENGTH pre' ≤ LENGTH pre
Proof
  Induct >- (rw[] >> gvs[] >> metis_tac[LESS_EQ_REFL])
  >> rpt strip_tac
  >> Cases_on ‘closed_loop (server_with hf lfd) (start_world lfd sch) (n + d)’
  >> PairCases_on ‘r’
  >> qpat_x_assum ‘∀h' w' perf'. _’ (qspecl_then [‘q’, ‘r0’, ‘r1’] mp_tac)
  >> simp[] >> strip_tac
  >- (disj1_tac
      >> qspecl_then [‘n + d’, ‘q’, ‘r0’, ‘r1’, ‘n + SUC d’, ‘h'’, ‘w'’, ‘perf'’] mp_tac
           (Q.GENL [‘m’, ‘h’, ‘w’, ‘perf’, ‘N’, ‘h'’, ‘w'’, ‘perf'’] sw_accepted_later)
      >> simp[])
  >> qspecl_then [‘n + d’, ‘q’, ‘r0’, ‘r1’, ‘h'’, ‘w'’, ‘perf'’, ‘pre'’, ‘post'’] mp_tac
       (Q.GENL [‘n’, ‘h’, ‘w’, ‘perf’, ‘h'’, ‘w'’, ‘perf'’, ‘pre’, ‘post’] sw_round_queue)
  >> gvs[ADD1] >> strip_tac >> simp[] >> metis_tac[LESS_EQ_TRANS]
QED

(* MAIN: pending connections are accepted.  A connection with p connections
   ahead of it in the listener's queue is handed out within 3 (p + 1)
   rounds. *)
Theorem sw_queue_progress:
  ∀p n h w perf pre post.
    hok hf ∧ closed_loop (server_with hf lfd) (start_world lfd sch) n = (h, w, perf) ∧
    w.listeners = [(lfd, pre ++ c :: post)] ∧ LENGTH pre ≤ p ⇒
    ∀N hN wN pN.
      n + 3 * (p + 1) ≤ N ∧
      closed_loop (server_with hf lfd) (start_world lfd sch) N = (hN, wN, pN) ⇒
      MEM c (accepted (sperf pN))
Proof
  completeInduct_on ‘p’ >> rpt strip_tac
  (* the server accepts in some round n + i, i ≤ 2 *)
  >> qspecl_then [‘n’, ‘h’, ‘w’, ‘perf’, ‘pre ++ c :: post’] mp_tac
       (Q.GENL [‘n’, ‘h’, ‘w’, ‘perf’, ‘q’] sw_accept_soon)
  >> simp[] >> strip_tac
  (* until then, c does not lose its place *)
  >> qspecl_then [‘i’, ‘hi’, ‘wi’, ‘pi’] mp_tac sw_queue_later
  >> impl_tac >- gs[] >> strip_tac
  >- (qspecl_then [‘n + i’, ‘hi’, ‘wi’, ‘pi’, ‘N’, ‘hN’, ‘wN’, ‘pN’] mp_tac
        (Q.GENL [‘m’, ‘h’, ‘w’, ‘perf’, ‘N’, ‘h'’, ‘w'’, ‘perf'’] sw_accepted_later)
      >> simp[])
  (* in round n + i it gets handed out, or moves up the queue *)
  >> Cases_on ‘closed_loop (server_with hf lfd) (start_world lfd sch) (n + i + 1)’
  >> PairCases_on ‘r’ >> rename1 ‘_ = (hj, wj, pj)’
  >> qspecl_then [‘n + i’, ‘hi’, ‘wi’, ‘pi’, ‘hj’, ‘wj’, ‘pj’, ‘pre'’, ‘post'’] mp_tac
       (Q.GENL [‘n’, ‘h’, ‘w’, ‘perf’, ‘h'’, ‘w'’, ‘perf'’, ‘pre’, ‘post’] sw_round_queue)
  >> simp[] >> strip_tac
  >- (qspecl_then [‘n + i + 1’, ‘hj’, ‘wj’, ‘pj’, ‘N’, ‘hN’, ‘wN’, ‘pN’] mp_tac
        (Q.GENL [‘m’, ‘h’, ‘w’, ‘perf’, ‘N’, ‘h'’, ‘w'’, ‘perf'’] sw_accepted_later)
      >> simp[])
  (* then by induction, with fewer connections ahead of it *)
  >> first_x_assum (qspec_then ‘p − 1’ mp_tac) >> simp[]
  >> disch_then (qspecl_then [‘n + i + 1’, ‘hj’, ‘wj’, ‘pj’, ‘pre''’, ‘post''’] mp_tac)
  >> impl_tac >- gs[]
  >> disch_then (qspecl_then [‘N’, ‘hN’, ‘wN’, ‘pN’] mp_tac) >> simp[]
QED

(* Every connection known at round n has been handed out by round n + 3 q *)
Theorem sw_handed_out_by:
  hok hf ∧ closed_loop (server_with hf lfd) (start_world lfd sch) n = (h, w, perf) ∧
  ALOOKUP w.conns c = SOME cn ∧ w.listeners = [(lfd, q)] ⇒
  ∃M hM wM pM. n ≤ M ∧ M ≤ n + 3 * LENGTH q ∧
     closed_loop (server_with hf lfd) (start_world lfd sch) M = (hM, wM, pM) ∧
     MEM c (accepted (sperf pM))
Proof
  strip_tac
  >> qpat_assum ‘closed_loop _ _ n = _’ (strip_assume_tac o MATCH_MP sw_conns_known)
  >> gvs[] >> first_x_assum (qspec_then ‘c’ mp_tac) >> simp[] >> strip_tac
  (* already handed out *)
  >- (qexistsl_tac [‘n’, ‘h’, ‘w’, ‘perf’] >> simp[])
  (* pending, with l1 ahead of it *)
  >> qpat_x_assum ‘MEM c q’ (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >> gvs[]
  >> Cases_on ‘closed_loop (server_with hf lfd) (start_world lfd sch) (n + 3 * (LENGTH l1 + 1))’
  >> PairCases_on ‘r’ >> rename1 ‘_ = (hM, wM, pM)’
  >> qexistsl_tac [‘n + 3 * (LENGTH l1 + 1)’, ‘hM’, ‘wM’, ‘pM’] >> simp[]
  >> qspecl_then [‘LENGTH l1’, ‘n’, ‘h’, ‘w’, ‘perf’, ‘l1’, ‘l2’] mp_tac sw_queue_progress
  >> impl_tac >- gs[]
  >> disch_then (qspecl_then [‘n + 3 * (LENGTH l1 + 1)’, ‘hM’, ‘wM’, ‘pM’] mp_tac)
  >> simp[]
QED

