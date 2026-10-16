(*
  What makes the echo server act (model): handler_cause, lifted through
  the server's both-composition.

  The server's actions change with a new snapshot s only if
  - the listener is readable in s, or
  - some fd is readable in s that the server has accepted more often
    than a read of it returned EOF (a connection whose handler still
    runs), or
  - s brings Data in response to a read.
  With the world static and nothing left to read, accept or answer
  (quiescence, design/33 §2.5), none of these can happen, so the server
  stops acting.

  MAIN: both_cause, server_cause.
*)
Theory asyncEchoServerCause
Ancestors
  pair list rich_list arithmetic option pred_set
  asyncCore asyncLevel1 asyncLoop asyncTranscript asyncServer
  asyncServerSafety asyncProgress asyncM4LiveServer asyncEchoCause
Libs
  preamble

(* Unchanged actions: no new actions *)
Theorem actions_same_new_actions:
  (m (h ++ [s])).actions = (m h).actions ⇒ new_actions (log_of m) (h ++ [s]) = []
Proof
  simp[new_actions_SNOC, log_of_def, DROP_LENGTH_NIL]
QED

(* MAIN: when two computations run side by side, the actions change with a
   new snapshot only if one side's change with its share of it *)
Theorem both_cause:
  (both m1 m2 (q ++ [s])).actions ≠ (both m1 m2 q).actions ⇒
  (m1 (left_view m1 m2 q ++
       [s with results :=
          TAKE (LENGTH (new_actions (log_of m1) (left_view m1 m2 q))) s.results])).actions ≠
  (m1 (left_view m1 m2 q)).actions ∨
  (m2 (right_view m1 m2 q ++
       [s with results :=
          DROP (LENGTH (new_actions (log_of m1) (left_view m1 m2 q))) s.results])).actions ≠
  (m2 (right_view m1 m2 q)).actions
Proof
  CCONTR_TAC >> gvs[] >>
  qpat_x_assum ‘_ ≠ _’ mp_tac >>
  simp[both_def, par_log_SNOC, left_view_SNOC_eq, right_view_SNOC_eq] >>
  drule actions_same_new_actions >> qpat_x_assum ‘_ = _’ mp_tac >>
  drule actions_same_new_actions >> simp[]
QED

Theorem server_NIL:
  (server lfd []).actions = []
Proof
  ONCE_REWRITE_TAC[server_steps] >> DEP_REWRITE_TAC[bind_running] >>
  simp[readable_def, wait_def, first_some_def]
QED

Theorem both_NIL:
  (both m1 m2 []).actions = (m1 []).actions ++ (m2 []).actions
Proof
  simp[both_def, par_log_def, par_actions_NIL, log_of_def]
QED

Theorem MEM_TAKE_DROP_oHD[local]:
  oHD (TAKE k l) = SOME x ∨ oHD (DROP k l) = SOME x ⇒ MEM x l
Proof
  ‘∀l'. oHD l' = SOME x ⇒ MEM x l'’ by (Cases >> simp[]) >>
  metis_tac[MEM_TAKE, MEM_DROP_IMP]
QED

(* A finished computation does not act any more *)
Theorem finished_same_actions:
  wf m ∧ (m h).result ≠ NONE ⇒ (m (h ++ [s])).actions = (m h).actions
Proof
  rpt strip_tac >> Cases_on ‘(m h).result’ >> gvs[] >>
  ‘m (h ++ [s]) = m h’ suffices_by simp[] >>
  irule wf_finished_stays >> simp[IS_PREFIX_APPEND]
QED

Theorem after_accept_NIL[local]:
  (after_accept lfd r []).actions = []
Proof
  Cases_on ‘r’ >> simp[after_accept_def, asyncLevel1Theory.map_def, both_NIL, handler_NIL, server_NIL]
QED

(* The accept and EOF counts of the server just after accepting fd0: a
   running handler for fd0 is a connection accepted and not yet EOF-read,
   and the rest of the server's open connections stay open *)
Theorem accept_counts[local]:
  ((handler fd0 (left_view (handler fd0) (server lfd) h)).result = NONE ⇒
   eofs fd0 (trans (both (handler fd0) (server lfd)) h) ≤
   accs fd0 (trans (both (handler fd0) (server lfd)) h)) ∧
  (eofs g (trans (server lfd) (right_view (handler fd0) (server lfd) h)) <
   accs g (trans (server lfd) (right_view (handler fd0) (server lfd) h)) ⇒
   eofs g (trans (both (handler fd0) (server lfd)) h) <
   accs g (trans (both (handler fd0) (server lfd)) h) + (if fd0 = g then 1 else 0))
Proof
  simp[trans_both_counts, handler_eofs] >>
  qspec_then ‘right_view (handler fd0) (server lfd) h’
    (assume_tac o CONJUNCT1) server_live >>
  rw[] >> gvs[handler_eofs] >> rw[] >> gvs[]
QED

(* MAIN: the server's actions change only for a reason in the new snapshot *)
Theorem server_cause:
  ∀q s. (server lfd (q ++ [s])).actions ≠ (server lfd q).actions ⇒
        Readable lfd ∈ s.ready ∨
        (∃fd. Readable fd ∈ s.ready ∧
              eofs fd (trans (server lfd) q) < accs fd (trans (server lfd) q)) ∨
        ∃d. MEM (Data d) s.results
Proof
  gen_tac >> completeInduct_on ‘LENGTH q’ >> rpt strip_tac >> gvs[PULL_FORALL] >>
  qspecl_then [‘readable lfd : (event, response) snapshot list ->
                               (action, unit option) outcome’, ‘q ++ [s]’]
    strip_assume_tac history_split
  (* still waiting for the listener after s: no actions either way *)
  >- (‘(server lfd (q ++ [s])).actions = [] ∧ (server lfd q).actions = []’
        by (ONCE_REWRITE_TAC[server_steps] >>
            ‘∀h. h ≼ q ++ [s] ⇒
                 (bind (readable lfd)
                    (λu. bind (emit (Accept lfd)) (after_accept lfd)) h).actions = []’
              by (rpt strip_tac >>
                  ‘bind (readable lfd) (λu. bind (emit (Accept lfd)) (after_accept lfd)) h =
                   <| actions := (readable lfd h).actions; result := NONE |>’
                    by (irule bind_running >> rpt strip_tac >>
                        gvs[IS_PREFIX_EQ_TAKE] >>
                        first_x_assum (qspec_then ‘MIN n n'’ mp_tac) >>
                        simp[TAKE_TAKE_MIN]) >>
                  simp[readable_def, wait_def]) >>
            simp[]) >>
      gvs[])
  >> ‘x = ()’ by simp[oneTheory.one] >> gvs[] >>
  ‘first_readable lfd h1’ by simp[first_readable_def] >>
  Cases_on ‘h2’ using SNOC_CASES
  (* the wait finished at s itself *)
  >- (disj1_tac >> gvs[] >> metis_tac[first_readable_last])
  >> ‘s = x ∧ q = h1 ++ l’
       by (‘SNOC s q = SNOC x (h1 ++ l)’ by gvs[SNOC_APPEND] >> fs[SNOC_11])
  >> gvs[] >> rename1 ‘h1 ++ q2’ >> drule server_accepts >> strip_tac >>
  Cases_on ‘q2’
  (* s brings the accept's response: still just the accept *)
  >- (gvs[] >> qpat_x_assum ‘_ ≠ _’ mp_tac >>
      first_assum (qspec_then ‘[s]’ SUBST1_TAC) >>
      first_assum (qspec_then ‘[]’ (SUBST1_TAC o REWRITE_RULE[APPEND_NIL])) >>
      simp[bind_emit_NIL] >>
      Cases_on ‘oHD (s : (event, response) snapshot).results’
      >- (‘(bind (emit (Accept lfd)) (after_accept lfd) [s]).actions = [Accept lfd]’
            by (irule bind_emit_unanswered >> simp[]) >> simp[]) >>
      rename1 ‘oHD s.results = SOME r’ >>
      qspecl_then [‘s’, ‘r’, ‘Accept lfd’, ‘after_accept lfd’, ‘[]’] mp_tac
        (Q.GENL [‘s’, ‘r’, ‘a’, ‘f’, ‘q’] bind_emit_CONS) >>
      simp[after_accept_NIL])
  >> rename1 ‘h1 ++ s1 :: q3’ >>
  qpat_x_assum ‘_ ≠ _’ (assume_tac o REWRITE_RULE[GSYM APPEND_ASSOC, APPEND]) >>
  Cases_on ‘oHD (s1 : (event, response) snapshot).results’
  (* the accept is unanswered *)
  >- (qpat_x_assum ‘_ ≠ _’ mp_tac >> ASM_REWRITE_TAC[] >>
      qspecl_then [‘s1’, ‘Accept lfd’, ‘after_accept lfd’, ‘q3’] mp_tac
        (Q.GENL [‘s’, ‘a’, ‘f’, ‘t’] bind_emit_unanswered) >>
      qspecl_then [‘s1’, ‘Accept lfd’, ‘after_accept lfd’, ‘q3 ++ [s]’] mp_tac
        (Q.GENL [‘s’, ‘a’, ‘f’, ‘t’] bind_emit_unanswered) >>
      simp[])
  (* after the accept's response r, in s1: as after_accept lfd r *)
  >> rename1 ‘oHD s1.results = SOME r’ >>
  ‘∀q. (server lfd (h1 ++ s1 :: q)).actions = Accept lfd :: (after_accept lfd r q).actions’
    by (ASM_REWRITE_TAC[] >> gen_tac >>
        qspecl_then [‘s1’, ‘r’, ‘Accept lfd’, ‘after_accept lfd’, ‘q’] mp_tac
          (Q.GENL [‘s’, ‘r’, ‘a’, ‘f’, ‘q’] bind_emit_CONS) >>
        simp[]) >>
  ‘trans (server lfd) (h1 ++ s1 :: q3) = (Accept lfd, SOME r) :: trans (after_accept lfd r) q3’
    by (drule_all server_trans_accept >>
        disch_then (qspec_then ‘q3’ (ACCEPT_TAC o REWRITE_RULE[GSYM APPEND_ASSOC, APPEND]))) >>
  qpat_x_assum ‘_ ≠ _’ mp_tac >>
  qpat_x_assum ‘∀q. (server _ _).actions = _’ (fn th => REWRITE_TAC[th]) >>
  qpat_x_assum ‘trans _ _ = _’ (fn th => REWRITE_TAC[th]) >>
  simp[is_acc_def, is_eof_def] >> strip_tac >>
  Cases_on ‘∃fd0. r = Accepted fd0’
  (* a new connection fd0: its handler, alongside the rest of the server *)
  >- (gvs[after_accept_def, asyncLevel1Theory.map_def] >> drule both_cause >> strip_tac
      >- (‘(handler fd0 (left_view (handler fd0) (server lfd) q3)).result = NONE’
            by metis_tac[finished_same_actions, wf_handler] >>
          drule handler_cause >> simp[] >> strip_tac
          >- (disj2_tac >> disj1_tac >> qexists_tac ‘fd0’ >> simp[] >>
              drule (CONJUNCT1 accept_counts) >> simp[])
          >> disj2_tac >> disj2_tac >> metis_tac[MEM_TAKE_DROP_oHD])
      >> qpat_x_assum ‘∀q s. _’
           (qspecl_then [‘right_view (handler fd0) (server lfd) q3’,
                         ‘s with results :=
                            DROP (LENGTH (new_actions (log_of (handler fd0))
                                            (left_view (handler fd0) (server lfd) q3)))
                                 s.results’] mp_tac) >>
      simp[] >> strip_tac >> simp[]
      >- (disj2_tac >> disj1_tac >> qexists_tac ‘fd’ >> simp[] >>
          drule (CONJUNCT2 accept_counts) >> rw[] >> simp[])
      >> metis_tac[MEM_DROP_IMP])
  (* otherwise the server again *)
  >> ‘after_accept lfd r = server lfd’ by (Cases_on ‘r’ >> gvs[after_accept_def]) >>
  gvs[] >> qpat_x_assum ‘∀q s. _’ (qspecl_then [‘q3’, ‘s’] mp_tac) >> simp[] >>
  rw[] >> gvs[] >> metis_tac[]
QED
