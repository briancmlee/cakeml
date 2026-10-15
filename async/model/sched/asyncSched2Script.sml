(*
  M2 at Level 2: no busy-waiting.

  A blocking scheduler skips a round (it blocks, e.g. in select) when every
  task is idle: no task has a request in flight, and no unfinished task has
  a declared event that is ready.  The headline theorem: such a scheduler
  emits exactly the same actions, and its tasks finish with exactly the same
  results, as the scheduler that polls every task in every round.

  The proof: the pool of tasks is the Level 2 computation all2 cs, which is
  quiet because every combinator is (asyncLevel2).  Quietness says an
  irrelevant snapshot can be deleted from the history without changing
  anything; a blocking scheduler is one that deletes them, one at a time.
*)
Theory asyncSched2
Ancestors
  pair list rich_list arithmetic option pred_set
  asyncCore asyncLevel1 asyncChoose asyncLevel2 asyncLoop2 asyncSched
Libs
  BasicProvers

(* The tasks as one Level 2 computation *)
Definition all2_def:
  all2 [] = return2 [] ∧
  all2 (c :: cs) = map2 (λ(x, xs). x :: xs) (both2 c (all2 cs))
End

Theorem erase_all2:
  ∀cs. erase (all2 cs) = all (MAP erase cs)
Proof
  Induct >> simp[all2_def, all_def, erase_map2, erase_both2, erase_return2]
QED

Theorem all2_run:
  (all2 cs).run = all (MAP erase cs)
Proof
  metis_tac[erase_all2, erase_def]
QED

Theorem wf2_all2:
  ∀cs. EVERY wf2 cs ⇒ wf2 (all2 cs)
Proof
  Induct >> simp[all2_def, wf2_return2] >> rpt strip_tac
  >> gvs[wf2_def]
  >> conj_tac
  >- (simp[map2_def, both2_def] >> irule wf_map >> irule wf_both >> simp[])
  >> irule quiet_map2 >> irule quiet_both2 >> simp[]
QED

(* ------------------------------------------------------------------------
   Skipping irrelevant snapshots, in general
   ------------------------------------------------------------------------ *)

(* Snapshot s is irrelevant to c after h: c has no request in flight, s
   carries no responses, and (if c is still waiting) none of the events c
   waits for is ready in s *)
Definition irrelevant_def:
  irrelevant c h s ⇔
    new_actions (log_of c.run) h = [] ∧ s.results = [] ∧
    ((c.run h).result = NONE ⇒ DISJOINT (c.interest h) s.ready)
End

(* The snapshots a blocking scheduler acts on: those for which `skip` does
   not hold, judged on the snapshots kept so far *)
Definition blocked_def:
  blocked skip kept [] = kept ∧
  blocked skip kept (s :: rest) =
    blocked skip (if skip kept s then kept else kept ++ [s]) rest
End

(* full and kept are indistinguishable for c, now and later *)
Definition same_for_def:
  same_for c full kept ⇔
    (∀k. c.run (full ++ k) = c.run (kept ++ k) ∧
         ((c.run (full ++ k)).result = NONE ⇒
          c.interest (full ++ k) = c.interest (kept ++ k))) ∧
    new_actions (log_of c.run) full = new_actions (log_of c.run) kept
End

Theorem same_for_step:
  wf c.run ∧ quiet c ∧ (∀h s. skip h s ⇒ irrelevant c h s) ∧
  same_for c full kept ⇒
  same_for c (full ++ [s]) (if skip kept s then kept else kept ++ [s])
Proof
  strip_tac >> Cases_on ‘skip kept s’ >> simp[]
  >- (* s is skipped: delete it from full *)
     (‘new_actions (log_of c.run) kept = [] ∧ s.results = [] ∧
       ((c.run kept).result = NONE ⇒ DISJOINT (c.interest kept) s.ready)’
        by metis_tac[irrelevant_def]
      >> ‘c.run full = c.run kept ∧
          ((c.run full).result = NONE ⇒ c.interest full = c.interest kept) ∧
          new_actions (log_of c.run) full = []’
        by (fs[same_for_def] >> first_x_assum (qspec_then ‘[]’ mp_tac) >> simp[])
      (* by quietness (or, if c has finished, by well-formedness) *)
      >> ‘∀k. c.run (full ++ [s] ++ k) = c.run (full ++ k) ∧
              ((c.run full).result = NONE ⇒
               c.interest (full ++ [s] ++ k) = c.interest (full ++ k))’
        by (gen_tac >> Cases_on ‘(c.run full).result’
            >- (qpat_x_assum ‘quiet c’ mp_tac >> simp[quiet_def]
                >> disch_then (qspecl_then [‘full’, ‘s’, ‘k’] mp_tac) >> gvs[])
            >> simp[]
            >> ‘c.run (full ++ [s] ++ k) = c.run full ∧ c.run (full ++ k) = c.run full’
                 by (conj_tac >> irule wf_finished_stays >> simp[]
                     >> metis_tac[IS_PREFIX_APPEND3, APPEND_ASSOC])
            >> simp[])
      >> qpat_x_assum ‘same_for _ _ _’ (strip_assume_tac o REWRITE_RULE[same_for_def])
      >> simp[same_for_def] >> conj_tac
      >- (gen_tac
          >> qpat_x_assum ‘∀k. c.run (full ++ [s] ++ k) = _ ∧ _’
               (qspec_then ‘k’ strip_assume_tac)
          >> qpat_x_assum ‘∀k. c.run (full ++ k) = _ ∧ _’
               (qspec_then ‘k’ strip_assume_tac)
          >> simp[] >> strip_tac
          >> ‘(c.run full).result = NONE’
               by (irule wf_unfinished_before >> simp[]
                   >> qexists_tac ‘full ++ [s] ++ k’ >> simp[]
                   >> metis_tac[IS_PREFIX_APPEND3, APPEND_ASSOC])
          >> gvs[])
      >> qpat_x_assum ‘∀k. c.run (full ++ [s] ++ k) = _ ∧ _’ (qspec_then ‘[]’ mp_tac)
      >> simp[new_actions_SNOC, log_of_def, DROP_LENGTH_NIL])
  (* s is kept: both histories grow by s *)
  >> qpat_x_assum ‘same_for _ _ _’ (strip_assume_tac o REWRITE_RULE[same_for_def])
  >> simp[same_for_def] >> conj_tac
  >- (gen_tac >> first_x_assum (qspec_then ‘[s] ++ k’ mp_tac) >> simp[])
  >> simp[new_actions_SNOC, log_of_def]
  >> first_assum (qspec_then ‘[]’ mp_tac) >> first_x_assum (qspec_then ‘[s]’ mp_tac)
  >> simp[]
QED

(* MAIN: skipping irrelevant snapshots is sound.  If c is well-formed and
   quiet, then acting only on the snapshots a blocking scheduler keeps gives
   the same outcome as acting on all of them. *)
Theorem blocked_sound:
  wf c.run ∧ quiet c ∧ (∀h s. skip h s ⇒ irrelevant c h s) ⇒
  ∀H. c.run (blocked skip [] H) = c.run H
Proof
  strip_tac
  >> ‘∀H full kept. same_for c full kept ⇒
        c.run (blocked skip kept H) = c.run (full ++ H)’
       suffices_by (rpt strip_tac >> first_x_assum (qspecl_then [‘H’, ‘[]’, ‘[]’] mp_tac)
                    >> simp[same_for_def])
  >> Induct >> simp[blocked_def]
  >- (rw[same_for_def] >> first_x_assum (qspec_then ‘[]’ mp_tac) >> simp[])
  >> rpt strip_tac
  >> ‘full ++ h :: H = (full ++ [h]) ++ H’ by simp[]
  >> pop_assum SUBST1_TAC
  >> first_x_assum irule >> irule same_for_step >> simp[]
QED

(* ------------------------------------------------------------------------
   The blocking scheduler
   ------------------------------------------------------------------------ *)

(* A task is idle for snapshot s: it has no request in flight, and if it is
   still waiting, none of the events it waits for is ready in s *)
Definition idle_task_def:
  idle_task c t s ⇔
    in_flight t = [] ∧
    ((t.comp t.view).result = NONE ⇒ DISJOINT (c.interest t.view) s.ready)
End

(* The scheduler blocks through snapshot s when every task is idle and s
   carries no responses *)
Definition sched_idle_def:
  sched_idle cs h s ⇔
    s.results = [] ∧ LIST_REL (λc t. idle_task c t s) cs (run (MAP erase cs) h)
End

Theorem all2_interest_cons:
  (all2 (c :: cs)).interest h =
    waiting_on c (left_view c.run (all (MAP erase cs)) h) ∪
    waiting_on (all2 cs) (right_view c.run (all (MAP erase cs)) h)
Proof
  simp[all2_def, map2_def, both2_def, all2_run]
QED

Theorem idle_waiting_on:
  ∀cs h. LIST_REL (λc t. idle_task c t s) cs (run (MAP erase cs) h) ⇒
         DISJOINT (waiting_on (all2 cs) h) s.ready
Proof
  Induct >- simp[waiting_on_def, all2_def, return2_def, return_def]
  >> qx_genl_tac [‘c’, ‘h’] >> simp[run_cons, erase_def] >> strip_tac
  >> simp[waiting_on_def] >> rw[] >> simp[all2_interest_cons]
  >> fs[idle_task_def, waiting_on_def] >> rw[]
QED

Theorem sched_idle_irrelevant:
  sched_idle cs h s ⇒ irrelevant (all2 cs) h s
Proof
  rw[sched_idle_def, irrelevant_def]
  >- (simp[all2_run, GSYM round_actions_all, round_actions_def]
      >> simp[FLAT_EQ_NIL, EVERY_MAP]
      >> fs[LIST_REL_EL_EQN, EVERY_EL, idle_task_def])
  >> drule idle_waiting_on >> simp[waiting_on_def]
QED

(* MAIN: no busy-waiting.  A scheduler that blocks through every round in
   which all tasks are idle emits exactly the same actions, and its tasks
   finish with exactly the same results, as the scheduler that polls every
   task in every round. *)
Theorem no_busy_waiting:
  EVERY wf2 cs ⇒
  ∀H. let K = blocked (sched_idle cs) [] H in
      sched_log (MAP erase cs) K = sched_log (MAP erase cs) H ∧
      ∀xs. LIST_REL (λt x. (t.comp t.view).result = SOME x) (run (MAP erase cs) K) xs ⇔
           LIST_REL (λt x. (t.comp t.view).result = SOME x) (run (MAP erase cs) H) xs
Proof
  strip_tac >> gen_tac >> simp[]
  >> ‘EVERY wf (MAP erase cs)’ by fs[EVERY_MAP, EVERY_MEM, wf2_def, erase_def]
  >> drule wf2_all2 >> simp[wf2_def] >> strip_tac
  >> ‘(all2 cs).run (blocked (sched_idle cs) [] H) = (all2 cs).run H’
       by (irule blocked_sound >> simp[sched_idle_irrelevant])
  >> fs[all2_run, sched_log_all, GSYM all_result]
QED

(* MAIN: progress under blocking: the scheduler never blocks through a
   snapshot in which some waiting task has a declared event ready (or in
   which some task has a request in flight) *)
Theorem ready_task_polled:
  n < LENGTH cs ∧ t = EL n (run (MAP erase cs) h) ∧
  (in_flight t ≠ [] ∨
   (t.comp t.view).result = NONE ∧ ¬DISJOINT ((EL n cs).interest t.view) s.ready) ⇒
  ¬sched_idle cs h s
Proof
  rw[sched_idle_def, LIST_REL_EL_EQN]
  >> qexists_tac ‘n’ >> simp[idle_task_def]
  >> Cases_on ‘in_flight (EL n (run (MAP erase cs) h)) = []’ >> fs[]
QED
