(*
  M2: the scheduler, as a pure step function.

  A scheduler state is a list of tasks.  Each task is a computation together
  with its own view: the snapshots it has been shown, each carrying only the
  responses to that task's own actions.

  One round (step):
   - deliver the new snapshot to every task: the snapshot's responses are
     split among the tasks in pool order, each task getting as many as it
     has requests in flight (the actions it emitted in the previous round);
   - poll every task; the round's actions are the tasks' new actions, in
     pool order.

  Main results:
   - tasks are never lost (run_tasks);
   - every task is polled in every round and sees every snapshot's ready set
     and time (run_views_world);
   - composition: the scheduler running the tasks ms *is* the M1
     computation `all ms` (the tasks combined with both), both in the actions
     it emits (sched_log_all) and in the tasks' results (all_result).  So
     every M1 theorem applies to the whole system.

  Design decision (recorded for the user): the pool is fixed.  Dynamic
  spawning (a Spawn action carrying a computation) would need an action
  type that contains computations, i.e. a recursive type through a function
  space, which HOL's datatypes cannot express.  Fork/join inside a task is
  available through `both`.
*)
Theory asyncSched
Ancestors
  pair list rich_list arithmetic option asyncCore asyncLevel1 asyncChoose
Libs
  BasicProvers

Datatype:
  task = <| comp : ('e, 'r) snapshot list -> ('act, 'a option) outcome ;
            view : ('e, 'r) snapshot list |>
End

(* The actions a task emitted in its latest round: the requests whose
   responses are due in the next snapshot *)
Definition in_flight_def:
  in_flight t = new_actions (log_of t.comp) t.view
End

(* One round: deliver snapshot s, splitting its responses among the tasks
   in pool order *)
Definition step_def:
  step [] s = [] ∧
  step (t :: ts) s =
    let k = LENGTH (in_flight t) in
      (t with view := t.view ++ [s with results := TAKE k s.results]) ::
      step ts (s with results := DROP k s.results)
End

(* The actions the tasks emit in the round they have just been polled in,
   in pool order *)
Definition round_actions_def:
  round_actions ts = FLAT (MAP in_flight ts)
End

Definition start_def:
  start ms = MAP (λm. <| comp := m; view := [] |>) ms
End

(* One round of the scheduler: deliver s, poll, and append the round's
   actions to the log *)
Definition sched_round_def:
  sched_round (ts, log) s =
    let ts' = step ts s in (ts', log ++ round_actions ts')
End

(* The scheduler after the snapshots h: the tasks, and everything emitted so
   far (round 0's actions, then each later round's) *)
Definition sched_def:
  sched ms h = FOLDL sched_round (start ms, round_actions (start ms)) h
End

Definition run_def:
  run ms h = FST (sched ms h)
End

Definition sched_log_def:
  sched_log ms h = SND (sched ms h)
End

(* The tasks as one M1 computation: all of them side by side, with the list
   of their results *)
Definition all_def:
  all [] = return [] ∧
  all (m :: ms) = map (λ(x, xs). x :: xs) (both m (all ms))
End

(* ------------------------------------------------------------------------
   The scheduler, round by round
   ------------------------------------------------------------------------ *)

Theorem run_NIL[simp]:
  run ms [] = start ms
Proof
  simp[run_def, sched_def]
QED

Theorem sched_SNOC[local]:
  sched ms (h ++ [s]) = sched_round (sched ms h) s
Proof
  simp[sched_def, FOLDL_APPEND]
QED

Theorem run_SNOC:
  run ms (h ++ [s]) = step (run ms h) s
Proof
  simp[run_def, sched_SNOC] >> Cases_on ‘sched ms h’ >> simp[sched_round_def]
QED

Theorem sched_log_NIL:
  sched_log ms [] = round_actions (start ms)
Proof
  simp[sched_log_def, sched_def]
QED

Theorem sched_log_SNOC:
  sched_log ms (h ++ [s]) = sched_log ms h ++ round_actions (run ms (h ++ [s]))
Proof
  simp[sched_log_def, run_def, sched_SNOC]
  >> Cases_on ‘sched ms h’ >> simp[sched_round_def]
QED

(* The key lemma: the first task's view is its left view in `both`, and the
   other tasks are scheduled on the right view, exactly as `both` routes
   responses *)
Theorem run_cons:
  ∀h. run (m :: ms) h =
        <| comp := m; view := left_view m (all ms) h |> ::
        run ms (right_view m (all ms) h)
Proof
  Induct_on ‘h’ using SNOC_INDUCT
  >- simp[start_def]
  >> simp[SNOC_APPEND, run_SNOC, step_def, in_flight_def,
          left_view_SNOC_eq, right_view_SNOC_eq]
QED

Theorem run_no_tasks[simp]:
  ∀h. run [] h = []
Proof
  Induct_on ‘h’ using SNOC_INDUCT >> simp[start_def, SNOC_APPEND, run_SNOC, step_def]
QED

(* MAIN: tasks are never lost: the scheduler keeps every task, in order *)
Theorem run_tasks:
  ∀ms h. MAP (λt. t.comp) (run ms h) = ms
Proof
  Induct >> simp[start_def, run_cons]
QED

Theorem LENGTH_run[simp]:
  LENGTH (run ms h) = LENGTH ms
Proof
  metis_tac[run_tasks, LENGTH_MAP]
QED

(* MAIN: fairness and progress: every task is polled in every round, and
   sees every snapshot's ready set and time *)
Theorem run_views_world:
  ∀ms h. EVERY (λt. MAP (λs. (s.ready, s.now)) t.view = MAP (λs. (s.ready, s.now)) h)
               (run ms h)
Proof
  Induct >> simp[start_def, run_cons, both_views_world]
  >> qx_genl_tac [‘m’, ‘h’]
  >> first_x_assum (qspec_then ‘right_view m (all ms) h’ mp_tac)
  >> simp[both_views_world]
QED

(* ------------------------------------------------------------------------
   Composition: the scheduler is the M1 computation `all ms`
   ------------------------------------------------------------------------ *)

Theorem log_of_all_cons:
  log_of (all (m :: ms)) = log_of (both m (all ms))
Proof
  simp[all_def]
QED

(* Each round, the scheduler emits what `all ms` emits *)
Theorem round_actions_all:
  ∀ms h. round_actions (run ms h) = new_actions (log_of (all ms)) h
Proof
  Induct
  >- (simp[round_actions_def, start_def, all_def]
      >> Cases_on ‘h’ using SNOC_CASES
      >> simp[SNOC_APPEND, new_actions_NIL, new_actions_SNOC, log_of_def, return_def])
  >> qx_genl_tac [‘m’, ‘h’]
  >> simp[run_cons, round_actions_def, in_flight_def, log_of_all_cons]
  >> first_x_assum (qspec_then ‘right_view m (all ms) h’ mp_tac)
  >> simp[round_actions_def] >> disch_then kall_tac
  >> Cases_on ‘h’ using SNOC_CASES
  >- simp[new_actions_NIL, log_of_def, both_def, par_log_def, par_actions_NIL,
          left_view_def, right_view_def]
  >> simp[SNOC_APPEND, both_new_actions]
QED

Theorem wf_all:
  ∀ms. EVERY wf ms ⇒ wf (all ms)
Proof
  Induct >> simp[all_def, wf_return] >> rpt strip_tac
  >> irule wf_map >> irule wf_both >> simp[]
QED

(* MAIN: composition, actions: everything the scheduler emits is exactly
   the action log of the M1 computation `all ms` *)
Theorem sched_log_all:
  EVERY wf ms ⇒ ∀h. sched_log ms h = (all ms h).actions
Proof
  strip_tac >> drule wf_all >> strip_tac
  >> Induct_on ‘h’ using SNOC_INDUCT
  >- (qspecl_then [‘ms’, ‘[]’] mp_tac round_actions_all
      >> simp[sched_log_NIL, new_actions_NIL, log_of_def])
  >> simp[SNOC_APPEND, sched_log_SNOC, round_actions_all] >> rpt strip_tac
  >> qspecl_then [‘log_of (all ms)’, ‘h’, ‘x’] mp_tac
       (Q.GENL [‘acts’, ‘h’, ‘s’] new_actions_prefix)
  >> simp[log_of_def, wf_SNOC_actions]
QED

(* MAIN: composition, results: `all ms` has finished with the list xs exactly
   when every task has finished on its view, with the corresponding element
   of xs *)
Theorem all_result:
  ∀ms h xs. (all ms h).result = SOME xs ⇔
            LIST_REL (λt x. (t.comp t.view).result = SOME x) (run ms h) xs
Proof
  Induct >> simp[all_def, return_def, start_def]
  >> qx_genl_tac [‘m’, ‘h’, ‘xs’] >> simp[map_def, run_cons]
  >> eq_tac >> rw[]
  >- (PairCases_on ‘z’ >> gvs[both_result])
  >> qexists_tac ‘(x, ys)’ >> simp[both_result]
QED

(* Sanity check: two tasks each emit a request in round 0; the next
   snapshot's responses are split between them in pool order *)
Theorem example_sched_routing:
  let H = [<| ready := ({} : num set); now := 0; results := [1; 2 : num] |>] in
    sched_log [emit (10 : num); emit 20] H = [10; 20] ∧
    MAP (λt. (t.comp t.view).result) (run [emit (10 : num); emit 20] H) =
      [SOME 1; SOME 2]
Proof
  EVAL_TAC
QED
