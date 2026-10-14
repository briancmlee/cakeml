(*
  choose, in the style of OCaml's Async: nothing is lost.

  choose m1 m2 runs m1 and m2 side by side until one of them finishes.  It
  returns the winner's result together with the loser, *still running*, as
  a computation the caller can continue (or drop):

     choose m1 m2 : (('a × 'b computation) + ('a computation × 'b)) computation

  Ties go to m1.  There is no implicit cancellation, and no response is
  lost: the loser is returned *suspended*, i.e. with every response to its
  earlier actions already delivered to it, and its next poll still to come.
  Whoever holds the loser makes that poll, whenever they like.

  The responses to the actions a computation emits in round n arrive in
  snapshot n+1, so a value created in round n cannot contain them.  Hence:
   - if m1 wins in round n, m2 is not polled in round n.  The loser is m2
     with snapshot n delivered but not yet polled;
   - if m2 wins in round n, m1 has already been polled in round n.  If that
     poll emitted nothing, the loser is m1 as it is (its poll in round n
     emitted nothing, so it does not matter whether we count that poll as
     done or still to come).  Otherwise choose waits one more round for the
     responses and returns m1 with them delivered.
*)
Theory asyncChoose
Ancestors
  pair list rich_list arithmetic option sum asyncCore asyncLevel1
Libs
  BasicProvers

(* ------------------------------------------------------------------------
   The rest of a computation
   ------------------------------------------------------------------------ *)

(* resume m p: the rest of m after it has been polled with p (and with every
   prefix of p).  It shows m the history p ++ h, and reports only the actions
   m emits after p. *)
Definition resume_def:
  resume m p h =
    <| actions := DROP (LENGTH (m p).actions) (m (p ++ h)).actions;
       result := (m (p ++ h)).result |>
End

(* suspended m r: the rest of m after it has been polled with every proper
   prefix of r, when the last snapshot of r has been delivered but m has not
   been polled with it yet.  Its first poll is m's poll with r. *)
Definition suspended_def:
  suspended m r =
    if r = [] then m else (λh. resume m (FRONT r) (LAST r :: h))
End

(* ------------------------------------------------------------------------
   choose
   ------------------------------------------------------------------------ *)

(* One of the two sides has finished, on what it has been shown so far *)
Definition either_done_def:
  either_done m1 m2 p ⇔
    (m1 (left_view m1 m2 p)).result ≠ NONE ∨
    (m2 (right_view m1 m2 p)).result ≠ NONE
End

(* The log of m1 and m2 side by side, before the last round of p *)
Definition log_before_def:
  log_before m1 m2 p = if p = [] then [] else par_log m1 m2 (FRONT p)
End

(* choose m1 m2: see the comment at the top of the file.  n is the first
   round in which a side has finished; p the history up to it; l and r what
   the two sides have been shown. *)
Definition choose_def:
  choose m1 m2 h =
    case first_prefix (either_done m1 m2) h of
      NONE => <| actions := par_log m1 m2 h; result := NONE |>
    | SOME n =>
        let p = TAKE n h;
            l = left_view m1 m2 p;
            r = right_view m1 m2 p
        in
          case (m1 l).result of
            SOME x =>
              (* m1 wins; m2 is not polled in this round *)
              <| actions := log_before m1 m2 p ++ new_actions (log_of m1) l;
                 result := SOME (INL (x, suspended m2 r)) |>
          | NONE =>
              (* m2 wins; m1 has been polled in this round *)
              let y = THE (m2 r).result in
              if new_actions (log_of m1) l = [] then
                <| actions := par_log m1 m2 p;
                   result := SOME (INR (suspended m1 l, y)) |>
              else if LENGTH h = n then
                (* m1 has requests in flight: wait for their responses *)
                <| actions := par_log m1 m2 p; result := NONE |>
              else
                <| actions := par_log m1 m2 p;
                   result :=
                     SOME (INR (suspended m1 (left_view m1 m2 (TAKE (n + 1) h)),
                                y)) |>
End

(* A computation that emits A in its first round and has already finished
   with x.  For example, return x = finished [] x. *)
Definition finished_def:
  finished A x h = <| actions := A; result := SOME x |>
End

(* ------------------------------------------------------------------------
   resume and suspended
   ------------------------------------------------------------------------ *)

Theorem DROP_prefix[local]:
  l1 ≼ l2 ⇒ DROP n l1 ≼ DROP n l2
Proof
  rw[IS_PREFIX_APPEND] >> simp[DROP_APPEND]
QED

Theorem APPEND_SNOC_CONS[local]:
  l ++ [x] ++ h = l ++ x :: h
Proof
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND]
QED

Theorem FRONT_SNOC'[local]:
  FRONT (p ++ [s]) = p
Proof
  simp[FRONT_APPEND]
QED

Theorem DROP_DROP_LENGTH[local]:
  n ≤ LENGTH a ⇒ DROP (LENGTH (DROP n a)) (DROP n b) = DROP (LENGTH a) b
Proof
  simp[DROP_DROP_T, LENGTH_DROP]
QED

Theorem resume_result[simp]:
  (resume m p h).result = (m (p ++ h)).result
Proof
  simp[resume_def]
QED

(* MAIN: the rest of a well-formed computation is well-formed *)
Theorem wf_resume:
  wf m ⇒ wf (resume m p)
Proof
  rw[wf_def, resume_def]
  >- (irule DROP_prefix >> metis_tac[APPEND_ASSOC])
  >> metis_tac[APPEND_ASSOC]
QED

(* MAIN: resuming twice is resuming once, after both prefixes *)
Theorem resume_resume:
  wf m ⇒ resume (resume m p) q = resume m (p ++ q)
Proof
  rw[FUN_EQ_THM, resume_def, DROP_DROP_T]
  >> ‘(m p).actions ≼ (m (p ++ q)).actions’
       by (irule wf_actions_grow >> simp[])
  >> imp_res_tac IS_PREFIX_LENGTH
  >> simp[]
QED

(* MAIN: the rest of a computation that has finished is return *)
Theorem resume_finished:
  wf m ∧ (m p).result = SOME x ⇒ resume m p = return x
Proof
  rw[FUN_EQ_THM, resume_def, return_def] >> rename1 ‘m (p ++ h)’
  >> ‘m (p ++ h) = m p’ by (irule wf_finished_stays >> simp[])
  >> simp[DROP_LENGTH_NIL]
QED

Theorem suspended_NIL[simp]:
  suspended m [] = m
Proof
  simp[suspended_def]
QED

Theorem suspended_SNOC:
  suspended m (p ++ [s]) h = resume m p (s :: h)
Proof
  simp[suspended_def, FRONT_APPEND, LAST_APPEND_CONS]
QED

(* The suspended computation shows m the history r ++ h *)
Theorem suspended_result[simp]:
  (suspended m r h).result = (m (r ++ h)).result
Proof
  Cases_on ‘r’ using SNOC_CASES >> simp[suspended_SNOC, SNOC_APPEND, APPEND_SNOC_CONS]
QED

Theorem suspended_actions:
  (suspended m r h).actions =
    DROP (if r = [] then 0 else LENGTH (m (FRONT r)).actions) (m (r ++ h)).actions
Proof
  Cases_on ‘r’ using SNOC_CASES
  >> simp[suspended_SNOC, SNOC_APPEND, resume_def, FRONT_APPEND]
QED

Theorem wf_suspended:
  wf m ⇒ wf (suspended m r)
Proof
  strip_tac
  >> simp[wf_def, outcome_component_equality, suspended_actions]
  >> rpt gen_tac >> conj_tac
  >- (irule DROP_prefix >> metis_tac[wf_SNOC_actions, APPEND_ASSOC])
  >> strip_tac
  >> ‘m (r ++ h ++ [s]) = m (r ++ h)’ by metis_tac[wf_SNOC_finished]
  >> simp[]
QED

(* The suspended computation's new actions in each round are m's *)
Theorem new_actions_suspended:
  wf m ⇒ new_actions (log_of (suspended m r)) h = new_actions (log_of m) (r ++ h)
Proof
  strip_tac >> Cases_on ‘r’ using SNOC_CASES >- simp[]
  >> REWRITE_TAC[SNOC_APPEND] >> rename1 ‘p ++ [s]’
  >> Cases_on ‘h’ using SNOC_CASES
  >- simp[new_actions_NIL, log_of_def, suspended_actions, FRONT_APPEND,
          new_actions_SNOC]
  >> REWRITE_TAC[SNOC_APPEND]
  >> ‘p ++ [s] ++ (l ++ [x]) = (p ++ [s] ++ l) ++ [x]’ by REWRITE_TAC[APPEND_ASSOC]
  >> pop_assum SUBST1_TAC
  >> REWRITE_TAC[new_actions_SNOC, log_of_def, suspended_actions]
  >> REWRITE_TAC[APPEND_NIL, NOT_CONS_NIL, APPEND_eq_NIL, FRONT_SNOC',
                 APPEND_ASSOC]
  >> irule DROP_DROP_LENGTH
  >> irule IS_PREFIX_LENGTH
  >> irule wf_actions_grow >> simp[]
  >> REWRITE_TAC[GSYM APPEND_ASSOC, IS_PREFIX_APPEND3]
QED

(* The first poll of a suspended computation is m's poll with r *)
Theorem suspended_first_poll:
  wf m ⇒ (suspended m r []).actions = new_actions (log_of m) r
Proof
  strip_tac >> drule_then (qspecl_then [‘r’, ‘[]’] mp_tac) new_actions_suspended
  >> simp[new_actions_NIL, log_of_def]
QED

Theorem settled_resume:
  wf m ∧ settled m ⇒ settled (resume m p)
Proof
  rw[settled_def] >> Cases_on ‘h’ using SNOC_CASES
  >- simp[new_actions_NIL, log_of_def, resume_def, DROP_LENGTH_NIL]
  >> fs[SNOC_APPEND]
  >> ‘LENGTH (m (p ++ l ++ [x])).actions ≤ LENGTH (m (p ++ l)).actions’
       by (first_x_assum (qspec_then ‘p ++ l ++ [x]’ mp_tac)
           >> simp[new_actions_SNOC, log_of_def])
  >> ‘LENGTH (m p).actions ≤ LENGTH (m (p ++ l)).actions’
       by (irule IS_PREFIX_LENGTH >> irule wf_actions_grow >> simp[])
  >> simp[new_actions_SNOC, log_of_def, resume_def]
QED

Theorem settled_suspended:
  wf m ∧ settled m ⇒ settled (suspended m r)
Proof
  rw[settled_def, new_actions_suspended]
QED

(* A finished computation, once suspended, just reports what it emitted in
   its last poll *)
Theorem suspended_finished:
  wf m ∧ (m r).result = SOME x ⇒
  suspended m r = finished (new_actions (log_of m) r) x
Proof
  strip_tac
  >> ‘∀h. m (r ++ h) = m r’ by (rw[] >> irule wf_finished_stays >> simp[])
  >> rw[FUN_EQ_THM, finished_def, outcome_component_equality, suspended_actions]
  >> gvs[new_actions_def, log_of_def]
QED

Theorem return_finished:
  return x = finished [] x
Proof
  simp[FUN_EQ_THM, return_def, finished_def]
QED

(* ------------------------------------------------------------------------
   Splitting `both` at a point in the history
   ------------------------------------------------------------------------ *)

(* The log of both, split into the rounds before the last one and the last *)
Theorem par_log_log_before:
  par_log m1 m2 p =
    log_before m1 m2 p ++
    new_actions (log_of m1) (left_view m1 m2 p) ++
    new_actions (log_of m2) (right_view m1 m2 p)
Proof
  Cases_on ‘p’ using SNOC_CASES
  >- simp[log_before_def, par_log_def, par_actions_NIL, new_actions_NIL, log_of_def]
  >> simp[log_before_def, SNOC_APPEND, FRONT_SNOC', par_log_SNOC]
QED

(* Running m1 and m2 side by side on p ++ q is the same as running them on
   p, and then running the rest of each of them (suspended after p) side by
   side on q. *)
Theorem views_split:
  wf m1 ⇒
  ∀q. left_view m1 m2 (p ++ q) =
        left_view m1 m2 p ++
        left_view (suspended m1 (left_view m1 m2 p))
                  (suspended m2 (right_view m1 m2 p)) q ∧
      right_view m1 m2 (p ++ q) =
        right_view m1 m2 p ++
        right_view (suspended m1 (left_view m1 m2 p))
                   (suspended m2 (right_view m1 m2 p)) q
Proof
  strip_tac >> Induct_on ‘q’ using SNOC_INDUCT >> simp[SNOC_APPEND]
  >> rpt gen_tac >> strip_tac
  >> ‘p ++ (q ++ [x]) = (p ++ q) ++ [x]’ by simp[]
  >> pop_assum SUBST1_TAC
  >> simp[left_view_SNOC_eq, right_view_SNOC_eq, new_actions_suspended]
QED

Theorem par_log_split:
  wf m1 ∧ wf m2 ⇒
  ∀q. par_log m1 m2 (p ++ q) =
        log_before m1 m2 p ++
        par_log (suspended m1 (left_view m1 m2 p))
                (suspended m2 (right_view m1 m2 p)) q
Proof
  strip_tac >> Induct_on ‘q’ using SNOC_INDUCT
  >- (simp[Once par_log_log_before]
      >> simp[par_log_def, par_actions_NIL, log_of_def, suspended_first_poll])
  >> simp[SNOC_APPEND] >> rpt strip_tac
  >> ‘p ++ (q ++ [x]) = (p ++ q) ++ [x]’ by simp[]
  >> pop_assum SUBST1_TAC
  >> simp[par_log_SNOC, new_actions_suspended]
  >> qspecl_then [‘m1’, ‘m2’, ‘p’] mp_tac (Q.GENL [‘m1’, ‘m2’, ‘p’] views_split)
  >> impl_tac >- simp[]
  >> disch_then (qspec_then ‘q ++ [x]’ strip_assume_tac) >> fs[]
QED

(* MAIN: both m1 m2 can be split at any point p of the history *)
Theorem both_split:
  wf m1 ∧ wf m2 ⇒
  both m1 m2 (p ++ q) =
    let rest = both (suspended m1 (left_view m1 m2 p))
                    (suspended m2 (right_view m1 m2 p)) q
    in <| actions := log_before m1 m2 p ++ rest.actions;
          result := rest.result |>
Proof
  strip_tac
  >> qspecl_then [‘m1’, ‘m2’, ‘p’] mp_tac (Q.GENL [‘m1’, ‘m2’, ‘p’] views_split)
  >> impl_tac >- simp[]
  >> disch_then (qspec_then ‘q’ strip_assume_tac)
  >> simp[both_def, par_log_split, GSYM par_log_def]
QED

(* ------------------------------------------------------------------------
   both, when one side has already finished
   ------------------------------------------------------------------------ *)

Theorem new_actions_finished:
  new_actions (log_of (finished A x)) h = if h = [] then A else []
Proof
  rw[new_actions_def, log_of_def, finished_def, DROP_LENGTH_NIL]
QED

Theorem snapshot_results_id[local,simp]:
  s with results := s.results = s
Proof
  simp[snapshot_component_equality]
QED

Theorem right_view_finished:
  ∀q. right_view (finished A x) c q = skip_results (LENGTH A) q
Proof
  Induct_on ‘q’ using SNOC_INDUCT
  >- simp[skip_results_def]
  >> simp[SNOC_APPEND, right_view_SNOC_eq, new_actions_finished]
  >> rpt strip_tac
  >> Cases_on ‘q = []’ >> simp[skip_results_def, skip_results_APPEND]
QED

Theorem right_view_return:
  right_view (return x) c q = q
Proof
  simp[return_finished, right_view_finished]
QED

Theorem par_log_finished:
  ∀q. par_log (finished A x) c q =
        A ++ par_log (return x) c (skip_results (LENGTH A) q)
Proof
  Induct_on ‘q’ using SNOC_INDUCT
  >- simp[par_log_def, par_actions_NIL, skip_results_def, log_of_def,
          finished_def, return_def]
  >> simp[SNOC_APPEND] >> rpt strip_tac
  >> ‘∃s'. skip_results (LENGTH A) (q ++ [x']) = skip_results (LENGTH A) q ++ [s']’
       by simp[skip_results_SNOC]
  >> simp[par_log_SNOC, new_actions_finished]
  >> qpat_x_assum ‘skip_results _ _ = _’ (SUBST1_TAC o GSYM)
  >> simp[right_view_finished, right_view_return, return_finished,
          new_actions_finished]
QED

(* A finished left side: its last actions come first, and their responses
   are skipped *)
Theorem both_finished_left:
  both (finished A x) c q =
    let rest = both (return x) c (skip_results (LENGTH A) q) in
      <| actions := A ++ rest.actions; result := rest.result |>
Proof
  simp[both_def, GSYM par_log_def, par_log_finished]
  >> simp[right_view_finished, right_view_return]
  >> simp[finished_def, return_def]
QED

(* The left view only depends on the left side *)
Theorem left_view_right_irrelevant:
  ∀q. left_view m1 m2 q = left_view m1 m2' q
Proof
  Induct_on ‘q’ using SNOC_INDUCT >> simp[SNOC_APPEND, left_view_SNOC_eq]
QED

(* If the left side emits nothing in its first round, the results of the
   first snapshot do not matter to it *)
Theorem left_view_skip:
  (c []).actions = [] ⇒
  ∀q. left_view c m2 (skip_results k q) = left_view c m2 q
Proof
  strip_tac >> Induct_on ‘q’ using SNOC_INDUCT >- simp[skip_results_def]
  >> simp[SNOC_APPEND] >> rpt strip_tac
  >> Cases_on ‘q = []’
  >- simp[skip_results_def, left_view_SNOC_eq |> Q.INST [‘h’ |-> ‘[]’]
                                              |> SIMP_RULE (srw_ss()) [],
          new_actions_NIL, log_of_def]
  >> simp[skip_results_APPEND, left_view_SNOC_eq]
QED

Theorem par_log_finished_right:
  (c []).actions = [] ⇒
  ∀q. par_log c (finished B y) q =
        B ++ par_log c (return y) (skip_results (LENGTH B) q)
Proof
  strip_tac >> Induct_on ‘q’ using SNOC_INDUCT
  >- simp[par_log_def, par_actions_NIL, skip_results_def, log_of_def,
          finished_def, return_def]
  >> simp[SNOC_APPEND] >> rpt strip_tac
  >> ‘∃s'. skip_results (LENGTH B) (q ++ [x]) = skip_results (LENGTH B) q ++ [s']’
       by simp[skip_results_SNOC]
  >> simp[par_log_SNOC, new_actions_finished]
  >> qpat_x_assum ‘skip_results _ _ = _’ (SUBST1_TAC o GSYM)
  >> simp[left_view_skip, return_finished, new_actions_finished]
  >> metis_tac[left_view_right_irrelevant]
QED

(* A finished right side: its last actions come after the left side's
   first ones (which are none), and their responses are skipped *)
Theorem both_finished_right:
  (c []).actions = [] ⇒
  both c (finished B y) q =
    let rest = both c (return y) (skip_results (LENGTH B) q) in
      <| actions := B ++ rest.actions; result := rest.result |>
Proof
  strip_tac
  >> simp[both_def, GSYM par_log_def, par_log_finished_right]
  >> simp[left_view_skip, finished_def, return_def]
  >> metis_tac[left_view_right_irrelevant]
QED

(* ------------------------------------------------------------------------
   choose: characterisation
   ------------------------------------------------------------------------ *)

(* Before a side has finished, choose behaves like both, unfinished *)
Theorem choose_running:
  first_prefix (either_done m1 m2) h = NONE ⇒
  choose m1 m2 h = <| actions := par_log m1 m2 h; result := NONE |>
Proof
  simp[choose_def]
QED

Theorem choose_before:
  first_prefix (either_done m1 m2) h = SOME n ∧ k < n ⇒
  choose m1 m2 (TAKE k h) = <| actions := par_log m1 m2 (TAKE k h); result := NONE |>
Proof
  rw[] >> irule choose_running
  >> gvs[first_prefix_SOME, first_prefix_NONE, TAKE_TAKE_MIN, LENGTH_TAKE_EQ]
  >> rw[] >> first_x_assum irule >> gvs[MIN_DEF] >> rw[]
QED

(* p is the history up to the first round where a side has finished *)
Definition first_either_done_def:
  first_either_done m1 m2 p ⇔
    first_prefix (either_done m1 m2) p = SOME (LENGTH p)
End

Theorem first_either_done_TAKE:
  first_prefix (either_done m1 m2) h = SOME n ⇒
  first_either_done m1 m2 (TAKE n h) ∧ n ≤ LENGTH h
Proof
  strip_tac >> drule first_prefix_TAKE
  >> disch_then (qspec_then ‘n’ mp_tac)
  >> gvs[first_prefix_SOME, first_either_done_def, LENGTH_TAKE]
QED

Theorem first_either_done_before:
  first_either_done m1 m2 p ∧ k < LENGTH p ⇒
  choose m1 m2 (TAKE k p) = <| actions := par_log m1 m2 (TAKE k p); result := NONE |>
Proof
  rw[first_either_done_def] >> drule_all choose_before >> simp[]
QED

Theorem first_either_done_either:
  first_either_done m1 m2 p ⇒
  (m1 (left_view m1 m2 p)).result ≠ NONE ∨ (m2 (right_view m1 m2 p)).result ≠ NONE
Proof
  rw[first_either_done_def, first_prefix_SOME]
  >> gvs[either_done_def, TAKE_LENGTH_ID]
QED

Theorem choose_at:
  first_either_done m1 m2 p ⇒
  choose m1 m2 p =
    let l = left_view m1 m2 p; r = right_view m1 m2 p in
      case (m1 l).result of
        SOME x =>
          <| actions := log_before m1 m2 p ++ new_actions (log_of m1) l;
             result := SOME (INL (x, suspended m2 r)) |>
      | NONE =>
          <| actions := par_log m1 m2 p;
             result := if new_actions (log_of m1) l = []
                       then SOME (INR (suspended m1 l, THE (m2 r).result))
                       else NONE |>
Proof
  rw[first_either_done_def] >> simp[choose_def, TAKE_LENGTH_ID]
  >> CASE_TAC >> rw[]
QED

(* In the first round where a side has finished, choose's new actions are
   what it reports beyond the log of the rounds before *)
Theorem choose_new_actions_at:
  first_either_done m1 m2 p ⇒
  new_actions (log_of (choose m1 m2)) p =
    DROP (LENGTH (log_before m1 m2 p)) (choose m1 m2 p).actions
Proof
  Cases_on ‘p’ using SNOC_CASES
  >- simp[new_actions_NIL, log_of_def, log_before_def]
  >> rename1 ‘SNOC s p’ >> rw[SNOC_APPEND]
  >> drule_then (qspec_then ‘LENGTH p’ mp_tac) first_either_done_before
  >> simp[TAKE_LENGTH_APPEND] >> strip_tac
  >> simp[new_actions_SNOC, log_of_def, log_before_def, FRONT_SNOC']
QED

(* MAIN: if m1 has finished in the first round where a side finished, choose
   finishes in that round with m1's result and m2 suspended *)
Theorem choose_left_wins:
  first_either_done m1 m2 p ∧ (m1 (left_view m1 m2 p)).result = SOME x ⇒
  first_done (choose m1 m2) p (INL (x, suspended m2 (right_view m1 m2 p))) ∧
  (choose m1 m2 p).actions =
    log_before m1 m2 p ++ new_actions (log_of m1) (left_view m1 m2 p) ∧
  new_actions (log_of (choose m1 m2)) p = new_actions (log_of m1) (left_view m1 m2 p)
Proof
  strip_tac >> drule choose_new_actions_at >> drule choose_at
  >> simp[] >> rpt strip_tac
  >- (simp[first_done_def] >> rpt strip_tac
      >> drule_all first_either_done_before >> simp[])
  >> simp[DROP_LENGTH_APPEND]
QED

(* MAIN: if m2 has finished in that round but m1 has not, and m1 emitted
   nothing in that round, choose finishes with m2's result and m1 suspended *)
Theorem choose_right_wins:
  first_either_done m1 m2 p ∧ (m1 (left_view m1 m2 p)).result = NONE ∧
  (m2 (right_view m1 m2 p)).result = SOME y ∧
  new_actions (log_of m1) (left_view m1 m2 p) = [] ⇒
  first_done (choose m1 m2) p (INR (suspended m1 (left_view m1 m2 p), y)) ∧
  (choose m1 m2 p).actions = par_log m1 m2 p ∧
  new_actions (log_of (choose m1 m2)) p = new_actions (log_of m2) (right_view m1 m2 p)
Proof
  strip_tac >> drule choose_new_actions_at >> drule choose_at
  >> simp[] >> rpt strip_tac
  >- (simp[first_done_def] >> rpt strip_tac
      >> drule_all first_either_done_before >> simp[])
  >> simp[Once par_log_log_before, DROP_LENGTH_APPEND]
QED

(* If m1 did emit something in that round, choose waits one round *)
Theorem choose_right_waits:
  first_either_done m1 m2 p ∧ (m1 (left_view m1 m2 p)).result = NONE ∧
  new_actions (log_of m1) (left_view m1 m2 p) ≠ [] ⇒
  choose m1 m2 p = <| actions := par_log m1 m2 p; result := NONE |>
Proof
  strip_tac >> drule choose_at >> simp[]
QED

(* MAIN: ... and then finishes with m2's result and m1 suspended, with the
   responses to its last actions delivered *)
Theorem choose_right_wins_later:
  first_either_done m1 m2 p ∧ (m1 (left_view m1 m2 p)).result = NONE ∧
  (m2 (right_view m1 m2 p)).result = SOME y ∧
  new_actions (log_of m1) (left_view m1 m2 p) ≠ [] ⇒
  first_done (choose m1 m2) (p ++ [s])
             (INR (suspended m1 (left_view m1 m2 (p ++ [s])), y)) ∧
  (choose m1 m2 (p ++ [s])).actions = par_log m1 m2 p ∧
  new_actions (log_of (choose m1 m2)) (p ++ [s]) = []
Proof
  strip_tac
  >> ‘first_prefix (either_done m1 m2) (p ++ [s]) = SOME (LENGTH p)’
       by gvs[first_either_done_def, first_prefix_APPEND]
  >> ‘choose m1 m2 (p ++ [s]) =
        <| actions := par_log m1 m2 p;
           result := SOME (INR (suspended m1 (left_view m1 m2 (p ++ [s])), y)) |>’
       by simp[choose_def, TAKE_LENGTH_APPEND, TAKE_LENGTH_TOO_LONG]
  >> drule_all choose_right_waits >> strip_tac
  >> simp[first_done_def, new_actions_SNOC, log_of_def]
  >> rpt strip_tac
  >> Cases_on ‘n = LENGTH p’ >> simp[TAKE_LENGTH_APPEND]
  >> ‘n < LENGTH p’ by simp[]
  >> drule_all first_either_done_before >> simp[TAKE_APPEND1]
QED

(* ------------------------------------------------------------------------
   Nothing is lost
   ------------------------------------------------------------------------ *)

(* Continue choose's result by running the winner's result alongside the
   loser, so that the pair of results comes out as from both *)
Definition rejoin_def:
  rejoin r =
    case r of
      INL (x, rest2) => both (return x) rest2
    | INR (rest1, y) => both rest1 (return y)
End

(* bind_continues and bind_running, with their type variables renamed apart, so that it can be
   applied to an assumption without capturing the goal's type variables *)
val bind_continues' = GEN_TYVARIFY bind_continues;
val bind_running' = GEN_TYVARIFY bind_running;

Theorem choose_rejoin_left[local]:
  wf m1 ∧ wf m2 ∧ first_either_done m1 m2 p ∧
  (m1 (left_view m1 m2 p)).result = SOME x ⇒
  bind (choose m1 m2) rejoin (p ++ q) = both m1 m2 (p ++ q)
Proof
  strip_tac >> drule_all choose_left_wins >> strip_tac
  >> qpat_x_assum ‘first_done _ _ _’
       (fn th => simp[MATCH_MP bind_continues' th])
  >> ‘suspended m1 (left_view m1 m2 p) =
        finished (new_actions (log_of m1) (left_view m1 m2 p)) x’
       by (irule suspended_finished >> simp[])
  >> simp[rejoin_def, both_split, both_finished_left]
QED

Theorem choose_rejoin_right[local]:
  wf m1 ∧ wf m2 ∧ first_either_done m1 m2 p ∧
  (m1 (left_view m1 m2 p)).result = NONE ∧
  (m2 (right_view m1 m2 p)).result = SOME y ∧
  new_actions (log_of m1) (left_view m1 m2 p) = [] ⇒
  bind (choose m1 m2) rejoin (p ++ q) = both m1 m2 (p ++ q)
Proof
  strip_tac >> drule_all choose_right_wins >> strip_tac
  >> qpat_x_assum ‘first_done _ _ _’
       (fn th => simp[MATCH_MP bind_continues' th])
  >> ‘suspended m2 (right_view m1 m2 p) =
        finished (new_actions (log_of m2) (right_view m1 m2 p)) y’
       by (irule suspended_finished >> simp[])
  >> ‘(suspended m1 (left_view m1 m2 p) []).actions = []’
       by simp[suspended_first_poll]
  >> simp[rejoin_def, both_split, both_finished_right]
  >> simp[Once par_log_log_before]
QED

Theorem choose_rejoin_right_later[local]:
  wf m1 ∧ wf m2 ∧ first_either_done m1 m2 p ∧
  (m1 (left_view m1 m2 p)).result = NONE ∧
  (m2 (right_view m1 m2 p)).result = SOME y ∧
  new_actions (log_of m1) (left_view m1 m2 p) ≠ [] ⇒
  bind (choose m1 m2) rejoin (p ++ q) = both m1 m2 (p ++ q)
Proof
  strip_tac >> Cases_on ‘q’
  >- (* the round after has not happened yet: both are still running *)
     (simp[]
      >> ‘∀n. n ≤ LENGTH p ⇒ (choose m1 m2 (TAKE n p)).result = NONE’
           by (rw[] >> Cases_on ‘n = LENGTH p’
               >- simp[TAKE_LENGTH_ID, choose_right_waits]
               >> ‘n < LENGTH p’ by simp[]
               >> drule_all first_either_done_before >> simp[])
      >> qpat_x_assum ‘∀n. _’ (fn th => simp[MATCH_MP bind_running' th])
      >> simp[choose_right_waits, both_def, GSYM par_log_def])
  >> rename1 ‘p ++ s :: q’
  >> ‘p ++ s :: q = (p ++ [s]) ++ q’ by simp[]
  >> pop_assum SUBST1_TAC
  >> drule_all choose_right_wins_later
  >> disch_then (qspec_then ‘s’ strip_assume_tac)
  >> qpat_x_assum ‘first_done _ _ _’
       (fn th => simp[MATCH_MP bind_continues' th])
  (* m2 had already finished before the round after *)
  >> ‘∃s2. right_view m1 m2 (p ++ [s]) = right_view m1 m2 p ++ [s2]’
       by simp[right_view_SNOC_eq]
  >> ‘m2 (right_view m1 m2 p ++ [s2]) = m2 (right_view m1 m2 p)’
       by (irule wf_SNOC_finished >> simp[])
  >> ‘new_actions (log_of m2) (right_view m1 m2 (p ++ [s])) = []’
       by (simp[] >> irule wf_finished_new_actions >> simp[])
  >> ‘suspended m2 (right_view m1 m2 (p ++ [s])) =
        finished (new_actions (log_of m2) (right_view m1 m2 (p ++ [s]))) y’
       by (irule suspended_finished >> simp[])
  >> pop_assum mp_tac
  >> qpat_x_assum ‘new_actions (log_of m2) _ = []’ (fn th => REWRITE_TAC[th])
  >> REWRITE_TAC[GSYM return_finished] >> strip_tac
  >> simp[rejoin_def, both_split, log_before_def, FRONT_SNOC']
QED

(* MAIN: nothing is lost.  Running choose and then continuing with the
   winner's result alongside the loser is exactly running both sides with
   both: the same actions in the same order, and the same results. *)
Theorem choose_rejoin:
  wf m1 ∧ wf m2 ⇒ bind (choose m1 m2) rejoin = both m1 m2
Proof
  rw[FUN_EQ_THM] >> rename1 ‘_ h = _ h’
  >> Cases_on ‘first_prefix (either_done m1 m2) h’
  >- (* no side has finished yet *)
     (‘∀n. n ≤ LENGTH h ⇒ (choose m1 m2 (TAKE n h)).result = NONE’
        by (rw[] >> simp[choose_running, first_prefix_TAKE_NONE])
      >> qpat_x_assum ‘∀n. _’ (fn th => simp[MATCH_MP bind_running' th])
      >> ‘¬either_done m1 m2 h’
           by (fs[first_prefix_NONE] >> first_x_assum (qspec_then ‘LENGTH h’ mp_tac)
               >> simp[TAKE_LENGTH_ID])
      >> fs[either_done_def]
      >> simp[choose_running, both_def, GSYM par_log_def])
  (* a side has finished, first after p *)
  >> rename1 ‘_ = SOME n’
  >> drule first_either_done_TAKE >> strip_tac
  >> qabbrev_tac ‘p = TAKE n h’
  >> ‘h = p ++ DROP n h’ by simp[Abbr ‘p’]
  >> pop_assum SUBST1_TAC
  >> Cases_on ‘(m1 (left_view m1 m2 p)).result’
  >- (‘(m2 (right_view m1 m2 p)).result ≠ NONE’
        by metis_tac[first_either_done_either]
      >> Cases_on ‘(m2 (right_view m1 m2 p)).result’ >> fs[]
      >> Cases_on ‘new_actions (log_of m1) (left_view m1 m2 p) = []’
      >- (irule choose_rejoin_right >> simp[])
      >> irule choose_rejoin_right_later >> simp[])
  >> irule choose_rejoin_left >> simp[]
QED

(* ------------------------------------------------------------------------
   choose preserves well-formedness and settledness
   ------------------------------------------------------------------------ *)

Theorem IS_PREFIX_APPEND_APPEND[local]:
  l ≼ l ++ a ++ b
Proof
  REWRITE_TAC[GSYM APPEND_ASSOC, IS_PREFIX_APPEND3]
QED

(* MAIN: choose is well-formed, whatever its arguments *)
Theorem wf_choose:
  wf (choose m1 m2)
Proof
  simp[wf_def] >> rpt gen_tac
  >> Cases_on ‘first_prefix (either_done m1 m2) h’
  >- (* no side had finished before s *)
     (simp[choose_running]
      >> Cases_on ‘first_prefix (either_done m1 m2) (h ++ [s])’
      >- simp[choose_running, par_log_SNOC, IS_PREFIX_APPEND_APPEND]
      >> rename1 ‘_ = SOME n’
      >> ‘n = LENGTH h + 1’ by gvs[first_prefix_SNOC, AllCaseEqs()]
      >> ‘first_either_done m1 m2 (h ++ [s])’ by simp[first_either_done_def]
      >> drule choose_at >> simp[] >> disch_then kall_tac
      >> every_case_tac
      >> rw[log_before_def, FRONT_SNOC', par_log_SNOC, IS_PREFIX_APPEND_APPEND])
  (* a side had finished before s: nothing changes, except that choose may
     finish now if it was waiting for responses *)
  >> rename1 ‘_ = SOME n’
  >> ‘first_prefix (either_done m1 m2) (h ++ [s]) = SOME n’
       by simp[first_prefix_APPEND]
  >> ‘n ≤ LENGTH h’ by fs[first_prefix_SOME]
  >> simp[choose_def, TAKE_APPEND1]
  >> rpt (CASE_TAC >> simp[])
  >> ‘n + 1 ≤ LENGTH h’ by simp[]
  >> simp[TAKE_APPEND1]
QED

(* To show settledness, it is enough to look at the round where m first
   finishes *)
Theorem settled_from_first_done:
  wf m ∧ (∀h x. first_done m h x ⇒ new_actions (log_of m) h = []) ⇒ settled m
Proof
  rw[settled_def]
  >> qspecl_then [‘m’, ‘h’] strip_assume_tac history_split
  >- (first_x_assum (qspec_then ‘LENGTH h’ mp_tac) >> simp[TAKE_LENGTH_ID])
  >> Cases_on ‘h2’ using SNOC_CASES >- (gvs[] >> metis_tac[])
  >> gvs[SNOC_APPEND]
  >> ‘(m (h1 ++ l)).result ≠ NONE’
       by (‘m (h1 ++ l) = m h1’ by (irule wf_finished_stays >> gvs[first_done_def])
           >> gvs[first_done_def])
  >> ‘h1 ++ (l ++ [x']) = (h1 ++ l) ++ [x']’ by simp[]
  >> pop_assum SUBST1_TAC
  >> irule wf_finished_new_actions >> simp[]
QED

(* A computation first finishes after h only, not after a shorter prefix *)
Theorem first_done_TAKE:
  first_done m h x ∧ k ≤ LENGTH h ∧ (m (TAKE k h)).result ≠ NONE ⇒ k = LENGTH h
Proof
  rw[first_done_def] >> spose_not_then assume_tac
  >> ‘k < LENGTH h’ by simp[] >> res_tac
QED

(* MAIN: if both sides are settled, so is choose: nothing it emits in the
   round where it finishes can lose its response *)
Theorem settled_choose:
  settled m1 ∧ settled m2 ⇒ settled (choose m1 m2)
Proof
  rw[] >> irule settled_from_first_done >> simp[wf_choose]
  >> rpt strip_tac >> rename1 ‘first_done _ h z’
  >> Cases_on ‘first_prefix (either_done m1 m2) h’
  >- gvs[first_done_def, choose_running]
  >> rename1 ‘_ = SOME n’
  >> drule first_either_done_TAKE >> strip_tac
  >> qabbrev_tac ‘p = TAKE n h’
  >> ‘LENGTH p = n’ by simp[Abbr ‘p’]
  (* choose first finishes after h, so if it has finished after a prefix of
     h, that prefix is h *)
  >> ‘∀k. k ≤ LENGTH h ∧ (choose m1 m2 (TAKE k h)).result ≠ NONE ⇒ TAKE k h = h’
       by (rpt strip_tac
           >> qspecl_then [‘choose m1 m2’, ‘h’, ‘z’, ‘k’] mp_tac
                (Q.GENL [‘m’, ‘h’, ‘x’, ‘k’] first_done_TAKE)
           >> simp[TAKE_LENGTH_ID])
  >> Cases_on ‘(m1 (left_view m1 m2 p)).result’
  >- (‘(m2 (right_view m1 m2 p)).result ≠ NONE’
        by metis_tac[first_either_done_either]
      >> Cases_on ‘(m2 (right_view m1 m2 p)).result’ >> fs[]
      >> Cases_on ‘new_actions (log_of m1) (left_view m1 m2 p) = []’
      >- (* m2 wins now *)
         (drule_all choose_right_wins >> strip_tac
          >> ‘p = h’ by (fs[Abbr ‘p’] >> first_x_assum irule >> fs[first_done_def])
          >> qpat_x_assum ‘Abbrev _’ kall_tac >> gvs[settled_def])
      (* m2 wins one round later *)
      >> Cases_on ‘n = LENGTH h’
      >- (‘p = h’ by simp[Abbr ‘p’, TAKE_LENGTH_ID]
          >> drule_all choose_right_waits >> strip_tac >> gvs[first_done_def])
      >> ‘n < LENGTH h’ by simp[]
      >> drule_all choose_right_wins_later
      >> disch_then (qspec_then ‘EL n h’ strip_assume_tac)
      >> ‘p ++ [EL n h] = TAKE (n + 1) h’
           by simp[Abbr ‘p’, TAKE_EL_SNOC, SNOC_APPEND]
      >> ‘LENGTH h ≤ n + 1’
           by (first_x_assum irule
               >> qpat_x_assum ‘_ = TAKE (n + 1) h’ (SUBST_ALL_TAC o GSYM)
               >> fs[first_done_def])
      >> ‘TAKE (n + 1) h = h’ by simp[TAKE_LENGTH_TOO_LONG]
      >> gvs[])
  (* m1 wins *)
  >> drule_all choose_left_wins >> strip_tac
  >> ‘p = h’ by (fs[Abbr ‘p’] >> first_x_assum irule >> fs[first_done_def])
  >> qpat_x_assum ‘Abbrev _’ kall_tac >> gvs[settled_def]
QED
