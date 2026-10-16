(*
  Model-side lemmas for choose in the CF layer (libChoose): what
  choose m1 m2 is before its first poll, and after one more poll.

  With k = LENGTH (m1 []).actions, w1 = take_snap k w and w2 = skip_snap k w
  (each side's share of snapshot w), and m1', m2' = the sides with their
  shares delivered (suspended m1 [w1], suspended m2 [w2]):
   - m1 finished at once:           choose is finished, INL (x, m2);
   - m2 finished, m1 emitted nothing: choose is finished, INR (m1, y);
   - m2 finished, m1 emitted:       choose waits one round, then returns
                                    INR (m1', y);
   - neither finished:              after w, choose is choose m1' m2'.
*)
Theory libChooseModel
Ancestors
  list rich_list asyncCore asyncLevel1 asyncChoose libModel
  libBothModel
Libs
  preamble

(* ------------------------------------------------------------------------
   One snapshot of the views, logs and decisions
   ------------------------------------------------------------------------ *)

Theorem suspended_suspended:
  ∀q r m. wf m ⇒ suspended (suspended m r) q = suspended m (r ++ q)
Proof
  Induct_on ‘q’ using SNOC_INDUCT >- simp[] >>
  rpt strip_tac >> fs[SNOC_APPEND] >>
  ‘suspended (suspended m r) (q ++ [x]) =
   suspended (suspended (suspended m r) q) [x]’
    by simp[suspended_suspended_one, wf_suspended] >>
  simp[suspended_suspended_one] >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND]
QED

Theorem views_cons:
  wf m1 ⇒
  left_view m1 m2 (w :: q) =
    take_snap (LENGTH (m1 []).actions) w ::
    left_view (suspended m1 [take_snap (LENGTH (m1 []).actions) w])
              (suspended m2 [skip_snap (LENGTH (m1 []).actions) w]) q ∧
  right_view m1 m2 (w :: q) =
    skip_snap (LENGTH (m1 []).actions) w ::
    right_view (suspended m1 [take_snap (LENGTH (m1 []).actions) w])
               (suspended m2 [skip_snap (LENGTH (m1 []).actions) w]) q
Proof
  strip_tac >>
  drule (Q.GENL [‘m1’, ‘m2’, ‘p’] views_split) >>
  disch_then (qspecl_then [‘m2’, ‘[w]’, ‘q’] mp_tac) >>
  simp[left_view_one, right_view_one]
QED

Theorem par_log_cons:
  wf m1 ∧ wf m2 ⇒
  par_log m1 m2 (w :: q) =
    (m1 []).actions ++ (m2 []).actions ++
    par_log (suspended m1 [take_snap (LENGTH (m1 []).actions) w])
            (suspended m2 [skip_snap (LENGTH (m1 []).actions) w]) q
Proof
  strip_tac >>
  mp_tac (Q.INST [‘p’ |-> ‘[w]’] par_log_split) >> simp[] >>
  disch_then (qspec_then ‘q’ mp_tac) >>
  simp[left_view_one, right_view_one, log_before_def, par_log_def,
       par_actions_NIL, log_of_def]
QED

Theorem log_before_cons:
  wf m1 ∧ wf m2 ⇒
  log_before m1 m2 (w :: q) =
    (m1 []).actions ++ (m2 []).actions ++
    log_before (suspended m1 [take_snap (LENGTH (m1 []).actions) w])
               (suspended m2 [skip_snap (LENGTH (m1 []).actions) w]) q
Proof
  strip_tac >> Cases_on ‘q’ using SNOC_CASES
  >- simp[log_before_def, par_log_def, par_actions_NIL, log_of_def]
  >> simp[log_before_def, SNOC_APPEND, FRONT_APPEND] >>
  ‘FRONT (w :: (l ++ [x])) = w :: l’ by simp[FRONT_DEF, FRONT_APPEND] >>
  simp[par_log_cons]
QED

Theorem either_done_cons:
  wf m1 ⇒
  either_done m1 m2 (w :: q) =
    either_done (suspended m1 [take_snap (LENGTH (m1 []).actions) w])
                (suspended m2 [skip_snap (LENGTH (m1 []).actions) w]) q
Proof
  strip_tac >> simp[either_done_def, views_cons]
QED

Theorem first_prefix_either_cons:
  wf m1 ∧ (m1 []).result = NONE ∧ (m2 []).result = NONE ⇒
  first_prefix (either_done m1 m2) (w :: h) =
    OPTION_MAP SUC
      (first_prefix
         (either_done (suspended m1 [take_snap (LENGTH (m1 []).actions) w])
                      (suspended m2 [skip_snap (LENGTH (m1 []).actions) w])) h)
Proof
  strip_tac >> simp[Once first_prefix_def] >>
  ‘¬either_done m1 m2 []’ by simp[either_done_def] >> simp[] >>
  AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
  simp[FUN_EQ_THM, either_done_cons]
QED

(* ------------------------------------------------------------------------
   choose before its first poll, and after one more poll
   ------------------------------------------------------------------------ *)

(* m1 has finished before its first poll: m1 wins at once, m2 is not polled *)
Theorem choose_left_done:
  (m1 []).result = SOME x ⇒
  choose m1 m2 = finished (m1 []).actions (INL (x, m2))
Proof
  rw[FUN_EQ_THM, finished_def, choose_def, Once first_prefix_def,
     either_done_def] >>
  simp[log_before_def, new_actions_NIL, log_of_def]
QED

(* m2 has finished and m1 has not, and m1 emitted nothing: m2 wins at once *)
Theorem choose_right_done_quiet:
  (m1 []).result = NONE ∧ (m2 []).result = SOME y ∧ (m1 []).actions = [] ⇒
  choose m1 m2 = finished (m2 []).actions (INR (m1, y))
Proof
  rw[FUN_EQ_THM, finished_def, choose_def, Once first_prefix_def,
     either_done_def] >>
  simp[new_actions_NIL, log_of_def, par_log_def, par_actions_NIL]
QED

Theorem choose_right_done_waits_NIL[local]:
  (m1 []).result = NONE ∧ (m2 []).result = SOME y ∧ (m1 []).actions ≠ [] ⇒
  choose m1 m2 [] = <| actions := (m1 []).actions ++ (m2 []).actions;
                       result := NONE |>
Proof
  strip_tac >> ONCE_REWRITE_TAC[choose_def] >>
  ONCE_REWRITE_TAC[first_prefix_def] >>
  simp[either_done_def, new_actions_NIL, log_of_def, par_log_def,
       par_actions_NIL]
QED

Theorem choose_right_done_waits_CONS[local]:
  (m1 []).result = NONE ∧ (m2 []).result = SOME y ∧ (m1 []).actions ≠ [] ⇒
  choose m1 m2 (w :: h) =
    <| actions := (m1 []).actions ++ (m2 []).actions;
       result :=
         SOME (INR (suspended m1 [take_snap (LENGTH (m1 []).actions) w], y)) |>
Proof
  strip_tac >> ONCE_REWRITE_TAC[choose_def] >>
  ONCE_REWRITE_TAC[first_prefix_def] >>
  simp[either_done_def, new_actions_NIL, log_of_def, par_log_def,
       par_actions_NIL, left_view_one]
QED

(* m2 has finished and m1 has not, but m1 emitted actions: choose waits
   one round for their responses, then returns m1 with them delivered *)
Theorem choose_right_done_waits:
  (m1 []).result = NONE ∧ (m2 []).result = SOME y ∧ (m1 []).actions ≠ [] ⇒
  (choose m1 m2 []).actions = (m1 []).actions ++ (m2 []).actions ∧
  (choose m1 m2 []).result = NONE ∧
  suspended (choose m1 m2) [w] =
    finished [] (INR (suspended m1 [take_snap (LENGTH (m1 []).actions) w], y))
Proof
  strip_tac >>
  simp[choose_right_done_waits_NIL, FUN_EQ_THM, suspended_one, finished_def,
       choose_right_done_waits_CONS] >>
  rpt strip_tac >> mp_tac (Q.INST [‘h’ |-> ‘x’] choose_right_done_waits_CONS) >>
  simp[]
QED

Theorem choose_NIL_running:
  (m1 []).result = NONE ∧ (m2 []).result = NONE ⇒
  (choose m1 m2 []).actions = (m1 []).actions ++ (m2 []).actions ∧
  (choose m1 m2 []).result = NONE
Proof
  strip_tac >> ONCE_REWRITE_TAC[choose_def] >>
  ONCE_REWRITE_TAC[first_prefix_def] >>
  simp[either_done_def, par_log_def, par_actions_NIL, log_of_def]
QED

Theorem TAKE_SUC_ADD1[local,simp]:
  TAKE (SUC n + 1) (w :: h) = w :: TAKE (n + 1) h
Proof
  simp[GSYM ADD1]
QED

Theorem DROP_LENGTH_APPEND2[local]:
  DROP (LENGTH a + LENGTH b) (a ++ b ++ c) = c ∧
  DROP (LENGTH a + LENGTH b) (a ++ b ++ c ++ d) = c ++ d
Proof
  ‘LENGTH a + LENGTH b = LENGTH (a ++ b)’ by simp[] >>
  pop_assum SUBST1_TAC >>
  ‘a ++ b ++ c ++ d = (a ++ b) ++ (c ++ d)’ by simp[] >>
  pop_assum SUBST1_TAC >>
  REWRITE_TAC[DROP_LENGTH_APPEND]
QED

(* Neither side has finished: polling choose polls each side with its share
   of the snapshot (as for both) and continues as choose. *)
Theorem suspended_choose:
  wf m1 ∧ wf m2 ∧ (m1 []).result = NONE ∧ (m2 []).result = NONE ⇒
  suspended (choose m1 m2) [w] =
    choose (suspended m1 [take_snap (LENGTH (m1 []).actions) w])
           (suspended m2 [skip_snap (LENGTH (m1 []).actions) w])
Proof
  strip_tac >> simp[FUN_EQ_THM] >> qx_gen_tac ‘h’ >>
  simp[suspended_one, choose_NIL_running] >>
  simp[choose_def, first_prefix_either_cons] >>
  Cases_on ‘first_prefix
              (either_done (suspended m1 [take_snap (LENGTH (m1 []).actions) w])
                           (suspended m2 [skip_snap (LENGTH (m1 []).actions) w])) h’ >>
  simp[par_log_cons, views_cons, log_before_cons, new_actions_suspended,
       suspended_suspended, DROP_LENGTH_APPEND2] >>
  rw[] >> gvs[par_log_cons, views_cons, log_before_cons, new_actions_suspended,
              suspended_suspended, DROP_LENGTH_APPEND2] >>
  every_case_tac >> gvs[] >> simp[DROP_LENGTH_APPEND2, ADD1]
QED

(* The same three cases, stated for a side that is literally `finished`
   (the form the CF proof sees), so they can be used as rewrites. *)
Theorem choose_finished_left:
  choose (finished A x) m2 = finished A (INL (x, m2))
Proof
  rw[FUN_EQ_THM] >> ONCE_REWRITE_TAC[choose_def] >>
  ONCE_REWRITE_TAC[first_prefix_def] >>
  simp[either_done_def, finished_def, log_before_def, new_actions_NIL,
       log_of_def]
QED

Theorem choose_finished_right_quiet:
  (m1 []).result = NONE ∧ (m1 []).actions = [] ⇒
  choose m1 (finished B y) = finished B (INR (m1, y))
Proof
  strip_tac >>
  mp_tac (Q.INST [‘m2’ |-> ‘finished B y’] choose_right_done_quiet) >>
  simp[finished_def]
QED

Theorem choose_finished_right_waits:
  (m1 []).result = NONE ∧ (m1 []).actions ≠ [] ⇒
  (choose m1 (finished B y) []).actions = (m1 []).actions ++ B ∧
  (choose m1 (finished B y) []).result = NONE ∧
  suspended (choose m1 (finished B y)) [w] =
    finished [] (INR (suspended m1 [take_snap (LENGTH (m1 []).actions) w], y))
Proof
  strip_tac >>
  mp_tac (Q.INST [‘m2’ |-> ‘finished B y’] choose_right_done_waits) >>
  simp[finished_def]
QED
