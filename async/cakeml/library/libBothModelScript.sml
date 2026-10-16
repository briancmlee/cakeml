(*
  Model-side lemmas for both (libBoth): what  both m1 m2  is after
  one more poll, and when both sides have already finished.
  The routing (par_views) reduces, for one snapshot, to TAKE/DROP of its
  results at the number of actions the left side emitted in its first round.
*)
Theory libBothModel
Ancestors
  list rich_list asyncCore asyncLevel1 asyncChoose libModel
Libs
  preamble

(* One snapshot with only its first k results *)
Definition take_snap_def:
  take_snap k (s : ('e,'r) snapshot) = s with results := TAKE k s.results
End

Theorem par_views_one[local]:
  par_views acts1 acts2 [w] =
    ([w with results := TAKE (LENGTH (acts1 [])) w.results],
     [w with results := DROP (LENGTH (acts1 [])) w.results])
Proof
  mp_tac (par_views_SNOC |> Q.INST [‘h’ |-> ‘[]’, ‘s’ |-> ‘w’]) >>
  REWRITE_TAC[APPEND] >> simp[new_actions_NIL]
QED

Theorem left_view_one:
  left_view m1 m2 [w] = [take_snap (LENGTH (m1 []).actions) w]
Proof
  simp[left_view_def, par_views_one, new_actions_NIL, log_of_def,
       take_snap_def]
QED

Theorem right_view_one:
  right_view m1 m2 [w] = [skip_snap (LENGTH (m1 []).actions) w]
Proof
  simp[right_view_def, par_views_one, new_actions_NIL, log_of_def,
       skip_snap_def]
QED

Theorem both_NIL_poll:
  (both m1 m2 []).actions = (m1 []).actions ++ (m2 []).actions ∧
  (both m1 m2 []).result =
    case ((m1 []).result, (m2 []).result) of
      (SOME x, SOME y) => SOME (x, y)
    | _ => NONE
Proof
  simp[both_def, par_log_def, par_actions_NIL, log_of_def]
QED

(* Polling both polls each side, with its share of the responses: the
   left side gets the first k, where k is the number of actions it emitted
   in its first round. *)
Theorem suspended_both:
  wf m1 ∧ wf m2 ⇒
  suspended (both m1 m2) [w] =
    both (suspended m1 [take_snap (LENGTH (m1 []).actions) w])
         (suspended m2 [skip_snap (LENGTH (m1 []).actions) w])
Proof
  strip_tac >> simp[FUN_EQ_THM] >> qx_gen_tac ‘h’ >>
  mp_tac (both_split |> Q.INST [‘p’ |-> ‘[w]’, ‘q’ |-> ‘h’]) >>
  simp[left_view_one, right_view_one, suspended_one, log_before_def,
       both_NIL_poll, par_log_def, par_actions_NIL, log_of_def] >>
  strip_tac >> simp[outcome_component_equality] >>
  simp[DROP_APPEND, DROP_LENGTH_NIL]
QED

Theorem both_return_return:
  both (return x) (return y) = finished [] (x, y)
Proof
  simp[FUN_EQ_THM, finished_def, both_def, return_def] >>
  Induct_on ‘x'’ using SNOC_INDUCT >>
  simp[par_log_def, par_actions_NIL, log_of_def, return_def] >>
  gvs[par_log_def, SNOC_APPEND, par_actions_SNOC] >>
  rpt strip_tac >> pairarg_tac >>
  simp[new_actions_def, log_of_def, return_def]
QED

(* Two finished sides: both has finished too *)
Theorem both_finished_finished:
  both (finished A x) (finished B y) = finished (A ++ B) (x, y)
Proof
  simp[FUN_EQ_THM] >> qx_gen_tac ‘h’ >>
  simp[both_finished_left] >>
  simp[both_finished_right, return_def, both_return_return] >>
  simp[finished_def]
QED
