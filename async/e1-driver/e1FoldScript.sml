(*
  Fold programs: a computation given by a state folded over the history.
  The state after history h is FOLDL step init h; each round emits the
  state's acts; the computation has finished (result SOME ()) once fin
  holds of the state.  The generic E1 driver runs such a program directly:
  it keeps the state and calls (translated) init, step, acts and fin.
*)
Theory e1Fold
Ancestors
  asyncCore asyncLevel1
Libs
  preamble

Definition fold_prog_def:
  fold_prog (init : 'st) (step : 'st -> ('e, 'r) snapshot -> 'st)
            (acts : 'st -> 'act list) (fin : 'st -> bool) h =
    <| actions := FLAT (GENLIST (λk. acts (FOLDL step init (TAKE k h))) (SUC (LENGTH h)));
       result := if fin (FOLDL step init h) then SOME () else NONE |>
End

Theorem fold_state_SNOC:
  FOLDL step init (h ++ [s]) = step (FOLDL step init h) s
Proof
  simp[FOLDL_APPEND]
QED

Theorem fold_prog_actions_SNOC:
  (fold_prog init step acts fin (h ++ [s])).actions =
  (fold_prog init step acts fin h).actions ++ acts (FOLDL step init (h ++ [s]))
Proof
  simp[fold_prog_def] >>
  ‘SUC (LENGTH h + 1) = SUC (SUC (LENGTH h))’ by simp[] >>
  pop_assum SUBST1_TAC >> REWRITE_TAC [GENLIST] >>
  ‘GENLIST (λk. acts (FOLDL step init (TAKE k (h ++ [s])))) (LENGTH h) =
   GENLIST (λk. acts (FOLDL step init (TAKE k h))) (LENGTH h)’
    by (irule GENLIST_CONG >> rw[] >> simp[TAKE_APPEND1]) >>
  pop_assum SUBST1_TAC >>
  simp[SNOC_APPEND, FLAT_APPEND, TAKE_LENGTH_ID_rwt, TAKE_APPEND1]
QED

(* The round polled with h emits the acts of the state after h *)
Theorem fold_prog_new_actions:
  new_actions (log_of (fold_prog init step acts fin)) h = acts (FOLDL step init h)
Proof
  Cases_on ‘h’ using SNOC_CASES
  >- simp[new_actions_def, log_of_def, fold_prog_def] >>
  simp[new_actions_def, log_of_def, SNOC_APPEND, FRONT_APPEND, fold_prog_actions_SNOC] >>
  simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]
QED

Theorem fold_prog_result:
  (fold_prog init step acts fin h).result =
    if fin (FOLDL step init h) then SOME () else NONE
Proof
  simp[fold_prog_def]
QED
