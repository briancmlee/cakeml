(*
  Model-side lemmas for map2 and both2 in the Level 2 CF library
  (asyncL2LibSpec): what each is one poll later, as asyncL2BlkModel does
  for bind2.  As at Level 1 (asyncCfActBothModel), both2 routes the
  snapshot's results by TAKE/DROP at the number of actions the left side
  emitted in its first round; the declared interest follows the same
  routing.
*)
Theory asyncL2LibModel
Ancestors
  list rich_list asyncCore asyncLevel1 asyncChoose asyncLevel2
  asyncCfActModel asyncCfActBothModel asyncL2BlkModel
Libs
  preamble

Theorem comp2_eq[local]:
  c1 = c2 ⇔ c1.run = c2.run ∧ c1.interest = c2.interest
Proof
  simp[DB.fetch "asyncLevel2" "comp2_component_equality"]
QED

(* What a computation waits for, one snapshot later *)
Theorem waiting_on_suspended2:
  waiting_on c (w :: h) = waiting_on (suspended2 c [w]) h
Proof
  simp[waiting_on_def, suspended2_def, suspended_one]
QED

Theorem suspended2_map2:
  suspended2 (map2 f c) [w] = map2 f (suspended2 c [w])
Proof
  rw[comp2_eq, map2_def, suspended2_def, FUN_EQ_THM, suspended_one, asyncLevel1Theory.map_def]
QED

Theorem map2_finished:
  c.run = finished A x ⇒ (map2 f c).run = finished A (f x)
Proof
  rw[map2_def, asyncLevel1Theory.map_def, finished_def, FUN_EQ_THM]
QED

(* The views of both sides after one snapshot, and then on *)
Theorem views_CONS[local]:
  wf m1 ⇒
  left_view m1 m2 (w :: h) =
    take_snap (LENGTH (m1 []).actions) w ::
    left_view (suspended m1 [take_snap (LENGTH (m1 []).actions) w])
              (suspended m2 [skip_snap (LENGTH (m1 []).actions) w]) h ∧
  right_view m1 m2 (w :: h) =
    skip_snap (LENGTH (m1 []).actions) w ::
    right_view (suspended m1 [take_snap (LENGTH (m1 []).actions) w])
               (suspended m2 [skip_snap (LENGTH (m1 []).actions) w]) h
Proof
  strip_tac >>
  qspecl_then [‘m1’, ‘m2’, ‘[w]’] mp_tac (Q.GENL [‘m1’, ‘m2’, ‘p’] views_split) >>
  simp[left_view_one, right_view_one]
QED

(* MAIN: one poll of both2 polls each side with its share of the results;
   the declared interest is the union of what the unfinished sides declare
   on their own views. *)
Theorem suspended2_both2:
  wf c1.run ∧ wf c2.run ⇒
  suspended2 (both2 c1 c2) [w] =
    both2 (suspended2 c1 [take_snap (LENGTH (c1.run []).actions) w])
          (suspended2 c2 [skip_snap (LENGTH (c1.run []).actions) w])
Proof
  rw[comp2_eq]
  >- simp[both2_def, suspended2_def, suspended_both]
  >> simp[both2_def, suspended2_def, FUN_EQ_THM, views_CONS] >>
  simp[GSYM suspended2_run, GSYM waiting_on_suspended2] >>
  simp[waiting_on_def, suspended2_def]
QED

Theorem both2_NIL:
  ((both2 c1 c2).run []).actions = (c1.run []).actions ++ (c2.run []).actions ∧
  (both2 c1 c2).interest [] = waiting_on c1 [] ∪ waiting_on c2 []
Proof
  simp[both2_def, both_NIL_poll] >>
  simp[left_view_def, right_view_def]
QED

Theorem both2_finished_finished:
  c1.run = finished A x ∧ c2.run = finished B y ⇒
  (both2 c1 c2).run = finished (A ++ B) (x, y)
Proof
  simp[both2_def, both_finished_finished]
QED
