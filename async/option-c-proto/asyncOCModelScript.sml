(*
  Option C: the Level 2 CF library, replayed into the socket program's
  translation chain (design/33 §2.1, "replay").  Model side: what each
  Level 2 combinator is one poll later.  Same content as
  loop/blocking-l2/asyncL2BlkModel and option-c/library/asyncL2LibModel
  on spike/option-c.
*)
Theory asyncOCModel
Ancestors
  list rich_list asyncCore asyncLevel1 asyncChoose asyncLevel2 asyncLoop2
  asyncCfActModel asyncCfActBothModel
Libs
  preamble

(* Level 2 versions of cf-actions' prepend and skipping (bind's finished
   case): the interest is g's, on the snapshots g is shown. *)
Definition prepend2_def:
  prepend2 A g = <| run := prepend A g.run; interest := g.interest |>
End

Definition skipping2_def:
  skipping2 k g =
    <| run := skipping k g.run; interest := λh. g.interest (skip_results k h) |>
End


Theorem comp2_eq[local]:
  c1 = c2 ⇔ c1.run = c2.run ∧ c1.interest = c2.interest
Proof
  simp[DB.fetch "asyncLevel2" "comp2_component_equality"]
QED

(* ------------------------------------------------------------------------
   One poll later
   ------------------------------------------------------------------------ *)

Theorem suspended2_run:
  (suspended2 c r).run = suspended c.run r
Proof
  simp[suspended2_def]
QED

Theorem suspended2_interest:
  (suspended2 c r).interest h = c.interest (r ++ h)
Proof
  simp[suspended2_def]
QED

Theorem suspended2_wait_on_NONE:
  ¬(e ∈ w.ready ∧ IS_SOME (p w)) ⇒ suspended2 (wait_on e p) [w] = wait_on e p
Proof
  rw[comp2_eq, suspended2_def, wait_on_def]
  \\ TRY (simp[FUN_EQ_THM] \\ NO_TAC)
  \\ irule suspended_wait_NONE \\ rw[] \\ gvs[NOT_IS_SOME_EQ_NONE]
QED

Theorem suspended2_wait_on_SOME:
  e ∈ w.ready ∧ p w = SOME a ⇒
  (suspended2 (wait_on e p) [w]).run = finished [] a
Proof
  rw[suspended2_def, wait_on_def] \\ irule suspended_wait_SOME \\ simp[]
QED

Theorem suspended2_emit2_CONS:
  w.results = r :: rs ⇒ (suspended2 (emit2 a) [w]).run = finished [] r
Proof
  rw[suspended2_def, emit2_def] \\ irule suspended_emit_CONS \\ simp[]
QED

Theorem suspended2_emit2_NIL:
  w.results = [] ⇒ suspended2 (emit2 a) [w] = never2
Proof
  rw[comp2_eq, suspended2_def, emit2_def, asyncLoop2Theory.never2_def, FUN_EQ_THM]
  \\ simp[suspended_emit_NIL]
QED

Theorem suspended2_never2:
  suspended2 never2 [w] = never2
Proof
  rw[comp2_eq, suspended2_def, asyncLoop2Theory.never2_def, never_def]
  \\ TRY (simp[FUN_EQ_THM] \\ NO_TAC)
  \\ irule suspended_wait_NONE \\ simp[]
QED

Theorem suspended2_prepend2:
  suspended2 (prepend2 A g) [w] = suspended2 g [w]
Proof
  rw[comp2_eq, suspended2_def, prepend2_def, suspended_prepend]
QED

Theorem suspended2_skipping2:
  suspended2 (skipping2 k g) [w] = suspended2 g [skip_snap k w]
Proof
  rw[comp2_eq, suspended2_def, skipping2_def, suspended_skipping, FUN_EQ_THM,
     skip_results_def, skip_snap_def]
QED


(* bind2, first part finished: emit its actions, then run f x without the
   responses that belong to the first part *)
Theorem bind2_finished:
  c.run = finished A x ⇒
  bind2 c f = prepend2 A (skipping2 (LENGTH A) (f x))
Proof
  strip_tac \\ simp[comp2_eq, bind2_def, prepend2_def, skipping2_def]
  \\ conj_tac >- fs[bind_finished]
  \\ fs[FUN_EQ_THM, bind_interest_def, Once first_prefix_def, finished_def,
        new_actions_def, log_of_def]
QED

(* bind2, first part still running: one poll of bind2 c f is bind2 of one
   poll of c *)
Theorem suspended2_bind2:
  wf c.run ∧ (c.run []).result = NONE ⇒
  suspended2 (bind2 c f) [w] = bind2 (suspended2 c [w]) f
Proof
  rw[comp2_eq, bind2_def, suspended2_def, suspended_bind, FUN_EQ_THM]
  \\ simp[bind_interest_def]
  \\ simp[Once first_prefix_def]
  \\ ‘(λp. (suspended c.run [w] p).result ≠ NONE) =
      (λt. (c.run (w::t)).result ≠ NONE)’
    by simp[FUN_EQ_THM, suspended_one]
  \\ simp[]
  \\ Cases_on ‘first_prefix (λt. (c.run (w::t)).result ≠ NONE) x’ \\ simp[]
  \\ simp[suspended_one, new_actions_suspended]
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
