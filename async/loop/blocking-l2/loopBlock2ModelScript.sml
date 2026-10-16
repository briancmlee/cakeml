(*
  Model-side lemmas for the Level 2 CF layer: what a Level 2 computation
  (comp2, async/model/asyncLevel2Script.sml) becomes one poll later
  (suspended2 c [w]), one lemma per implementation step, as
  libModel does for Level 1.  A comp2 is a record of the Level 1
  computation (run) and its declared interest; each lemma is an equation
  of records, so the interest is tracked exactly.
*)
Theory loopBlock2Model
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncLevel2 libModel
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

(* A finished Level 2 computation (its interest is irrelevant) *)
Definition finished2_def:
  finished2 A x = <| run := finished A x; interest := K ∅ |>
End

Definition never2_def:
  never2 = <| run := never; interest := K ∅ |>
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
  rw[comp2_eq, suspended2_def, emit2_def, never2_def, FUN_EQ_THM]
  \\ simp[suspended_emit_NIL]
QED

Theorem suspended2_never2:
  suspended2 never2 [w] = never2
Proof
  rw[comp2_eq, suspended2_def, never2_def, never_def]
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
