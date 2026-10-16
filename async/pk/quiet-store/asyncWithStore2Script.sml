(*
  with_store at Level 2 (design/37 §3; design/33 §4's amendment).

  with_store δ s0 m (asyncWithStore) answers m's Kv queries itself, in the
  NEXT snapshot.  While an answer is pending, a snapshot in which nothing
  m declared is ready still matters to m: it carries the store's answers.
  So with_store2 declares one extra event, now, while a query is pending:

     with_store2 now δ s0 c: run      = with_store δ s0 c.run
                             interest = {now} (if a Kv query is pending)
                                        ∪ c's interest on the inner history

  The loop reports now ready in every snapshot (design/37 §4), so it never
  sleeps with answers owed.  Plain quiet fails for with_store2 (a
  snapshot without now, taken while a query is pending, cannot be
  deleted); it holds for the loop's snapshots, those reporting now
  (quiet_on).

  MAIN: erase_with_store2, finite_with_store2, quiet_with_store2.
*)
Theory asyncWithStore2
Ancestors
  pair list rich_list arithmetic option pred_set
  asyncCore asyncLevel1 asyncLevel2 asyncWithStore
Libs
  BasicProvers

(* m has emitted Kv queries in the last round of the inner history: their
   answers come with the next snapshot *)
Definition kv_pending_def:
  kv_pending δ s0 m h ⇔ queries (new_actions (log_of m) (inner_hist δ s0 m h)) ≠ []
End

Definition with_store2_def:
  with_store2 now δ s0 c =
    <| run := with_store δ s0 c.run;
       interest := λh. (if kv_pending δ s0 c.run h then {now} else ∅) ∪
                       c.interest (inner_hist δ s0 c.run h) |>
End

(* quiet, for the snapshots satisfying R only *)
Definition quiet_on_def:
  quiet_on R c ⇔
    ∀h s h'.
      R s ∧ (c.run h).result = NONE ∧ new_actions (log_of c.run) h = [] ∧
      s.results = [] ∧ DISJOINT (c.interest h) s.ready ⇒
      c.run (h ++ [s] ++ h') = c.run (h ++ h') ∧
      c.interest (h ++ [s] ++ h') = c.interest (h ++ h')
End

(* quiet is quiet_on for every R: the existing servers are instances *)
Theorem quiet_quiet_on:
  quiet c ⇒ quiet_on R c
Proof
  rw[quiet_def, quiet_on_def]
QED

(* MAIN: the Level 1 computation underneath is with_store's *)
Theorem erase_with_store2:
  erase (with_store2 now δ s0 c) = with_store δ s0 (erase c)
Proof
  simp[erase_def, with_store2_def]
QED

(* MAIN: finitely many declared events *)
Theorem finite_with_store2:
  (∀h. FINITE (c.interest h)) ⇒ ∀h. FINITE ((with_store2 now δ s0 c).interest h)
Proof
  rw[with_store2_def] >> rw[]
QED

(* ------------------------------------------------------------------------
   Deleting a snapshot that carries nothing for m
   ------------------------------------------------------------------------ *)

Theorem acts_NIL[local]:
  ∀acts. socks acts = [] ∧ queries acts = [] ⇒ acts = []
Proof
  Induct >> simp[] >> Cases >> simp[]
QED

Theorem merge_NIL[local]:
  merge [] rs ans = []
Proof
  simp[merge_def]
QED

(* If m is quiet at the inner history ih and s carries nothing for it,
   splicing s in changes neither m's run nor its new actions, at any
   extension k *)
Theorem quiet_splice[local]:
  ∀c ih s.
  quiet c ∧ (c.run ih).result = NONE ∧ new_actions (log_of c.run) ih = [] ∧
  s.results = [] ∧ DISJOINT (c.interest ih) s.ready ⇒
  ∀k. c.run (ih ++ [s] ++ k) = c.run (ih ++ k) ∧
      c.interest (ih ++ [s] ++ k) = c.interest (ih ++ k) ∧
      new_actions (log_of c.run) (ih ++ [s] ++ k) = new_actions (log_of c.run) (ih ++ k)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  ‘∀k. c.run (ih ++ [s] ++ k) = c.run (ih ++ k) ∧
       c.interest (ih ++ [s] ++ k) = c.interest (ih ++ k)’
    by (gen_tac >> qpat_x_assum ‘quiet c’ (irule o REWRITE_RULE[quiet_def]) >> simp[]) >>
  simp[] >>
  Cases_on ‘k’ using SNOC_CASES
  >- (simp[new_actions_SNOC, log_of_def] >>
      first_x_assum (qspec_then ‘[]’ mp_tac) >> simp[] >> strip_tac >>
      qpat_x_assum ‘new_actions _ ih = []’ mp_tac >> simp[DROP_LENGTH_NIL])
  >> REWRITE_TAC[GSYM APPEND_ASSOC, SNOC_APPEND] >>
  ONCE_REWRITE_TAC[APPEND_ASSOC] >>
  simp[new_actions_SNOC, log_of_def] >>
  first_assum (qspec_then ‘l’ mp_tac) >>
  first_x_assum (qspec_then ‘l ++ [x]’ mp_tac) >>
  simp[]
QED

(* The inner histories, with s spliced in and without: s reaches m with
   no results (the inner snapshot has the store's result type) *)
Theorem inner_hist_splice[local]:
  quiet c ∧ (c.run (inner_hist δ s0 c.run h)).result = NONE ∧
  new_actions (log_of c.run) (inner_hist δ s0 c.run h) = [] ∧
  s.results = [] ∧ DISJOINT (c.interest (inner_hist δ s0 c.run h)) s.ready ⇒
  ∀h'. ∃k. inner_hist δ s0 c.run (h ++ [s] ++ h') =
             inner_hist δ s0 c.run h ++ [s with results := []] ++ k ∧
           inner_hist δ s0 c.run (h ++ h') = inner_hist δ s0 c.run h ++ k
Proof
  strip_tac >>
  ‘∀k. c.run (inner_hist δ s0 c.run h ++ [s with results := []] ++ k) =
         c.run (inner_hist δ s0 c.run h ++ k) ∧
       c.interest (inner_hist δ s0 c.run h ++ [s with results := []] ++ k) =
         c.interest (inner_hist δ s0 c.run h ++ k) ∧
       new_actions (log_of c.run) (inner_hist δ s0 c.run h ++ [s with results := []] ++ k) =
         new_actions (log_of c.run) (inner_hist δ s0 c.run h ++ k)’
    by (irule quiet_splice >> simp[]) >>
  Induct_on ‘h'’ using SNOC_INDUCT
  >- (qexists_tac ‘[]’ >> simp[inner_hist_SNOC, merge_NIL])
  >> rpt strip_tac >>
  REWRITE_TAC[SNOC_APPEND, APPEND_ASSOC] >>
  simp[inner_hist_SNOC] >>
  qpat_x_assum ‘∃k. _’ strip_assume_tac >>
  qpat_x_assum ‘inner_hist _ _ _ (h ++ [s] ++ h') = _’ (fn th => REWRITE_TAC[th]) >>
  qpat_x_assum ‘inner_hist _ _ _ (h ++ h') = _’ (fn th => REWRITE_TAC[th]) >>
  first_x_assum (qspec_then ‘k’ strip_assume_tac) >>
  qexists_tac ‘k ++ [x with results :=
                       merge (new_actions (log_of c.run) (inner_hist δ s0 c.run h ++ k))
                             x.results
                             (store_answers δ s0 (c.run (inner_hist δ s0 c.run h ++ k)).actions
                                (new_actions (log_of c.run) (inner_hist δ s0 c.run h ++ k)))]’ >>
  gvs[]
QED

(* MAIN: with_store2 is quiet for every snapshot that reports now, if the
   inner computation is well-formed and quiet *)
Theorem quiet_with_store2:
  wf c.run ∧ quiet c ⇒ quiet_on (λs. now ∈ s.ready) (with_store2 now δ s0 c)
Proof
  rw[quiet_on_def, with_store2_def] >>
  gvs[with_store_def, new_actions_with_store] >>
  ‘¬kv_pending δ s0 c.run h’ by (strip_tac >> gvs[IN_DISJOINT] >> metis_tac[]) >>
  qabbrev_tac ‘ih = inner_hist δ s0 c.run h’ >>
  ‘new_actions (log_of c.run) ih = []’
    by (irule acts_NIL >> gvs[kv_pending_def, Abbr ‘ih’]) >>
  ‘DISJOINT (c.interest ih) s.ready’ by gvs[IN_DISJOINT] >>
  ‘∃k. inner_hist δ s0 c.run (h ++ [s] ++ h') = ih ++ [s with results := []] ++ k ∧
       inner_hist δ s0 c.run (h ++ h') = ih ++ k’
    by (simp[Abbr ‘ih’] >> irule inner_hist_splice >> gvs[]) >>
  ‘∀k. c.run (ih ++ [s with results := []] ++ k) = c.run (ih ++ k) ∧
       c.interest (ih ++ [s with results := []] ++ k) = c.interest (ih ++ k) ∧
       new_actions (log_of c.run) (ih ++ [s with results := []] ++ k) =
         new_actions (log_of c.run) (ih ++ k)’
    by (irule quiet_splice >> simp[]) >>
  simp[kv_pending_def]
QED
