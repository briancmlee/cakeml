(*
  Model-side lemmas for the actions/responses CF layer (asyncCfActProg).

  The CakeML representation (see async/design/05-cf-actions.md) polls a
  computation once per round and gets back (actions, residual).  The
  residual after a poll with snapshot w implements the model computation
  "m with w delivered", which the model calls  suspended m [w].

  This theory states, for each primitive and for bind, what
  suspended (...) [w] is: one lemma per implementation step.  Only two
  small new notions are needed, both used by bind once its first part has
  finished:
   - prepend A g: g, with the actions A emitted before its first round;
   - skipping k g: g, with the first k results of its first snapshot removed.
*)
Theory asyncCfActModel
Ancestors
  list rich_list asyncCore asyncLevel1 asyncChoose
Libs
  preamble

(* ------------------------------------------------------------------------
   Two helpers for bind's finished case
   ------------------------------------------------------------------------ *)

(* g, with the actions A emitted at the start of its first round *)
Definition prepend_def:
  prepend A g h = <| actions := A ++ (g h).actions; result := (g h).result |>
End

(* g, with the first k results of its first snapshot removed: the
   responses that belong to someone else (cf. skip_results in bind) *)
Definition skipping_def:
  skipping k g h = g (skip_results k h)
End

(* One snapshot with its first k results removed *)
Definition skip_snap_def:
  skip_snap k (s : ('e,'r) snapshot) = s with results := DROP k s.results
End

(* ------------------------------------------------------------------------
   Basic facts about "one poll later"
   ------------------------------------------------------------------------ *)

Theorem suspended_one:
  suspended m [w] h =
    <| actions := DROP (LENGTH (m []).actions) (m (w :: h)).actions;
       result := (m (w :: h)).result |>
Proof
  simp[suspended_def, resume_def]
QED

(* The actions of the first poll of  suspended m [w]  are the model's
   new actions of m in round 1 *)
Theorem suspended_one_actions_NIL:
  (suspended m [w] []).actions = new_actions (log_of m) [w]
Proof
  simp[suspended_one, new_actions_def, log_of_def]
QED

(* A finished computation reports no further actions *)
Theorem suspended_finished_one:
  suspended (finished A x) [w] = finished [] x
Proof
  simp[FUN_EQ_THM, suspended_one, finished_def, DROP_LENGTH_NIL]
QED

Theorem suspended_wait_SOME:
  p w = SOME a ⇒ suspended (wait p) [w] = finished [] a
Proof
  simp[FUN_EQ_THM, suspended_one, finished_def, wait_def, first_some_def]
QED

Theorem suspended_wait_NONE:
  p w = NONE ⇒ suspended (wait p) [w] = wait p
Proof
  simp[FUN_EQ_THM, suspended_one, wait_def, first_some_def]
QED

(* emit a, polled with a snapshot carrying its response r *)
Theorem suspended_emit_CONS:
  w.results = r :: rs ⇒ suspended (emit a) [w] = finished [] r
Proof
  simp[FUN_EQ_THM, suspended_one, finished_def, emit_def]
QED

(* emit a, polled with a snapshot without a response: it never finishes *)
Theorem suspended_emit_NIL:
  w.results = [] ⇒ suspended (emit a) [w] = never
Proof
  simp[FUN_EQ_THM, suspended_one, never_def, emit_def, wait_def] >>
  strip_tac >> Induct >> simp[first_some_def]
QED

Theorem suspended_prepend:
  suspended (prepend A g) [w] = suspended g [w]
Proof
  simp[FUN_EQ_THM, suspended_one, prepend_def, DROP_APPEND, DROP_LENGTH_NIL]
QED

Theorem suspended_skipping:
  suspended (skipping k g) [w] = suspended g [skip_snap k w]
Proof
  simp[FUN_EQ_THM, suspended_one, skipping_def, skip_results_def, skip_snap_def]
QED

Theorem prepend_finished:
  prepend A (finished B x) = finished (A ++ B) x
Proof
  simp[FUN_EQ_THM, prepend_def, finished_def]
QED

Theorem skipping_finished:
  skipping k (finished B x) = finished B x
Proof
  simp[FUN_EQ_THM, skipping_def, finished_def]
QED

Theorem prepend_NIL_poll[simp]:
  (prepend A g []).actions = A ++ (g []).actions ∧
  (prepend A g []).result = (g []).result
Proof
  simp[prepend_def]
QED

Theorem skipping_NIL_poll[simp]:
  skipping k g [] = g []
Proof
  simp[skipping_def, skip_results_def]
QED

(* ------------------------------------------------------------------------
   bind
   ------------------------------------------------------------------------ *)

(* A bind whose first part has already finished (before its first poll)
   is the continuation, after the first part's actions, with the responses
   to those actions removed from its first snapshot. *)
Theorem bind_finished:
  bind (finished A x) f = prepend A (skipping (LENGTH A) (f x))
Proof
  simp[FUN_EQ_THM, bind_def, prepend_def, skipping_def, finished_def,
       Once first_prefix_def, new_actions_def, log_of_def]
QED

Theorem bind_NIL_running:
  (m []).result = NONE ⇒
  (bind m f []).actions = (m []).actions ∧ (bind m f []).result = NONE
Proof
  strip_tac >> ONCE_REWRITE_TAC[bind_def] >> ONCE_REWRITE_TAC[first_prefix_def] >> gvs[]
QED

(* Polling a bind whose first part is still running polls the first part.
   (wf is needed because the residual only reports actions after those of
   the first poll, and bind's log is m's log followed by the continuation's.) *)
Theorem suspended_bind:
  wf m ∧ (m []).result = NONE ⇒
  suspended (bind m f) [w] = bind (suspended m [w]) f
Proof
  strip_tac >> simp[FUN_EQ_THM] >> qx_gen_tac ‘h’ >>
  ‘first_prefix (λp. (m p).result ≠ NONE) (w :: h) =
   OPTION_MAP SUC (first_prefix (λp. (suspended m [w] p).result ≠ NONE) h)’
    by simp[Once first_prefix_def, suspended_one] >>
  simp[suspended_one, bind_NIL_running] >>
  simp[bind_def] >>
  Cases_on ‘first_prefix (λp. (suspended m [w] p).result ≠ NONE) h’ >>
  gvs[suspended_one] >>
  rename1 ‘TAKE n h’ >>
  ‘new_actions (log_of (suspended m [w])) (TAKE n h) =
   new_actions (log_of m) (w :: TAKE n h)’
    by (drule_then (qspecl_then [‘[w]’, ‘TAKE n h’] mp_tac)
          new_actions_suspended >> simp[]) >>
  gvs[suspended_one] >>
  irule DROP_APPEND1 >>
  irule IS_PREFIX_LENGTH >> irule wf_actions_grow >> simp[]
QED

(* ------------------------------------------------------------------------
   Iterated polls: the residual after the snapshots r is  suspended m r
   ------------------------------------------------------------------------ *)

Theorem suspended_suspended_one:
  wf m ⇒ suspended (suspended m r) [w] = suspended m (r ++ [w])
Proof
  strip_tac >> Cases_on ‘r’ using SNOC_CASES >- simp[] >>
  rename1 ‘SNOC s p’ >>
  simp[FUN_EQ_THM, suspended_one, SNOC_APPEND, suspended_SNOC, resume_def,
       DROP_DROP_T] >>
  rpt strip_tac >>
  ‘(m p).actions ≼ (m (p ++ [s])).actions’ by simp[wf_SNOC_actions] >>
  imp_res_tac IS_PREFIX_LENGTH >>
  simp[] >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND]
QED
