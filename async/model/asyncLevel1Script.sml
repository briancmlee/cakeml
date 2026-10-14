(*
  Level 1 of the async model: plain polling.

  A computation is a function from histories (snapshot lists, oldest first)
  to outcomes whose result is an option:

     m : ('e,'r) snapshot list -> ('act, 'a option) outcome

  (m h).result = SOME x  means m has finished with x after history h;
  (m h).actions          is everything m has emitted so far.

  Conventions (see async/design/01-semantics.md):
  - Rounds.  Polling with history h is round LENGTH h.  Actions emitted in
    round n are performed by the world before snapshot n+1, whose `results`
    field holds their responses, in emission order.
  - bind.  When m finishes in round n, the continuation starts in the same
    round n (so pure steps cost nothing), but only sees snapshots from n+1
    on.  A `wait` or `emit` inside the continuation therefore needs a fresh
    snapshot to finish; this is what makes loops well-defined.
  - both/choose.  The two sides see the same snapshots; within a round the
    left side's actions come first; each side only gets the responses to
    its own actions.
*)
Theory asyncLevel1
Ancestors
  pair list rich_list pred_set arithmetic option asyncCore
Libs
  BasicProvers

(* ------------------------------------------------------------------------
   Well-formedness
   ------------------------------------------------------------------------ *)

(* The action log of a computation, as a function of the history *)
Definition log_of_def:
  log_of m h = (m h).actions
End

(* A computation is well-formed if, whenever one more snapshot arrives,
   - its action log only grows, and
   - once it has finished, nothing changes any more (same result, no new
     actions). *)
Definition wf_def:
  wf m ⇔
    ∀h s. (m h).actions ≼ (m (h ++ [s])).actions ∧
          ((m h).result ≠ NONE ⇒ m (h ++ [s]) = m h)
End

Theorem wf_SNOC_actions:
  wf m ⇒ (m h).actions ≼ (m (h ++ [s])).actions
Proof
  rw[wf_def]
QED

Theorem wf_SNOC_finished:
  wf m ∧ (m h).result ≠ NONE ⇒ m (h ++ [s]) = m h
Proof
  rw[wf_def]
QED

(* MAIN: the action log of a well-formed computation only grows *)
Theorem wf_actions_grow:
  wf m ∧ h1 ≼ h2 ⇒ (m h1).actions ≼ (m h2).actions
Proof
  rpt strip_tac
  >> qpat_x_assum ‘_ ≼ _’ (strip_assume_tac o REWRITE_RULE[IS_PREFIX_APPEND])
  >> gvs[] >> rename1 ‘h1 ++ ext’
  >> qid_spec_tac ‘ext’ >> Induct_on ‘ext’ using SNOC_INDUCT
  >> rw[SNOC_APPEND]
  >> irule IS_PREFIX_TRANS
  >> qexists_tac ‘(m (h1 ++ ext)).actions’
  >> simp[] >> metis_tac[wf_SNOC_actions, APPEND_ASSOC]
QED

(* MAIN: once a well-formed computation has finished, it stays finished
   with the same result and the same actions *)
Theorem wf_finished_stays:
  wf m ∧ (m h1).result = SOME x ∧ h1 ≼ h2 ⇒ m h2 = m h1
Proof
  rpt strip_tac
  >> qpat_x_assum ‘_ ≼ _’ (strip_assume_tac o REWRITE_RULE[IS_PREFIX_APPEND])
  >> gvs[] >> rename1 ‘h1 ++ ext’
  >> qid_spec_tac ‘ext’ >> Induct_on ‘ext’ using SNOC_INDUCT
  >> rw[SNOC_APPEND]
  >> metis_tac[wf_SNOC_finished, APPEND_ASSOC, NOT_NONE_SOME]
QED

(* If a well-formed computation has not finished, it had not finished on
   any shorter history either *)
Theorem wf_unfinished_before:
  wf m ∧ (m h).result = NONE ∧ h1 ≼ h ⇒ (m h1).result = NONE
Proof
  rw[] >> Cases_on ‘(m h1).result’ >> simp[]
  >> ‘m h = m h1’ by metis_tac[wf_finished_stays] >> gvs[]
QED

(* m first finishes, with result x, exactly after the snapshots h *)
Definition first_done_def:
  first_done m h x ⇔
    (m h).result = SOME x ∧ ∀n. n < LENGTH h ⇒ (m (TAKE n h)).result = NONE
End

Theorem first_prefix_done_SOME:
  first_prefix (λp. (m p).result ≠ NONE) h = SOME n ⇔
    n ≤ LENGTH h ∧ ∃x. first_done m (TAKE n h) x
Proof
  rw[first_prefix_SOME, first_done_def]
  >> eq_tac >> rw[]
  >- (Cases_on ‘(m (TAKE n h)).result’ >> gvs[]
      >> rw[] >> gvs[LENGTH_TAKE, TAKE_TAKE])
  >> gvs[LENGTH_TAKE]
  >> first_x_assum drule >> simp[TAKE_TAKE]
QED

Theorem first_prefix_done_APPEND:
  first_done m h1 x ⇒
  first_prefix (λp. (m p).result ≠ NONE) (h1 ++ h2) = SOME (LENGTH h1)
Proof
  rw[first_prefix_done_SOME, TAKE_LENGTH_APPEND] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Primitives
   ------------------------------------------------------------------------ *)

(* return x: finished from the start, with x, having done nothing *)
Definition return_def:
  return x h = <| actions := []; result := SOME x |>
End

(* The first SOME that p gives on a list of snapshots *)
Definition first_some_def:
  first_some p [] = NONE ∧
  first_some p (s :: rest) =
    case p s of
      SOME x => SOME x
    | NONE => first_some p rest
End

(* wait p: finishes at the first snapshot s with p s = SOME x, with x.
   Never finishes on the empty history: waiting always takes a snapshot. *)
Definition wait_def:
  wait p h = <| actions := []; result := first_some p h |>
End

(* emit a: emits a immediately and finishes at the next snapshot, with the
   response to a (the first of the results routed to it). *)
Definition emit_def:
  emit a h =
    <| actions := [a];
       result := case h of [] => NONE | s :: _ => oHD s.results |>
End

(* ------------------------------------------------------------------------
   Combinators
   ------------------------------------------------------------------------ *)

(* bind m f: run m; when it finishes with x (after the first n snapshots),
   run f x on the rest of the history.  The continuation starts in the same
   round, but the responses to m's actions of that round are not passed on. *)
Definition bind_def:
  bind m f h =
    case first_prefix (λp. (m p).result ≠ NONE) h of
      NONE => <| actions := (m h).actions; result := NONE |>
    | SOME n =>
        let hm = TAKE n h;
            k = LENGTH (new_actions (log_of m) hm);
            next = f (THE (m hm).result) (skip_results k (DROP n h))
        in
          <| actions := (m hm).actions ++ next.actions;
             result := next.result |>
End

(* map f m: m, with f applied to its result *)
Definition map_def:
  map f m h = <| actions := (m h).actions; result := OPTION_MAP f (m h).result |>
End

(* The snapshots each side sees when two computations run side by side *)
Definition left_view_def:
  left_view m1 m2 h = FST (par_views (log_of m1) (log_of m2) h)
End

Definition right_view_def:
  right_view m1 m2 h = SND (par_views (log_of m1) (log_of m2) h)
End

(* The actions of two computations running side by side: in each round,
   the left side's new actions, then the right side's. *)
Definition par_log_def:
  par_log m1 m2 h = par_actions (log_of m1) (log_of m2) h
End

(* both m1 m2: run m1 and m2 side by side; finish when both have finished,
   with both results. *)
Definition both_def:
  both m1 m2 h =
    <| actions := par_log m1 m2 h;
       result :=
         case ((m1 (left_view m1 m2 h)).result,
               (m2 (right_view m1 m2 h)).result) of
           (SOME x, SOME y) => SOME (x, y)
         | _ => NONE |>
End

(* race m1 m2: run side by side; the result is m1's if it has one, else
   m2's.  Not well-formed on its own (it keeps going after finishing). *)
Definition race_def:
  race m1 m2 h =
    <| actions := par_log m1 m2 h;
       result :=
         case (m1 (left_view m1 m2 h)).result of
           SOME x => SOME x
         | NONE => (m2 (right_view m1 m2 h)).result |>
End

(* choose m1 m2: run side by side; finish as soon as either has finished,
   preferring m1 if both finish in the same round.  The other side is
   abandoned: it emits nothing more and its pending responses are lost. *)
Definition choose_def:
  choose m1 m2 = freeze (λout. out.result ≠ NONE) (race m1 m2)
End

(* A computation that never finishes and does nothing *)
Definition never_def:
  never = wait (λs. NONE)
End

(* ------------------------------------------------------------------------
   Basic facts about histories
   ------------------------------------------------------------------------ *)

Theorem TAKE_prefix[local]:
  TAKE n l ≼ l
Proof
  simp[IS_PREFIX_APPEND] >> metis_tac[TAKE_DROP]
QED

Theorem outcome_eta[local,simp]:
  <| actions := out.actions; result := out.result |> = out
Proof
  simp[outcome_component_equality]
QED

(* Every history either never sees m finish, or splits at the point where
   m first finished. *)
Theorem history_split:
  ∀m h.
    (∀n. n ≤ LENGTH h ⇒ (m (TAKE n h)).result = NONE) ∨
    ∃h1 h2 x. h = h1 ++ h2 ∧ first_done m h1 x
Proof
  rpt gen_tac
  >> Cases_on ‘first_prefix (λp. (m p).result ≠ NONE) h’
  >- gvs[first_prefix_NONE]
  >> gvs[first_prefix_done_SOME]
  >> disj2_tac >> qexistsl_tac [‘TAKE x h’, ‘DROP x h’] >> simp[]
  >> metis_tac[]
QED

Theorem first_done_finished:
  first_done m h x ⇒ (m h).result = SOME x
Proof
  rw[first_done_def]
QED

Theorem first_done_NIL:
  first_done m [] x ⇔ (m []).result = SOME x
Proof
  rw[first_done_def]
QED

(* ------------------------------------------------------------------------
   bind: characterisation
   ------------------------------------------------------------------------ *)

(* MAIN: until m finishes, bind m f behaves like m (with no result) *)
Theorem bind_running:
  (∀n. n ≤ LENGTH h ⇒ (m (TAKE n h)).result = NONE) ⇒
  bind m f h = <| actions := (m h).actions; result := NONE |>
Proof
  rw[bind_def]
  >> ‘first_prefix (λp. (m p).result ≠ NONE) h = NONE’
       by simp[first_prefix_NONE]
  >> simp[]
QED

Theorem bind_running_wf:
  wf m ∧ (m h).result = NONE ⇒
  bind m f h = <| actions := (m h).actions; result := NONE |>
Proof
  rw[] >> irule bind_running >> rw[]
  >> irule wf_unfinished_before >> metis_tac[TAKE_prefix]
QED

(* MAIN: once m has first finished with x, after the snapshots h1, bind m f
   continues as f x on the remaining snapshots h2, except that the
   responses to m's actions of its last round are not passed to f x. *)
Theorem bind_continues:
  first_done m h1 x ⇒
  ∀f h2.
  bind m f (h1 ++ h2) =
    let next = f x (skip_results (LENGTH (new_actions (log_of m) h1)) h2) in
      <| actions := (m h1).actions ++ next.actions; result := next.result |>
Proof
  rpt strip_tac >> drule first_prefix_done_APPEND
  >> disch_then (qspec_then ‘h2’ assume_tac)
  >> simp[bind_def, TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND]
  >> gvs[first_done_def]
QED

Theorem bind_continues_actions:
  first_done m h1 x ⇒
  ∀f h2.
  (bind m f (h1 ++ h2)).actions =
    (m h1).actions ++
    (f x (skip_results (LENGTH (new_actions (log_of m) h1)) h2)).actions
Proof
  rpt strip_tac >> drule bind_continues >> simp[]
QED

Theorem bind_continues_result:
  first_done m h1 x ⇒
  ∀f h2.
  (bind m f (h1 ++ h2)).result =
    (f x (skip_results (LENGTH (new_actions (log_of m) h1)) h2)).result
Proof
  rpt strip_tac >> drule bind_continues >> simp[]
QED

(* Before m's first finishing point, bind has not finished *)
Theorem bind_before_first_done:
  first_done m h1 x ∧ n < LENGTH h1 ⇒
  bind m f (TAKE n h1) = <| actions := (m (TAKE n h1)).actions; result := NONE |>
Proof
  rw[first_done_def] >> irule bind_running
  >> rw[TAKE_TAKE_MIN, LENGTH_TAKE_EQ] >> gvs[]
  >> first_x_assum irule >> rw[MIN_DEF]
QED

(* If m first finished after h1, and then f x first finished after
   (the routed version of) q1, then bind m f first finished after h1 ++ q1 *)
Theorem first_done_bind:
  first_done m h1 x ∧
  first_done (f x) (skip_results (LENGTH (new_actions (log_of m) h1)) q1) y ⇒
  first_done (bind m f) (h1 ++ q1) y
Proof
  rw[] >> simp[first_done_def]
  >> qpat_x_assum ‘first_done m _ _’
       (fn th => assume_tac th >> assume_tac (MATCH_MP bind_continues_result th))
  >> conj_tac
  >- gvs[first_done_def]
  >> rw[]
  >> Cases_on ‘n < LENGTH h1’
  >- (simp[TAKE_APPEND1] >> drule_all bind_before_first_done >> simp[])
  >> ‘TAKE n (h1 ++ q1) = h1 ++ TAKE (n - LENGTH h1) q1’
       by simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG]
  >> simp[GSYM TAKE_skip_results]
  >> gvs[first_done_def]
QED

(* In the rounds after m finished, bind's new actions are f x's *)
Theorem new_actions_bind_after:
  first_done m h1 x ∧ q ≠ [] ⇒
  new_actions (log_of (bind m f)) (h1 ++ q) =
  new_actions (log_of (f x))
              (skip_results (LENGTH (new_actions (log_of m) h1)) q)
Proof
  rw[]
  >> Cases_on ‘q’ using SNOC_CASES >> gvs[SNOC_APPEND]
  >> rename1 ‘h1 ++ q ++ [s]’
  >> ‘∃s'. skip_results (LENGTH (new_actions (log_of m) h1)) (q ++ [s]) =
           skip_results (LENGTH (new_actions (log_of m) h1)) q ++ [s']’
       by (Cases_on ‘q’ >> simp[skip_results_def])
  >> ‘∀h2. (bind m f (h1 ++ h2)).actions = (m h1).actions ++
          (f x (skip_results (LENGTH (new_actions (log_of m) h1)) h2)).actions’
       by metis_tac[bind_continues_actions]
  >> first_assum (qspec_then ‘q ++ [s]’ mp_tac)
  >> first_x_assum (qspec_then ‘q’ mp_tac)
  >> simp[new_actions_SNOC, log_of_def, DROP_APPEND, DROP_LENGTH_NIL]
QED

(* In the round where m finishes, bind's new actions are m's, then those
   f x emits straight away *)
Theorem new_actions_bind_at:
  wf m ∧ first_done m h1 x ⇒
  new_actions (log_of (bind m f)) h1 =
  new_actions (log_of m) h1 ++ (f x []).actions
Proof
  rw[]
  >> drule_then (qspecl_then [‘f’, ‘[]’] mp_tac) bind_continues_actions
  >> simp[skip_results_def] >> strip_tac
  >> Cases_on ‘h1’ using SNOC_CASES
  >- simp[new_actions_NIL, log_of_def]
  >> gvs[SNOC_APPEND] >> rename1 ‘h0 ++ [s]’
  >> simp[new_actions_SNOC, log_of_def]
  >> ‘bind m f h0 = <| actions := (m h0).actions; result := NONE |>’
       by (‘h0 = TAKE (LENGTH h0) (h0 ++ [s])’ by simp[TAKE_LENGTH_APPEND]
           >> pop_assum SUBST1_TAC
           >> irule bind_before_first_done >> simp[] >> metis_tac[])
  >> simp[]
  >> ‘(m h0).actions ≼ (m (h0 ++ [s])).actions’ by metis_tac[wf_SNOC_actions]
  >> gvs[IS_PREFIX_APPEND, DROP_APPEND, DROP_LENGTH_APPEND]
  >> ‘LENGTH (m h0).actions − (LENGTH l + LENGTH (m h0).actions) = 0’
       by simp[]
  >> simp[]
QED

Theorem bind_running_TAKE:
  (∀n. n ≤ LENGTH h ⇒ (m (TAKE n h)).result = NONE) ⇒
  ∀f n. bind m f (TAKE n h) =
        <| actions := (m (TAKE n h)).actions; result := NONE |>
Proof
  rw[] >> irule bind_running
  >> rw[TAKE_TAKE_MIN, LENGTH_TAKE_EQ] >> first_x_assum irule
  >> gvs[MIN_DEF] >> rw[]
QED

(* If f x never finishes on what it is shown, then neither does bind m f *)
Theorem bind_unfinished_after:
  first_done m h1 x ∧
  (∀n. n ≤ LENGTH h2 ⇒
       (f x (TAKE n (skip_results (LENGTH (new_actions (log_of m) h1)) h2))).result
       = NONE) ⇒
  ∀n. n ≤ LENGTH (h1 ++ h2) ⇒ (bind m f (TAKE n (h1 ++ h2))).result = NONE
Proof
  rw[]
  >> Cases_on ‘n < LENGTH h1’
  >- (simp[TAKE_APPEND1] >> drule_all bind_before_first_done >> simp[])
  >> ‘TAKE n (h1 ++ h2) = h1 ++ TAKE (n - LENGTH h1) h2’
       by simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG]
  >> simp[]
  >> drule_then (qspecl_then [‘f’, ‘TAKE (n - LENGTH h1) h2’] mp_tac) bind_continues_result
  >> simp[GSYM TAKE_skip_results]
QED

(* ------------------------------------------------------------------------
   Monad laws.  These are equalities of computations (functions), not just
   equivalences.  Right identity and associativity need m to be
   well-formed.
   ------------------------------------------------------------------------ *)

(* MAIN: monad law, left identity *)
Theorem bind_left_identity:
  bind (return x) f = f x
Proof
  rw[FUN_EQ_THM, bind_def, return_def, Once first_prefix_def,
     new_actions_NIL, log_of_def]
QED

(* MAIN: monad law, right identity *)
Theorem bind_right_identity:
  wf m ⇒ bind m return = m
Proof
  rw[FUN_EQ_THM] >> rename1 ‘bind m return h’
  >> Cases_on ‘(m h).result’
  >- simp[bind_running_wf, outcome_component_equality]
  >> qspecl_then [‘m’, ‘h’] strip_assume_tac history_split
  >- (first_x_assum (qspec_then ‘LENGTH h’ mp_tac) >> simp[TAKE_LENGTH_ID])
  >> gvs[]
  >> qpat_assum ‘first_done _ _ _’ (fn th => simp[MATCH_MP bind_continues th])
  >> simp[return_def]
  >> ‘m (h1 ++ h2) = m h1’
       by (irule wf_finished_stays >> gvs[first_done_def]
           >> metis_tac[IS_PREFIX_APPEND3])
  >> simp[outcome_component_equality] >> gvs[first_done_def]
QED

(* MAIN: monad law, associativity *)
Theorem bind_assoc:
  wf m ⇒ bind (bind m f) g = bind m (λx. bind (f x) g)
Proof
  rw[FUN_EQ_THM] >> rename1 ‘_ h = _ h’
  >> qspecl_then [‘m’, ‘h’] strip_assume_tac history_split
  >- (* m does not finish within h: neither side finishes *)
     (‘bind m (λx. bind (f x) g) h =
         <| actions := (m h).actions; result := NONE |>’
        by (irule bind_running >> simp[])
      >> ‘bind m f h = <| actions := (m h).actions; result := NONE |>’
        by (irule bind_running >> simp[])
      >> ‘bind (bind m f) g h =
            <| actions := (bind m f h).actions; result := NONE |>’
        by (irule bind_running >> rw[]
            >> qpat_assum ‘∀n. _’
                 (fn th => simp[MATCH_MP bind_running_TAKE th]))
      >> simp[])
  (* m first finishes after h1, with x *)
  >> gvs[]
  >> qpat_assum ‘first_done m h1 x’ (fn th => simp[MATCH_MP bind_continues th])
  >> qspecl_then [‘f x’, ‘skip_results (LENGTH (new_actions (log_of m) h1)) h2’]
       strip_assume_tac history_split
  >- (* f x does not finish within what it sees *)
     (‘bind (f x) g (skip_results (LENGTH (new_actions (log_of m) h1)) h2) =
         <| actions :=
              (f x (skip_results (LENGTH (new_actions (log_of m) h1)) h2)).actions;
            result := NONE |>’
        by (irule bind_running >> first_assum ACCEPT_TAC)
      >> ‘bind (bind m f) g (h1 ++ h2) =
            <| actions := (bind m f (h1 ++ h2)).actions; result := NONE |>’
        by (irule bind_running >> rpt strip_tac >> irule bind_unfinished_after
            >> conj_tac >- simp[]
            >> qexists_tac ‘x’ >> fs[])
      >> qpat_assum ‘first_done m h1 x’
           (fn th => simp[MATCH_MP bind_continues_actions th]))
  (* f x first finishes after p1, with y *)
  >> rename1 ‘first_done (f x) p1 y’ >> rename1 ‘_ = p1 ++ p2’
  >> qabbrev_tac ‘k = LENGTH (new_actions (log_of m) h1)’
  >> qabbrev_tac ‘j = LENGTH p1’
  >> ‘TAKE j (skip_results k h2) = p1 ∧ DROP j (skip_results k h2) = p2’
       by (qpat_x_assum ‘_ = p1 ++ p2’ (fn th => simp[th])
           >> simp[Abbr ‘j’, TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND])
  >> ‘first_done (bind m f) (h1 ++ TAKE j h2) y’
       by (irule first_done_bind >> qexists_tac ‘x’
           >> gvs[TAKE_skip_results, Abbr ‘k’])
  >> ‘h1 ++ h2 = (h1 ++ TAKE j h2) ++ DROP j h2’ by simp[]
  >> pop_assum SUBST1_TAC
  >> qpat_assum ‘first_done (bind m f) _ _’
       (fn th => simp[MATCH_MP bind_continues th])
  >> qpat_assum ‘skip_results k h2 = _’ (fn th => REWRITE_TAC[th])
  >> qpat_assum ‘first_done (f x) p1 y’
       (fn th => simp[MATCH_MP bind_continues th])
  >> qpat_assum ‘first_done m h1 x’
       (fn th => simp[MATCH_MP bind_continues_actions th])
  >> ‘skip_results k (TAKE j h2) = p1’ by metis_tac[TAKE_skip_results]
  >> pop_assum SUBST1_TAC
  (* what is left: g is shown the same snapshots on both sides *)
  >> qsuff_tac
       ‘skip_results (LENGTH (new_actions (log_of (bind m f)) (h1 ++ TAKE j h2)))
                     (DROP j h2) =
        skip_results (LENGTH (new_actions (log_of (f x)) p1)) p2’
  >- simp[]
  >> qpat_x_assum ‘Abbrev (j = _)’
       (assume_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> qpat_x_assum ‘Abbrev (k = _)’
       (assume_tac o REWRITE_RULE[markerTheory.Abbrev_def])
  >> ‘LENGTH h2 = LENGTH p1 + LENGTH p2’
       by metis_tac[LENGTH_skip_results, LENGTH_APPEND]
  >> Cases_on ‘j = 0’
  >- (* f x finished in the round it started: the responses of that round
        are split between m, f x and g *)
     (‘p1 = []’ by metis_tac[LENGTH_NIL]
      >> ‘p2 = skip_results k h2’ by metis_tac[APPEND]
      >> qpat_x_assum ‘j = 0’ SUBST_ALL_TAC
      >> qpat_x_assum ‘p1 = []’ SUBST_ALL_TAC
      >> qpat_x_assum ‘p2 = _’ SUBST_ALL_TAC
      >> REWRITE_TAC[TAKE_0, DROP_0, APPEND_NIL]
      >> qpat_assum ‘wf m’ (fn w => qpat_assum ‘first_done m h1 x’
           (fn th => REWRITE_TAC[MATCH_MP new_actions_bind_at (CONJ w th)]))
      >> qpat_x_assum ‘k = _’ SUBST_ALL_TAC
      >> simp[new_actions_NIL, log_of_def, skip_results_skip_results])
  (* f x finished in a later round *)
  >> ‘0 < LENGTH h2’ by simp[]
  >> ‘TAKE j h2 ≠ []’ by (simp[TAKE_EQ_NIL] >> strip_tac >> fs[])
  >> ‘DROP j h2 = p2’ by metis_tac[DROP_skip_results, NOT_ZERO_LT_ZERO]
  >> qpat_x_assum ‘k = _’ SUBST_ALL_TAC
  >> qpat_assum ‘TAKE j h2 ≠ []’ (fn ne => qpat_assum ‘first_done m h1 x’
       (fn th => REWRITE_TAC[MATCH_MP new_actions_bind_after (CONJ th ne)]))
  >> ‘skip_results (LENGTH (new_actions (log_of m) h1)) (TAKE j h2) = p1’
       by metis_tac[TAKE_skip_results]
  >> simp[]
QED
