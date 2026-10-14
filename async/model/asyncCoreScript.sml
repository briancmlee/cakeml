(*
  Machinery shared by both levels of the async model.

  A computation is polled once per round.  Its meaning is a function of the
  history of snapshots it has been polled with so far (oldest first):

     history  = snapshot list            (chronological, oldest first)
     meaning  : history -> outcome

  The empty history is the very first poll, before any snapshot has arrived.

  This theory defines the parts that do not depend on what a "result" is:
   - snapshots and outcomes;
   - first_prefix: where in a history something first became true;
   - new_actions: the actions emitted in the latest round;
   - skip_results / par_views: how responses are routed to sub-computations;
   - freeze: stop a computation the moment it is done;
   - fix: guarded recursion, justified by "each unfolding uses up a snapshot".
*)
Theory asyncCore
Ancestors
  pair list rich_list pred_set arithmetic
Libs
  BasicProvers

(* ------------------------------------------------------------------------
   Snapshots and outcomes
   ------------------------------------------------------------------------ *)

(* What the world shows a computation when it is polled once:
   - ready:   the events that are ready now (fd readable, timer expired, ...);
   - now:     the current time;
   - results: the responses to the actions this computation emitted in the
              previous round, in the order they were emitted. *)
Datatype:
  snapshot = <| ready : 'e set ; now : num ; results : 'r list |>
End

(* What a computation has done after being polled with a history:
   - actions: every action emitted so far, oldest first (it only grows);
   - result:  whether it has finished (the type differs between levels). *)
Datatype:
  outcome = <| actions : 'act list ; result : 'x |>
End

(* ------------------------------------------------------------------------
   first_prefix P h: the length of the shortest prefix of h satisfying P
   ------------------------------------------------------------------------ *)

Definition first_prefix_def:
  first_prefix P h =
    if P [] then SOME 0
    else case h of
           [] => NONE
         | s :: rest => OPTION_MAP SUC (first_prefix (λt. P (s :: t)) rest)
End

Theorem TAKE_SUC_CONS[local]:
  TAKE (SUC n) (s :: t) = s :: TAKE n t
Proof
  simp[]
QED

Theorem first_prefix_SOME:
  ∀h P n.
    first_prefix P h = SOME n ⇔
      n ≤ LENGTH h ∧ P (TAKE n h) ∧ ∀k. k < n ⇒ ¬P (TAKE k h)
Proof
  Induct
  >- (rw[Once first_prefix_def] >> eq_tac >> rw[])
  >> rpt gen_tac >> simp[Once first_prefix_def]
  >> Cases_on ‘P []’ >> simp[]
  >- (eq_tac >> rw[] >> Cases_on ‘n’ >> gvs[]
      >> first_x_assum (qspec_then ‘0’ mp_tac) >> simp[])
  >> Cases_on ‘n’ >> simp[]
  >> rename1 ‘SUC n’
  >> eq_tac >> rw[]
  >- (Cases_on ‘k’ >> gvs[])
  >> first_x_assum (qspec_then ‘SUC k’ mp_tac) >> simp[]
QED

Theorem first_prefix_NONE:
  ∀h P. first_prefix P h = NONE ⇔ ∀k. k ≤ LENGTH h ⇒ ¬P (TAKE k h)
Proof
  Induct
  >- (rw[Once first_prefix_def])
  >> rpt gen_tac >> simp[Once first_prefix_def]
  >> Cases_on ‘P []’ >> simp[]
  >- (qexists_tac ‘0’ >> simp[])
  >> eq_tac >> rw[]
  >- (Cases_on ‘k’ >> gvs[])
  >> first_x_assum (qspec_then ‘SUC k’ mp_tac) >> simp[]
QED

(* If P holds of some prefix, first_prefix finds one *)
Theorem first_prefix_exists:
  ∀h P n. n ≤ LENGTH h ∧ P (TAKE n h) ⇒ ∃m. first_prefix P h = SOME m ∧ m ≤ n
Proof
  rpt strip_tac
  >> Cases_on ‘first_prefix P h’
  >- (gvs[first_prefix_NONE] >> metis_tac[])
  >> gvs[first_prefix_SOME]
  >> CCONTR_TAC >> gvs[NOT_LESS_EQUAL]
QED

(* Searching a longer history finds the same first prefix, if there is one
   within the shorter history. *)
Theorem first_prefix_APPEND:
  ∀h P n h'. first_prefix P h = SOME n ⇒ first_prefix P (h ++ h') = SOME n
Proof
  rw[first_prefix_SOME, TAKE_APPEND1]
  >> ‘k ≤ LENGTH h’ by simp[]
  >> simp[TAKE_APPEND1]
QED

(* On a history one snapshot longer, the search either finds what it found
   before, or (if it found nothing before) finds the whole history or nothing. *)
Theorem first_prefix_SNOC:
  ∀h P s.
    first_prefix P (h ++ [s]) =
      case first_prefix P h of
        SOME n => SOME n
      | NONE => if P (h ++ [s]) then SOME (LENGTH h + 1) else NONE
Proof
  rpt gen_tac
  >> Cases_on ‘first_prefix P h’ >> simp[first_prefix_APPEND]
  >> gvs[first_prefix_NONE]
  >> IF_CASES_TAC
  >- (simp[first_prefix_SOME, TAKE_LENGTH_TOO_LONG] >> rw[]
      >> ‘k ≤ LENGTH h’ by simp[] >> simp[TAKE_APPEND1])
  >> simp[first_prefix_NONE] >> rw[]
  >> Cases_on ‘k ≤ LENGTH h’ >> simp[TAKE_APPEND1]
  >> ‘k = LENGTH h + 1’ by simp[] >> gvs[TAKE_LENGTH_TOO_LONG]
QED

(* first_prefix only looks at prefixes of h *)
Theorem first_prefix_TAKE:
  ∀h P n k.
    first_prefix P h = SOME n ∧ n ≤ k ⇒ first_prefix P (TAKE k h) = SOME n
Proof
  rw[first_prefix_SOME, LENGTH_TAKE_EQ]
  >> rw[TAKE_TAKE_MIN, MIN_DEF] >> ‘k = n’ by simp[] >> gvs[]
QED

Theorem first_prefix_TAKE_NONE:
  ∀h P k.
    first_prefix P h = NONE ⇒ first_prefix P (TAKE k h) = NONE
Proof
  rw[first_prefix_NONE, TAKE_TAKE_MIN]
  >> first_x_assum irule
  >> gvs[LENGTH_TAKE_EQ, MIN_DEF] >> rw[] >> gvs[]
QED

(* ------------------------------------------------------------------------
   new_actions acts h: the actions emitted in the round polled with h,
   given acts = the cumulative action log as a function of the history.
   ------------------------------------------------------------------------ *)

Definition new_actions_def:
  new_actions acts h =
    if h = [] then acts [] else DROP (LENGTH (acts (FRONT h))) (acts h)
End

Theorem new_actions_NIL:
  new_actions acts [] = acts []
Proof
  simp[new_actions_def]
QED

Theorem new_actions_SNOC:
  new_actions acts (h ++ [s]) = DROP (LENGTH (acts h)) (acts (h ++ [s]))
Proof
  simp[new_actions_def, FRONT_APPEND]
QED

(* When the log only grows, the log is the old log plus the new actions *)
Theorem new_actions_prefix:
  acts h ≼ acts (h ++ [s]) ⇒
  acts (h ++ [s]) = acts h ++ new_actions acts (h ++ [s])
Proof
  rw[new_actions_SNOC, IS_PREFIX_APPEND] >> simp[DROP_APPEND, DROP_LENGTH_NIL]
QED

(* ------------------------------------------------------------------------
   Routing responses.

   The response to an action emitted in round n arrives in the results of
   snapshot n+1, at the action's position within that round's actions.
   Combinators therefore pass each sub-computation only the results that
   belong to it.
   ------------------------------------------------------------------------ *)

(* skip_results k h: h, with the first k results of its first snapshot
   removed.  Used by bind: the continuation starts in the round where the
   first computation finished, so the first k responses of the following
   snapshot belong to the first computation, not to the continuation. *)
Definition skip_results_def:
  skip_results k [] = [] ∧
  skip_results k (s :: rest) = (s with results := DROP k s.results) :: rest
End

Theorem skip_results_0[simp]:
  skip_results 0 h = h
Proof
  Cases_on ‘h’ >> simp[skip_results_def, theorem "snapshot_component_equality"]
QED

Theorem LENGTH_skip_results[simp]:
  LENGTH (skip_results k h) = LENGTH h
Proof
  Cases_on ‘h’ >> simp[skip_results_def]
QED

Theorem skip_results_skip_results:
  skip_results j (skip_results k h) = skip_results (k + j) h
Proof
  Cases_on ‘h’ >> simp[skip_results_def, DROP_DROP_T]
QED

Theorem TAKE_skip_results:
  TAKE n (skip_results k h) = skip_results k (TAKE n h)
Proof
  Cases_on ‘h’ >> Cases_on ‘n’ >> simp[skip_results_def]
QED

Theorem DROP_skip_results:
  0 < n ⇒ DROP n (skip_results k h) = DROP n h
Proof
  Cases_on ‘h’ >> Cases_on ‘n’ >> simp[skip_results_def]
QED

Theorem skip_results_APPEND:
  h1 ≠ [] ⇒ skip_results k (h1 ++ h2) = skip_results k h1 ++ h2
Proof
  Cases_on ‘h1’ >> simp[skip_results_def]
QED

Theorem skip_results_SNOC_NIL:
  skip_results k ([] ++ [s]) = [s with results := DROP k s.results]
Proof
  simp[skip_results_def]
QED

(* par_views acts1 acts2 h = (h1, h2): what each of two sub-computations
   running side by side sees, when the parent is polled with h.
   Both see the same ready set and time.  In each round the left one's
   actions come first, so of the following snapshot's results, the first
   k1 belong to the left one and the rest to the right one. *)
Definition par_views_def:
  par_views acts1 acts2 h =
    if h = [] then ([], [])
    else
      let (h1, h2) = par_views acts1 acts2 (FRONT h);
          k1 = LENGTH (new_actions acts1 h1);
          s = LAST h
      in
        (h1 ++ [s with results := TAKE k1 s.results],
         h2 ++ [s with results := DROP k1 s.results])
Termination
  WF_REL_TAC ‘measure (LENGTH o SND o SND)’
  >> Cases_on ‘h’ using SNOC_CASES >> simp[FRONT_APPEND]
End

Theorem par_views_NIL[simp]:
  par_views acts1 acts2 [] = ([], [])
Proof
  simp[Once par_views_def]
QED

Theorem par_views_SNOC:
  par_views acts1 acts2 (h ++ [s]) =
    let (h1, h2) = par_views acts1 acts2 h;
        k1 = LENGTH (new_actions acts1 h1)
    in
      (h1 ++ [s with results := TAKE k1 s.results],
       h2 ++ [s with results := DROP k1 s.results])
Proof
  simp[Once par_views_def, FRONT_APPEND]
QED

Theorem LENGTH_par_views:
  ∀h. LENGTH (FST (par_views acts1 acts2 h)) = LENGTH h ∧
      LENGTH (SND (par_views acts1 acts2 h)) = LENGTH h
Proof
  Induct_on ‘h’ using SNOC_INDUCT
  >> simp[SNOC_APPEND, par_views_SNOC]
  >> gen_tac >> pairarg_tac >> gvs[]
QED

(* The views of a prefix are the prefixes of the views *)
Theorem par_views_TAKE:
  ∀h n. par_views acts1 acts2 (TAKE n h) =
          (TAKE n (FST (par_views acts1 acts2 h)),
           TAKE n (SND (par_views acts1 acts2 h)))
Proof
  Induct_on ‘h’ using SNOC_INDUCT
  >> simp[SNOC_APPEND] >> rpt gen_tac
  >> Cases_on ‘n ≤ LENGTH h’
  >- (simp[TAKE_APPEND1, par_views_SNOC] >> pairarg_tac >> gvs[]
      >> ‘LENGTH h1 = LENGTH h ∧ LENGTH h2 = LENGTH h’
         by metis_tac[LENGTH_par_views, FST, SND]
      >> simp[TAKE_APPEND1])
  >> ‘TAKE n (h ++ [x]) = h ++ [x]’ by simp[TAKE_LENGTH_TOO_LONG]
  >> simp[par_views_SNOC] >> pairarg_tac >> gvs[]
  >> ‘LENGTH h1 = LENGTH h ∧ LENGTH h2 = LENGTH h’
     by metis_tac[LENGTH_par_views, FST, SND]
  >> simp[TAKE_LENGTH_TOO_LONG]
QED

(* par_actions acts1 acts2 h: the parent's action log.  Each round, the left
   sub-computation's new actions, then the right one's. *)
Definition par_actions_def:
  par_actions acts1 acts2 h =
    let (h1, h2) = par_views acts1 acts2 h in
      (if h = [] then [] else par_actions acts1 acts2 (FRONT h)) ++
      new_actions acts1 h1 ++ new_actions acts2 h2
Termination
  WF_REL_TAC ‘measure (LENGTH o SND o SND)’
  >> Cases_on ‘h’ using SNOC_CASES >> simp[FRONT_APPEND]
End

Theorem par_actions_NIL:
  par_actions acts1 acts2 [] = acts1 [] ++ acts2 []
Proof
  simp[Once par_actions_def, new_actions_NIL]
QED

Theorem par_actions_SNOC:
  par_actions acts1 acts2 (h ++ [s]) =
    let (h1, h2) = par_views acts1 acts2 (h ++ [s]) in
      par_actions acts1 acts2 h ++ new_actions acts1 h1 ++ new_actions acts2 h2
Proof
  simp[Once par_actions_def, FRONT_APPEND]
QED

(* The parent's log only grows, whatever the sub-computations do *)
Theorem par_actions_grows:
  par_actions acts1 acts2 h ≼ par_actions acts1 acts2 (h ++ [s])
Proof
  simp[par_actions_SNOC] >> pairarg_tac >> simp[]
  >> metis_tac[IS_PREFIX_APPEND3, APPEND_ASSOC]
QED

(* ------------------------------------------------------------------------
   freeze done m: behaves like m until the first time `done` holds of m's
   outcome, and from then on stays exactly as it was at that moment.
   ------------------------------------------------------------------------ *)

Definition freeze_def:
  freeze is_done m h =
    case first_prefix (λp. is_done (m p)) h of
      NONE => m h
    | SOME n => m (TAKE n h)
End

Theorem freeze_SNOC:
  freeze is_done m (h ++ [s]) =
    if is_done (freeze is_done m h) then freeze is_done m h
    else m (h ++ [s])
Proof
  simp[freeze_def, first_prefix_SNOC]
  >> Cases_on ‘first_prefix (λp. is_done (m p)) h’ >> simp[]
  >- (‘¬is_done (m h)’
        by (gvs[first_prefix_NONE]
            >> first_x_assum (qspec_then ‘LENGTH h’ mp_tac)
            >> simp[TAKE_LENGTH_ID])
      >> rw[TAKE_LENGTH_TOO_LONG])
  >> gvs[first_prefix_SOME] >> simp[TAKE_APPEND1]
QED

(* ------------------------------------------------------------------------
   Guarded recursion.

   Computations are functions of histories, so a recursive definition
     r = body r
   is justified when body only needs r on *shorter* histories: then r on
   histories of length n is determined by r on lengths < n, and the
   unfolding can be computed by recursion on the length of the history.
   This is the usual "contractive map" argument from guarded recursion.

   We allow parameterised recursion (r : 'p -> computation), e.g. a loop
   whose state is a buffer.
   ------------------------------------------------------------------------ *)

(* m1 and m2 behave identically on histories shorter than n *)
Definition agree_below_def:
  agree_below n m1 m2 ⇔ ∀h. LENGTH h < n ⇒ m1 h = m2 h
End

(* G (a computation built from the recursive call r) only depends on r's
   behaviour on histories shorter than the current one. *)
Definition guarded_def:
  guarded G ⇔
    ∀n r1 r2. (∀p. agree_below n (r1 p) (r2 p)) ⇒
              agree_below (n + 1) (G r1) (G r2)
End

(* G does not look at r on histories longer than the current one.
   Every combinator is non-expansive in each argument. *)
Definition nonexpansive_def:
  nonexpansive G ⇔
    ∀n r1 r2. (∀p. agree_below n (r1 p) (r2 p)) ⇒
              agree_below n (G r1) (G r2)
End

(* A recursive definition r p = body r p is guarded when, for each parameter p,
   the body is guarded in r. *)
Definition contractive_def:
  contractive body ⇔ ∀p. guarded (λr. body r p)
End

(* The fixpoint: to compute r on a history of length n, unfold n+1 times.
   The starting point ARB is never reached when body is contractive. *)
Definition fix_def:
  fix body p h = FUNPOW body (SUC (LENGTH h)) ARB p h
End

Theorem agree_below_0[simp]:
  agree_below 0 m1 m2
Proof
  simp[agree_below_def]
QED

Theorem agree_below_mono:
  agree_below n m1 m2 ∧ k ≤ n ⇒ agree_below k m1 m2
Proof
  rw[agree_below_def]
QED

Theorem agree_below_refl[simp]:
  agree_below n m m
Proof
  simp[agree_below_def]
QED

Theorem contractive_step:
  contractive body ∧ (∀p. agree_below n (r1 p) (r2 p)) ⇒
  ∀p. agree_below (n + 1) (body r1 p) (body r2 p)
Proof
  rw[contractive_def, guarded_def]
  >> first_x_assum (qspec_then ‘p’ mp_tac) >> simp[]
QED

(* The n-th unfolding from any starting point b is correct below n *)
Theorem FUNPOW_agree:
  contractive body ⇒
  ∀n k b1 b2 p. n ≤ k ⇒
    agree_below n (FUNPOW body n b1 p) (FUNPOW body k b2 p)
Proof
  strip_tac >> Induct >> simp[] >> rpt strip_tac
  >> Cases_on ‘k’ >> gvs[FUNPOW_SUC, ADD1]
  >> irule contractive_step >> simp[]
QED

Theorem fix_agree_FUNPOW:
  contractive body ⇒ ∀n b p. agree_below n (FUNPOW body n b p) (fix body p)
Proof
  rw[agree_below_def, fix_def]
  >> drule FUNPOW_agree
  >> disch_then (qspecl_then [‘SUC (LENGTH h)’, ‘n’, ‘ARB’, ‘b’, ‘p’] mp_tac)
  >> simp[agree_below_def]
QED

(* MAIN: a guarded recursive definition can be unfolded once *)
Theorem fix_unfold:
  contractive body ⇒ fix body = body (fix body)
Proof
  rw[FUN_EQ_THM]
  >> rename1 ‘fix body p h’
  >> ‘fix body p h = body (FUNPOW body (LENGTH h) ARB) p h’
     by simp[fix_def, FUNPOW_SUC]
  >> simp[]
  >> ‘∀p. agree_below (LENGTH h) (FUNPOW body (LENGTH h) ARB p) (fix body p)’
     by metis_tac[fix_agree_FUNPOW]
  >> drule_all contractive_step
  >> simp[agree_below_def]
QED

(* MAIN: a guarded recursive definition has exactly one solution *)
Theorem fix_unique:
  contractive body ∧ body r = r ⇒ r = fix body
Proof
  strip_tac
  >> ‘∀n p. agree_below n (r p) (fix body p)’ suffices_by
       (rw[FUN_EQ_THM, agree_below_def]
        >> first_x_assum (qspecl_then [‘SUC (LENGTH x')’, ‘x’] mp_tac)
        >> simp[agree_below_def])
  >> Induct >> simp[]
  >> drule_then (assume_tac o GSYM) fix_unfold
  >> ‘∀p. agree_below (n + 1) (body r p) (body (fix body) p)’
     by (irule contractive_step >> simp[])
  >> gvs[ADD1] >> metis_tac[]
QED

(* A property is "closed" if it holds of any m that, on every bounded
   set of histories, agrees with something that has the property.
   Well-formedness is closed (it talks about one step at a time). *)
Definition closed_def:
  closed P ⇔ ∀m. (∀n. ∃m'. agree_below n m m' ∧ P m') ⇒ P m
End

(* A closed property that holds of some computation m0 and is preserved by
   the body holds of the fixpoint *)
Theorem fix_preserves:
  contractive body ∧ closed P ∧ P m0 ∧
  (∀r. (∀p. P (r p)) ⇒ ∀p. P (body r p)) ⇒
  ∀p. P (fix body p)
Proof
  rw[closed_def] >> first_x_assum irule >> rw[]
  >> qexists_tac ‘FUNPOW body n (K m0) p’
  >> conj_tac
  >- (‘agree_below n (FUNPOW body n (K m0) p) (fix body p)’
        by metis_tac[fix_agree_FUNPOW]
      >> fs[agree_below_def])
  >> ‘∀n p. P (FUNPOW body n (K m0) p)’ suffices_by simp[]
  >> Induct >> simp[FUNPOW_SUC]
QED

(* Guardedness and non-expansiveness: basic closure properties *)

Theorem nonexpansive_const:
  nonexpansive (λr. m)
Proof
  simp[nonexpansive_def]
QED

Theorem nonexpansive_call:
  nonexpansive (λr. r p)
Proof
  simp[nonexpansive_def]
QED

Theorem guarded_const:
  guarded (λr. m)
Proof
  simp[guarded_def]
QED

Theorem guarded_nonexpansive:
  guarded G ⇒ nonexpansive G
Proof
  rw[guarded_def, nonexpansive_def]
  >> first_x_assum drule >> rw[agree_below_def]
QED

(* ------------------------------------------------------------------------
   More about freeze
   ------------------------------------------------------------------------ *)

(* If the frozen computation is not done, nothing was frozen yet *)
Theorem freeze_not_done:
  ¬is_done (freeze is_done m h) ⇒ freeze is_done m h = m h
Proof
  rw[freeze_def] >> every_case_tac >> gvs[first_prefix_SOME]
QED

(* ------------------------------------------------------------------------
   Congruence: these functions only look at prefixes of the history.
   Used to show that combinators are non-expansive.
   ------------------------------------------------------------------------ *)

Theorem first_prefix_cong:
  ∀h P Q.
    (∀k. k ≤ LENGTH h ⇒ (P (TAKE k h) ⇔ Q (TAKE k h))) ⇒
    first_prefix P h = first_prefix Q h
Proof
  rpt strip_tac
  >> Cases_on ‘first_prefix P h’ >> Cases_on ‘first_prefix Q h’
  >> gvs[first_prefix_SOME, first_prefix_NONE]
  >> TRY (metis_tac[])
  >> CCONTR_TAC
  >> ‘x < x' ∨ x' < x’ by decide_tac
  >> metis_tac[]
QED

Theorem new_actions_cong:
  (∀p. LENGTH p ≤ LENGTH h ⇒ a p = b p) ⇒ new_actions a h = new_actions b h
Proof
  rw[new_actions_def]
  >> ‘LENGTH (FRONT h) ≤ LENGTH h’
       by (Cases_on ‘h’ using SNOC_CASES >> gvs[FRONT_APPEND])
  >> simp[]
QED

(* The views only depend on the left side's log on shorter histories *)
Theorem par_views_cong:
  ∀h. (∀p. LENGTH p < LENGTH h ⇒ a1 p = b1 p) ⇒
      par_views a1 a2 h = par_views b1 b2 h
Proof
  Induct_on ‘h’ using SNOC_INDUCT
  >> simp[SNOC_APPEND, par_views_SNOC] >> rpt strip_tac
  >> ‘par_views a1 a2 h = par_views b1 b2 h’ by simp[]
  >> simp[] >> pairarg_tac >> simp[]
  >> ‘LENGTH h1 = LENGTH h’ by metis_tac[LENGTH_par_views, FST]
  >> ‘new_actions a1 h1 = new_actions b1 h1’
       by (irule new_actions_cong >> simp[])
  >> simp[]
QED

Theorem par_actions_cong:
  ∀h. (∀p. LENGTH p ≤ LENGTH h ⇒ a1 p = b1 p ∧ a2 p = b2 p) ⇒
      par_actions a1 a2 h = par_actions b1 b2 h
Proof
  Induct_on ‘h’ using SNOC_INDUCT
  >- simp[par_actions_NIL]
  >> simp[SNOC_APPEND, par_actions_SNOC] >> rpt strip_tac
  >> ‘par_actions a1 a2 h = par_actions b1 b2 h’ by simp[]
  >> ‘par_views a1 a2 (h ++ [x]) = par_views b1 b2 (h ++ [x])’
       by (irule par_views_cong >> simp[])
  >> simp[] >> pairarg_tac >> simp[]
  >> ‘LENGTH h1 = LENGTH h + 1 ∧ LENGTH h2 = LENGTH h + 1’
       by metis_tac[LENGTH_par_views, FST, SND, LENGTH_APPEND, LENGTH]
  >> ‘new_actions a1 h1 = new_actions b1 h1 ∧ new_actions a2 h2 = new_actions b2 h2’
       by (conj_tac >> irule new_actions_cong >> simp[])
  >> simp[]
QED

Theorem freeze_agree:
  agree_below n m m' ⇒ agree_below n (freeze is_done m) (freeze is_done m')
Proof
  rw[agree_below_def, freeze_def]
  >> ‘first_prefix (λp. is_done (m p)) h = first_prefix (λp. is_done (m' p)) h’
       by (irule first_prefix_cong >> rw[] >> simp[LENGTH_TAKE_EQ] >> rw[])
  >> simp[] >> CASE_TAC >> simp[LENGTH_TAKE_EQ] >> rw[]
QED

Theorem skip_results_SNOC:
  ∃s'. skip_results k (h ++ [s]) = skip_results k h ++ [s']
Proof
  Cases_on ‘h’ >> simp[skip_results_def]
QED

Theorem par_views_SNOC_exists:
  ∃s1 s2. par_views a1 a2 (h ++ [s]) =
          (FST (par_views a1 a2 h) ++ [s1], SND (par_views a1 a2 h) ++ [s2])
Proof
  simp[par_views_SNOC] >> pairarg_tac >> simp[]
QED

(* The views show the same ready sets and times as the parent's history *)
Theorem par_views_world:
  ∀h. MAP (λs. (s.ready, s.now)) (FST (par_views a1 a2 h)) =
        MAP (λs. (s.ready, s.now)) h ∧
      MAP (λs. (s.ready, s.now)) (SND (par_views a1 a2 h)) =
        MAP (λs. (s.ready, s.now)) h
Proof
  Induct_on ‘h’ using SNOC_INDUCT
  >> simp[SNOC_APPEND, par_views_SNOC] >> gen_tac
  >> pairarg_tac >> gvs[]
QED
