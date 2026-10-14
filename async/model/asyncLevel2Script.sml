(*
  Level 2 of the async model: polling with declared interest.

  A Level 2 computation is a Level 1 computation (`run`) together with the
  set of events it is waiting for (`interest`), as a function of the history:

     c.run      : history -> outcome          (as at Level 1)
     c.interest : history -> event set        (meaningful while unfinished)

  so that after a history h the computation is either Done x or
  Waiting (c.interest h) (see `status`).

  `erase c = c.run` forgets the interest.  Every Level 2 combinator is
  defined so that erasing it gives the Level 1 combinator, so erasure
  commutes with every combinator by construction and every Level 1 law
  transfers.

  What Level 2 adds is a property Level 1 cannot state: a *quiet*
  computation makes no progress, now or later, on a snapshot in which none
  of the events it declared is ready (and no response is due).  Such a
  snapshot can be deleted from the history without changing anything.  This
  is what justifies a scheduler that blocks (e.g. in select) instead of
  polling every round.
*)
Theory asyncLevel2
Ancestors
  pair list rich_list arithmetic option pred_set sum asyncCore asyncLevel1
  asyncChoose
Libs
  BasicProvers

Datatype:
  comp2 = <| run : ('e, 'r) snapshot list -> ('act, 'a option) outcome ;
             interest : ('e, 'r) snapshot list -> 'e set |>
End

Datatype:
  status = Done 'a | Waiting ('e set)
End

(* The Level 1 computation underneath *)
Definition erase_def:
  erase c = c.run
End

(* Where c stands after the history h *)
Definition status_def:
  status c h =
    case (c.run h).result of
      SOME x => Done x
    | NONE => Waiting (c.interest h)
End

(* ------------------------------------------------------------------------
   Primitives and combinators
   ------------------------------------------------------------------------ *)

Definition return2_def:
  return2 x = <| run := return x; interest := K ∅ |>
End

(* wait_on e p: finishes at the first snapshot s in which e is ready and
   p s = SOME x.  It only looks at snapshots in which e is ready. *)
Definition wait_on_def:
  wait_on e p =
    <| run := wait (λs. if e ∈ s.ready then p s else NONE);
       interest := K {e} |>
End

(* emit2 a: waits for nothing but the response to a *)
Definition emit2_def:
  emit2 a = <| run := emit a; interest := K ∅ |>
End

Definition map2_def:
  map2 f c = <| run := map f c.run; interest := c.interest |>
End

(* While c is running, bind2 c f waits for what c waits for; afterwards, for
   what f x waits for (on the snapshots it has been shown). *)
Definition bind_interest_def:
  bind_interest c f h =
    case first_prefix (λp. (c.run p).result ≠ NONE) h of
      NONE => c.interest h
    | SOME n =>
        let hc = TAKE n h;
            k = LENGTH (new_actions (log_of c.run) hc)
        in
          (f (THE (c.run hc).result)).interest (skip_results k (DROP n h))
End

Definition bind2_def:
  bind2 c f =
    <| run := bind c.run (λx. (f x).run); interest := bind_interest c f |>
End

(* What c is waiting for, if it has not finished *)
Definition waiting_on_def:
  waiting_on c h = if (c.run h).result = NONE then c.interest h else ∅
End

(* both2 waits for what either unfinished side waits for *)
Definition both2_def:
  both2 c1 c2 =
    <| run := both c1.run c2.run;
       interest := λh. waiting_on c1 (left_view c1.run c2.run h) ∪
                       waiting_on c2 (right_view c1.run c2.run h) |>
End

(* ------------------------------------------------------------------------
   Erasure commutes with every combinator (by construction)
   ------------------------------------------------------------------------ *)

(* MAIN: erasure commutes with return *)
Theorem erase_return2:
  erase (return2 x) = return x
Proof
  simp[erase_def, return2_def]
QED

(* MAIN: erasing wait_on gives a Level 1 wait that ignores snapshots in
   which e is not ready *)
Theorem erase_wait_on:
  erase (wait_on e p) = wait (λs. if e ∈ s.ready then p s else NONE)
Proof
  simp[erase_def, wait_on_def]
QED

(* MAIN: erasure commutes with emit *)
Theorem erase_emit2:
  erase (emit2 a) = emit a
Proof
  simp[erase_def, emit2_def]
QED

(* MAIN: erasure commutes with map *)
Theorem erase_map2:
  erase (map2 f c) = map f (erase c)
Proof
  simp[erase_def, map2_def]
QED

(* MAIN: erasure commutes with bind *)
Theorem erase_bind2:
  erase (bind2 c f) = bind (erase c) (λx. erase (f x))
Proof
  simp[erase_def, bind2_def]
QED

(* MAIN: erasure commutes with both *)
Theorem erase_both2:
  erase (both2 c1 c2) = both (erase c1) (erase c2)
Proof
  simp[erase_def, both2_def]
QED

(* The escape hatch: waiting on an event that is ready in every snapshot
   (e.g. `Always` in a world that always reports it) is plain Level 1 waiting *)
Theorem wait_on_always:
  EVERY (λs. e ∈ s.ready) h ⇒ erase (wait_on e p) h = wait p h
Proof
  simp[erase_def, wait_on_def, wait_def] >> Induct_on ‘h’
  >> simp[first_some_def]
QED

(* ------------------------------------------------------------------------
   Level 1 laws, transferred
   ------------------------------------------------------------------------ *)

(* MAIN: monad law at Level 2 (up to erasure), left identity *)
Theorem bind2_left_identity:
  erase (bind2 (return2 x) f) = erase (f x)
Proof
  simp[erase_bind2, erase_return2, bind_left_identity]
QED

(* MAIN: monad law at Level 2 (up to erasure), right identity *)
Theorem bind2_right_identity:
  wf (erase c) ⇒ erase (bind2 c return2) = erase c
Proof
  strip_tac >> simp[erase_bind2, erase_return2]
  >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[bind_right_identity]
QED

(* MAIN: monad law at Level 2 (up to erasure), associativity *)
Theorem bind2_assoc:
  wf (erase c) ⇒
  erase (bind2 (bind2 c f) g) = erase (bind2 c (λx. bind2 (f x) g))
Proof
  strip_tac >> simp[erase_bind2, bind_assoc]
QED

(* In fact left identity holds exactly, interest included *)
Theorem bind2_left_identity_exact:
  bind2 (return2 x) f = f x
Proof
  simp[bind2_def, return2_def, bind_left_identity,
       theorem "comp2_component_equality"]
  >> simp[FUN_EQ_THM, bind_interest_def, Once first_prefix_def, return_def,
          new_actions_NIL, log_of_def]
QED

(* ------------------------------------------------------------------------
   Quiet: no progress without a declared ready event
   ------------------------------------------------------------------------ *)

(* c is quiet if, whenever it has not finished and has no request in flight,
   a snapshot with no responses and none of its declared events ready can be
   deleted from the history without changing anything, now or later. *)
Definition quiet_def:
  quiet c ⇔
    ∀h s h'.
      (c.run h).result = NONE ∧ new_actions (log_of c.run) h = [] ∧
      s.results = [] ∧ DISJOINT (c.interest h) s.ready ⇒
      c.run (h ++ [s] ++ h') = c.run (h ++ h') ∧
      c.interest (h ++ [s] ++ h') = c.interest (h ++ h')
End

Definition wf2_def:
  wf2 c ⇔ wf c.run ∧ quiet c
End

(* MAIN: no progress without a declared ready event.  If c is waiting, has
   no request in flight, and none of the events it waits for is ready, then
   polling it again changes nothing. *)
Theorem no_progress_without_ready_event:
  wf2 c ∧ status c h = Waiting E ∧ new_actions (log_of c.run) h = [] ∧
  DISJOINT E s.ready ∧ s.results = [] ⇒
  c.run (h ++ [s]) = c.run h ∧ status c (h ++ [s]) = Waiting E
Proof
  simp[wf2_def, status_def, AllCaseEqs()] >> strip_tac
  >> gvs[quiet_def]
  >> first_x_assum (qspecl_then [‘h’, ‘s’, ‘[]’] mp_tac) >> simp[]
QED

Theorem first_some_APPEND:
  first_some p (l1 ++ l2) =
    case first_some p l1 of SOME x => SOME x | NONE => first_some p l2
Proof
  Induct_on ‘l1’ >> simp[first_some_def] >> rpt strip_tac
  >> every_case_tac >> gvs[]
QED

Theorem quiet_return2:
  quiet (return2 x)
Proof
  simp[quiet_def, return2_def, return_def]
QED

(* MAIN: the Level 2 primitives are quiet *)
Theorem quiet_wait_on:
  quiet (wait_on e p)
Proof
  rw[quiet_def, wait_on_def, wait_def, first_some_APPEND, first_some_def]
QED

Theorem quiet_emit2:
  quiet (emit2 a)
Proof
  rw[quiet_def, emit2_def, emit_def] >> Cases_on ‘h’
  >> gvs[new_actions_NIL, log_of_def, emit_def]
QED

(* MAIN: map2 is quiet if its argument is *)
Theorem quiet_map2:
  quiet c ⇒ quiet (map2 f c)
Proof
  rw[quiet_def, map2_def, map_def] >> Cases_on ‘(c.run h).result’ >> gvs[]
  >> first_x_assum drule_all >> simp[]
QED

(* ------------------------------------------------------------------------
   bind2 is quiet
   ------------------------------------------------------------------------ *)

val bind_continues' = GEN_TYVARIFY bind_continues;
val bind_running' = GEN_TYVARIFY bind_running;

Theorem new_actions_delete:
  (∀k. m (h ++ [s] ++ k) = m (h ++ k)) ∧ k ≠ [] ⇒
  new_actions (log_of m) (h ++ [s] ++ k) = new_actions (log_of m) (h ++ k)
Proof
  strip_tac >> Cases_on ‘k’ using SNOC_CASES >> fs[SNOC_APPEND]
  >> ‘h ++ [s] ++ (l ++ [x]) = (h ++ [s] ++ l) ++ [x] ∧
      h ++ (l ++ [x]) = (h ++ l) ++ [x]’ by simp[]
  >> ASM_REWRITE_TAC[new_actions_SNOC, log_of_def]
  >> first_assum (qspec_then ‘l ++ [x]’ mp_tac)
  >> first_x_assum (qspec_then ‘l’ mp_tac)
  >> simp[]
QED

(* Deleting a snapshot that m ignores, before m finishes, delays m's
   finishing point by one snapshot and changes nothing else *)
Theorem first_finish_delete:
  (∀k. m (h ++ [s] ++ k) = m (h ++ k)) ∧
  (∀j. j ≤ LENGTH h ⇒ (m (TAKE j h)).result = NONE) ⇒
  (first_prefix (λp. (m p).result ≠ NONE) (h ++ [s] ++ h') = NONE ⇔
   first_prefix (λp. (m p).result ≠ NONE) (h ++ h') = NONE) ∧
  ∀n. first_prefix (λp. (m p).result ≠ NONE) (h ++ h') = SOME n ⇒
      first_prefix (λp. (m p).result ≠ NONE) (h ++ [s] ++ h') = SOME (SUC n) ∧
      m (TAKE (SUC n) (h ++ [s] ++ h')) = m (TAKE n (h ++ h')) ∧
      new_actions (log_of m) (TAKE (SUC n) (h ++ [s] ++ h')) =
        new_actions (log_of m) (TAKE n (h ++ h')) ∧
      DROP (SUC n) (h ++ [s] ++ h') = DROP n (h ++ h')
Proof
  strip_tac
  >> ‘first_prefix (λp. (m p).result ≠ NONE) (h ++ [s] ++ h') =
      OPTION_MAP SUC (first_prefix (λp. (m p).result ≠ NONE) (h ++ h'))’
       by (irule first_prefix_delete >> simp[first_prefix_NONE])
  >> simp[] >> rpt gen_tac >> strip_tac
  (* m finishes somewhere in h' *)
  >> ‘LENGTH h < n ∧ n ≤ LENGTH h + LENGTH h'’
       by (fs[first_prefix_SOME] >> spose_not_then assume_tac
           >> ‘n ≤ LENGTH h’ by simp[]
           >> ‘TAKE n (h ++ h') = TAKE n h’ by simp[TAKE_APPEND1]
           >> gvs[])
  >> ‘∃j. n = LENGTH h + j ∧ 0 < j’ by (qexists_tac ‘n - LENGTH h’ >> simp[])
  >> gvs[]
  >> ‘TAKE (SUC (j + LENGTH h)) (h ++ [s] ++ h') = h ++ [s] ++ TAKE j h' ∧
      TAKE (j + LENGTH h) (h ++ h') = h ++ TAKE j h' ∧
      DROP (SUC (j + LENGTH h)) (h ++ [s] ++ h') = DROP j h' ∧
      DROP (j + LENGTH h) (h ++ h') = DROP j h'’
       by simp[TAKE_APPEND, DROP_APPEND, TAKE_LENGTH_TOO_LONG,
               DROP_LENGTH_TOO_LONG, ADD1]
  >> ASM_REWRITE_TAC[]
  >> simp[] >> irule new_actions_delete >> simp[] >> Cases_on ‘h'’ >> gvs[]
QED

Theorem bind_interest_running:
  (∀n. n ≤ LENGTH h ⇒ (c.run (TAKE n h)).result = NONE) ⇒
  bind_interest c f h = c.interest h
Proof
  rw[bind_interest_def]
  >> ‘first_prefix (λp. (c.run p).result ≠ NONE) h = NONE’
       by simp[first_prefix_NONE]
  >> simp[]
QED

Theorem bind_interest_continues:
  first_done c.run h1 x ⇒
  ∀f h2.
  bind_interest c f (h1 ++ h2) =
    (f x).interest (skip_results (LENGTH (new_actions (log_of c.run) h1)) h2)
Proof
  rpt strip_tac >> drule first_prefix_done_APPEND
  >> disch_then (qspec_then ‘h2’ assume_tac)
  >> simp[bind_interest_def, TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND]
  >> gvs[first_done_def]
QED

Theorem new_actions_bind_running:
  (∀n. n ≤ LENGTH h ⇒ (m (TAKE n h)).result = NONE) ⇒
  new_actions (log_of (bind m f)) h = new_actions (log_of m) h
Proof
  strip_tac
  >> ‘∀n. bind m f (TAKE n h) = <| actions := (m (TAKE n h)).actions; result := NONE |>’
       by (qpat_x_assum ‘∀n. _’
             (fn th => simp[MATCH_MP (GEN_TYVARIFY bind_running_TAKE) th]))
  >> Cases_on ‘h’ using SNOC_CASES
  >- (first_x_assum (qspec_then ‘0’ mp_tac) >> simp[new_actions_NIL, log_of_def])
  >> fs[SNOC_APPEND, new_actions_SNOC, log_of_def]
  >> first_assum (qspec_then ‘LENGTH l’ mp_tac)
  >> first_x_assum (qspec_then ‘LENGTH l + 1’ mp_tac)
  >> simp[TAKE_LENGTH_APPEND, TAKE_LENGTH_TOO_LONG]
QED

(* Rewrite with bind_continues and bind_interest_continues, using the
   first_done assumption (type variables renamed apart, see asyncChoose) *)
val continues_tac =
  qpat_assum ‘first_done _ _ _’
    (fn th => simp[MATCH_MP bind_continues' th,
                   MATCH_MP (GEN_TYVARIFY bind_interest_continues) th]);

(* MAIN: bind2 is quiet if c is, and f x is for every result c can actually
   produce *)
Theorem quiet_bind2_on:
  wf c.run ∧ quiet c ∧ (∀x. can_return c.run x ⇒ quiet (f x)) ⇒ quiet (bind2 c f)
Proof
  strip_tac >> simp[quiet_def, bind2_def] >> rpt gen_tac >> strip_tac
  >> qspecl_then [‘c.run’, ‘h’] strip_assume_tac history_split
  >- (* c is still running after h *)
     (‘bind_interest c f h = c.interest h’ by simp[bind_interest_running]
      >> ‘new_actions (log_of c.run) h = []’
           by metis_tac[new_actions_bind_running]
      >> ‘(c.run h).result = NONE’
           by (first_x_assum (qspec_then ‘LENGTH h’ mp_tac) >> simp[TAKE_LENGTH_ID])
      >> ‘∀k. c.run (h ++ [s] ++ k) = c.run (h ++ k) ∧
              c.interest (h ++ [s] ++ k) = c.interest (h ++ k)’
           by (gen_tac >> qpat_x_assum ‘quiet c’ mp_tac >> simp[quiet_def]
               >> disch_then irule >> gvs[])
      >> qspecl_then [‘c.run’, ‘h’, ‘s’, ‘h'’] mp_tac
           (Q.GENL [‘m’, ‘h’, ‘s’, ‘h'’] first_finish_delete)
      >> impl_tac >- simp[]
      >> strip_tac
      >> Cases_on ‘first_prefix (λp. (c.run p).result ≠ NONE) (h ++ h')’
      >- (‘first_prefix (λp. (c.run p).result ≠ NONE) (h ++ [s] ++ h') = NONE’
            by fs[]
          >> ONCE_REWRITE_TAC[bind_def, bind_interest_def] >> ASM_REWRITE_TAC[]
          >> simp[])
      >> qpat_x_assum ‘∀n. SOME _ = SOME n ⇒ _’ (qspec_then ‘x’ mp_tac)
      >> REWRITE_TAC[] >> strip_tac
      >> ONCE_REWRITE_TAC[bind_def, bind_interest_def] >> ASM_REWRITE_TAC[]
      >> simp[])
  (* c has finished, first after h1: from then on bind2 behaves like f x *)
  >> qpat_x_assum ‘h = _’ SUBST_ALL_TAC
  >> qabbrev_tac ‘kc = LENGTH (new_actions (log_of c.run) h1)’
  (* f x is in the same situation as bind2 c f *)
  >> ‘((f x).run (skip_results kc h2)).result = NONE ∧
      DISJOINT ((f x).interest (skip_results kc h2)) s.ready’
       by (qpat_x_assum ‘(bind _ _ _).result = NONE’ mp_tac
           >> qpat_x_assum ‘DISJOINT _ _’ mp_tac >> continues_tac)
  >> ‘new_actions (log_of (f x).run) (skip_results kc h2) = [] ∧
      skip_results kc (h2 ++ [s] ++ h') = skip_results kc h2 ++ [s] ++ h' ∧
      skip_results kc (h2 ++ h') = skip_results kc h2 ++ h'’
       by (Cases_on ‘h2 = []’
           >- (qpat_x_assum ‘new_actions _ (h1 ++ h2) = []’ mp_tac
               >> qspecl_then [‘c.run’, ‘h1’, ‘x’, ‘λx. (f x).run’] mp_tac
                    (Q.GENL [‘m’, ‘h1’, ‘x’, ‘f’] new_actions_bind_at)
               >> simp[] >> disch_then kall_tac >> strip_tac
               >> ‘kc = 0’ by simp[Abbr ‘kc’]
               >> simp[new_actions_NIL, log_of_def])
           >> qpat_x_assum ‘new_actions _ (h1 ++ h2) = []’ mp_tac
           >> qspecl_then [‘c.run’, ‘h1’, ‘x’, ‘h2’, ‘λx. (f x).run’] mp_tac
                (Q.GENL [‘m’, ‘h1’, ‘x’, ‘q’, ‘f’] new_actions_bind_after)
           >> simp[skip_results_APPEND])
  >> ‘quiet (f x)’ by metis_tac[first_done_can_return]
  >> pop_assum (mp_tac o REWRITE_RULE[quiet_def])
  >> disch_then (qspecl_then [‘skip_results kc h2’, ‘s’, ‘h'’] mp_tac)
  >> impl_tac >- simp[]
  >> strip_tac
  >> ‘h1 ++ h2 ++ [s] ++ h' = h1 ++ (h2 ++ [s] ++ h') ∧
      h1 ++ h2 ++ h' = h1 ++ (h2 ++ h')’ by simp[]
  >> ASM_REWRITE_TAC[]
  >> continues_tac
QED


(* MAIN: bind2 is quiet if its parts are *)
Theorem quiet_bind2:
  wf c.run ∧ quiet c ∧ (∀x. quiet (f x)) ⇒ quiet (bind2 c f)
Proof
  rw[] >> irule quiet_bind2_on >> simp[]
QED
(* ------------------------------------------------------------------------
   both2 is quiet
   ------------------------------------------------------------------------ *)

Theorem snapshot_results_NIL[local]:
  s.results = [] ⇒ s with results := [] = s
Proof
  simp[snapshot_component_equality]
QED

(* A side of both2 for which s is irrelevant: either it waits for none of
   s's events, or it has finished *)
Theorem side_delete:
  wf c.run ∧ quiet c ∧ new_actions (log_of c.run) v = [] ∧ s.results = [] ∧
  DISJOINT (waiting_on c v) s.ready ⇒
  ∀k. c.run (v ++ [s] ++ k) = c.run (v ++ k) ∧
      waiting_on c (v ++ [s] ++ k) = waiting_on c (v ++ k)
Proof
  strip_tac >> gen_tac
  >> Cases_on ‘(c.run v).result’
  >- (gvs[waiting_on_def, quiet_def]
      >> first_x_assum (qspecl_then [‘v’, ‘s’, ‘k’] mp_tac) >> simp[])
  >> ‘c.run (v ++ [s] ++ k) = c.run v ∧ c.run (v ++ k) = c.run v’
       by (conj_tac >> irule wf_finished_stays >> simp[]
           >> metis_tac[IS_PREFIX_APPEND3, APPEND_ASSOC])
  >> simp[waiting_on_def]
QED

(* Deleting s from the parent's history deletes it from both sides' views *)
Theorem views_delete:
  (∀k. m1 (left_view m1 m2 h ++ [s] ++ k) = m1 (left_view m1 m2 h ++ k)) ∧
  new_actions (log_of m1) (left_view m1 m2 h) = [] ∧ s.results = [] ⇒
  ∀h'. ∃R1 R2.
    left_view m1 m2 (h ++ [s] ++ h') = left_view m1 m2 h ++ [s] ++ R1 ∧
    left_view m1 m2 (h ++ h') = left_view m1 m2 h ++ R1 ∧
    right_view m1 m2 (h ++ [s] ++ h') = right_view m1 m2 h ++ [s] ++ R2 ∧
    right_view m1 m2 (h ++ h') = right_view m1 m2 h ++ R2
Proof
  strip_tac >> Induct_on ‘h'’ using SNOC_INDUCT
  >- simp[left_view_SNOC_eq, right_view_SNOC_eq, snapshot_results_NIL]
  >> simp[SNOC_APPEND] >> rpt strip_tac
  >> qpat_x_assum ‘∃R1 R2. _’ strip_assume_tac
  >> ‘h ++ [s] ++ (h' ++ [x]) = (h ++ [s] ++ h') ++ [x] ∧
      h ++ (h' ++ [x]) = (h ++ h') ++ [x]’ by simp[]
  >> ASM_REWRITE_TAC[left_view_SNOC_eq, right_view_SNOC_eq]
  >> ‘new_actions (log_of m1) (left_view m1 m2 h ++ [s] ++ R1) =
      new_actions (log_of m1) (left_view m1 m2 h ++ R1)’
       by (Cases_on ‘R1 = []’
           >- (gvs[new_actions_SNOC, log_of_def]
               >> first_x_assum (qspec_then ‘[]’ mp_tac)
               >> simp[DROP_LENGTH_NIL])
           >> irule new_actions_delete >> simp[])
  >> qexistsl_tac
       [‘R1 ++ [x with results :=
                  TAKE (LENGTH (new_actions (log_of m1)
                                  (left_view m1 m2 h ++ R1))) x.results]’,
        ‘R2 ++ [x with results :=
                  DROP (LENGTH (new_actions (log_of m1)
                                  (left_view m1 m2 h ++ R1))) x.results]’]
  >> simp[]
QED

Theorem par_log_delete:
  (∀k. m1 (left_view m1 m2 h ++ [s] ++ k) = m1 (left_view m1 m2 h ++ k)) ∧
  (∀k. m2 (right_view m1 m2 h ++ [s] ++ k) = m2 (right_view m1 m2 h ++ k)) ∧
  new_actions (log_of m1) (left_view m1 m2 h) = [] ∧ s.results = [] ⇒
  ∀h'. par_log m1 m2 (h ++ [s] ++ h') = par_log m1 m2 (h ++ h')
Proof
  strip_tac >> drule_all views_delete >> strip_tac
  >> Induct_on ‘h'’ using SNOC_INDUCT
  >- (simp[par_log_SNOC]
      >> first_x_assum (qspec_then ‘[]’ strip_assume_tac)
      >> gvs[new_actions_SNOC, log_of_def, DROP_LENGTH_NIL]
      >> qpat_x_assum ‘∀k. m1 _ = _’ (qspec_then ‘[]’ mp_tac)
      >> qpat_x_assum ‘∀k. m2 _ = _’ (qspec_then ‘[]’ mp_tac)
      >> simp[DROP_LENGTH_NIL])
  >> simp[SNOC_APPEND] >> rpt strip_tac
  >> ‘h ++ [s] ++ (h' ++ [x]) = (h ++ [s] ++ h') ++ [x] ∧
      h ++ (h' ++ [x]) = (h ++ h') ++ [x]’ by simp[]
  >> ASM_REWRITE_TAC[par_log_SNOC]
  >> first_x_assum (qspec_then ‘h' ++ [x]’ strip_assume_tac)
  >> ‘h ++ [s] ++ (h' ++ [x]) = (h ++ [s] ++ h') ++ [x] ∧
      h ++ (h' ++ [x]) = (h ++ h') ++ [x]’ by simp[]
  >> gvs[]
  >> ‘LENGTH (left_view m1 m2 (h ++ h' ++ [x])) = LENGTH h + LENGTH h' + 1 ∧
      LENGTH (right_view m1 m2 (h ++ h' ++ [x])) = LENGTH h + LENGTH h' + 1’
       by SIMP_TAC (srw_ss()) []
  >> ‘LENGTH R1 = LENGTH h' + 1’
       by (qpat_x_assum ‘LENGTH (left_view _ _ _) = _’ mp_tac
           >> qpat_x_assum ‘left_view m1 m2 (h ++ h' ++ [x]) = _’
                (fn th => REWRITE_TAC[th])
           >> simp[])
  >> ‘LENGTH R2 = LENGTH h' + 1’
       by (qpat_x_assum ‘LENGTH (right_view _ _ _) = _’ mp_tac
           >> qpat_x_assum ‘right_view m1 m2 (h ++ h' ++ [x]) = _’
                (fn th => REWRITE_TAC[th])
           >> simp[])
  >> ‘R1 ≠ [] ∧ R2 ≠ []’ by (conj_tac >> strip_tac >> fs[])
  >> ‘new_actions (log_of m1) (left_view m1 m2 h ++ [s] ++ R1) =
      new_actions (log_of m1) (left_view m1 m2 h ++ R1) ∧
      new_actions (log_of m2) (right_view m1 m2 h ++ [s] ++ R2) =
      new_actions (log_of m2) (right_view m1 m2 h ++ R2)’
       by (conj_tac >> irule new_actions_delete >> simp[])
  >> simp[]
QED

(* MAIN: both2 is quiet if its sides are *)
Theorem quiet_both2:
  wf c1.run ∧ wf c2.run ∧ quiet c1 ∧ quiet c2 ⇒ quiet (both2 c1 c2)
Proof
  strip_tac >> simp[quiet_def, both2_def] >> rpt gen_tac >> strip_tac
  >> qabbrev_tac ‘l = left_view c1.run c2.run h’
  >> qabbrev_tac ‘r = right_view c1.run c2.run h’
  (* neither side has a request in flight *)
  >> ‘new_actions (log_of c1.run) l = [] ∧ new_actions (log_of c2.run) r = []’
       by (Cases_on ‘h’ using SNOC_CASES
           >- (gvs[Abbr ‘l’, Abbr ‘r’, new_actions_NIL, both_def, par_log_def,
                   par_actions_NIL, log_of_def])
           >> gvs[SNOC_APPEND, both_new_actions, Abbr ‘l’, Abbr ‘r’])
  (* so s makes no difference to either side *)
  >> ‘∀k. c1.run (l ++ [s] ++ k) = c1.run (l ++ k) ∧
          waiting_on c1 (l ++ [s] ++ k) = waiting_on c1 (l ++ k)’
       by (irule side_delete >> fs[])
  >> ‘∀k. c2.run (r ++ [s] ++ k) = c2.run (r ++ k) ∧
          waiting_on c2 (r ++ [s] ++ k) = waiting_on c2 (r ++ k)’
       by (irule side_delete >> fs[])
  >> qspecl_then [‘c1.run’, ‘c2.run’, ‘h’, ‘s’] mp_tac
       (Q.GENL [‘m1’, ‘m2’, ‘h’, ‘s’] views_delete)
  >> impl_tac >- fs[Abbr ‘l’]
  >> disch_then (qspec_then ‘h'’ strip_assume_tac)
  >> qspecl_then [‘c1.run’, ‘c2.run’, ‘h’, ‘s’] mp_tac
       (Q.GENL [‘m1’, ‘m2’, ‘h’, ‘s’] par_log_delete)
  >> impl_tac >- fs[Abbr ‘l’, Abbr ‘r’]
  >> disch_then (qspec_then ‘h'’ strip_assume_tac)
  >> fs[Abbr ‘l’, Abbr ‘r’]
  >> simp[both_def, GSYM par_log_def]
QED

(* ------------------------------------------------------------------------
   choose2
   ------------------------------------------------------------------------ *)

(* choose, with the way the loser is packaged as a parameter: k1 l is the
   left side as a loser, after it has been shown l (and similarly k2) *)
Definition choose_with_def:
  choose_with k1 k2 m1 m2 h =
    case first_prefix (either_done m1 m2) h of
      NONE => <| actions := par_log m1 m2 h; result := NONE |>
    | SOME n =>
        let p = TAKE n h;
            l = left_view m1 m2 p;
            r = right_view m1 m2 p
        in
          case (m1 l).result of
            SOME x =>
              <| actions := log_before m1 m2 p ++ new_actions (log_of m1) l;
                 result := SOME (INL (x, k2 r)) |>
          | NONE =>
              let y = THE (m2 r).result in
              if new_actions (log_of m1) l = [] then
                <| actions := par_log m1 m2 p;
                   result := SOME (INR (k1 l, y)) |>
              else if LENGTH h = n then
                <| actions := par_log m1 m2 p; result := NONE |>
              else
                <| actions := par_log m1 m2 p;
                   result :=
                     SOME (INR (k1 (left_view m1 m2 (TAKE (n + 1) h)), y)) |>
End

Theorem choose_as_choose_with:
  choose m1 m2 = choose_with (suspended m1) (suspended m2) m1 m2
Proof
  simp[FUN_EQ_THM, choose_def, choose_with_def]
QED

(* Mapping over the loser *)
Definition map_loser_def:
  map_loser g1 g2 r =
    case r of INL (x, l) => INL (x, g2 l) | INR (l, y) => INR (g1 l, y)
End

Theorem map_choose_with:
  map (map_loser g1 g2) (choose_with k1 k2 m1 m2) =
  choose_with (g1 o k1) (g2 o k2) m1 m2
Proof
  simp[FUN_EQ_THM, map_def, choose_with_def] >> gen_tac
  >> rpt (CASE_TAC >> simp[map_loser_def])
QED

(* The rest of a Level 2 computation, suspended after r *)
Definition suspended2_def:
  suspended2 c r = <| run := suspended c.run r; interest := λh. c.interest (r ++ h) |>
End

(* Until a side finishes, choose2 waits for what either side waits for.
   Afterwards it is finished, or (for one round) waits only for responses. *)
Definition choose_interest_def:
  choose_interest c1 c2 h =
    case first_prefix (either_done c1.run c2.run) h of
      NONE => waiting_on c1 (left_view c1.run c2.run h) ∪
              waiting_on c2 (right_view c1.run c2.run h)
    | SOME _ => ∅
End

Definition choose2_def:
  choose2 c1 c2 =
    <| run := choose_with (suspended2 c1) (suspended2 c2) c1.run c2.run;
       interest := choose_interest c1 c2 |>
End

(* MAIN: erasure commutes with choose (erasing the loser too) *)
Theorem erase_choose2:
  map (map_loser erase erase) (erase (choose2 c1 c2)) =
  choose (erase c1) (erase c2)
Proof
  simp[erase_def, choose2_def, map_choose_with, choose_as_choose_with]
  >> ‘erase o suspended2 c1 = suspended c1.run ∧
      erase o suspended2 c2 = suspended c2.run’
       by simp[FUN_EQ_THM, erase_def, suspended2_def]
  >> simp[]
QED

(* ------------------------------------------------------------------------
   choose2 is quiet
   ------------------------------------------------------------------------ *)

Theorem TAKE_IS_PREFIX[local]:
  TAKE n h ≼ h
Proof
  metis_tac[TAKE_DROP, IS_PREFIX_APPEND3]
QED

Theorem choose_finished_before[local]:
  (choose m1 m2 p).result ≠ NONE ∧ p ≼ h ⇒ (choose m1 m2 h).result ≠ NONE
Proof
  strip_tac >> Cases_on ‘(choose m1 m2 p).result’ >> fs[]
  >> ‘choose m1 m2 h = choose m1 m2 p’
       by (irule wf_finished_stays >> simp[wf_choose] >> metis_tac[])
  >> simp[]
QED

(* If choose has not finished and has no request in flight, no side has
   finished yet (the round in which choose waits for responses has requests
   in flight) *)
Theorem choose_quiet_point:
  (choose m1 m2 h).result = NONE ∧ new_actions (log_of (choose m1 m2)) h = [] ⇒
  first_prefix (either_done m1 m2) h = NONE
Proof
  rpt strip_tac >> spose_not_then assume_tac
  >> Cases_on ‘first_prefix (either_done m1 m2) h’ >> fs[]
  >> rename1 ‘_ = SOME n’
  >> drule first_either_done_TAKE >> strip_tac
  >> qabbrev_tac ‘p = TAKE n h’
  >> ‘p ≼ h’ by simp[Abbr ‘p’, TAKE_IS_PREFIX]
  >> Cases_on ‘(m1 (left_view m1 m2 p)).result’
  >- (‘(m2 (right_view m1 m2 p)).result ≠ NONE’
        by metis_tac[first_either_done_either]
      >> Cases_on ‘(m2 (right_view m1 m2 p)).result’ >> fs[]
      >> Cases_on ‘new_actions (log_of m1) (left_view m1 m2 p) = []’
      >- (drule_all choose_right_wins >> strip_tac
          >> ‘(choose m1 m2 p).result ≠ NONE’ by fs[first_done_def]
          >> metis_tac[choose_finished_before])
      >> Cases_on ‘n = LENGTH h’
      >- (‘p = h’ by simp[Abbr ‘p’, TAKE_LENGTH_ID]
          >> drule choose_new_actions_at >> drule_all choose_right_waits
          >> rpt strip_tac >> gvs[]
          >> qpat_x_assum ‘LENGTH _ ≤ _’ mp_tac
          >> simp[Once par_log_log_before]
          >> Cases_on ‘new_actions (log_of m1) (left_view m1 m2 h)’ >> fs[])
      >> ‘n < LENGTH h’ by simp[]
      >> drule_all choose_right_wins_later
      >> disch_then (qspec_then ‘EL n h’ strip_assume_tac)
      >> ‘p ++ [EL n h] = TAKE (n + 1) h’
           by simp[Abbr ‘p’, TAKE_EL_SNOC, SNOC_APPEND]
      >> ‘(choose m1 m2 (TAKE (n + 1) h)).result ≠ NONE’
           by (qpat_x_assum ‘_ = TAKE (n + 1) h’ (SUBST_ALL_TAC o GSYM)
               >> fs[first_done_def])
      >> metis_tac[choose_finished_before, TAKE_IS_PREFIX])
  >> drule_all choose_left_wins >> strip_tac
  >> ‘(choose m1 m2 p).result ≠ NONE’ by fs[first_done_def]
  >> metis_tac[choose_finished_before]
QED

(* choose2's log and finishing are those of the Level 1 choose *)
Theorem choose2_run:
  ((choose2 c1 c2).run h).actions = (choose c1.run c2.run h).actions ∧
  (((choose2 c1 c2).run h).result = NONE ⇔ (choose c1.run c2.run h).result = NONE)
Proof
  simp[choose2_def, choose_as_choose_with] >> simp[choose_with_def]
  >> rpt (CASE_TAC >> simp[])
QED

Theorem log_of_choose2:
  log_of (choose2 c1 c2).run = log_of (choose c1.run c2.run)
Proof
  simp[FUN_EQ_THM, log_of_def, choose2_run]
QED

(* Deleting an irrelevant snapshot from a suspended side's view *)
Theorem suspended2_delete:
  (∀k. c.run (v ++ [s] ++ k) = c.run (v ++ k) ∧
       c.interest (v ++ [s] ++ k) = c.interest (v ++ k)) ∧ R ≠ [] ⇒
  suspended2 c (v ++ [s] ++ R) = suspended2 c (v ++ R)
Proof
  strip_tac
  >> ‘FRONT (v ++ [s] ++ R) = v ++ [s] ++ FRONT R ∧
      FRONT (v ++ R) = v ++ FRONT R’
       by (Cases_on ‘R’ using SNOC_CASES >> fs[FRONT_APPEND, SNOC_APPEND]
           >> REWRITE_TAC[GSYM APPEND_ASSOC, FRONT_APPEND, NOT_CONS_NIL]
           >> simp[FRONT_APPEND])
  >> simp[suspended2_def, theorem "comp2_component_equality"] >> conj_tac
  >- (simp[FUN_EQ_THM, outcome_component_equality, suspended_actions]
      >> qx_gen_tac ‘g’
      >> first_assum (qspec_then ‘R ++ g’ mp_tac)
      >> first_assum (qspec_then ‘FRONT R’ mp_tac)
      >> REWRITE_TAC[APPEND_ASSOC] >> simp[])
  >> CONV_TAC FUN_EQ_CONV >> qx_gen_tac ‘g’ >> BETA_TAC
  >> first_assum (qspec_then ‘R ++ g’ mp_tac)
  >> REWRITE_TAC[APPEND_ASSOC] >> simp[]
QED

(* Deleting a snapshot that both sides ignore, before either has finished,
   changes nothing about choose (with any packaging of the loser that also
   ignores it) *)
Theorem choose_with_delete:
  (∀k. m1 (left_view m1 m2 h ++ [s] ++ k) = m1 (left_view m1 m2 h ++ k)) ∧
  (∀k. m2 (right_view m1 m2 h ++ [s] ++ k) = m2 (right_view m1 m2 h ++ k)) ∧
  new_actions (log_of m1) (left_view m1 m2 h) = [] ∧ s.results = [] ∧
  (∀R. R ≠ [] ⇒ k1 (left_view m1 m2 h ++ [s] ++ R) = k1 (left_view m1 m2 h ++ R)) ∧
  (∀R. R ≠ [] ⇒ k2 (right_view m1 m2 h ++ [s] ++ R) = k2 (right_view m1 m2 h ++ R)) ∧
  first_prefix (either_done m1 m2) h = NONE ⇒
  ∀h'. (first_prefix (either_done m1 m2) (h ++ [s] ++ h') = NONE ⇔
        first_prefix (either_done m1 m2) (h ++ h') = NONE) ∧
       choose_with k1 k2 m1 m2 (h ++ [s] ++ h') = choose_with k1 k2 m1 m2 (h ++ h')
Proof
  strip_tac
  >> qspecl_then [‘m1’, ‘m2’, ‘h’, ‘s’] mp_tac
       (Q.GENL [‘m1’, ‘m2’, ‘h’, ‘s’] views_delete)
  >> impl_tac >- simp[]
  >> strip_tac
  >> qspecl_then [‘m1’, ‘m2’, ‘h’, ‘s’] mp_tac
       (Q.GENL [‘m1’, ‘m2’, ‘h’, ‘s’] par_log_delete)
  >> impl_tac >- simp[]
  >> strip_tac
  (* whether a side has finished does not depend on s *)
  >> ‘∀k. either_done m1 m2 (h ++ [s] ++ k) ⇔ either_done m1 m2 (h ++ k)’
       by (gen_tac >> qpat_assum ‘∀h'. ∃R1 R2. _’ (qspec_then ‘k’ strip_assume_tac)
           >> simp[either_done_def])
  >> gen_tac
  >> ‘first_prefix (either_done m1 m2) (h ++ [s] ++ h') =
      OPTION_MAP SUC (first_prefix (either_done m1 m2) (h ++ h'))’
       by (irule first_prefix_delete >> simp[])
  >> Cases_on ‘first_prefix (either_done m1 m2) (h ++ h')’
  >- simp[choose_with_def]
  >> rename1 ‘_ = SOME n’
  >> ‘LENGTH h < n ∧ n ≤ LENGTH h + LENGTH h'’
       by (fs[first_prefix_SOME, first_prefix_NONE] >> spose_not_then assume_tac
           >> ‘n ≤ LENGTH h’ by simp[]
           >> ‘TAKE n (h ++ h') = TAKE n h’ by simp[TAKE_APPEND1]
           >> metis_tac[])
  >> ‘∃j. n = LENGTH h + j ∧ 0 < j’ by (qexists_tac ‘n - LENGTH h’ >> simp[])
  >> gvs[]
  >> ‘j ≤ LENGTH h'’ by simp[]
  >> qabbrev_tac ‘q = TAKE j h'’
  >> ‘q ≠ []’ by (simp[Abbr ‘q’] >> Cases_on ‘h'’ >> fs[])
  >> ‘TAKE (SUC (j + LENGTH h)) (h ++ [s] ++ h') = h ++ [s] ++ q ∧
      TAKE (j + LENGTH h) (h ++ h') = h ++ q’
       by simp[Abbr ‘q’, TAKE_APPEND, TAKE_LENGTH_TOO_LONG, ADD1]
  >> qpat_assum ‘∀h'. ∃R1 R2. _’ (qspec_then ‘q’ strip_assume_tac)
  >> ‘R1 ≠ [] ∧ R2 ≠ []’
       by (‘LENGTH (left_view m1 m2 (h ++ q)) = LENGTH h + LENGTH q ∧
            LENGTH (right_view m1 m2 (h ++ q)) = LENGTH h + LENGTH q’
             by SIMP_TAC (srw_ss()) []
           >> ‘LENGTH q ≠ 0’ by (Cases_on ‘q’ >> fs[])
           >> conj_tac >> strip_tac
           >> qpat_x_assum ‘LENGTH (_ _ _ (h ++ q)) = _’ mp_tac
           >> qpat_x_assum ‘LENGTH (_ _ _ (h ++ q)) = _’ mp_tac
           >> qpat_x_assum ‘left_view m1 m2 (h ++ q) = _’ (fn th => REWRITE_TAC[th])
           >> qpat_x_assum ‘right_view m1 m2 (h ++ q) = _’ (fn th => REWRITE_TAC[th])
           >> simp[])
  >> ‘new_actions (log_of m1) (left_view m1 m2 h ++ [s] ++ R1) =
      new_actions (log_of m1) (left_view m1 m2 h ++ R1)’
       by (irule new_actions_delete >> simp[])
  >> ‘log_before m1 m2 (h ++ [s] ++ q) = log_before m1 m2 (h ++ q)’
       by (simp[log_before_def]
           >> ‘FRONT (h ++ [s] ++ q) = h ++ [s] ++ FRONT q ∧
               FRONT (h ++ q) = h ++ FRONT q’
                by (Cases_on ‘q’ using SNOC_CASES >> fs[SNOC_APPEND]
                    >> REWRITE_TAC[GSYM APPEND_ASSOC, FRONT_APPEND, NOT_CONS_NIL]
                    >> simp[FRONT_APPEND])
           >> simp[])
  (* the round after, for the case where choose waits for responses *)
  >> qabbrev_tac ‘q' = TAKE (j + 1) h'’
  >> qabbrev_tac ‘M = j + LENGTH h’
  >> qabbrev_tac ‘N = SUC M’
  >> ‘TAKE (N + 1) (h ++ [s] ++ h') = h ++ [s] ++ q' ∧
      TAKE (M + 1) (h ++ h') = h ++ q' ∧
      (LENGTH (h ++ [s] ++ h') = N ⇔ LENGTH (h ++ h') = M)’
       by simp[Abbr ‘q'’, Abbr ‘M’, Abbr ‘N’, TAKE_APPEND, TAKE_LENGTH_TOO_LONG,
               ADD1]
  >> qpat_assum ‘∀h'. ∃R1 R2. _’ (qspec_then ‘q'’ strip_assume_tac)
  >> rename1 ‘left_view m1 m2 (h ++ q') = left_view m1 m2 h ++ R1'’
  >> ‘R1' ≠ []’
       by (‘LENGTH (left_view m1 m2 (h ++ q')) = LENGTH h + LENGTH q'’
             by SIMP_TAC (srw_ss()) []
           >> ‘LENGTH q' ≠ 0’
                by (qpat_x_assum ‘j ≤ LENGTH h'’ mp_tac
                    >> qpat_x_assum ‘0 < j’ mp_tac
                    >> qpat_x_assum ‘Abbrev (q' = _)’
                         (fn th => REWRITE_TAC[REWRITE_RULE[markerTheory.Abbrev_def] th])
                    >> SIMP_TAC (srw_ss()) [LENGTH_TAKE_EQ]
                    >> Cases_on ‘h'’ >> SIMP_TAC (srw_ss() ++ ARITH_ss) [])
           >> strip_tac
           >> qpat_x_assum ‘LENGTH (_ _ _ (h ++ q')) = _’ mp_tac
           >> qpat_x_assum ‘left_view m1 m2 (h ++ q') = _’ (fn th => REWRITE_TAC[th])
           >> simp[])
  >> ONCE_REWRITE_TAC[choose_with_def] >> ASM_REWRITE_TAC[]
  >> simp[]
QED

(* MAIN: choose2 is quiet if its sides are *)
Theorem quiet_choose2:
  wf c1.run ∧ wf c2.run ∧ quiet c1 ∧ quiet c2 ⇒ quiet (choose2 c1 c2)
Proof
  strip_tac >> simp[quiet_def] >> rpt gen_tac >> strip_tac
  (* no side has finished yet, so choose2 is running both sides *)
  >> ‘first_prefix (either_done c1.run c2.run) h = NONE’
       by (irule choose_quiet_point >> gvs[choose2_run, log_of_choose2])
  >> qabbrev_tac ‘l = left_view c1.run c2.run h’
  >> qabbrev_tac ‘r = right_view c1.run c2.run h’
  >> ‘(c1.run l).result = NONE ∧ (c2.run r).result = NONE’
       by (qpat_x_assum ‘first_prefix _ h = NONE’ mp_tac
           >> simp[first_prefix_NONE] >> disch_then (qspec_then ‘LENGTH h’ mp_tac)
           >> simp[TAKE_LENGTH_ID, either_done_def, Abbr ‘l’, Abbr ‘r’])
  (* neither side has a request in flight *)
  >> ‘new_actions (log_of c1.run) l = [] ∧ new_actions (log_of c2.run) r = []’
       by (qpat_x_assum ‘new_actions _ h = []’ mp_tac
           >> simp[log_of_choose2]
           >> Cases_on ‘h’ using SNOC_CASES
           >- simp[Abbr ‘l’, Abbr ‘r’, new_actions_NIL, log_of_def, choose_running,
                   par_log_def, par_actions_NIL]
           >> fs[SNOC_APPEND]
           >> ‘first_prefix (either_done c1.run c2.run) l' = NONE’
                by fs[first_prefix_SNOC, AllCaseEqs()]
           >> simp[new_actions_SNOC, log_of_def, choose_running, par_log_SNOC,
                   Abbr ‘l’, Abbr ‘r’]
           >> Cases_on ‘new_actions (log_of c1.run) (left_view c1.run c2.run (l' ++ [x]))’
           >> Cases_on ‘new_actions (log_of c2.run) (right_view c1.run c2.run (l' ++ [x]))’
           >> simp[])
  >> ‘DISJOINT (c1.interest l) s.ready ∧ DISJOINT (c2.interest r) s.ready’
       by (qpat_x_assum ‘DISJOINT _ _’ mp_tac
           >> simp[choose2_def, choose_interest_def, waiting_on_def,
                   Abbr ‘l’, Abbr ‘r’])
  (* so s makes no difference to either side *)
  >> ‘∀k. c1.run (l ++ [s] ++ k) = c1.run (l ++ k) ∧
          c1.interest (l ++ [s] ++ k) = c1.interest (l ++ k)’
       by (gen_tac >> qpat_x_assum ‘quiet c1’ mp_tac >> simp[quiet_def]
           >> disch_then irule >> simp[])
  >> ‘∀k. c2.run (r ++ [s] ++ k) = c2.run (r ++ k) ∧
          c2.interest (r ++ [s] ++ k) = c2.interest (r ++ k)’
       by (gen_tac >> qpat_x_assum ‘quiet c2’ mp_tac >> simp[quiet_def]
           >> disch_then irule >> simp[])
  >> qspecl_then [‘c1.run’, ‘c2.run’, ‘h’, ‘s’, ‘suspended2 c1’, ‘suspended2 c2’]
       mp_tac (Q.GENL [‘m1’, ‘m2’, ‘h’, ‘s’, ‘k1’, ‘k2’] choose_with_delete)
  >> impl_tac
  >- (fs[Abbr ‘l’, Abbr ‘r’] >> rpt strip_tac
      >> irule suspended2_delete >> simp[])
  >> disch_then (qspec_then ‘h'’ strip_assume_tac)
  >> simp[choose2_def, choose_interest_def]
  >> Cases_on ‘first_prefix (either_done c1.run c2.run) (h ++ h')’
  >> Cases_on ‘first_prefix (either_done c1.run c2.run) (h ++ [s] ++ h')’ >> fs[]
  (* still running: the waiting sets are the sides' *)
  >> qspecl_then [‘c1.run’, ‘c2.run’, ‘h’, ‘s’] mp_tac
       (Q.GENL [‘m1’, ‘m2’, ‘h’, ‘s’] views_delete)
  >> impl_tac >- fs[Abbr ‘l’]
  >> disch_then (qspec_then ‘h'’ strip_assume_tac)
  >> fs[Abbr ‘l’, Abbr ‘r’, waiting_on_def]
QED
