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
  pair list rich_list arithmetic option pred_set asyncCore asyncLevel1
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

(* MAIN: monad laws at Level 2, up to erasure *)
Theorem bind2_left_identity:
  erase (bind2 (return2 x) f) = erase (f x)
Proof
  simp[erase_bind2, erase_return2, bind_left_identity]
QED

Theorem bind2_right_identity:
  wf (erase c) ⇒ erase (bind2 c return2) = erase c
Proof
  strip_tac >> simp[erase_bind2, erase_return2]
  >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[bind_right_identity]
QED

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

(* MAIN: bind2 is quiet if its parts are *)
Theorem quiet_bind2:
  wf c.run ∧ quiet c ∧ (∀x. quiet (f x)) ⇒ quiet (bind2 c f)
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
  >> ‘quiet (f x)’ by simp[]
  >> pop_assum (mp_tac o REWRITE_RULE[quiet_def])
  >> disch_then (qspecl_then [‘skip_results kc h2’, ‘s’, ‘h'’] mp_tac)
  >> impl_tac >- simp[]
  >> strip_tac
  >> ‘h1 ++ h2 ++ [s] ++ h' = h1 ++ (h2 ++ [s] ++ h') ∧
      h1 ++ h2 ++ h' = h1 ++ (h2 ++ h')’ by simp[]
  >> ASM_REWRITE_TAC[]
  >> continues_tac
QED
