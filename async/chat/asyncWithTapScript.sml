(*
  with_tap: an effect handler that also OBSERVES its inner computation's I/O.

  It generalises with_store (asyncWithStore).  The inner computation m
  emits Sock a (an action for the world) and Kv q (a query on a store).
  with_tap σ δ s0 m is an ordinary computation that emits only m's Sock
  actions.  It keeps a store that starts as s0 and that it updates, in the
  order of m's action log:
   - on each Sock action whose response r has arrived: σ st a r (the tap);
   - on each query q: δ st q = (answer, new store), the answer going back
     to m at q's position among the round's results, as with_store does.
  So the store at any position of m's transcript is a fold over the
  transcript up to that position (tap_answers).  with_store δ s0 m is the
  special case σ st a r = st.

  Why: a sequencer whose order is defined by I/O (e.g. "the order in which
  lines were read") gets that order by construction: the tap sees the
  reads exactly in the order the world performed them.

  MAIN results:
   - wf_with_tap: with_tap preserves well-formedness;
   - new_actions_with_tap: each round, with_tap emits m's Sock actions;
   - trans_with_tap: the transcript of with_tap σ δ s0 m is m's transcript
     on the inner history, with the Kv entries removed;
   - tap_answers: every answer m has received was computed by δ on the fold
     of the transcript before the query.
*)
Theory asyncWithTap
Ancestors
  pair list rich_list arithmetic option asyncCore asyncLevel1 asyncTranscript
  asyncWithStore
Libs
  BasicProvers

(* ------------------------------------------------------------------------
   One round
   ------------------------------------------------------------------------ *)

(* Run the store over a round's actions acts, given the world's results rs
   for its Sock actions (in order): the answers to the queries, and the
   store after the round.  A Sock action without a result is not tapped. *)
Definition run_tap_def:
  run_tap σ δ st [] rs = ([], st) ∧
  run_tap σ δ st (Sock x :: acts) rs =
    (case rs of
     | [] => run_tap σ δ st acts []
     | r :: rs' => run_tap σ δ (σ st x r) acts rs') ∧
  run_tap σ δ st (Kv q :: acts) rs =
    (let (b, st1) = δ st q;
         (bs, st2) = run_tap σ δ st1 acts rs
     in (b :: bs, st2))
End

(* The fold over a transcript: answered Sock entries are tapped, queries
   are run (answered or not) *)
Definition tap_fold_def:
  tap_fold σ δ st [] = st ∧
  tap_fold σ δ st ((Sock x, r) :: tr) =
    tap_fold σ δ (case r of SOME (SockR y) => σ st x y | _ => st) tr ∧
  tap_fold σ δ st ((Kv q, r) :: tr) = tap_fold σ δ (SND (δ st q)) tr
End

(* The history m sees, and the store, when with_tap σ δ s0 m sees h *)
Definition tap_state_def:
  tap_state σ δ s0 m h =
    if h = [] then ([], s0)
    else
      let (ih, st) = tap_state σ δ s0 m (FRONT h);
          acts = new_actions (log_of m) ih;
          s = LAST h;
          (ans, st') = run_tap σ δ st acts s.results
      in (ih ++ [s with results := merge acts s.results ans], st')
Termination
  WF_REL_TAC ‘measure (LENGTH o SND o SND o SND o SND)’
  >> Cases_on ‘h’ using SNOC_CASES >> simp[FRONT_APPEND]
End

Definition tap_hist_def:
  tap_hist σ δ s0 m h = FST (tap_state σ δ s0 m h)
End

Definition with_tap_def:
  with_tap σ δ s0 m h =
    <| actions := socks (m (tap_hist σ δ s0 m h)).actions;
       result := (m (tap_hist σ δ s0 m h)).result |>
End

(* ------------------------------------------------------------------------
   Lists
   ------------------------------------------------------------------------ *)

Theorem LENGTH_run_tap[simp]:
  ∀acts st rs. LENGTH (FST (run_tap σ δ st acts rs)) = LENGTH (queries acts)
Proof
  Induct >> simp[run_tap_def] >> Cases >> simp[run_tap_def] >> rpt gen_tac
  >- (Cases_on ‘rs’ >> simp[])
  >> rpt (pairarg_tac >> gvs[]) >> metis_tac[FST]
QED

Theorem tap_fold_APPEND:
  ∀l1 st. tap_fold σ δ st (l1 ++ l2) = tap_fold σ δ (tap_fold σ δ st l1) l2
Proof
  Induct >> simp[tap_fold_def] >> PairCases >> Cases_on ‘h0’ >> simp[tap_fold_def]
QED

Theorem tap_fold_zipr_NIL:
  ∀acts st. tap_fold σ δ st (zipr acts []) = SND (run_tap σ δ st acts [])
Proof
  Induct >> simp[zipr_def, tap_fold_def, run_tap_def] >> Cases >>
  simp[zipr_def, tap_fold_def, run_tap_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[])
QED

(* The round's transcript, as the store sees it: the fold over it is the
   store after the round, and each answered query got δ on the fold of the
   entries before it *)
Theorem tap_fold_round:
  ∀acts st rs.
    tap_fold σ δ st (zipr acts (merge acts rs (FST (run_tap σ δ st acts rs)))) =
    SND (run_tap σ δ st acts rs)
Proof
  Induct >> simp[zipr_def, merge_def, tap_fold_def, run_tap_def] >> Cases >>
  rpt gen_tac
  >- (Cases_on ‘rs’ >> simp[merge_def, zipr_def, tap_fold_def, run_tap_def,
                            tap_fold_zipr_NIL])
  >> simp[run_tap_def] >> rpt (pairarg_tac >> gvs[]) >>
  simp[merge_def, zipr_def, tap_fold_def] >>
  qpat_x_assum ‘run_tap _ _ _ _ _ = _’ (fn th => assume_tac th >>
    first_x_assum (qspecl_then [‘st1’, ‘rs’] mp_tac) >> simp[th])
QED

(* Each entry of a round's transcript that is an answered query has δ's
   answer on the fold of the entries before it *)
Definition answers_ok_def:
  answers_ok σ δ st tr ⇔
    ∀i q r. i < LENGTH tr ∧ EL i tr = (Kv q, SOME r) ⇒
            r = KvR (FST (δ (tap_fold σ δ st (TAKE i tr)) q))
End

Theorem answers_ok_NIL[simp]:
  answers_ok σ δ st []
Proof
  simp[answers_ok_def]
QED

Theorem answers_ok_CONS:
  answers_ok σ δ st (e :: tr) ⇔
    (∀q r. e = (Kv q, SOME r) ⇒ r = KvR (FST (δ st q))) ∧
    answers_ok σ δ (tap_fold σ δ st [e]) tr
Proof
  rw[answers_ok_def, EQ_IMP_THM]
  >- (first_x_assum (qspec_then ‘0’ mp_tac) >> simp[tap_fold_def])
  >- (first_x_assum (qspec_then ‘SUC i’ mp_tac) >> simp[] >>
      ‘tap_fold σ δ st (e :: TAKE i tr) =
       tap_fold σ δ (tap_fold σ δ st [e]) (TAKE i tr)’
        by simp[GSYM tap_fold_APPEND] >> simp[])
  >> Cases_on ‘i’ >> gvs[tap_fold_def] >>
  first_x_assum drule >> simp[] >>
  ‘tap_fold σ δ st (e :: TAKE n tr) =
   tap_fold σ δ (tap_fold σ δ st [e]) (TAKE n tr)’
    by simp[GSYM tap_fold_APPEND] >> simp[]
QED

Theorem answers_ok_APPEND:
  ∀l1 st. answers_ok σ δ st (l1 ++ l2) ⇔
          answers_ok σ δ st l1 ∧ answers_ok σ δ (tap_fold σ δ st l1) l2
Proof
  Induct >> simp[answers_ok_CONS, tap_fold_def] >> rpt gen_tac >>
  simp[GSYM tap_fold_APPEND] >> metis_tac[]
QED

Theorem answers_ok_zipr_NIL:
  ∀acts st. answers_ok σ δ st (zipr acts [])
Proof
  Induct >> simp[zipr_def, answers_ok_CONS]
QED

Theorem answers_ok_round:
  ∀acts st rs.
    answers_ok σ δ st (zipr acts (merge acts rs (FST (run_tap σ δ st acts rs))))
Proof
  Induct >> simp[zipr_def, merge_def] >> Cases >> rpt gen_tac
  >- (Cases_on ‘rs’ >> simp[merge_def, zipr_def, answers_ok_zipr_NIL, run_tap_def,
                            answers_ok_CONS, tap_fold_def])
  >> simp[run_tap_def] >> rpt (pairarg_tac >> gvs[]) >>
  simp[merge_def, zipr_def, answers_ok_CONS, tap_fold_def] >>
  qpat_x_assum ‘run_tap _ _ _ _ _ = _’ (fn th => assume_tac th >>
    first_x_assum (qspecl_then [‘st1’, ‘rs’] mp_tac) >> simp[th])
QED

Theorem untag_zipr_merge_tap:
  untag (zipr acts (merge acts rs (FST (run_tap σ δ st acts rs)))) =
  zipr (socks acts) rs
Proof
  irule untag_zipr_merge >> simp[]
QED

(* ------------------------------------------------------------------------
   The inner history
   ------------------------------------------------------------------------ *)

Theorem tap_state_NIL[simp]:
  tap_state σ δ s0 m [] = ([], s0)
Proof
  simp[Once tap_state_def]
QED

Theorem tap_state_SNOC:
  tap_state σ δ s0 m (h ++ [s]) =
    let (ih, st) = tap_state σ δ s0 m h;
        acts = new_actions (log_of m) ih;
        (ans, st') = run_tap σ δ st acts s.results
    in (ih ++ [s with results := merge acts s.results ans], st')
Proof
  simp[Once tap_state_def, FRONT_APPEND]
QED

Theorem tap_hist_NIL[simp]:
  tap_hist σ δ s0 m [] = []
Proof
  simp[tap_hist_def]
QED

Theorem tap_hist_SNOC:
  tap_hist σ δ s0 m (h ++ [s]) =
    let ih = tap_hist σ δ s0 m h;
        acts = new_actions (log_of m) ih
    in ih ++ [s with results :=
                merge acts s.results
                  (FST (run_tap σ δ (SND (tap_state σ δ s0 m h)) acts s.results))]
Proof
  simp[tap_hist_def, tap_state_SNOC] >>
  Cases_on ‘tap_state σ δ s0 m h’ >> simp[] >> rpt (pairarg_tac >> gvs[])
QED

Theorem LENGTH_tap_hist[simp]:
  ∀h. LENGTH (tap_hist σ δ s0 m h) = LENGTH h
Proof
  Induct_on ‘h’ using SNOC_INDUCT >> simp[SNOC_APPEND, tap_hist_SNOC]
QED

(* MAIN: the inner history of a prefix is the prefix of the inner history *)
Theorem tap_hist_TAKE:
  ∀h n. tap_hist σ δ s0 m (TAKE n h) = TAKE n (tap_hist σ δ s0 m h)
Proof
  Induct_on ‘h’ using SNOC_INDUCT >> simp[SNOC_APPEND] >> rpt gen_tac >>
  Cases_on ‘n ≤ LENGTH h’
  >- simp[TAKE_APPEND1, tap_hist_SNOC] >>
  ‘TAKE n (h ++ [x]) = h ++ [x]’ by simp[TAKE_LENGTH_TOO_LONG] >>
  simp[tap_hist_SNOC, TAKE_LENGTH_TOO_LONG]
QED

(* ------------------------------------------------------------------------
   with_tap is a computation like any other
   ------------------------------------------------------------------------ *)

(* MAIN: with_tap preserves well-formedness *)
Theorem wf_with_tap:
  wf m ⇒ wf (with_tap σ δ s0 m)
Proof
  rw[wf_def, with_tap_def, tap_hist_SNOC] >>
  qmatch_goalsub_abbrev_tac ‘tap_hist σ δ s0 m h ++ [s']’
  >- (first_x_assum (qspecl_then [‘tap_hist σ δ s0 m h’, ‘s'’] strip_assume_tac) >>
      gvs[IS_PREFIX_APPEND]) >>
  first_x_assum (qspecl_then [‘tap_hist σ δ s0 m h’, ‘s'’] strip_assume_tac) >>
  gvs[]
QED

(* MAIN: each round, with_tap emits m's Sock actions of that round *)
Theorem new_actions_with_tap:
  wf m ⇒
  new_actions (log_of (with_tap σ δ s0 m)) h =
    socks (new_actions (log_of m) (tap_hist σ δ s0 m h))
Proof
  strip_tac >> Cases_on ‘h’ using SNOC_CASES
  >- simp[new_actions_NIL, log_of_def, with_tap_def] >>
  REWRITE_TAC[SNOC_APPEND] >>
  qabbrev_tac ‘ih = tap_hist σ δ s0 m l’ >>
  qabbrev_tac ‘s' = x with results :=
                 merge (new_actions (log_of m) ih) x.results
                   (FST (run_tap σ δ (SND (tap_state σ δ s0 m l))
                          (new_actions (log_of m) ih) x.results))’ >>
  ‘tap_hist σ δ s0 m (l ++ [x]) = ih ++ [s']’
    by simp[tap_hist_SNOC, Abbr ‘ih’, Abbr ‘s'’] >>
  ‘new_actions (log_of (with_tap σ δ s0 m)) (l ++ [x]) =
   DROP (LENGTH (socks (m ih).actions)) (socks (m (ih ++ [s'])).actions)’
    by simp[new_actions_SNOC, log_of_def, with_tap_def, Abbr ‘ih’] >>
  simp[] >>
  drule wf_log_SNOC >> disch_then (qspecl_then [‘ih’, ‘s'’] SUBST1_TAC) >>
  simp[DROP_LENGTH_APPEND]
QED

(* The results m sees in round n *)
Theorem EL_tap_hist:
  n < LENGTH h ⇒
  (EL n (tap_hist σ δ s0 m h)).results =
    let ih = TAKE n (tap_hist σ δ s0 m h);
        acts = new_actions (log_of m) ih
    in merge acts (EL n h).results
         (FST (run_tap σ δ (SND (tap_state σ δ s0 m (TAKE n h))) acts (EL n h).results))
Proof
  strip_tac >>
  ‘TAKE (SUC n) h = TAKE n h ++ [EL n h]’ by simp[TAKE_SUC_EL] >>
  ‘TAKE (SUC n) (tap_hist σ δ s0 m h) =
   TAKE n (tap_hist σ δ s0 m h) ++ [EL n (tap_hist σ δ s0 m h)]’
    by simp[TAKE_SUC_EL] >>
  ‘tap_hist σ δ s0 m (TAKE (SUC n) h) = TAKE (SUC n) (tap_hist σ δ s0 m h)’
    by simp[tap_hist_TAKE] >>
  qpat_x_assum ‘tap_hist _ _ _ _ (TAKE (SUC n) h) = _’ mp_tac >>
  ASM_REWRITE_TAC[] >> REWRITE_TAC[tap_hist_SNOC] >> simp[tap_hist_TAKE] >>
  disch_then (SUBST1_TAC o SYM) >> simp[]
QED

Theorem untag_zipr_NIL[local]:
  ∀acts. untag (zipr acts []) = zipr (socks acts) []
Proof
  Induct >> simp[zipr_def, untag_def] >> Cases >> simp[zipr_def] >>
  fs[untag_def]
QED

Theorem round_trans_with_tap:
  wf m ∧ n ≤ LENGTH h ⇒
  round_trans (with_tap σ δ s0 m) h n =
    untag (round_trans m (tap_hist σ δ s0 m h) n)
Proof
  rw[round_trans_def, new_actions_with_tap, tap_hist_TAKE, responses_at_def] >>
  Cases_on ‘n < LENGTH h’ >> simp[untag_zipr_NIL] >>
  simp[EL_tap_hist, untag_zipr_merge_tap]
QED

(* MAIN: the transcript of with_tap σ δ s0 m is m's transcript on the inner
   history, without its Kv entries *)
Theorem trans_with_tap:
  wf m ⇒
  trans (with_tap σ δ s0 m) h = untag (trans m (tap_hist σ δ s0 m h))
Proof
  rw[trans_def, untag_FLAT, MAP_GENLIST] >>
  AP_TERM_TAC >> simp[GENLIST_FUN_EQ, round_trans_with_tap]
QED

(* ------------------------------------------------------------------------
   The answers
   ------------------------------------------------------------------------ *)

(* The store at the start of round k is the fold over rounds < k *)
Theorem tap_state_rounds:
  ∀k. k ≤ LENGTH h ⇒
      SND (tap_state σ δ s0 m (TAKE k h)) =
      tap_fold σ δ s0 (FLAT (GENLIST (round_trans m (tap_hist σ δ s0 m h)) k))
Proof
  Induct >- simp[tap_fold_def] >> strip_tac >>
  ‘k < LENGTH h’ by simp[] >>
  ‘TAKE (SUC k) h = TAKE k h ++ [EL k h]’ by simp[TAKE_SUC_EL] >>
  simp[GENLIST, SNOC_APPEND, tap_fold_APPEND] >>
  qpat_x_assum ‘k ≤ _ ⇒ _’ mp_tac >> impl_tac >- simp[] >>
  disch_then (SUBST1_TAC o SYM) >>
  simp[round_trans_def, responses_at_def, EL_tap_hist, GSYM tap_hist_TAKE] >>
  simp[tap_state_SNOC] >>
  Cases_on ‘tap_state σ δ s0 m (TAKE k h)’ >> simp[] >>
  ‘q = tap_hist σ δ s0 m (TAKE k h)’ by simp[tap_hist_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[tap_fold_round, FST, SND]
QED

(* MAIN: every answer m has received to a query was computed by δ on the
   store obtained by folding over m's transcript up to that query *)
Theorem tap_answers:
  wf m ⇒ answers_ok σ δ s0 (trans m (tap_hist σ δ s0 m h))
Proof
  strip_tac >>
  qabbrev_tac ‘ih = tap_hist σ δ s0 m h’ >>
  ‘∀k. k ≤ SUC (LENGTH ih) ⇒
       answers_ok σ δ s0 (FLAT (GENLIST (round_trans m ih) k))’
    suffices_by (disch_then (qspec_then ‘SUC (LENGTH ih)’ mp_tac) >>
                 simp[trans_def]) >>
  Induct >- simp[] >> strip_tac >>
  qpat_x_assum ‘_ ⇒ _’ mp_tac >> impl_tac >- simp[] >> strip_tac >>
  simp[GENLIST, SNOC_APPEND, answers_ok_APPEND] >>
  Cases_on ‘k < LENGTH ih’
  >- (‘k < LENGTH h’ by fs[Abbr ‘ih’] >>
      ‘SND (tap_state σ δ s0 m (TAKE k h)) =
       tap_fold σ δ s0 (FLAT (GENLIST (round_trans m ih) k))’
        by (simp[Abbr ‘ih’] >> irule tap_state_rounds >> simp[]) >>
      pop_assum (SUBST1_TAC o SYM) >>
      simp[round_trans_def, responses_at_def, Abbr ‘ih’, tap_hist_TAKE, EL_tap_hist] >>
      simp[GSYM tap_hist_TAKE, answers_ok_round]) >>
  simp[round_trans_def, responses_at_def, answers_ok_zipr_NIL]
QED
