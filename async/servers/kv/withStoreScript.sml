(*
  with_store: shared state as a pure effect handler.

  An inner computation m may emit two kinds of action: Sock a (an action
  for the world, e.g. a socket call) and Kv q (a query on a store).
  with_store δ s0 m is an ordinary computation that emits only m's Sock
  actions.  It answers m's Kv queries itself, on a store that starts as
  s0 and is updated by δ (δ s q = (answer, new store)): the queries of a
  round are answered, in order, in the next snapshot, at their positions
  among that round's results, exactly as the world answers Sock actions.

  Nothing is hidden: with_store δ s0 m is a function of its history, like
  every computation.  The store after a history is a function of the
  queries m has emitted so far (store_after), and the history m sees
  (inner_hist) is the outer history with the store's answers merged in.

  MAIN results:
   - wf_with_store, with_store_agree / nonexpansive_with_store: with_store
     preserves well-formedness and the guardedness bookkeeping of fix;
   - new_actions_with_store: each round, with_store emits m's Sock actions;
   - trans_with_store: the transcript of with_store δ s0 m is that of m on
     the inner history, with the Kv entries removed;
   - kv_answers: every Kv query m has received an answer to was answered
     by running δ over ALL of m's queries so far, in order (the answer at
     its position).  This is the linearization of the store.
*)
Theory withStore
Ancestors
  pair list rich_list arithmetic option asyncCore asyncLevel1 asyncTranscript
Libs
  BasicProvers

Datatype:
  kact = Sock 'a | Kv 'q
End

Datatype:
  kres = SockR 'r | KvR 'b
End

(* The Kv queries / Sock actions among some actions, in order *)
Definition queries_def:
  queries acts = FLAT (MAP (λa. case a of Kv q => [q] | Sock x => []) acts)
End

Definition socks_def:
  socks acts = FLAT (MAP (λa. case a of Sock x => [x] | Kv q => []) acts)
End

(* Run the store over some queries: the answers, and the final store *)
Definition run_store_def:
  run_store δ s [] = ([], s) ∧
  run_store δ s (q :: qs) =
    let (b, s1) = δ s q;
        (bs, s2) = run_store δ s1 qs
    in (b :: bs, s2)
End

(* A round's results for m: the world's results at the Sock actions, the
   store's answers at the Kv queries, in order.  If the world gave fewer
   results than there are Sock actions, the rest of the round is
   unanswered, as it would be for m alone. *)
Definition merge_def:
  merge [] rs ans = [] ∧
  merge (Sock x :: acts) rs ans =
    (case rs of [] => [] | r :: rs' => SockR r :: merge acts rs' ans) ∧
  merge (Kv q :: acts) rs ans =
    (case ans of [] => [] | b :: ans' => KvR b :: merge acts rs ans')
End

(* The answers to the last queries of a log all: those of its suffix acts *)
Definition store_answers_def:
  store_answers δ s0 all acts =
    DROP (LENGTH (queries all) - LENGTH (queries acts))
         (FST (run_store δ s0 (queries all)))
End

(* The history m sees, when with_store δ s0 m sees h *)
Definition inner_hist_def:
  inner_hist δ s0 m h =
    if h = [] then []
    else
      let ih = inner_hist δ s0 m (FRONT h);
          acts = new_actions (log_of m) ih;
          s = LAST h
      in ih ++ [s with results :=
                  merge acts s.results (store_answers δ s0 (m ih).actions acts)]
Termination
  WF_REL_TAC ‘measure (LENGTH o SND o SND o SND)’
  >> Cases_on ‘h’ using SNOC_CASES >> simp[FRONT_APPEND]
End

Definition with_store_def:
  with_store δ s0 m h =
    <| actions := socks (m (inner_hist δ s0 m h)).actions;
       result := (m (inner_hist δ s0 m h)).result |>
End

(* The store after the history h *)
Definition store_after_def:
  store_after δ s0 m h = SND (run_store δ s0 (queries (m (inner_hist δ s0 m h)).actions))
End

(* ------------------------------------------------------------------------
   Lists
   ------------------------------------------------------------------------ *)

Theorem queries_APPEND[simp]:
  queries (l1 ++ l2) = queries l1 ++ queries l2
Proof
  simp[queries_def]
QED

Theorem socks_APPEND[simp]:
  socks (l1 ++ l2) = socks l1 ++ socks l2
Proof
  simp[socks_def]
QED

Theorem queries_simps[simp]:
  queries [] = [] ∧
  queries (Kv q :: l) = q :: queries l ∧ queries (Sock x :: l) = queries l
Proof
  simp[queries_def]
QED

Theorem socks_simps[simp]:
  socks [] = [] ∧
  socks (Sock x :: l) = x :: socks l ∧ socks (Kv q :: l) = socks l
Proof
  simp[socks_def]
QED

Theorem LENGTH_run_store[simp]:
  ∀qs s. LENGTH (FST (run_store δ s qs)) = LENGTH qs
Proof
  Induct >> simp[run_store_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[FST]
QED

(* MAIN: running the store over more queries extends the answers *)
Theorem run_store_APPEND:
  ∀qs1 qs2 s.
    run_store δ s (qs1 ++ qs2) =
      let (bs1, s1) = run_store δ s qs1;
          (bs2, s2) = run_store δ s1 qs2
      in (bs1 ++ bs2, s2)
Proof
  Induct >> simp[run_store_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem run_store_APPEND_FST:
  FST (run_store δ s (qs1 ++ qs2)) =
    FST (run_store δ s qs1) ++ FST (run_store δ (SND (run_store δ s qs1)) qs2)
Proof
  simp[run_store_APPEND] >> rpt (pairarg_tac >> gvs[])
QED

Theorem run_store_APPEND_SND:
  SND (run_store δ s (qs1 ++ qs2)) =
    SND (run_store δ (SND (run_store δ s qs1)) qs2)
Proof
  simp[run_store_APPEND] >> rpt (pairarg_tac >> gvs[])
QED

Theorem store_answers_APPEND:
  store_answers δ s0 (old ++ acts) acts =
    FST (run_store δ (SND (run_store δ s0 (queries old))) (queries acts))
Proof
  simp[store_answers_def, run_store_APPEND_FST, DROP_APPEND] >>
  simp[DROP_LENGTH_TOO_LONG]
QED

Theorem LENGTH_store_answers:
  LENGTH (store_answers δ s0 (old ++ acts) acts) = LENGTH (queries acts)
Proof
  simp[store_answers_APPEND]
QED

Theorem TAKE_SUC_EL:
  ∀l n. n < LENGTH l ⇒ TAKE (SUC n) l = TAKE n l ++ [EL n l]
Proof
  Induct >> Cases_on ‘n’ >> fs[]
QED

(* ------------------------------------------------------------------------
   The inner history
   ------------------------------------------------------------------------ *)

Theorem inner_hist_NIL[simp]:
  inner_hist δ s0 m [] = []
Proof
  simp[Once inner_hist_def]
QED

Theorem inner_hist_SNOC:
  inner_hist δ s0 m (h ++ [s]) =
    let ih = inner_hist δ s0 m h;
        acts = new_actions (log_of m) ih
    in ih ++ [s with results :=
                merge acts s.results (store_answers δ s0 (m ih).actions acts)]
Proof
  simp[Once inner_hist_def, FRONT_APPEND]
QED

Theorem LENGTH_inner_hist[simp]:
  ∀h. LENGTH (inner_hist δ s0 m h) = LENGTH h
Proof
  Induct_on ‘h’ using SNOC_INDUCT >> simp[SNOC_APPEND, inner_hist_SNOC]
QED

(* MAIN: the inner history of a prefix is the prefix of the inner history *)
Theorem inner_hist_TAKE:
  ∀h n. inner_hist δ s0 m (TAKE n h) = TAKE n (inner_hist δ s0 m h)
Proof
  Induct_on ‘h’ using SNOC_INDUCT >> simp[SNOC_APPEND] >> rpt gen_tac >>
  Cases_on ‘n ≤ LENGTH h’
  >- simp[TAKE_APPEND1, inner_hist_SNOC] >>
  ‘TAKE n (h ++ [x]) = h ++ [x]’ by simp[TAKE_LENGTH_TOO_LONG] >>
  simp[inner_hist_SNOC, TAKE_LENGTH_TOO_LONG]
QED

(* The inner history only depends on m's behaviour on shorter histories *)
Theorem inner_hist_cong:
  ∀h. (∀p. LENGTH p < LENGTH h ⇒ m1 p = m2 p) ⇒
      inner_hist δ s0 m1 h = inner_hist δ s0 m2 h
Proof
  Induct_on ‘h’ using SNOC_INDUCT >> simp[SNOC_APPEND, inner_hist_SNOC] >>
  rpt strip_tac >>
  ‘inner_hist δ s0 m1 h = inner_hist δ s0 m2 h’ by simp[] >>
  simp[] >>
  ‘new_actions (log_of m1) (inner_hist δ s0 m2 h) =
   new_actions (log_of m2) (inner_hist δ s0 m2 h)’
    by (irule new_actions_cong >> simp[log_of_def]) >>
  simp[]
QED

(* ------------------------------------------------------------------------
   with_store is a computation like any other
   ------------------------------------------------------------------------ *)

(* MAIN: with_store preserves well-formedness *)
Theorem wf_with_store:
  wf m ⇒ wf (with_store δ s0 m)
Proof
  rw[wf_def, with_store_def, inner_hist_SNOC] >>
  qmatch_goalsub_abbrev_tac ‘inner_hist δ s0 m h ++ [s']’
  >- (first_x_assum (qspecl_then [‘inner_hist δ s0 m h’, ‘s'’] strip_assume_tac) >>
      gvs[IS_PREFIX_APPEND]) >>
  first_x_assum (qspecl_then [‘inner_hist δ s0 m h’, ‘s'’] strip_assume_tac) >>
  gvs[]
QED

(* MAIN: with_store keeps the bookkeeping of guarded recursion: computations
   that agree on histories shorter than n give with_stores that do too *)
Theorem with_store_agree:
  agree_below n m1 m2 ⇒
  agree_below n (with_store δ s0 m1) (with_store δ s0 m2)
Proof
  rw[agree_below_def, with_store_def] >>
  ‘inner_hist δ s0 m1 h = inner_hist δ s0 m2 h’
    by (irule inner_hist_cong >> simp[]) >>
  simp[]
QED

Theorem nonexpansive_with_store:
  nonexpansive (λr. M r) ⇒ nonexpansive (λr. with_store δ s0 (M r))
Proof
  rw[nonexpansive_def] >> irule with_store_agree >> simp[]
QED

(* With a growing log, a round adds the round's new actions *)
Theorem wf_log_SNOC:
  wf m ⇒ ∀h s. (m (h ++ [s])).actions = (m h).actions ++ new_actions (log_of m) (h ++ [s])
Proof
  rpt strip_tac >>
  ‘log_of m h ≼ log_of m (h ++ [s])’ by fs[wf_def, log_of_def] >>
  drule new_actions_prefix >> simp[log_of_def]
QED

(* MAIN: each round, with_store emits m's Sock actions of that round *)
Theorem new_actions_with_store:
  wf m ⇒
  new_actions (log_of (with_store δ s0 m)) h =
    socks (new_actions (log_of m) (inner_hist δ s0 m h))
Proof
  strip_tac >> Cases_on ‘h’ using SNOC_CASES
  >- simp[new_actions_NIL, log_of_def, with_store_def] >>
  REWRITE_TAC[SNOC_APPEND] >>
  qabbrev_tac ‘ih = inner_hist δ s0 m l’ >>
  qabbrev_tac ‘s' = x with results :=
                 merge (new_actions (log_of m) ih) x.results
                   (store_answers δ s0 (m ih).actions (new_actions (log_of m) ih))’ >>
  ‘inner_hist δ s0 m (l ++ [x]) = ih ++ [s']’
    by simp[inner_hist_SNOC, Abbr ‘ih’, Abbr ‘s'’] >>
  ‘new_actions (log_of (with_store δ s0 m)) (l ++ [x]) =
   DROP (LENGTH (socks (m ih).actions)) (socks (m (ih ++ [s'])).actions)’
    by simp[new_actions_SNOC, log_of_def, with_store_def, Abbr ‘ih’] >>
  simp[] >>
  drule wf_log_SNOC >> disch_then (qspecl_then [‘ih’, ‘s'’] SUBST1_TAC) >>
  simp[DROP_LENGTH_APPEND]
QED

(* ------------------------------------------------------------------------
   Transcripts
   ------------------------------------------------------------------------ *)

(* The Sock entries of an inner transcript, as outer entries *)
Definition untag_def:
  untag tr =
    FLAT (MAP (λ(a, r). case a of
                 Sock x => [(x, case r of SOME (SockR y) => SOME y | _ => NONE)]
               | Kv q => []) tr)
End

(* The Kv entries of an inner transcript: each query with its answer *)
Definition kvs_def:
  kvs tr = FLAT (MAP (λ(a, r). case a of Kv q => [(q, r)] | Sock x => []) tr)
End

Theorem untag_APPEND[simp]:
  untag (l1 ++ l2) = untag l1 ++ untag l2
Proof
  simp[untag_def]
QED

Theorem kvs_APPEND[simp]:
  kvs (l1 ++ l2) = kvs l1 ++ kvs l2
Proof
  simp[kvs_def]
QED

Theorem untag_FLAT:
  untag (FLAT l) = FLAT (MAP untag l)
Proof
  Induct_on ‘l’ >> simp[] >> simp[untag_def]
QED

Theorem kvs_FLAT:
  kvs (FLAT l) = FLAT (MAP kvs l)
Proof
  Induct_on ‘l’ >> simp[] >> simp[kvs_def]
QED

Theorem untag_zipr_NIL[local]:
  ∀acts. untag (zipr acts []) = zipr (socks acts) []
Proof
  Induct >> simp[zipr_def, untag_def] >> Cases >> simp[zipr_def] >>
  fs[untag_def]
QED

Theorem untag_zipr_merge:
  ∀acts rs ans.
    LENGTH (queries acts) ≤ LENGTH ans ⇒
    untag (zipr acts (merge acts rs ans)) = zipr (socks acts) rs
Proof
  Induct >> simp[zipr_def, merge_def, untag_def] >> Cases >> rpt gen_tac
  >- (Cases_on ‘rs’ >> simp[merge_def, zipr_def]
      >- (simp[GSYM untag_def] >> simp[untag_zipr_NIL] >> simp[untag_def])
      >> strip_tac >> simp[GSYM untag_def]) >>
  Cases_on ‘ans’ >> simp[merge_def, zipr_def, GSYM untag_def]
QED

Theorem MAP_FST_kvs:
  ∀tr. MAP FST (kvs tr) = queries (MAP FST tr)
Proof
  Induct >> simp[kvs_def] >> PairCases >> Cases_on ‘h0’ >> simp[GSYM kvs_def]
QED

(* With a growing log, the log is an older log plus the new actions *)
Theorem log_new_actions:
  wf m ⇒ ∃old. (m h).actions = old ++ new_actions (log_of m) h
Proof
  strip_tac >> Cases_on ‘h’ using SNOC_CASES
  >- simp[new_actions_NIL, log_of_def] >>
  qexists_tac ‘(m l).actions’ >> REWRITE_TAC[SNOC_APPEND] >>
  simp[wf_log_SNOC]
QED

(* The results m sees in round n *)
Theorem EL_inner_hist:
  n < LENGTH h ⇒
  (EL n (inner_hist δ s0 m h)).results =
    let ih = TAKE n (inner_hist δ s0 m h);
        acts = new_actions (log_of m) ih
    in merge acts (EL n h).results (store_answers δ s0 (m ih).actions acts)
Proof
  strip_tac >>
  ‘TAKE (SUC n) h = TAKE n h ++ [EL n h]’ by simp[TAKE_SUC_EL] >>
  ‘TAKE (SUC n) (inner_hist δ s0 m h) =
   TAKE n (inner_hist δ s0 m h) ++ [EL n (inner_hist δ s0 m h)]’
    by simp[TAKE_SUC_EL] >>
  ‘inner_hist δ s0 m (TAKE (SUC n) h) = TAKE (SUC n) (inner_hist δ s0 m h)’
    by simp[inner_hist_TAKE] >>
  qpat_x_assum ‘inner_hist _ _ _ (TAKE (SUC n) h) = _’ mp_tac >>
  ASM_REWRITE_TAC[] >> REWRITE_TAC[inner_hist_SNOC] >> simp[inner_hist_TAKE] >>
  disch_then (SUBST1_TAC o SYM) >> simp[]
QED

Theorem round_trans_with_store:
  wf m ∧ n ≤ LENGTH h ⇒
  round_trans (with_store δ s0 m) h n =
    untag (round_trans m (inner_hist δ s0 m h) n)
Proof
  rw[round_trans_def, new_actions_with_store, inner_hist_TAKE, responses_at_def] >>
  Cases_on ‘n < LENGTH h’ >> simp[untag_zipr_NIL] >>
  simp[EL_inner_hist] >>
  qmatch_goalsub_abbrev_tac ‘merge acts _ (store_answers _ _ all acts)’ >>
  ‘∃old. all = old ++ acts’
    by (unabbrev_all_tac >> simp[log_new_actions]) >>
  simp[untag_zipr_merge, LENGTH_store_answers]
QED

(* MAIN: the transcript of with_store δ s0 m is m's transcript on the inner
   history, without its Kv entries *)
Theorem trans_with_store:
  wf m ⇒
  trans (with_store δ s0 m) h = untag (trans m (inner_hist δ s0 m h))
Proof
  rw[trans_def, untag_FLAT, MAP_GENLIST] >>
  AP_TERM_TAC >> simp[GENLIST_FUN_EQ, round_trans_with_store]
QED

(* ------------------------------------------------------------------------
   The answers
   ------------------------------------------------------------------------ *)

(* Each entry of E is unanswered, or answered with the answer at its
   position in A *)
Definition fits_def:
  fits A E ⇔
    LENGTH E ≤ LENGTH A ∧
    ∀i. i < LENGTH E ⇒ SND (EL i E) = NONE ∨ SND (EL i E) = SOME (KvR (EL i A))
End

Theorem fits_APPEND[local]:
  fits A E1 ∧ fits (DROP (LENGTH E1) A) E2 ⇒ fits A (E1 ++ E2)
Proof
  rw[fits_def] >> Cases_on ‘i < LENGTH E1’ >> simp[EL_APPEND1, EL_APPEND2] >>
  first_x_assum (qspec_then ‘i - LENGTH E1’ mp_tac) >> simp[EL_DROP]
QED

Theorem fits_prefix[local]:
  fits A E ∧ A ≼ A' ⇒ fits A' E
Proof
  rw[fits_def, IS_PREFIX_APPEND] >> simp[] >>
  first_x_assum drule >> simp[EL_APPEND1]
QED

Theorem fits_NIL[simp]:
  fits A []
Proof
  simp[fits_def]
QED

Theorem fits_CONS:
  fits (b :: A) (e :: E) ⇔
    (SND e = NONE ∨ SND e = SOME (KvR b)) ∧ fits A E
Proof
  rw[fits_def, EQ_IMP_THM]
  >- (first_x_assum (qspec_then ‘0’ mp_tac) >> simp[])
  >- (first_x_assum (qspec_then ‘SUC i’ mp_tac) >> simp[])
  >> Cases_on ‘i’ >> gvs[]
QED

Theorem LENGTH_kvs_zipr[local]:
  LENGTH (kvs (zipr acts rs)) = LENGTH (queries acts)
Proof
  metis_tac[LENGTH_MAP, MAP_FST_kvs, MAP_FST_zipr]
QED

Theorem kvs_zipr_NIL_NONE[local]:
  ∀acts. EVERY (λe. SND e = NONE) (kvs (zipr acts []))
Proof
  Induct >> simp[zipr_def, kvs_def] >> Cases >> simp[] >> fs[kvs_def]
QED

Theorem kvs_zipr_NIL[local]:
  LENGTH (queries acts) ≤ LENGTH A ⇒ fits A (kvs (zipr acts []))
Proof
  rw[fits_def, LENGTH_kvs_zipr] >> disj1_tac >>
  pop_assum mp_tac >> qid_spec_tac ‘i’ >> pop_assum kall_tac >>
  qid_spec_tac ‘acts’ >>
  Induct >> simp[zipr_def, kvs_def] >> Cases >> simp[GSYM kvs_def] >>
  Cases >> simp[]
QED

Theorem kvs_zipr_merge[local]:
  ∀acts rs ans.
    LENGTH (queries acts) ≤ LENGTH ans ⇒
    fits ans (kvs (zipr acts (merge acts rs ans)))
Proof
  Induct >> simp[zipr_def, merge_def, kvs_def] >> Cases >> rpt gen_tac >>
  simp[GSYM kvs_def]
  >- (Cases_on ‘rs’ >> simp[merge_def, zipr_def, GSYM kvs_def]
      >- (strip_tac >> irule kvs_zipr_NIL >> simp[])
      >> strip_tac >> simp[kvs_def] >> simp[GSYM kvs_def]) >>
  Cases_on ‘ans’ >> simp[merge_def, zipr_def] >> strip_tac >>
  simp[kvs_def] >> simp[GSYM kvs_def, fits_CONS]
QED

(* The log, round by round *)
Theorem log_rounds:
  wf m ⇒
  ∀k. k ≤ LENGTH h ⇒
      (m (TAKE k h)).actions =
        FLAT (GENLIST (λj. new_actions (log_of m) (TAKE j h)) (SUC k))
Proof
  strip_tac >> Induct
  >- simp[new_actions_NIL, log_of_def] >>
  strip_tac >> ‘k ≤ LENGTH h’ by simp[] >>
  first_x_assum drule >> strip_tac >>
  ‘TAKE (SUC k) h = TAKE k h ++ [EL k h]’ by simp[TAKE_SUC_EL] >>
  ONCE_REWRITE_TAC[GENLIST] >> REWRITE_TAC[SNOC_APPEND, FLAT_APPEND] >>
  drule wf_log_SNOC >> strip_tac >> simp[]
QED

Theorem MAP_FST_rounds[local]:
  MAP FST (FLAT (GENLIST (round_trans m h) k)) =
  FLAT (GENLIST (λj. new_actions (log_of m) (TAKE j h)) k)
Proof
  simp[MAP_FLAT, MAP_GENLIST, combinTheory.o_DEF, round_trans_def]
QED

(* MAIN: every answer m has received to a Kv query is the answer that
   running the store over all of m's queries, in order, gives at that
   query's position *)
Theorem kv_answers:
  wf m ⇒
  let E = kvs (trans m (inner_hist δ s0 m h)) in
    MAP FST E = queries (m (inner_hist δ s0 m h)).actions ∧
    ∀i. i < LENGTH E ⇒
        SND (EL i E) = NONE ∨
        SND (EL i E) = SOME (KvR (EL i (FST (run_store δ s0 (MAP FST E)))))
Proof
  strip_tac >> simp[] >>
  qabbrev_tac ‘ih = inner_hist δ s0 m h’ >>
  ‘MAP FST (kvs (trans m ih)) = queries (m ih).actions’
    by simp[MAP_FST_kvs, MAP_FST_trans] >>
  simp[] >>
  qabbrev_tac ‘A = FST (run_store δ s0 (queries (m ih).actions))’ >>
  ‘fits A (kvs (trans m ih))’ suffices_by simp[fits_def] >>
  ‘∀k. k ≤ SUC (LENGTH ih) ⇒
       fits A (kvs (FLAT (GENLIST (round_trans m ih) k)))’
    suffices_by (disch_then (qspec_then ‘SUC (LENGTH ih)’ mp_tac) >>
                 simp[trans_def]) >>
  Induct >- simp[kvs_def] >> strip_tac >>
  ‘fits A (kvs (FLAT (GENLIST (round_trans m ih) k)))’
    by (first_x_assum irule >> simp[]) >>
  REWRITE_TAC[GENLIST, SNOC_APPEND, FLAT_APPEND, kvs_APPEND] >>
  irule fits_APPEND >> asm_rewrite_tac[] >>
  (* round k: its queries come right after those of rounds < k *)
  qabbrev_tac ‘acts = new_actions (log_of m) (TAKE k ih)’ >>
  qabbrev_tac ‘old = FLAT (GENLIST (λj. new_actions (log_of m) (TAKE j ih)) k)’ >>
  ‘LENGTH (kvs (FLAT (GENLIST (round_trans m ih) k))) = LENGTH (queries old)’
    by metis_tac[LENGTH_MAP, MAP_FST_kvs, MAP_FST_rounds] >>
  ‘(m (TAKE k ih)).actions = old ++ acts’
    by (‘k ≤ LENGTH ih’ by simp[] >>
        drule log_rounds >> disch_then (qspecl_then [‘ih’, ‘k’] mp_tac) >>
        simp[Abbr ‘old’, Abbr ‘acts’] >> ONCE_REWRITE_TAC[GENLIST] >>
        simp[SNOC_APPEND]) >>
  ‘∃rest. (m ih).actions = old ++ acts ++ rest’
    by (‘(m (TAKE k ih)).actions ≼ (m ih).actions’
          by (irule wf_actions_grow >> simp[IS_PREFIX_APPEND] >>
              metis_tac[TAKE_DROP]) >>
        gvs[IS_PREFIX_APPEND] >> metis_tac[]) >>
  qabbrev_tac ‘st = SND (run_store δ s0 (queries old))’ >>
  ‘DROP (LENGTH (queries old)) A =
   FST (run_store δ st (queries acts)) ++
   FST (run_store δ (SND (run_store δ st (queries acts))) (queries rest))’
    by (simp[Abbr ‘A’, Abbr ‘st’] >>
        qpat_x_assum ‘(m ih).actions = _’ SUBST1_TAC >>
        REWRITE_TAC[queries_APPEND, run_store_APPEND_FST, run_store_APPEND_SND,
                    GSYM APPEND_ASSOC] >>
        metis_tac[DROP_LENGTH_APPEND, LENGTH_run_store]) >>
  simp[] >> irule fits_prefix >>
  qexists_tac ‘FST (run_store δ st (queries acts))’ >> simp[] >>
  simp[round_trans_def, responses_at_def] >>
  Cases_on ‘k < LENGTH ih’ >> simp[]
  >- (‘k < LENGTH h’ by fs[Abbr ‘ih’] >>
      qunabbrev_tac ‘acts’ >> qunabbrev_tac ‘st’ >>
      fs[Abbr ‘ih’, EL_inner_hist, store_answers_APPEND] >>
      irule kvs_zipr_merge >> simp[]) >>
  irule kvs_zipr_NIL >> simp[]
QED
