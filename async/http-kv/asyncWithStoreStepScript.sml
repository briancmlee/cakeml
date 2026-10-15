(*
  with_store, one poll at a time: what the CakeML implementation does.

  with_store δ s0 m, polled with a snapshot w, is with_store again, of m
  polled with w' (w with the store's answers to m's first-round queries
  merged in), on the store after those queries:

     with_store_suspended:
       suspended (with_store δ s0 m) [w] = with_store δ s1 (suspended m [w'])

  So an implementation can keep the store in a closure argument and pass
  it on, round by round (asyncWithStoreProg).  Also: a finished m gives a
  finished with_store, and relabelling (asyncM4Relabel) commutes with
  with_store, Sock actions being relabelled and Kv queries kept.
*)
Theory asyncWithStoreStep
Ancestors
  pair list rich_list arithmetic option asyncCore asyncLevel1 asyncChoose
  asyncTranscript asyncCfActModel asyncM4Relabel asyncM4RelabelDist asyncProgress
  asyncWithStore
Libs
  BasicProvers

(* The first round's answers, the store after them, and the snapshot m sees *)
Definition first_answers_def:
  first_answers δ s0 (m : ('e, ('b, 'r) kres) snapshot list -> (('a, 'q) kact, 'x) outcome) =
    run_store δ s0 (queries (m []).actions)
End

Definition merged_def:
  merged acts (bs : 'b list) (w : ('e, 'r) snapshot) =
    ((w with results := merge acts w.results bs) : ('e, ('b, 'r) kres) snapshot)
End

Theorem queries_DROP[local]:
  LENGTH (queries (DROP k l)) ≤ LENGTH (queries l)
Proof
  ‘l = TAKE k l ++ DROP k l’ by simp[] >>
  pop_assum (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th]))) >>
  simp[]
QED

(* MAIN: the inner history, one snapshot at a time from the front *)
Theorem inner_hist_CONS:
  wf m ⇒
  ∀h. inner_hist δ s0 m (w :: h) =
        merged (m []).actions (FST (first_answers δ s0 m)) w ::
        inner_hist δ (SND (first_answers δ s0 m))
          (suspended m [merged (m []).actions (FST (first_answers δ s0 m)) w]) h
Proof
  strip_tac >>
  qabbrev_tac ‘a0 = (m []).actions’ >>
  qabbrev_tac ‘bs = FST (first_answers δ s0 m)’ >>
  qabbrev_tac ‘s1 = SND (first_answers δ s0 m)’ >>
  qabbrev_tac ‘w' = merged a0 bs w’ >>
  qabbrev_tac ‘m' = suspended m [w']’ >>
  Induct_on ‘h’ using SNOC_INDUCT
  >- simp[Once inner_hist_def, new_actions_NIL, log_of_def, Abbr ‘w'’, merged_def,
          store_answers_def, Abbr ‘bs’, first_answers_def, Abbr ‘a0’] >>
  rpt strip_tac >> simp[SNOC_APPEND] >>
  ‘w :: (h ++ [x]) = (w :: h) ++ [x]’ by simp[] >> pop_assum SUBST1_TAC >>
  REWRITE_TAC[inner_hist_SNOC] >> simp[] >>
  qabbrev_tac ‘ih = inner_hist δ s1 m' h’ >>
  ‘∀p. (m' p).actions = DROP (LENGTH a0) (m (w' :: p)).actions’
    by simp[Abbr ‘m'’, suspended_one, Abbr ‘a0’] >>
  ‘∀p. a0 ≼ (m (w' :: p)).actions’
    by (simp[Abbr ‘a0’] >> rpt strip_tac >> irule wf_actions_grow >> simp[]) >>
  ‘∀p. LENGTH a0 ≤ LENGTH (m (w' :: p)).actions’ by metis_tac[IS_PREFIX_LENGTH] >>
  ‘new_actions (log_of m) (w' :: ih) = new_actions (log_of m') ih’
    by (Cases_on ‘ih’ using SNOC_CASES
        >- simp[new_actions_def, log_of_def, Abbr ‘a0’] >>
        simp[SNOC_APPEND] >> ONCE_REWRITE_TAC[GSYM (CONJUNCT2 APPEND)] >>
        simp[new_actions_SNOC, log_of_def, DROP_DROP_T] >>
        (* TODO (WIP): finish, see HANDOFF-httpkv *)
        FAIL_TAC "WIP") >>
  FAIL_TAC "WIP"

QED

(* MAIN: with_store, polled once *)
Theorem with_store_suspended:
  wf m ⇒
  suspended (with_store δ s0 m) [w] =
    with_store δ (SND (first_answers δ s0 m))
      (suspended m [merged (m []).actions (FST (first_answers δ s0 m)) w])
Proof
  strip_tac >> simp[FUN_EQ_THM, suspended_one] >> gen_tac >>
  simp[with_store_def, inner_hist_CONS] >>
  qmatch_goalsub_abbrev_tac ‘m (w' :: ih)’ >>
  ‘(m []).actions ≼ (m (w' :: ih)).actions’
    by (irule wf_actions_grow >> simp[]) >>
  gvs[IS_PREFIX_APPEND] >>
  simp[suspended_one, DROP_LENGTH_APPEND]
QED

(* MAIN: a finished computation, with a store *)
Theorem with_store_finished:
  with_store δ s0 (finished A x) = finished (socks A) x
Proof
  simp[FUN_EQ_THM, with_store_def, finished_def]
QED

Theorem with_store_first:
  (with_store δ s0 m []).actions = socks (m []).actions ∧
  (with_store δ s0 m []).result = (m []).result
Proof
  simp[with_store_def]
QED

(* ------------------------------------------------------------------------
   Relabelling commutes with with_store
   ------------------------------------------------------------------------ *)

Definition kfa_def:
  kfa fa (Sock a) = Sock (fa a) ∧ kfa fa (Kv q) = Kv q
End

Definition kfr_def:
  kfr fr (SockR r) = SockR (fr r) ∧ kfr fr (KvR b) = KvR b
End

Theorem queries_kfa[simp]:
  queries (MAP (kfa fa) acts) = queries acts
Proof
  Induct_on ‘acts’ >> simp[] >> Cases >> simp[kfa_def]
QED

Theorem socks_kfa[simp]:
  socks (MAP (kfa fa) acts) = MAP fa (socks acts)
Proof
  Induct_on ‘acts’ >> simp[] >> Cases >> simp[kfa_def]
QED

Theorem merge_kfa[local]:
  ∀acts rs ans.
    MAP (kfr fr) (merge (MAP (kfa fa) acts) rs ans) = merge acts (MAP fr rs) ans
Proof
  Induct >> simp[merge_def] >> Cases >> rpt gen_tac >>
  simp[kfa_def, merge_def] >> every_case_tac >> gvs[kfr_def]
QED

Theorem inner_hist_relabel[local]:
  ∀h. MAP (snap_map fe (kfr fr))
        (inner_hist δ s0 (relabel (kfa fa) (snap_map fe (kfr fr)) m) h) =
      inner_hist δ s0 m (MAP (snap_map fe fr) h)
Proof
  Induct_on ‘h’ using SNOC_INDUCT >> simp[SNOC_APPEND, inner_hist_SNOC] >>
  rpt gen_tac >> pop_assum (SUBST1_TAC o SYM) >>
  simp[new_actions_relabel, relabel_def, store_answers_def, snap_map_def,
       merge_kfa]
QED

(* MAIN: relabelling commutes with with_store *)
Theorem relabel_with_store:
  relabel fa (snap_map fe fr) (with_store δ s0 m) =
  with_store δ s0 (relabel (kfa fa) (snap_map fe (kfr fr)) m)
Proof
  simp[FUN_EQ_THM, relabel_def, with_store_def, inner_hist_relabel]
QED

(* ------------------------------------------------------------------------
   Promptness
   ------------------------------------------------------------------------ *)

Theorem LENGTH_merge[local]:
  ∀acts rs ans.
    LENGTH (socks acts) ≤ LENGTH rs ∧ LENGTH (queries acts) ≤ LENGTH ans ⇒
    LENGTH acts ≤ LENGTH (merge acts rs ans)
Proof
  Induct >> simp[merge_def] >> Cases >> rpt gen_tac >> simp[merge_def] >>
  every_case_tac >> simp[]
QED

(* MAIN: if the world answers with_store's actions promptly, m's actions are
   answered promptly too (its queries by the store) *)
Theorem prompt_with_store:
  wf m ∧ prompt (with_store δ s0 m) h ⇒ prompt m (inner_hist δ s0 m h)
Proof
  rw[prompt_def] >> first_x_assum drule >>
  simp[new_actions_with_store, inner_hist_TAKE, responses_at_def] >>
  simp[EL_inner_hist] >> strip_tac >>
  qmatch_goalsub_abbrev_tac ‘merge acts _ (store_answers _ _ all acts)’ >>
  ‘∃old. all = old ++ acts’
    by (unabbrev_all_tac >> simp[log_new_actions]) >>
  irule LENGTH_merge >> simp[LENGTH_store_answers]
QED
