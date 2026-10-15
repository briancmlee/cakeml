(*
  Orders from sequences of requests, and commit points by position.

  A server linearizes requests as a sequence l of (connection, request).
  label l names each entry (c, i): c's i-th request in l.  If c's requests
  in l are exactly rss c, label l is an order (HttpKvSpec's is_order), and
  its replies are those of running the store over the requests of l.

  commits_at: commit points given by position in the order (asyncKvOrder's
  commits, for orders without repeated entries).
*)
Theory asyncKvLabel
Ancestors
  list rich_list words EchoSpec HttpSpec HttpSpecBodies HttpKvSpec asyncKvOrder
Libs
  preamble

Definition label_def:
  label (l : ('c # 'a) list) =
    GENLIST (λj. (FST (EL j l),
                  LENGTH (FILTER (λx. FST x = FST (EL j l)) (TAKE j l))))
            (LENGTH l)
End

Theorem LENGTH_label[simp]:
  LENGTH (label l) = LENGTH l
Proof
  simp[label_def]
QED

Theorem label_SNOC:
  label (l ++ [x]) = label l ++ [(FST x, LENGTH (FILTER (λy. FST y = FST x) l))]
Proof
  simp[label_def, GSYM ADD1] >> REWRITE_TAC[GENLIST, SNOC_APPEND] >>
  simp[EL_APPEND2, TAKE_LENGTH_APPEND] >>
  simp[GENLIST_FUN_EQ, EL_APPEND1, TAKE_APPEND1]
QED

Theorem MAP_FST_label:
  MAP FST (label l) = MAP FST l
Proof
  simp[label_def, MAP_GENLIST, combinTheory.o_DEF, LIST_EQ_REWRITE, EL_MAP]
QED

(* MAIN: c's entries in label l are c's first indices *)
Theorem label_FILTER:
  ∀l. MAP SND (FILTER (λx. FST x = c) (label l)) =
      COUNT_LIST (LENGTH (FILTER (λx. FST x = c) l))
Proof
  Induct_on ‘l’ using SNOC_INDUCT >- simp[label_def, COUNT_LIST_def] >>
  simp[SNOC_APPEND, label_SNOC, FILTER_APPEND] >>
  rw[COUNT_LIST_SNOC, SNOC_APPEND, GSYM ADD1]
QED

Theorem FILTER_TAKE_lt:
  ∀l i. i < LENGTH l ∧ P (EL i l) ⇒
        LENGTH (FILTER P (TAKE i l)) < LENGTH (FILTER P l)
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on ‘i’ >> rw[] >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem EL_FILTER_count[local]:
  ∀l i. i < LENGTH l ∧ P (EL i l) ⇒
        EL (LENGTH (FILTER P (TAKE i l))) (FILTER P l) = EL i l
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on ‘i’ >> rw[] >> gvs[]
QED

(* MAIN: if c's requests in l are R c, the requests named by label l are
   those of l *)
Theorem label_requests:
  (∀c. MAP SND (FILTER (λx. FST x = c) l) = R c) ⇒
  MAP (λ(d, i). EL i (R d)) (label l) = MAP SND l
Proof
  rw[LIST_EQ_REWRITE, EL_MAP, label_def] >>
  qabbrev_tac ‘c = FST (EL x l)’ >> first_x_assum (qspec_then ‘c’ strip_assume_tac) >>
  qabbrev_tac ‘k = LENGTH (FILTER (λx'. FST x' = c) (TAKE x l))’ >>
  ‘k < LENGTH (FILTER (λx'. FST x' = c) l)’
    by (qunabbrev_tac ‘k’ >> irule FILTER_TAKE_lt >> simp[Abbr ‘c’]) >>
  first_x_assum drule >> disch_then (SUBST1_TAC o SYM) >>
  ‘EL k (FILTER (λx'. FST x' = c) l) = EL x l’
    by (qunabbrev_tac ‘k’ >> irule EL_FILTER_count >> simp[Abbr ‘c’]) >>
  simp[]
QED

Theorem ZIP_FILTER_FST[local]:
  ∀a b X. MAP FST a = MAP FST b ∧ LENGTH a = LENGTH X ⇒
          MAP SND (FILTER (λ((d,i),x). d = c) (ZIP (a, X))) =
          MAP SND (FILTER (λp. FST (FST p) = c) (ZIP (b, X)))
Proof
  Induct >> Cases_on ‘b’ >> simp[] >> rpt gen_tac >> Cases_on ‘X’ >> simp[] >>
  PairCases_on ‘h’ >> PairCases_on ‘h'’ >> rw[] >> gvs[]
QED

(* MAIN: the replies of label l are those of running the store over l *)
Theorem replies_label:
  (∀c. MAP SND (FILTER (λx. FST x = c) l) = rss c) ⇒
  replies rss (label l) c =
    MAP SND (FILTER (λp. FST (FST p) = c)
                    (ZIP (l, kv_run (λk. NONE) (MAP SND l))))
Proof
  strip_tac >> simp[replies_def] >>
  drule label_requests >> simp[] >> strip_tac >>
  ‘∀rs st. LENGTH (kv_run st rs) = LENGTH rs’
    by (Induct >> simp[kv_run_def] >> rpt gen_tac >> pairarg_tac >> simp[]) >>
  irule ZIP_FILTER_FST >> simp[MAP_FST_label]
QED

(* MAIN: label l is an order if c's requests in l are rss c *)
Theorem is_order_label:
  (∀c. MAP SND (FILTER (λx. FST x = c) l) = rss c) ⇒ is_order rss (label l)
Proof
  rw[is_order_def, label_FILTER] >>
  first_x_assum (qspec_then ‘c’ (SUBST1_TAC o SYM)) >> simp[]
QED

(* ------------------------------------------------------------------------
   Commit points by position
   ------------------------------------------------------------------------ *)

Definition commits_at_def:
  commits_at rss order evs pj ⇔
    (∀j k. j ≤ k ∧ k < LENGTH order ⇒ pj j ≤ pj k) ∧
    ∀j. j < LENGTH order ⇒
        started rss (EL j order) (TAKE (pj j) evs) ∧
        ¬answered rss order (EL j order) (TAKE (pj j) evs)
End

Theorem earlier_EL[local]:
  ∀l i j. i < j ∧ j < LENGTH l ⇒ earlier l (EL i l) (EL j l)
Proof
  Induct >> simp[earlier_CONS] >> rpt gen_tac >> Cases_on ‘i’ >> Cases_on ‘j’ >>
  simp[] >> rw[] >> gvs[]
  >- (disj1_tac >> simp[MEM_EL] >> metis_tac[])
QED

(* MAIN: commit points by position give real time *)
Theorem commits_at_real_time:
  is_order rss order ∧ commits_at rss order evs pj ⇒
  ∀x y. MEM x order ∧ MEM y order ∧ FST x ≠ FST y ∧
        precedes rss order evs x y ⇒ earlier order x y
Proof
  rw[] >> gvs[MEM_EL] >> rename1 ‘precedes _ _ _ (EL i order) (EL j order)’ >>
  ‘i < j’ suffices_by metis_tac[earlier_EL] >>
  CCONTR_TAC >>
  ‘j ≤ i’ by simp[] >>
  ‘pj j ≤ pj i’ by fs[commits_at_def] >>
  qpat_x_assum ‘precedes _ _ _ _ _’ mp_tac >>
  simp[precedes_answered_started] >> rpt strip_tac >>
  ‘evs1 = TAKE (LENGTH evs1) evs’ by (gvs[IS_PREFIX_APPEND] >> simp[TAKE_LENGTH_APPEND]) >>
  qabbrev_tac ‘k = LENGTH evs1’ >>
  ‘pj i < k’
    by (CCONTR_TAC >>
        ‘TAKE k evs ≼ TAKE (pj i) evs’
          by (simp[IS_PREFIX_APPEND] >> qexists_tac ‘TAKE (pj i - k) (DROP k evs)’ >>
              simp[GSYM TAKE_SUM, TAKE_TAKE_MIN, MIN_DEF]) >>
        ‘answered rss order (EL i order) (TAKE (pj i) evs)’ suffices_by
          (fs[commits_at_def] >> metis_tac[]) >>
        Cases_on ‘EL i order’ >> gvs[answered_def] >>
        metis_tac[bytes_written_to_prefix, IS_PREFIX_TRANS]) >>
  ‘k < pj j’
    by (CCONTR_TAC >>
        ‘TAKE (pj j) evs ≼ TAKE k evs’
          by (simp[IS_PREFIX_APPEND] >> qexists_tac ‘TAKE (k - pj j) (DROP (pj j) evs)’ >>
              simp[GSYM TAKE_SUM, TAKE_TAKE_MIN, MIN_DEF]) >>
        ‘¬started rss (EL j order) (TAKE (pj j) evs)’ suffices_by
          (fs[commits_at_def] >> metis_tac[]) >>
        Cases_on ‘EL j order’ >> gvs[started_def] >>
        metis_tac[bytes_read_from_prefix, IS_PREFIX_TRANS]) >>
  decide_tac
QED
