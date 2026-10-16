(*
  The order construction of the key-value server, once, over a generic
  key view.

  HttpKvSpec's kv_safe (per connection) and HttpKvSpec2's kv_safe2 (per
  episode) are the same statement with different projections: what has
  been read from key c (RD c) and written to it (WR c), for keys of any
  type.  kv_safeG RD WR is that statement; kv_safe_G shows kv_safe is its
  instance at bytes_read_from / bytes_written_to (asyncKv2Safe does the
  same for kv_safe2 at ep_read / ep_written).

  MAIN: kv_safeG_rounds.  A run that is the concatenation of rounds EV i,
  with the store's queries G k after k rounds, is kv_safeG, if
  (kv_rounds) the projections at round boundaries are those of the model
  (RD c after k rounds is the bytes of RS k c; WR c after k+1 rounds is
  the bytes of WS k c), the model serves (kv_server_serves' two facts,
  for the model's fd kinv c of key c), the queries grow, the projections
  are monotone, keys and model fds correspond (kmap / kinv), and only
  finitely many keys have been read from.  The order is the store's
  queries, in its order, then the complete requests not queried yet; a
  query commits at the start of the round in which with_store answered it
  (asyncKvSafe's kv_comp_safe, with the projections as parameters).
*)
Theory asyncKvOrderGen
Ancestors
  words llist EchoSpec HttpSpec HttpSpecBodies HttpKvSpec asyncHttpParse
  asyncHttpParseH asyncHttpParseB asyncWithStore asyncKvModel asyncKvOrder
  asyncKvLabel asyncKvTraceLemmas asyncM4GTrans
Libs
  preamble

(* ------------------------------------------------------------------------
   The generic statement
   ------------------------------------------------------------------------ *)

Definition is_ord_def:
  is_ord (rss : 'k -> brequest list) (order : ('k # num) list) ⇔
    ∀c. MAP SND (FILTER (λx. FST x = c) order) = COUNT_LIST (LENGTH (rss c))
End

(* Real time, for the projections RD (read) and WR (written) *)
Definition precedesG_def:
  precedesG RD WR rss order evs (c, i) (d, j) ⇔
    ∃evs1. evs1 ≼ evs ∧
           reply_bytes (TAKE (SUC i) (replies rss order c)) ≼ WR c evs1 ∧
           RD d evs1 ≼ brequests (TAKE j (rss d))
End

Definition kv_safeG_def:
  kv_safeG RD WR io ⇔
    ∀evs rss rests.
      LPREFIX (fromList evs) io ∧
      (∀c. EVERY valid_brequest (rss c) ∧ no_full_brequest (rests c) ∧
           RD c evs = brequests (rss c) ++ rests c) ⇒
      ∃order.
        is_ord rss order ∧
        (∀x y. MEM x order ∧ MEM y order ∧ FST x ≠ FST y ∧
               precedesG RD WR rss order evs x y ⇒ earlier order x y) ∧
        ∀c. WR c evs ≼ reply_bytes (replies rss order c)
End

Theorem is_order_ord:
  is_order rss order ⇔ is_ord rss order
Proof
  simp[is_order_def, is_ord_def]
QED

Theorem precedes_G:
  precedes rss order evs x y ⇔
    precedesG bytes_read_from bytes_written_to rss order evs x y
Proof
  PairCases_on ‘x’ >> PairCases_on ‘y’ >> simp[precedes_def, precedesG_def]
QED

(* MAIN: kv_safe is the instance per connection *)
Theorem kv_safe_G:
  kv_safe io ⇔ kv_safeG bytes_read_from bytes_written_to io
Proof
  simp[kv_safe_def, kv_safeG_def, is_order_ord, precedes_G]
QED

(* ------------------------------------------------------------------------
   Commit points by position, for the projections (asyncKvLabel's)
   ------------------------------------------------------------------------ *)

Definition answeredG_def:
  answeredG WR rss order (c, i) evs1 ⇔
    reply_bytes (TAKE (SUC i) (replies rss order c)) ≼ WR c evs1
End

Definition startedG_def:
  startedG RD rss (d, j) evs1 ⇔ ¬(RD d evs1 ≼ brequests (TAKE j (rss d)))
End

Theorem precedesG_answered_started:
  precedesG RD WR rss order evs x y ⇔
    ∃evs1. evs1 ≼ evs ∧ answeredG WR rss order x evs1 ∧ ¬startedG RD rss y evs1
Proof
  PairCases_on ‘x’ >> PairCases_on ‘y’ >>
  simp[precedesG_def, answeredG_def, startedG_def]
QED

Definition commits_atG_def:
  commits_atG RD WR rss order evs pj ⇔
    (∀j k. j ≤ k ∧ k < LENGTH order ⇒ pj j ≤ pj k) ∧
    ∀j. j < LENGTH order ⇒
        startedG RD rss (EL j order) (TAKE (pj j) evs) ∧
        ¬answeredG WR rss order (EL j order) (TAKE (pj j) evs)
End

Theorem earlier_EL[local]:
  ∀l i j. i < j ∧ j < LENGTH l ⇒ earlier l (EL i l) (EL j l)
Proof
  Induct >> simp[earlier_CONS] >> rpt gen_tac >> Cases_on ‘i’ >> Cases_on ‘j’ >>
  simp[] >> rw[] >> gvs[]
  >- (disj1_tac >> simp[MEM_EL] >> metis_tac[])
QED

Theorem TAKE_prefix_mono[local]:
  ∀l a b. a ≤ b ⇒ TAKE a l ≼ TAKE b l
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on ‘a’ >> Cases_on ‘b’ >> simp[]
QED

(* MAIN: commit points by position give real time, for monotone
   projections *)
Theorem commits_atG_real_time:
  (∀c e1 e2. e1 ≼ e2 ⇒ RD c e1 ≼ RD c e2 ∧ WR c e1 ≼ WR c e2) ∧
  commits_atG RD WR rss order evs pj ⇒
  ∀x y. MEM x order ∧ MEM y order ∧ FST x ≠ FST y ∧
        precedesG RD WR rss order evs x y ⇒ earlier order x y
Proof
  rw[] >> gvs[MEM_EL] >> rename1 ‘precedesG _ _ _ _ _ (EL i order) (EL j order)’ >>
  ‘i < j’ suffices_by metis_tac[earlier_EL] >>
  CCONTR_TAC >>
  ‘j ≤ i’ by simp[] >>
  ‘pj j ≤ pj i’ by fs[commits_atG_def] >>
  ‘¬answeredG WR rss order (EL i order) (TAKE (pj i) evs) ∧
   startedG RD rss (EL j order) (TAKE (pj j) evs)’ by fs[commits_atG_def] >>
  qpat_x_assum ‘precedesG _ _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE [precedesG_answered_started]) >>
  ‘evs1 = TAKE (LENGTH evs1) evs’
    by (qpat_x_assum ‘evs1 ≼ evs’ mp_tac >> rw[IS_PREFIX_APPEND] >>
        simp[TAKE_LENGTH_APPEND]) >>
  qabbrev_tac ‘k = LENGTH evs1’ >>
  ‘pj i < k’
    by (CCONTR_TAC >>
        ‘TAKE k evs ≼ TAKE (pj i) evs’ by (irule TAKE_prefix_mono >> simp[]) >>
        Cases_on ‘EL i order’ >> gvs[answeredG_def] >>
        metis_tac[IS_PREFIX_TRANS]) >>
  ‘k < pj j’
    by (CCONTR_TAC >>
        ‘TAKE (pj j) evs ≼ TAKE k evs’ by (irule TAKE_prefix_mono >> simp[]) >>
        Cases_on ‘EL j order’ >> gvs[startedG_def] >>
        metis_tac[IS_PREFIX_TRANS]) >>
  decide_tac
QED

Theorem is_ord_label:
  (∀c. MAP SND (FILTER (λx. FST x = c) l) = rss c) ⇒ is_ord rss (label l)
Proof
  rw[is_ord_def, label_FILTER] >>
  first_x_assum (qspec_then ‘c’ (SUBST1_TAC o SYM)) >> simp[]
QED

(* ------------------------------------------------------------------------
   Lists
   ------------------------------------------------------------------------ *)

Theorem FLAT_GENLIST_prefix:
  a ≤ b ⇒ FLAT (GENLIST f a) ≼ FLAT (GENLIST f b)
Proof
  Induct_on ‘b’ >> rw[] >> Cases_on ‘a = SUC b’ >> simp[] >>
  ‘a ≤ b’ by simp[] >> first_x_assum drule >>
  rw[IS_PREFIX_APPEND, GENLIST, SNOC_APPEND, FLAT_APPEND] >> metis_tac[APPEND_ASSOC]
QED

Theorem prefix_TAKE_eq:
  a ≼ b ∧ k ≤ LENGTH a ⇒ TAKE k b = TAKE k a
Proof
  rw[IS_PREFIX_APPEND] >> simp[TAKE_APPEND1]
QED

Theorem prefix_TAKE_self:
  a ≼ b ⇒ TAKE (LENGTH a) b = a
Proof
  rw[IS_PREFIX_APPEND] >> simp[TAKE_LENGTH_APPEND]
QED

Theorem prefix_FLAT:
  ∀l1 l2. l1 ≼ l2 ⇒ FLAT l1 ≼ FLAT l2
Proof
  rw[IS_PREFIX_APPEND] >> simp[FLAT_APPEND]
QED

Theorem prefix_FILTER:
  ∀l1 l2. l1 ≼ l2 ⇒ FILTER P l1 ≼ FILTER P l2
Proof
  rw[IS_PREFIX_APPEND] >> simp[FILTER_APPEND]
QED

Theorem prefix_LENGTH_eq_TAKE:
  a ≼ b ⇒ a = TAKE (LENGTH a) b
Proof
  rw[IS_PREFIX_APPEND] >> simp[TAKE_LENGTH_APPEND]
QED

Theorem brequests_TAKE_prefix:
  brequests (TAKE k rs) ≼ brequests rs
Proof
  ‘rs = TAKE k rs ++ DROP k rs’ by simp[] >>
  pop_assum (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th]))) >>
  simp[brequests_def, bytes_APPEND, IS_PREFIX_APPEND]
QED

Theorem prefix_shorter_TAKE:
  a ≼ b ∧ LENGTH a ≤ j ⇒ a ≼ TAKE j b
Proof
  rw[IS_PREFIX_APPEND] >> simp[TAKE_APPEND] >> qexists_tac ‘TAKE (j - LENGTH a) l’ >> simp[]
QED

Theorem cnt_TAKE_lt:
  j < LENGTH L ⇒
  LENGTH (FILTER (λx. FST x = FST (EL j L)) (TAKE j L)) <
  LENGTH (FILTER (λx. FST x = FST (EL j L)) L)
Proof
  strip_tac >> irule FILTER_TAKE_lt >> simp[]
QED

Theorem FILTER_pend:
  ∀CS. ALL_DISTINCT CS ⇒
       FILTER (λx. FST x = c) (FLAT (MAP (λc. MAP (λr. (c, r)) (D c)) CS)) =
       if MEM c CS then MAP (λr. (c, r)) (D c) else []
Proof
  Induct >> simp[FILTER_APPEND] >> rpt strip_tac >> fs[] >>
  ‘FILTER (λx. FST x = c) (MAP (λr. (h, r)) (D h)) =
   if h = c then MAP (λr. (c, r)) (D c) else []’
    by (rw[FILTER_EQ_ID, EVERY_MAP, FILTER_EQ_NIL]) >>
  simp[] >> Cases_on ‘h = c’ >> gvs[]
QED

Theorem LENGTH_FILTER_ZIP:
  ∀L X. LENGTH X = LENGTH L ⇒
        LENGTH (FILTER (λp. FST (FST p) = c) (ZIP (L, X))) =
        LENGTH (FILTER (λx. FST x = c) L)
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on ‘X’ >> simp[] >> rw[]
QED

Theorem parse_all_b_NIL:
  parse_all_b "" = []
Proof
  simp[Once parse_all_b_def] >> EVAL_TAC
QED

(* The model's queries, renamed to keys *)
Theorem FILTER_key_map:
  ∀G. (∀c. kmap (kinv c) = c) ∧ (∀q. MEM q G ⇒ kinv (kmap (FST q)) = FST q) ⇒
      FILTER (λx. FST x = c) (MAP (λq. (kmap (FST q), SND q)) G) =
      MAP (λq. (c, SND q)) (FILTER (λq. FST q = kinv c) G)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  ‘kmap (FST h) = c ⇔ FST h = kinv c’ by metis_tac[] >>
  ‘∀q. MEM q G ⇒ kinv (kmap (FST q)) = FST q’ by metis_tac[] >>
  fs[] >> rw[]
QED

Theorem ZIP_key_map:
  ∀G A. (∀c. kmap (kinv c) = c) ∧ (∀q. MEM q G ⇒ kinv (kmap (FST q)) = FST q) ∧
        LENGTH A = LENGTH G ⇒
        FILTER (λp. FST (FST p) = c) (ZIP (MAP (λq. (kmap (FST q), SND q)) G, A)) =
        MAP (λp. ((c, SND (FST p)), SND p))
            (FILTER (λp. FST (FST p) = kinv c) (ZIP (G, A)))
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on ‘A’ >> simp[] >> strip_tac >>
  ‘kmap (FST h) = c ⇔ FST h = kinv c’ by metis_tac[] >>
  ‘∀q. MEM q G ⇒ kinv (kmap (FST q)) = FST q’ by metis_tac[] >>
  first_x_assum (qspec_then ‘t’ mp_tac) >> simp[] >> strip_tac >> rw[]
QED

(* ------------------------------------------------------------------------
   The key view of a run in rounds
   ------------------------------------------------------------------------ *)

Overload GP = “λ(EV : num -> 'e list) k. FLAT (GENLIST EV k)”

(* The run is the rounds EV i; after k rounds the store's queries are G k;
   RS k c is what the model has read on key c's fd by then, WS k c what it
   had written by the end of round k *)
Definition kv_rounds_def:
  kv_rounds RD WR EV G RS WS kmap kinv ⇔
    (∀i. EV i ≠ []) ∧
    (∀k1 k2. k1 ≤ k2 ⇒ G k1 ≼ G k2) ∧
    (∀c e1 e2. e1 ≼ e2 ⇒ RD c e1 ≼ RD c e2 ∧ WR c e1 ≼ WR c e2) ∧
    (∀c. WR c [] = []) ∧
    (∀k c. WR c (GP EV (SUC k)) = HttpSpec$bytes (FLAT (WS k c)) ∧
           RD c (GP EV k) = HttpSpec$bytes (RS k c)) ∧
    (∀k c. MAP SND (FILTER (λq. FST q = kinv c) (G k)) ≼ parse_all_b (RS k c) ∧
           WS k c ≼ MAP print_response (fd_answers (kinv c) (G k))) ∧
    (∀c. kmap (kinv c) = c) ∧
    (∀k q. MEM q (G k) ⇒ kinv (kmap (FST q)) = FST q) ∧
    (∀evs. ∃CS. ALL_DISTINCT CS ∧ ∀c. RD c evs ≠ [] ⇒ MEM c CS)
End

(* MAIN: the order construction, once *)
Theorem kv_safeG_rounds:
  kv_rounds RD WR EV G RS WS kmap kinv ⇒
  kv_safeG RD WR (LFLATTEN (LGENLIST (λi. fromList (EV i)) NONE))
Proof
  rw[kv_rounds_def, kv_safeG_def] >>
  drule_all LPREFIX_rounds_between >> strip_tac >>
  ‘∀k1 k2. k1 ≤ k2 ⇒ G k1 ≼ G k2 ∧ GP EV k1 ≼ GP EV k2’
    by metis_tac[FLAT_GENLIST_prefix] >>
  (* what has been read from each key *)
  ‘∀c. parse_all_b (MAP (CHR o w2n) (RD c evs)) = rss c’
    by (gen_tac >> irule read_brequests_parse >> simp[bytes_chars] >> metis_tac[]) >>
  ‘∀k c. k ≤ n ⇒ parse_all_b (RS k c) ≼ rss c’
    by (rpt strip_tac >>
        qpat_x_assum ‘∀c. parse_all_b _ = rss c’ (qspec_then ‘c’ (SUBST1_TAC o SYM)) >>
        irule parse_all_b_prefix >> ONCE_REWRITE_TAC[GSYM bytes_prefix_iff] >>
        simp[bytes_chars] >>
        qpat_assum ‘∀k c. WR _ _ = _ ∧ _’
          (qspecl_then [‘k’, ‘c’] (SUBST1_TAC o SYM o CONJUNCT2)) >>
        ‘GP EV k ≼ evs’ by metis_tac[IS_PREFIX_TRANS] >>
        metis_tac[]) >>
  qabbrev_tac ‘Gn = G n’ >>
  qabbrev_tac ‘Gc = λc. MAP SND (FILTER (λq. FST q = kinv c) Gn)’ >>
  ‘∀c. Gc c ≼ rss c’
    by (gen_tac >> simp[Abbr ‘Gc’, Abbr ‘Gn’] >> irule IS_PREFIX_TRANS >>
        qexists_tac ‘parse_all_b (RS n c)’ >> simp[]) >>
  (* the order *)
  qpat_assum ‘∀evs. ∃CS. _’ (qspec_then ‘evs’ strip_assume_tac) >>
  qabbrev_tac ‘L1 = MAP (λq. (kmap (FST q), SND q)) Gn’ >>
  qabbrev_tac ‘pend = FLAT (MAP (λc. MAP (λr. (c, r)) (DROP (LENGTH (Gc c)) (rss c))) CS)’ >>
  qabbrev_tac ‘L = L1 ++ pend’ >>
  ‘∀c. MAP SND (FILTER (λx. FST x = c) L1) = Gc c’
    by (gen_tac >> simp[Abbr ‘L1’, Abbr ‘Gc’] >>
        DEP_REWRITE_TAC[FILTER_key_map] >> simp[MAP_MAP_o, combinTheory.o_DEF] >>
        fs[Abbr ‘Gn’] >> metis_tac[]) >>
  ‘∀c. MAP SND (FILTER (λx. FST x = c) L) = rss c’
    by (gen_tac >> simp[Abbr ‘L’, FILTER_APPEND, Abbr ‘pend’, FILTER_pend] >> rw[]
        >- (qpat_x_assum ‘∀c. Gc c ≼ rss c’ (qspec_then ‘c’ mp_tac) >>
            simp[MAP_MAP_o, combinTheory.o_DEF] >> strip_tac >> fs[IS_PREFIX_APPEND] >>
            simp[DROP_LENGTH_APPEND]) >>
        ‘rss c = []’
          by (CCONTR_TAC >>
              ‘RD c evs ≠ []’ suffices_by metis_tac[] >>
              qpat_assum ‘∀c. EVERY _ _ ∧ _’ (qspec_then ‘c’ mp_tac) >>
              Cases_on ‘rss c’ >> fs[brequests_def, bytes_APPEND] >> rpt strip_tac >>
              qpat_x_assum ‘_ (print_brequest _) = []’
                (mp_tac o AP_TERM “LENGTH : word8 list -> num”) >>
              simp[print_brequest_NIL]) >>
        qpat_x_assum ‘∀c. Gc c ≼ rss c’ (qspec_then ‘c’ mp_tac) >> simp[]) >>
  (* what has been written, at evs *)
  ‘∀c. WR c evs ≼ reply_bytes (fd_answers (kinv c) Gn)’
    by (gen_tac >>
        ‘WR c evs ≼ WR c (GP EV (SUC n))’ by metis_tac[] >>
        ‘WR c (GP EV (SUC n)) ≼ reply_bytes (fd_answers (kinv c) Gn)’
          by (qpat_assum ‘∀k c. WR _ _ = _ ∧ _’
                (qspecl_then [‘n’, ‘c’] (SUBST1_TAC o CONJUNCT1)) >>
              simp[reply_bytes_def, bytes_prefix_iff, Abbr ‘Gn’] >>
              irule prefix_FLAT >>
              qpat_assum ‘∀k c. MAP SND _ ≼ _ ∧ _’
                (qspecl_then [‘n’, ‘c’] (ACCEPT_TAC o CONJUNCT2))) >>
        metis_tac[IS_PREFIX_TRANS]) >>
  qexists_tac ‘label L’ >>
  ‘is_ord rss (label L)’ by (irule is_ord_label >> simp[]) >>
  simp[] >>
  (* the replies *)
  qabbrev_tac ‘A = FST (run_store kv_delta (λk. NONE) Gn)’ >>
  ‘∀c. ∃X. replies rss (label L) c = fd_answers (kinv c) Gn ++ X’
    by (gen_tac >> simp[replies_label] >>
        ‘MAP SND L1 = MAP SND Gn’ by simp[Abbr ‘L1’, LIST_EQ_REWRITE, EL_MAP] >>
        ‘MAP SND L = MAP SND (Gn ++ MAP (λx. (0:num, SND x)) pend)’
          by (simp[Abbr ‘L’] >> simp[LIST_EQ_REWRITE, EL_MAP]) >>
        qpat_x_assum ‘MAP SND L = _’ SUBST1_TAC >>
        REWRITE_TAC[kv_run_store, run_store_APPEND_FST] >>
        simp[Abbr ‘L’] >>
        DEP_REWRITE_TAC[GSYM ZIP_APPEND] >> conj_tac >- simp[Abbr ‘L1’, Abbr ‘A’] >>
        simp[FILTER_APPEND, Abbr ‘L1’] >>
        DEP_REWRITE_TAC[ZIP_key_map] >>
        conj_tac >- (simp[Abbr ‘A’] >> fs[Abbr ‘Gn’] >> metis_tac[]) >>
        simp[fd_answers_def, MAP_MAP_o, combinTheory.o_DEF, ETA_AX]) >>
  ‘∀c. LENGTH (replies rss (label L) c) = LENGTH (rss c)’
    by (gen_tac >> simp[replies_label] >>
        DEP_REWRITE_TAC[LENGTH_FILTER_ZIP] >> simp[] >>
        qpat_x_assum ‘∀c. MAP SND (FILTER _ L) = _’
          (qspec_then ‘c’ (SUBST1_TAC o SYM)) >> simp[]) >>
  ‘∀c. LENGTH (fd_answers (kinv c) Gn) = LENGTH (Gc c)’
    by simp[LENGTH_fd_answers, Abbr ‘Gc’] >>
  ‘∀c. reply_bytes (fd_answers (kinv c) Gn) =
       reply_bytes (TAKE (LENGTH (Gc c)) (replies rss (label L) c))’
    by (gen_tac >> qpat_x_assum ‘∀c. ∃X. _’ (qspec_then ‘c’ strip_assume_tac) >>
        qpat_x_assum ‘∀c. LENGTH (fd_answers _ _) = _’
          (qspec_then ‘c’ (SUBST1_TAC o SYM)) >>
        simp[TAKE_LENGTH_APPEND]) >>
  conj_tac
  >- ((* real time *)
      qsuff_tac ‘∃pj. commits_atG RD WR rss (label L) evs pj’
      >- metis_tac[commits_atG_real_time] >>
      qexists_tac ‘λj. if j < LENGTH Gn then LENGTH (GP EV ($LEAST (λk. j < LENGTH (G k))))
                       else LENGTH evs’ >>
      ‘∀j. j < LENGTH Gn ⇒
           j < LENGTH (G ($LEAST (λk. j < LENGTH (G k)))) ∧
           $LEAST (λk. j < LENGTH (G k)) ≤ n ∧
           ∀m. m < $LEAST (λk. j < LENGTH (G k)) ⇒ LENGTH (G m) ≤ j’
        by (rpt gen_tac >> strip_tac >>
            qspecl_then [‘λk. j < LENGTH (G k)’, ‘n’] mp_tac
              (Q.GEN ‘P’ WhileTheory.FULL_LEAST_INTRO) >>
            simp[Abbr ‘Gn’] >> rw[] >>
            drule (Q.ISPEC ‘λk:num. j < LENGTH (G k)’ WhileTheory.LESS_LEAST) >> simp[]) >>
      ‘∀a b. a ≤ b ⇒ LENGTH (GP EV a) ≤ LENGTH (GP EV b)’
        by metis_tac[IS_PREFIX_LENGTH] >>
      ‘LENGTH (GP EV n) ≤ LENGTH evs’ by metis_tac[IS_PREFIX_LENGTH] >>
      ‘LENGTH L1 = LENGTH Gn’ by simp[Abbr ‘L1’] >>
      simp[commits_atG_def] >> conj_tac
      >- (rw[] >> gvs[]
          >- (qpat_x_assum ‘∀a b. a ≤ b ⇒ LENGTH _ ≤ LENGTH _’ irule >>
              qspecl_then [‘λk. j < LENGTH (G k)’,
                           ‘$LEAST (λk. j' < LENGTH (G k))’] mp_tac
                (Q.GEN ‘P’ WhileTheory.FULL_LEAST_INTRO) >>
              simp[] >> impl_tac
              >- (qpat_x_assum ‘∀j. j < LENGTH Gn ⇒ _’ (qspec_then ‘j'’ mp_tac) >> simp[]) >>
              simp[])
          >> irule LESS_EQ_TRANS >> qexists_tac ‘LENGTH (GP EV n)’ >> simp[] >>
          qpat_x_assum ‘∀a b. a ≤ b ⇒ LENGTH _ ≤ LENGTH _’ irule >>
          qpat_x_assum ‘∀j. j < LENGTH Gn ⇒ _’ (qspec_then ‘j’ mp_tac) >> simp[]) >>
      rpt gen_tac >> strip_tac >>
      qabbrev_tac ‘c = FST (EL j L)’ >>
      qabbrev_tac ‘i = LENGTH (FILTER (λx. FST x = c) (TAKE j L))’ >>
      ‘EL j (label L) = (c, i)’ by simp[label_def, EL_GENLIST, Abbr ‘c’, Abbr ‘i’] >>
      pop_assum SUBST1_TAC >>
      ‘i < LENGTH (rss c)’
        by (simp[Abbr ‘i’, Abbr ‘c’] >>
            qpat_x_assum ‘∀c. MAP SND (FILTER _ L) = _’
              (qspec_then ‘FST (EL j L)’ (SUBST1_TAC o SYM)) >>
            simp[] >> irule cnt_TAKE_lt >> fs[]) >>
      simp[startedG_def, answeredG_def] >>
      Cases_on ‘j < LENGTH Gn’ >> simp[]
      >- ((* a query, committed at the start of its first round cr *)
          qabbrev_tac ‘cr = $LEAST (λk. j < LENGTH (G k))’ >>
          qpat_x_assum ‘∀j. j < LENGTH Gn ⇒ _’ (qspec_then ‘j’ mp_tac) >> simp[] >> strip_tac >>
          ‘TAKE (LENGTH (GP EV cr)) evs = GP EV cr’
            by (irule prefix_TAKE_self >> irule IS_PREFIX_TRANS >>
                qexists_tac ‘GP EV n’ >> simp[]) >>
          simp[] >>
          qabbrev_tac ‘fd = FST (EL j Gn)’ >>
          ‘kinv (kmap fd) = fd’
            by (simp[Abbr ‘fd’] >> qpat_assum ‘∀k q. MEM q (G k) ⇒ _’ irule >>
                qexists_tac ‘n’ >> fs[Abbr ‘Gn’, EL_MEM]) >>
          ‘EL j L = (kmap fd, SND (EL j Gn))’
            by simp[Abbr ‘L’, EL_APPEND1, Abbr ‘L1’, EL_MAP] >>
          ‘kinv c = fd’ by simp[Abbr ‘c’] >>
          ‘LENGTH (FILTER (λq. FST q = fd) (TAKE j Gn)) = i’
            by (simp[Abbr ‘i’, Abbr ‘L’, TAKE_APPEND1, Abbr ‘L1’, GSYM MAP_TAKE] >>
                DEP_REWRITE_TAC[FILTER_key_map] >> simp[] >>
                rpt strip_tac >> ‘MEM q Gn’ by metis_tac[MEM_TAKE] >>
                qpat_assum ‘∀k q. MEM q (G k) ⇒ _’ irule >>
                qexists_tac ‘n’ >> fs[Abbr ‘Gn’]) >>
          ‘G cr ≼ Gn’ by simp[Abbr ‘Gn’] >>
          ‘TAKE (SUC j) Gn = TAKE (SUC j) (G cr)’ by (irule prefix_TAKE_eq >> simp[]) >>
          conj_tac
          >- ((* started: c's first i+1 requests were read before round cr *)
              irule brequests_TAKE_SUC >> simp[] >>
              qabbrev_tac ‘PR = parse_all_b (RS cr c)’ >>
              ‘PR ≼ rss c’
                by (qunabbrev_tac ‘PR’ >>
                    qpat_assum ‘∀k c. k ≤ n ⇒ parse_all_b _ ≼ rss c’ irule >> simp[]) >>
              ‘LENGTH (FILTER (λq. FST q = fd) (TAKE (SUC j) (G cr))) = SUC i’
                by (qpat_x_assum ‘TAKE (SUC j) Gn = _’ (SUBST1_TAC o SYM) >>
                    simp[TAKE_SUC_EL, FILTER_APPEND] >> simp[Abbr ‘fd’]) >>
              ‘LENGTH (FILTER (λq. FST q = fd) (TAKE (SUC j) (G cr))) ≤
               LENGTH (FILTER (λq. FST q = fd) (G cr))’
                by (irule IS_PREFIX_LENGTH >> irule prefix_FILTER >>
                    simp[IS_PREFIX_APPEND] >> metis_tac[TAKE_DROP]) >>
              ‘LENGTH (MAP SND (FILTER (λq. FST q = fd) (G cr))) ≤ LENGTH PR’
                by (qpat_assum ‘∀k c. MAP SND _ ≼ _ ∧ _’
                      (qspecl_then [‘cr’, ‘c’]
                         (mp_tac o MATCH_MP IS_PREFIX_LENGTH o CONJUNCT1)) >>
                    simp[Abbr ‘PR’]) >>
              ‘SUC i ≤ LENGTH PR’ by fs[] >>
              ‘TAKE (SUC i) (rss c) = TAKE (SUC i) PR’ by (irule prefix_TAKE_eq >> simp[]) >>
              simp[brequests_def, bytes_prefix_iff] >>
              irule parse_all_b_printed >> simp[Abbr ‘PR’, IS_PREFIX_APPEND] >>
              metis_tac[TAKE_DROP]) >>
          (* not answered: before round cr, at most c's first i answers *)
          ‘∃i'. i' ≤ i ∧ WR c (GP EV cr) ≼ reply_bytes (TAKE i' (replies rss (label L) c))’
            by (Cases_on ‘cr’
                >- (qexists_tac ‘0’ >> simp[]) >>
                rename1 ‘GP EV (SUC k2)’ >>
                ‘LENGTH (G k2) ≤ j’
                  by (qpat_x_assum ‘∀m. m < SUC k2 ⇒ _’ (qspec_then ‘k2’ mp_tac) >> simp[]) >>
                ‘G k2 ≼ Gn’ by simp[Abbr ‘Gn’] >>
                qexists_tac ‘LENGTH (fd_answers fd (G k2))’ >> conj_tac
                >- (simp[LENGTH_fd_answers] >>
                    qpat_x_assum ‘LENGTH (FILTER _ (TAKE j Gn)) = i’ (SUBST1_TAC o SYM) >>
                    irule IS_PREFIX_LENGTH >> irule prefix_FILTER >>
                    irule prefix_shorter_TAKE >> simp[]) >>
                ‘fd_answers fd (G k2) =
                 TAKE (LENGTH (fd_answers fd (G k2))) (replies rss (label L) c)’
                  by (irule prefix_LENGTH_eq_TAKE >> irule IS_PREFIX_TRANS >>
                      qexists_tac ‘fd_answers fd Gn’ >> conj_tac >>
                      TRY (irule fd_answers_prefix >> simp[] >> NO_TAC) >>
                      qpat_x_assum ‘∀c. ∃X. _’ (qspec_then ‘c’ strip_assume_tac) >> simp[]) >>
                pop_assum (SUBST1_TAC o SYM) >>
                qpat_assum ‘∀k c. WR _ _ = _ ∧ _’
                  (qspecl_then [‘k2’, ‘c’] (SUBST1_TAC o CONJUNCT1)) >>
                simp[reply_bytes_def, bytes_prefix_iff] >> irule prefix_FLAT >>
                qpat_x_assum ‘kinv c = fd’ (SUBST1_TAC o SYM) >>
                qpat_assum ‘∀k c. MAP SND _ ≼ _ ∧ _’
                  (qspecl_then [‘k2’, ‘c’] (ACCEPT_TAC o CONJUNCT2))) >>
          strip_tac >>
          qspecl_then [‘i’, ‘replies rss (label L) c’, ‘i'’, ‘WR c (GP EV cr)’]
            mp_tac (Q.GENL [‘i’, ‘R’, ‘j’, ‘x’] reply_bytes_TAKE) >> simp[]) >>
      (* a request not queried yet, committed at the end of evs *)
      ‘LENGTH (Gc c) ≤ i’
        by (qpat_x_assum ‘∀c. MAP SND (FILTER _ L1) = Gc c’ (qspec_then ‘c’ (SUBST1_TAC o SYM)) >>
            simp[Abbr ‘i’, Abbr ‘L’, TAKE_APPEND, TAKE_LENGTH_TOO_LONG, FILTER_APPEND]) >>
      conj_tac
      >- (irule brequests_TAKE_SUC >> simp[] >> irule IS_PREFIX_TRANS >>
          qexists_tac ‘brequests (rss c)’ >> simp[brequests_TAKE_prefix]) >>
      strip_tac >>
      qspecl_then [‘i’, ‘replies rss (label L) c’, ‘LENGTH (Gc c)’, ‘WR c evs’]
        mp_tac (Q.GENL [‘i’, ‘R’, ‘j’, ‘x’] reply_bytes_TAKE) >> simp[] >>
      qpat_x_assum ‘∀c. reply_bytes _ = _’ (qspec_then ‘c’ (SUBST1_TAC o SYM)) >>
      qpat_x_assum ‘∀c. WR c evs ≼ _’ (qspec_then ‘c’ ACCEPT_TAC)) >>
  gen_tac >> qpat_x_assum ‘∀c. ∃X. _’ (qspec_then ‘c’ strip_assume_tac) >> simp[] >>
  irule IS_PREFIX_TRANS >> qexists_tac ‘reply_bytes (fd_answers (kinv c) Gn)’ >>
  simp[reply_bytes_prefix]
QED
