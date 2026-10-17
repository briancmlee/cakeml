(*
  P4 (design/46), step A: the pure trace lemma that moves the key-value
  server's linearizability from the version-2 trace to the raw L0 trace
  (kv_server_view_safe).  It is the server-side mirror of moonshotKvClient's
  kv_client_view_safe.

  Both traces are seen through projections: RD2 c / WR2 c (what the v2
  server read from / wrote to its episode c), RD1 j / WR1 j (what the
  kernel handed the program / took from it in raw episode j).  vtr t is the
  v2 trace at instant t, and tm evs the instant paired with the raw prefix
  evs (for the honest L1, a raw prefix inside round n is paired with the
  v2 instant SUC n).  e pairs raw episodes with v2 episodes (partial,
  injective).  Per pair, the raw side has read AT LEAST what the server has
  (the L1 reads ahead) and sent AT MOST what it wrote (the outbox).

  The raw side may hold complete requests the server has not consumed yet.
  The order is the server's, renamed, then those requests, episode by
  episode: no reply bytes were sent for them, so the sent bytes stay a
  prefix of the replies, real time into them is satisfied (they come
  last), and real time out of them cannot hold (a reply is never empty).

  Copied verbatim from moonshotKvClient (spike/moonshot-*, not on this
  branch): brequests_CONS, brequests_NIL, brequests_split,
  LPREFIX_fromList_prefix, LENGTH_kv_run, filter_rename,
  filter_rename_none, zip_filter_rename, earlier_rename.  Remove the copies
  when both branches reach shared/base.
*)
Theory honestKvL0View
Ancestors
  words llist rich_list HttpSpec HttpSpecBodies HttpKvSpec asyncKvTraceLemmas
  asyncKvOrderGen
Libs
  preamble

(* ------------------------------------------------------------------------
   Lemmas (copies from moonshotKvClient)
   ------------------------------------------------------------------------ *)

Theorem brequests_CONS:
  brequests (r :: rs) = brequests [r] ++ brequests rs
Proof
  simp[brequests_def, bytes_def]
QED

Theorem brequests_NIL[simp]:
  brequests [] = [] ∧ (brequests rs = [] ⇔ rs = [])
Proof
  simp[brequests_def, bytes_def] >> Cases_on ‘rs’ >> simp[] >>
  rename1 ‘print_brequest r’ >> Cases_on ‘r’ >> simp[print_brequest_def]
QED

(* Any bytes are some complete valid requests, then no complete one *)
Theorem brequests_split:
  ∀bs. ∃rs rest. EVERY valid_brequest rs ∧ no_full_brequest rest ∧
                 bs = brequests rs ++ rest
Proof
  gen_tac >> completeInduct_on ‘LENGTH bs’ >> rw[] >>
  Cases_on ‘no_full_brequest bs’
  >- (qexistsl_tac [‘[]’, ‘bs’] >> simp[]) >>
  fs[no_full_brequest_def, IS_PREFIX_APPEND] >> rename1 ‘bs = brequests [r] ++ bs'’ >>
  ‘brequests [r] ≠ []’ by simp[] >>
  first_x_assum (qspec_then ‘LENGTH bs'’ mp_tac) >>
  impl_tac >- (gvs[] >> Cases_on ‘brequests [r]’ >> gvs[]) >>
  disch_then (qspec_then ‘bs'’ mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [‘r :: rs’, ‘rest’] >> gvs[] >> ONCE_REWRITE_TAC [brequests_CONS] >> simp[]
QED

Theorem LPREFIX_fromList_prefix:
  evs1 ≼ evs ∧ LPREFIX (fromList evs) io ⇒ LPREFIX (fromList evs1) io
Proof
  strip_tac >> irule LPREFIX_TRANS >> qexists_tac ‘fromList evs’ >>
  simp[LPREFIX_fromList, from_toList]
QED

Theorem LENGTH_kv_run[simp]:
  ∀st rs. LENGTH (kv_run st rs) = LENGTH rs
Proof
  Induct_on ‘rs’ >> simp[kv_run_def] >> rpt gen_tac >> pairarg_tac >> simp[]
QED

(* Renaming episodes by g, injective on the order's episodes *)
Theorem filter_rename:
  ∀order. (∀d. MEM d (MAP FST order) ⇒ (g d = c' ⇔ d = c)) ⇒
          MAP SND (FILTER (λx. FST x = c') (MAP (λ(d, i). (g d, i)) order)) =
          MAP SND (FILTER (λx. FST x = c) order)
Proof
  Induct >> simp[FORALL_PROD] >> rw[] >> gvs[]
QED

Theorem filter_rename_none:
  ∀order. (∀d. MEM d (MAP FST order) ⇒ g d ≠ c') ⇒
          FILTER (λx. FST x = c') (MAP (λ(d, i). (g d, i)) order) = []
Proof
  Induct >> simp[FORALL_PROD] >> rw[] >> gvs[]
QED

Theorem zip_filter_rename:
  ∀order ys. LENGTH ys = LENGTH order ∧
             (∀d. MEM d (MAP FST order) ⇒ (g d = g c ⇔ d = c)) ⇒
             MAP SND (FILTER (λ((d, i), a). d = g c) (ZIP (MAP (λ(d, i). (g d, i)) order, ys))) =
             MAP SND (FILTER (λ((d, i), a). d = c) (ZIP (order, ys)))
Proof
  Induct >> simp[FORALL_PROD] >> rpt gen_tac >> Cases_on ‘ys’ >> simp[] >>
  rw[] >> gvs[]
QED

Theorem earlier_rename:
  earlier order (a, b) (c, d) ⇒
  earlier (MAP (λ(x, y). (g x, y)) order) (g a, b) (g c, d)
Proof
  rw[earlier_def] >> simp[MAP_APPEND] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Lemmas: lists, requests, replies
   ------------------------------------------------------------------------ *)

Theorem prefix_MAP[local]:
  ∀l1 l2. l1 ≼ l2 ⇒ MAP f l1 ≼ MAP f l2
Proof
  Induct >> simp[] >> Cases_on ‘l2’ >> simp[]
QED

Theorem prefix_EL[local]:
  a ≼ b ∧ i < LENGTH a ⇒ EL i b = EL i a
Proof
  rw[IS_PREFIX_APPEND] >> simp[EL_APPEND1]
QED

Theorem COUNT_LIST_ext[local]:
  b ≤ n ⇒ COUNT_LIST b ++ GENLIST (λi. b + i) (n − b) = COUNT_LIST n
Proof
  rw[LIST_EQ_REWRITE, LENGTH_COUNT_LIST, EL_APPEND_EQN, EL_COUNT_LIST]
QED

(* Of two streams of complete requests, each followed by no complete one,
   the shorter has the fewer requests *)
Theorem brequests_prefix_mono:
  brequests a ++ ra ≼ brequests b ++ rb ∧ EVERY valid_brequest a ∧ EVERY valid_brequest b ∧
  no_full_brequest ra ∧ no_full_brequest rb ⇒ a ≼ b
Proof
  strip_tac >>
  ‘parse_all_b (MAP (CHR o w2n) (brequests a ++ ra)) = a’
    by (irule read_brequests_parse >> fs[bytes_chars]) >>
  ‘parse_all_b (MAP (CHR o w2n) (brequests b ++ rb)) = b’
    by (irule read_brequests_parse >> fs[bytes_chars]) >>
  metis_tac[parse_all_b_prefix, prefix_MAP]
QED

Theorem kv_run_APPEND[local]:
  ∀xs st ys. ∃st'. kv_run st (xs ++ ys) = kv_run st xs ++ kv_run st' ys
Proof
  Induct >> simp[kv_run_def] >- metis_tac[] >>
  rpt gen_tac >> pairarg_tac >> simp[]
QED

(* More of the order: the replies to a key grow *)
Theorem replies_APPEND:
  replies rss order c ≼ replies rss (order ++ X) c
Proof
  simp[replies_def] >>
  qspecl_then [‘MAP (λ(d, i). EL i (rss d)) order’, ‘λk. NONE’,
               ‘MAP (λ(d, i). EL i (rss d)) X’] strip_assume_tac kv_run_APPEND >>
  simp[MAP_APPEND] >>
  ‘ZIP (order ++ X, kv_run (λk. NONE) (MAP (λ(d, i). EL i (rss d)) order) ++
                    kv_run st' (MAP (λ(d, i). EL i (rss d)) X)) =
   ZIP (order, kv_run (λk. NONE) (MAP (λ(d, i). EL i (rss d)) order)) ++
   ZIP (X, kv_run st' (MAP (λ(d, i). EL i (rss d)) X))’
    by (irule (GSYM ZIP_APPEND) >> simp[]) >>
  simp[FILTER_APPEND]
QED

Theorem LENGTH_FILTER_pair[local]:
  ∀l. LENGTH (FILTER (λ((d, i), a). d = c) l) = LENGTH (FILTER (λx. FST x = c) (MAP FST l))
Proof
  Induct >> simp[FORALL_PROD] >> rw[]
QED

Theorem LENGTH_replies:
  LENGTH (replies rss order c) = LENGTH (FILTER (λx. FST x = c) order)
Proof
  simp[replies_def, LENGTH_FILTER_pair, MAP_ZIP]
QED

(* Replies depend only on the requests the order names *)
Theorem replies_rename_el:
  (∀d i. MEM (d, i) order ⇒ EL i (r2 (g d)) = EL i (r1 d) ∧ (g d = g c ⇔ d = c)) ⇒
  replies r2 (MAP (λ(d, i). (g d, i)) order) (g c) = replies r1 order c
Proof
  strip_tac >> simp[replies_def] >>
  ‘MAP (λ(d, i). EL i (r2 d)) (MAP (λ(d, i). (g d, i)) order) =
   MAP (λ(d, i). EL i (r1 d)) order’
    by (simp[MAP_MAP_o, combinTheory.o_DEF] >> irule MAP_CONG >> simp[FORALL_PROD]) >>
  simp[] >> irule zip_filter_rename >> simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

Theorem reply_bytes_APPEND[local]:
  reply_bytes (a ++ b) = reply_bytes a ++ reply_bytes b
Proof
  simp[reply_bytes_def, bytes_APPEND]
QED

Theorem reply_bytes_prefix:
  a ≼ b ⇒ reply_bytes a ≼ reply_bytes b
Proof
  rw[IS_PREFIX_APPEND] >> simp[reply_bytes_APPEND]
QED

Theorem reply_bytes_longer[local]:
  a ≼ b ∧ LENGTH a < LENGTH b ⇒ LENGTH (reply_bytes a) < LENGTH (reply_bytes b)
Proof
  rw[IS_PREFIX_APPEND] >> gvs[reply_bytes_APPEND] >>
  Cases_on ‘l’ >> gvs[reply_bytes_def, bytes_def] >>
  rename1 ‘print_response r’ >> Cases_on ‘r’ >> simp[print_response_def]
QED

(* A request after the replies P cannot have been answered by bytes that
   are a prefix of P's *)
Theorem unanswered_extra:
  P ≼ Q ∧ LENGTH P ≤ i ∧ i < LENGTH Q ∧ w ≼ reply_bytes P ⇒
  ¬(reply_bytes (TAKE (SUC i) Q) ≼ w)
Proof
  strip_tac >> strip_tac >>
  ‘P ≼ TAKE (SUC i) Q’ by (irule prefix_shorter_TAKE >> simp[]) >>
  ‘LENGTH (reply_bytes P) < LENGTH (reply_bytes (TAKE (SUC i) Q))’
    by (irule reply_bytes_longer >> simp[LENGTH_TAKE]) >>
  ‘reply_bytes (TAKE (SUC i) Q) ≼ reply_bytes P’ by metis_tac[IS_PREFIX_TRANS] >>
  drule IS_PREFIX_LENGTH >> simp[]
QED

Theorem earlier_APPEND[local]:
  earlier L x y ⇒ earlier (L ++ X) x y
Proof
  rw[earlier_def] >> metis_tac[APPEND_ASSOC]
QED

Theorem earlier_cross[local]:
  MEM x L ∧ MEM y X ⇒ earlier (L ++ X) x y
Proof
  rw[earlier_def] >> gvs[MEM_SPLIT] >>
  qexistsl_tac [‘l1’, ‘l2 ++ l1'’, ‘l2'’] >> simp[]
QED

(* ------------------------------------------------------------------------
   The transfer
   ------------------------------------------------------------------------ *)

(* The real-time case of two renamed requests: precedence moves from the
   raw trace back to the v2 trace at the paired instant *)
Theorem view_both_renamed:
  ∀(RD1 : 'c -> 'b list -> word8 list) WR1 rss1 (e : 'c -> 'd option) g io1 L X.
  (∀(t:num) t'. t ≤ t' ⇒ (vtr : num -> 'a list) t ≼ vtr t') ∧
  (∀evs evs'. LPREFIX (fromList evs) io1 ∧ evs' ≼ evs ⇒ tm evs' ≤ tm evs) ∧
  (∀evs j c. LPREFIX (fromList evs) io1 ∧ e j = SOME c ⇒
     RD2 c (vtr (tm evs)) ≼ RD1 j evs ∧ WR1 j evs ≼ WR2 c (vtr (tm evs))) ∧
  LPREFIX (fromList evs) io1 ∧
  e (g d) = SOME d ∧ e (g d') = SOME d' ∧
  l ≤ LENGTH (rss2 d') ∧ rss2 d' ≼ rss1 (g d') ∧
  replies rss1 L (g d) = replies rss2 order2 d ∧
  SUC i ≤ LENGTH (replies rss1 L (g d)) ∧
  precedesG RD1 WR1 rss1 (L ++ X) evs (g d, i) (g d', l) ⇒
  precedesG RD2 WR2 rss2 order2 (vtr (tm evs)) (d, i) (d', l)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘precedesG _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [precedesG_def]) >>
  rewrite_tac[precedesG_def] >> qexists_tac ‘vtr (tm evs1)’ >>
  ‘LPREFIX (fromList evs1) io1’ by (irule LPREFIX_fromList_prefix >> qexists_tac ‘evs’ >> simp[]) >>
  qpat_assum ‘∀evs j c. LPREFIX _ io1 ∧ e j = SOME c ⇒ _’
    (qspecl_then [‘evs1’, ‘g d’, ‘d’] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qpat_assum ‘∀evs j c. LPREFIX _ io1 ∧ e j = SOME c ⇒ _’
    (qspecl_then [‘evs1’, ‘g d'’, ‘d'’] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  rpt conj_tac
  >- (first_assum irule >> first_assum irule >> simp[])
  >- (‘TAKE (SUC i) (replies rss1 (L ++ X) (g d)) = TAKE (SUC i) (replies rss2 order2 d)’
        by (qpat_x_assum ‘replies _ L _ = _’ (SUBST1_TAC o SYM) >>
            irule prefix_TAKE_eq >> simp[replies_APPEND]) >>
      irule IS_PREFIX_TRANS >> qexists_tac ‘WR1 (g d) evs1’ >> simp[] >>
      qpat_x_assum ‘TAKE _ _ = _’ (SUBST1_TAC o SYM) >> simp[]) >>
  irule IS_PREFIX_TRANS >> qexists_tac ‘RD1 (g d') evs1’ >> simp[] >>
  ‘TAKE l (rss1 (g d')) = TAKE l (rss2 d')’ by (irule prefix_TAKE_eq >> simp[]) >>
  pop_assum (SUBST1_TAC o SYM) >> simp[]
QED

(* MAIN: the server's linearizability on the v2 trace (projections RD2,
   WR2) is linearizability on the raw trace (RD1, WR1), if at every raw
   prefix evs, per pair, the raw side read at least and sent at most what
   the server did by the paired instant, an unpaired raw episode sent
   nothing, an unpaired v2 episode read nothing, finitely many raw episodes
   were read from, and what was sent grows *)
Theorem kv_server_view_safe:
  (∀(t:num) t'. t ≤ t' ⇒ vtr t ≼ vtr t') ∧
  (∀t. LPREFIX (fromList (vtr t)) io2) ∧
  (∀evs evs'. LPREFIX (fromList evs) io1 ∧ evs' ≼ evs ⇒ tm evs' ≤ tm evs) ∧
  (∀j1 j2 c. e j1 = SOME c ∧ e j2 = SOME c ⇒ j1 = j2) ∧
  (∀evs j. LPREFIX (fromList evs) io1 ∧ e j = NONE ⇒ WR1 j evs = []) ∧
  (∀evs j c. LPREFIX (fromList evs) io1 ∧ e j = SOME c ⇒
     RD2 c (vtr (tm evs)) ≼ RD1 j evs ∧ WR1 j evs ≼ WR2 c (vtr (tm evs))) ∧
  (∀t c. (∀j. e j ≠ SOME c) ⇒ RD2 c (vtr t) = []) ∧
  (∀evs. LPREFIX (fromList evs) io1 ⇒ ∃CS. ∀j. RD1 j evs ≠ [] ⇒ MEM j CS) ∧
  (∀j evs evs'. evs' ≼ evs ⇒ WR1 j evs' ≼ WR1 j evs) ∧
  kv_safeG RD2 WR2 io2 ⇒
  kv_safeG RD1 WR1 io1
Proof
  strip_tac >> simp_tac std_ss [kv_safeG_def] >> rpt strip_tac >>
  rename1 ‘RD1 _ evs = brequests (rss1 _) ++ rests1 _’ >>
  qabbrev_tac ‘t = tm evs’ >>
  (* the server's requests at the paired instant *)
  ‘∀c. ∃rs rest. EVERY valid_brequest rs ∧ no_full_brequest rest ∧
                 RD2 c (vtr t) = brequests rs ++ rest’ by metis_tac[brequests_split] >>
  fs[SKOLEM_THM] >> rename1 ‘RD2 _ (vtr t) = brequests (rss2 _) ++ rests2 _’ >>
  qpat_assum ‘kv_safeG RD2 WR2 io2’ (mp_tac o REWRITE_RULE [kv_safeG_def]) >>
  disch_then (qspecl_then [‘vtr t’, ‘rss2’, ‘rests2’] mp_tac) >>
  impl_tac >- (conj_tac >- first_assum (qspec_then ‘t’ ACCEPT_TAC) >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then ‘order2’ strip_assume_tac) >>
  (* the pairing, backwards *)
  qabbrev_tac ‘g = λc. @j. e j = SOME c’ >>
  ‘∀j c. e j = SOME c ⇒ g c = j’
    by (rw[Abbr ‘g’] >> SELECT_ELIM_TAC >> metis_tac[]) >>
  ‘∀j c. e j = SOME c ⇒ rss2 c ≼ rss1 j’
    by (rpt strip_tac >> irule brequests_prefix_mono >>
        qpat_assum ‘∀c. EVERY _ (rss2 c) ∧ _’ (qspec_then ‘c’ strip_assume_tac) >>
        qpat_assum ‘∀c. EVERY _ (rss1 c) ∧ _’ (qspec_then ‘j’ strip_assume_tac) >>
        rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
        qexistsl_tac [‘rests2 c’, ‘rests1 j’] >>
        rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
        qpat_x_assum ‘RD2 c _ = _’ (SUBST1_TAC o SYM) >>
        qpat_x_assum ‘RD1 j _ = _’ (SUBST1_TAC o SYM) >>
        qpat_assum ‘∀evs j c. LPREFIX _ io1 ∧ e j = SOME c ⇒ _’
          (qspecl_then [‘evs’, ‘j’, ‘c’] mp_tac) >>
        simp[Abbr ‘t’]) >>
  (* every request in the server's order is of a paired episode *)
  ‘∀d i. MEM (d, i) order2 ⇒ i < LENGTH (rss2 d) ∧ e (g d) = SOME d’
    by (rpt gen_tac >> strip_tac >>
        ‘i < LENGTH (rss2 d)’
          by (qpat_assum ‘is_ord rss2 order2’ (mp_tac o Q.SPEC ‘d’ o REWRITE_RULE [is_ord_def]) >>
              disch_then (mp_tac o Q.AP_TERM ‘MEM i’) >>
              simp[MEM_COUNT_LIST, MEM_MAP, MEM_FILTER, EXISTS_PROD] >> metis_tac[]) >>
        simp[] >>
        ‘∃j. e j = SOME d’
          by (CCONTR_TAC >>
              ‘RD2 d (vtr t) = []’ by (qpat_assum ‘∀t c. (∀j. _) ⇒ _’ irule >> metis_tac[]) >>
              qpat_assum ‘∀c. EVERY _ (rss2 c) ∧ _’ (qspec_then ‘d’ strip_assume_tac) >>
              gvs[]) >>
        metis_tac[]) >>
  (* the raw episodes read from *)
  ‘∃CS. ∀j. RD1 j evs ≠ [] ⇒ MEM j CS’ by metis_tac[] >>
  ‘∀j. ¬MEM j (nub CS) ⇒ rss1 j = []’
    by (rw[] >> qpat_assum ‘∀c. EVERY _ (rss1 c) ∧ _’ (qspec_then ‘j’ strip_assume_tac) >>
        CCONTR_TAC >> gvs[] >> metis_tac[]) >>
  qabbrev_tac ‘base = λj. case e j of NONE => 0 | SOME c => LENGTH (rss2 c)’ >>
  qabbrev_tac ‘L = MAP (λ(d, i). (g d, i)) order2’ >>
  qabbrev_tac ‘X = FLAT (MAP (λj. MAP (λr. (j, r))
                                (GENLIST (λi. base j + i) (LENGTH (rss1 j) − base j))) (nub CS))’ >>
  ‘∀j. base j ≤ LENGTH (rss1 j)’
    by (rw[Abbr ‘base’] >> CASE_TAC >> simp[] >> metis_tac[IS_PREFIX_LENGTH]) >>
  (* each raw episode's part of the renamed order *)
  ‘∀j. MAP SND (FILTER (λx. FST x = j) L) = COUNT_LIST (base j)’
    by (gen_tac >> simp[Abbr ‘base’, Abbr ‘L’] >> Cases_on ‘e j’ >> simp[]
        >- (‘FILTER (λx. FST x = j) (MAP (λ(d, i). (g d, i)) order2) = []’
              by (irule filter_rename_none >> simp[MEM_MAP, EXISTS_PROD] >>
                  rpt strip_tac >> gvs[] >> metis_tac[NOT_SOME_NONE]) >>
            simp[COUNT_LIST_def]) >>
        rename1 ‘e j = SOME c’ >>
        ‘MAP SND (FILTER (λx. FST x = j) (MAP (λ(d, i). (g d, i)) order2)) =
         MAP SND (FILTER (λx. FST x = c) order2)’
          by (irule filter_rename >> simp[MEM_MAP, EXISTS_PROD] >>
              rpt strip_tac >> eq_tac >> strip_tac >> gvs[] >>
              metis_tac[SOME_11]) >>
        pop_assum SUBST1_TAC >>
        qpat_x_assum ‘is_ord rss2 order2’ (mp_tac o REWRITE_RULE [is_ord_def]) >> simp[]) >>
  ‘∀j. MAP SND (FILTER (λx. FST x = j) X) =
       if MEM j (nub CS) then GENLIST (λi. base j + i) (LENGTH (rss1 j) − base j) else []’
    by (gen_tac >> simp[Abbr ‘X’, FILTER_pend, all_distinct_nub] >>
        rw[MAP_MAP_o, combinTheory.o_DEF]) >>
  ‘is_ord rss1 (L ++ X)’
    by (simp_tac std_ss [is_ord_def, FILTER_APPEND, MAP_APPEND] >> qx_gen_tac ‘j’ >>
        qpat_assum ‘∀j. MAP SND (FILTER _ L) = _’ (qspec_then ‘j’ SUBST1_TAC) >>
        qpat_assum ‘∀j. MAP SND (FILTER _ X) = _’ (qspec_then ‘j’ SUBST1_TAC) >>
        qpat_assum ‘∀j. base j ≤ _’ (qspec_then ‘j’ assume_tac) >>
        Cases_on ‘MEM j (nub CS)’ >> asm_rewrite_tac[]
        >- (irule COUNT_LIST_ext >> first_assum ACCEPT_TAC) >>
        ‘rss1 j = []’ by (qpat_assum ‘∀j. ¬MEM j (nub CS) ⇒ _’ irule >> first_assum ACCEPT_TAC) >>
        ‘base j = 0’
          by (qpat_x_assum ‘base j ≤ _’ mp_tac >>
              qpat_assum ‘rss1 j = []’ (fn th => REWRITE_TAC [th]) >> simp[]) >>
        qpat_x_assum ‘base j = 0’ (fn th => REWRITE_TAC [th]) >>
        qpat_x_assum ‘rss1 j = []’ (fn th => REWRITE_TAC [th]) >>
        simp[COUNT_LIST_def]) >>
  (* the replies to the renamed order are the server's *)
  ‘∀j c. e j = SOME c ⇒ replies rss1 L j = replies rss2 order2 c’
    by (rpt strip_tac >> ‘g c = j’ by metis_tac[] >>
        pop_assum (SUBST1_TAC o SYM) >> simp[Abbr ‘L’] >>
        irule replies_rename_el >> rpt gen_tac >> strip_tac >>
        ‘i < LENGTH (rss2 d) ∧ e (g d) = SOME d’ by metis_tac[] >>
        conj_tac >- (irule prefix_EL >> metis_tac[]) >>
        eq_tac >> strip_tac >> gvs[] >> metis_tac[SOME_11]) >>
  ‘∀j. LENGTH (replies rss1 L j) = base j’
    by (gen_tac >> simp[LENGTH_replies] >>
        qpat_assum ‘∀j. MAP SND (FILTER _ L) = _’
          (qspec_then ‘j’ (mp_tac o AP_TERM “LENGTH : num list -> num”)) >>
        simp[LENGTH_COUNT_LIST]) >>
  ‘∀j. LENGTH (replies rss1 (L ++ X) j) = LENGTH (rss1 j)’
    by (gen_tac >> simp[LENGTH_replies] >>
        qpat_assum ‘is_ord rss1 (L ++ X)’
          (mp_tac o AP_TERM “LENGTH : num list -> num” o Q.SPEC ‘j’ o REWRITE_RULE [is_ord_def]) >>
        simp[LENGTH_COUNT_LIST]) >>
  (* what each raw episode sent is a prefix of the renamed order's replies *)
  ‘∀j. WR1 j evs ≼ reply_bytes (replies rss1 L j)’
    by (gen_tac >> Cases_on ‘e j’
        >- (‘WR1 j evs = []’ by metis_tac[] >> simp[]) >>
        rename1 ‘e j = SOME c’ >>
        ‘replies rss1 L j = replies rss2 order2 c’ by metis_tac[] >>
        pop_assum SUBST1_TAC >>
        irule IS_PREFIX_TRANS >> qexists_tac ‘WR2 c (vtr t)’ >> simp[] >>
        qpat_assum ‘∀evs j c. LPREFIX _ io1 ∧ e j = SOME c ⇒ _’
          (qspecl_then [‘evs’, ‘j’, ‘c’] mp_tac) >>
        simp[Abbr ‘t’]) >>
  qexists_tac ‘L ++ X’ >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (
    (* real time *)
    qx_gen_tac ‘ji’ >> qx_gen_tac ‘kl’ >> Cases_on ‘ji’ >> Cases_on ‘kl’ >>
    rename1 ‘precedesG _ _ _ _ _ (j, i) (k, l)’ >>
    simp_tac std_ss [MEM_APPEND, FST] >> strip_tac
    >- (
      (* both renamed *)
      ‘∀a b. MEM (a, b) L ⇔ ∃d. a = g d ∧ MEM (d, b) order2’
        by (simp[Abbr ‘L’, MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
      qpat_x_assum ‘MEM (j, i) L’ (fn th =>
        qpat_assum ‘∀a b. MEM _ L ⇔ _’ (fn eq => strip_assume_tac (REWRITE_RULE [eq] th))) >>
      qpat_x_assum ‘MEM (k, l) L’ (fn th =>
        qpat_x_assum ‘∀a b. MEM _ L ⇔ _’ (fn eq => strip_assume_tac (REWRITE_RULE [eq] th))) >>
      rpt BasicProvers.VAR_EQ_TAC >> rename1 ‘MEM (d, i) order2’ >> rename1 ‘MEM (d', l) order2’ >>
      qpat_assum ‘∀d i. MEM (d, i) order2 ⇒ _’ (fn th =>
        qpat_assum ‘MEM (d, i) order2’ (strip_assume_tac o MATCH_MP th) >>
        qpat_assum ‘MEM (d', l) order2’ (strip_assume_tac o MATCH_MP th)) >>
      ‘d ≠ d'’
        by (strip_tac >> qpat_x_assum ‘g _ ≠ g _’ mp_tac >>
            qpat_x_assum ‘d = d'’ SUBST1_TAC >> simp[]) >>
      irule earlier_APPEND >>
      ‘earlier (MAP (λ(d, i). (g d, i)) order2) (g d, i) (g d', l)’ suffices_by simp[Abbr ‘L’] >>
      irule earlier_rename >>
      qpat_assum ‘∀x y. MEM x order2 ∧ _ ⇒ _’ irule >>
      rpt conj_tac >>
      FIRST [first_assum ACCEPT_TAC, simp[] >> first_assum ACCEPT_TAC, ALL_TAC] >>
      qpat_x_assum ‘Abbrev (t = _)’ (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
      qspecl_then [‘RD1’, ‘WR1’, ‘rss1’, ‘e’, ‘g’, ‘io1’, ‘L’, ‘X’]
        mp_tac view_both_renamed >>
      impl_tac >- (
      rpt conj_tac >>
      FIRST [
        first_assum ACCEPT_TAC,
        qpat_assum ‘l < LENGTH _’ mp_tac >> simp[] >> NO_TAC,
        qpat_assum ‘∀j c. e j = SOME c ⇒ rss2 c ≼ rss1 j’ irule >> first_assum ACCEPT_TAC,
        qpat_assum ‘∀j c. e j = SOME c ⇒ replies _ _ j = _’ irule >> first_assum ACCEPT_TAC,
        qpat_assum ‘∀j. LENGTH (replies rss1 L j) = base j’ (fn th => REWRITE_TAC [th]) >>
          qpat_x_assum ‘Abbrev (base = _)’ (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
          qpat_assum ‘i < LENGTH _’ mp_tac >>
          qpat_assum ‘e (g d) = SOME d’ (fn th => simp[th]) >> NO_TAC]) >>
      disch_then ACCEPT_TAC)
    >- (irule earlier_cross >> conj_tac >> first_assum ACCEPT_TAC)
    >> (
      (* an extra request was not answered *)
      qpat_x_assum ‘precedesG RD1 WR1 _ _ _ _ _’
        (strip_assume_tac o REWRITE_RULE [precedesG_def]) >>
      ‘MEM i (MAP SND (FILTER (λx. FST x = j) X))’
        by qpat_assum ‘MEM (j, i) X’ (fn th => simp[MEM_MAP, MEM_FILTER, EXISTS_PROD, th]) >>
      ‘base j ≤ i ∧ i < LENGTH (rss1 j)’
        by (qpat_x_assum ‘MEM i (MAP SND _)’ mp_tac >>
            qpat_assum ‘∀j. MAP SND (FILTER _ X) = _’ (fn th => REWRITE_TAC [th]) >>
            IF_CASES_TAC >> simp[MEM_GENLIST, PULL_EXISTS]) >>
      ‘F’ suffices_by REWRITE_TAC [] >>
      qpat_x_assum ‘reply_bytes _ ≼ WR1 _ evs1’ mp_tac >> REWRITE_TAC [] >>
      match_mp_tac (Q.INST [‘P’ |-> ‘replies (rss1 : 'c -> brequest list) L (j : 'c)’] unanswered_extra) >>
      rpt conj_tac >>
      FIRST [
        MATCH_ACCEPT_TAC replies_APPEND,
        qpat_assum ‘∀j. LENGTH (replies rss1 L j) = base j’ (fn th => REWRITE_TAC [th]) >>
          first_assum ACCEPT_TAC,
        qpat_assum ‘∀j. LENGTH (replies rss1 (L ++ X) j) = _’ (fn th => REWRITE_TAC [th]) >>
          first_assum ACCEPT_TAC,
        (* IS_PREFIX_TRANS: the longer step comes first *)
        irule IS_PREFIX_TRANS >> qexists_tac ‘WR1 j evs’ >> conj_tac
        >- qpat_assum ‘∀j. WR1 j evs ≼ _’ MATCH_ACCEPT_TAC >>
        qpat_assum ‘∀j evs evs'. evs' ≼ evs ⇒ WR1 j evs' ≼ WR1 j evs’ irule >>
        first_assum ACCEPT_TAC]))
  >> gen_tac >> irule IS_PREFIX_TRANS >>
  qexists_tac ‘reply_bytes (replies rss1 L c)’ >>
  conj_tac >- simp[reply_bytes_prefix, replies_APPEND] >>
  qpat_assum ‘∀j. WR1 j evs ≼ _’ MATCH_ACCEPT_TAC
QED
