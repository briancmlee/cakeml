(*
  HttpKvSpec2's safety (per-episode linearizability) for the key-value
  server on the version-2 handle layer (kv2_safe).

  The proof is asyncKvSafe's kv_comp_safe (the order construction) with
  episodes for connections: the store's answered queries in its order,
  then the complete requests not queried yet, episode by episode; commit
  points at round starts.  The bridge to the model, at every round
  boundary, is asyncKv2Bridge (episode j is handle hdln lfdn j of the
  model run in the renamed world); a query's handle is turned back into
  its episode by unh.

  To be unified with kv_comp_safe over a generic key view (both are the
  same argument with different projections).
*)
Theory asyncKv2Safe
Ancestors
  words asyncCore asyncLevel1 asyncLevel2 asyncTranscript asyncServer
  asyncServerSafety asyncM4ServerUses ffiSpikeSocketFFI asyncM3World
  asyncM4GRounds asyncM4SockInv asyncM4SockModel asyncM4GTrans asyncRunOkGen
  EchoSpec EchoSpec2 HttpSpec HttpSpecBodies HttpKvSpec HttpKvSpec2
  asyncHttpParse asyncHttpParseH asyncHttpParseB asyncWithStore
  asyncServerWithK asyncKvHandler asyncKvModel asyncKvOrder asyncKvLabel
  asyncKvTraceLemmas socketV2FFI socketV2Fair asyncHLModel asyncHLSimWorld
  asyncHLSimTick asyncHLEpisodes asyncHLEchoSpec2 asyncProtoEof
  asyncHLEofGen asyncHLSimRunGen asyncHLSimTraceGen asyncProto2Model
  asyncKvEof asyncKv2Bridge llist ffi
Libs
  preamble

(* ------------------------------------------------------------------------
   Lists (as in asyncKvSafe, where these are local)
   ------------------------------------------------------------------------ *)

Theorem prefix_TAKE_eq[local]:
  a ≼ b ∧ k ≤ LENGTH a ⇒ TAKE k b = TAKE k a
Proof
  rw[IS_PREFIX_APPEND] >> simp[TAKE_APPEND1]
QED

Theorem prefix_TAKE_self[local]:
  a ≼ b ⇒ TAKE (LENGTH a) b = a
Proof
  rw[IS_PREFIX_APPEND] >> simp[TAKE_LENGTH_APPEND]
QED

Theorem prefix_FLAT[local]:
  ∀l1 l2. l1 ≼ l2 ⇒ FLAT l1 ≼ FLAT l2
Proof
  Induct >> simp[] >> Cases_on ‘l2’ >> simp[]
QED

Theorem prefix_MAP[local]:
  ∀l1 l2. l1 ≼ l2 ⇒ MAP f l1 ≼ MAP f l2
Proof
  Induct >> simp[] >> Cases_on ‘l2’ >> simp[]
QED

Theorem prefix_FILTER[local]:
  ∀l1 l2. l1 ≼ l2 ⇒ FILTER P l1 ≼ FILTER P l2
Proof
  Induct >> simp[] >> Cases_on ‘l2’ >> simp[] >> rw[]
QED

Theorem prefix_LENGTH_eq_TAKE[local]:
  a ≼ b ⇒ a = TAKE (LENGTH a) b
Proof
  rw[IS_PREFIX_APPEND] >> simp[TAKE_LENGTH_APPEND]
QED

Theorem brequests_TAKE_prefix[local]:
  brequests (TAKE k rs) ≼ brequests rs
Proof
  simp[brequests_def, bytes_prefix_iff] >> irule prefix_FLAT >>
  irule prefix_MAP >> simp[IS_PREFIX_APPEND] >> metis_tac[TAKE_DROP]
QED

Theorem prefix_shorter_TAKE[local]:
  a ≼ b ∧ LENGTH a ≤ j ⇒ a ≼ TAKE j b
Proof
  rw[IS_PREFIX_APPEND] >> simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG]
QED

Theorem cnt_TAKE_lt[local]:
  j < LENGTH L ⇒
  LENGTH (FILTER (λx. FST x = FST (EL j L)) (TAKE j L)) <
  LENGTH (FILTER (λx. FST x = FST (EL j L)) L)
Proof
  strip_tac >> irule FILTER_TAKE_lt >> simp[]
QED

Theorem FILTER_pend[local]:
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

Theorem LENGTH_FILTER_ZIP[local]:
  ∀L X. LENGTH X = LENGTH L ⇒
        LENGTH (FILTER (λp. FST (FST p) = c) (ZIP (L, X))) =
        LENGTH (FILTER (λx. FST x = c) L)
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on ‘X’ >> simp[] >> rw[]
QED

Theorem read_on_fd[local]:
  ∀tr. FLAT (read fd tr) ≠ [] ⇒ EXISTS (on_fd fd) tr
Proof
  Induct >> simp[read_def] >> PairCases >> simp[] >>
  every_case_tac >> rw[] >> gvs[GSYM read_def, on_fd_def]
QED

Theorem parse_all_b_NIL[local]:
  parse_all_b "" = []
Proof
  simp[Once parse_all_b_def] >> EVAL_TAC
QED

(* ------------------------------------------------------------------------
   Episodes and handles
   ------------------------------------------------------------------------ *)

(* A handle's episode *)
Definition unh_def:
  unh (lfdn:num) (fd:num) = if fd < lfdn then fd else fd − 1
End

Theorem unh_hdln[local]:
  unh lfdn (hdln lfdn j) = j
Proof
  rw[unh_def, hdln_def]
QED

Theorem hdln_11[local]:
  hdln lfdn j = hdln lfdn j' ⇔ j = j'
Proof
  rw[hdln_def] >> simp[]
QED

Theorem FILTER_conn_eps[local]:
  ∀G. (∀q. MEM q G ⇒ ∃j'. FST q = hdln lfdn j') ⇒
      FILTER (λx. FST x = j) (MAP (λq. (unh lfdn (FST q), SND q)) G) =
      MAP (λq. (j, SND q)) (FILTER (λq. FST q = hdln lfdn j) G)
Proof
  Induct >> simp[] >> PairCases >> rpt strip_tac >>
  first_assum (qspec_then ‘(h0,h1)’ mp_tac) >> simp_tac std_ss [] >> strip_tac >>
  ‘∀q. MEM q G ⇒ ∃j'. FST q = hdln lfdn j'’ by (rw[] >> metis_tac[]) >>
  fs[] >> gvs[unh_hdln, hdln_11] >> rw[] >> gvs[hdln_11]
QED

Theorem ZIP_conn_eps[local]:
  ∀G A. (∀q. MEM q G ⇒ ∃j'. FST q = hdln lfdn j') ∧ LENGTH A = LENGTH G ⇒
        FILTER (λp. FST (FST p) = j)
               (ZIP (MAP (λq. (unh lfdn (FST q), SND q)) G, A)) =
        MAP (λp. ((j, SND (FST p)), SND p))
            (FILTER (λp. FST (FST p) = hdln lfdn j) (ZIP (G, A)))
Proof
  Induct >> simp[] >> PairCases >> rpt gen_tac >> Cases_on ‘A’ >> simp[] >>
  strip_tac >>
  first_assum (qspec_then ‘(h0,h1)’ mp_tac) >> simp_tac std_ss [] >> strip_tac >>
  ‘∀q. MEM q G ⇒ ∃j'. FST q = hdln lfdn j'’ by (rw[] >> metis_tac[]) >>
  first_x_assum (qspec_then ‘t’ mp_tac) >> simp[] >> strip_tac >>
  gvs[unh_hdln, hdln_11] >> rw[] >> gvs[hdln_11]
QED

(* ------------------------------------------------------------------------
   Orders over episodes (asyncKvLabel's, for is_order2)
   ------------------------------------------------------------------------ *)

Theorem is_order2_label[local]:
  (∀j. MAP SND (FILTER (λx. FST x = j) l) = rss j) ⇒ is_order2 rss (label l)
Proof
  rw[is_order2_def, label_FILTER] >>
  first_x_assum (qspec_then ‘j’ (SUBST1_TAC o SYM)) >> simp[]
QED

Definition answered2_def:
  answered2 rss order (c, i) evs1 ⇔
    reply_bytes (TAKE (SUC i) (replies rss order c)) ≼ ep_written c evs1
End

Definition started2_def:
  started2 rss (d, j) evs1 ⇔ ¬(ep_read d evs1 ≼ brequests (TAKE j (rss d)))
End

Theorem precedes2_answered_started[local]:
  precedes2 rss order evs x y ⇔
    ∃evs1. evs1 ≼ evs ∧ answered2 rss order x evs1 ∧ ¬started2 rss y evs1
Proof
  PairCases_on ‘x’ >> PairCases_on ‘y’ >>
  simp[precedes2_def, answered2_def, started2_def]
QED

Definition commits_at2_def:
  commits_at2 rss order evs pj ⇔
    (∀j k. j ≤ k ∧ k < LENGTH order ⇒ pj j ≤ pj k) ∧
    ∀j. j < LENGTH order ⇒
        started2 rss (EL j order) (TAKE (pj j) evs) ∧
        ¬answered2 rss order (EL j order) (TAKE (pj j) evs)
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

Theorem answered2_mono[local]:
  answered2 rss order x e1 ∧ e1 ≼ e2 ⇒ answered2 rss order x e2
Proof
  PairCases_on ‘x’ >> rw[answered2_def] >>
  metis_tac[ep_written_mono, IS_PREFIX_TRANS]
QED

Theorem started2_mono[local]:
  started2 rss x e1 ∧ e1 ≼ e2 ⇒ started2 rss x e2
Proof
  PairCases_on ‘x’ >> rw[started2_def] >>
  metis_tac[ep_read_mono, IS_PREFIX_TRANS]
QED

(* Commit points by position give real time (asyncKvLabel's
   commits_at_real_time, per episode) *)
Theorem commits_at2_real_time[local]:
  commits_at2 rss order evs pj ⇒
  ∀x y. MEM x order ∧ MEM y order ∧ FST x ≠ FST y ∧
        precedes2 rss order evs x y ⇒ earlier order x y
Proof
  rw[] >> gvs[MEM_EL] >> rename1 ‘precedes2 _ _ _ (EL i order) (EL j order)’ >>
  ‘i < j’ suffices_by metis_tac[earlier_EL] >>
  CCONTR_TAC >>
  ‘j ≤ i’ by simp[] >>
  ‘pj j ≤ pj i’ by fs[commits_at2_def] >>
  ‘¬answered2 rss order (EL i order) (TAKE (pj i) evs) ∧
   started2 rss (EL j order) (TAKE (pj j) evs)’ by fs[commits_at2_def] >>
  qpat_x_assum ‘precedes2 _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE [precedes2_answered_started]) >>
  ‘evs1 = TAKE (LENGTH evs1) evs’
    by (qpat_x_assum ‘evs1 ≼ evs’ mp_tac >> rw[IS_PREFIX_APPEND] >>
        simp[TAKE_LENGTH_APPEND]) >>
  qabbrev_tac ‘k = LENGTH evs1’ >>
  ‘pj i < k’
    by (CCONTR_TAC >>
        ‘TAKE k evs ≼ TAKE (pj i) evs’ by (irule TAKE_prefix_mono >> simp[]) >>
        metis_tac[answered2_mono]) >>
  ‘k < pj j’
    by (CCONTR_TAC >>
        ‘TAKE (pj j) evs ≼ TAKE k evs’ by (irule TAKE_prefix_mono >> simp[]) >>
        metis_tac[started2_mono]) >>
  decide_tac
QED

(* ------------------------------------------------------------------------
   The model, round by round
   ------------------------------------------------------------------------ *)

Overload KHH1 = “λlfdn s2 k. MAP sfs (ghist (interest [n2w lfdn : word64])
                                (srelabel (kv_server lfdn)) (v1of (n2w lfdn) s2) k)”
Overload KG1 = “λlfdn s2 k. kv_queries lfdn (KHH1 lfdn s2 k)”

Theorem kv2_rounds_serves[local]:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ⇒
  MAP SND (FILTER (λq. FST q = fd) (KG1 lfdn s2 k)) ≼
    parse_all_b (FLAT (read fd (KT1 lfdn s2 k))) ∧
  written fd (KT1 lfdn s2 k) ≼ MAP print_response (fd_answers fd (KG1 lfdn s2 k))
Proof
  strip_tac >> irule kv_server_serves >>
  ‘(v1of (n2w lfdn) s2).listeners = [(n2w lfdn, [])] ∧ (v1of (n2w lfdn) s2).conns = []’
    by simp[v1of_def] >>
  metis_tac[gen_fresh, kv_server_uses_ok]
QED

Theorem kv2_rounds_mono[local]:
  k1 ≤ k2 ⇒ KG1 lfdn s2 k1 ≼ KG1 lfdn s2 k2 ∧ KP2 lfdn s2 k1 ≼ KP2 lfdn s2 k2
Proof
  strip_tac >> conj_tac
  >- (‘KHH1 lfdn s2 k1 = TAKE k1 (KHH1 lfdn s2 k2)’
        by simp[GSYM MAP_TAKE, ghist_TAKE] >>
      pop_assum SUBST1_TAC >> simp[kv_queries_TAKE]) >>
  rw[IS_PREFIX_APPEND] >>
  qexists_tac ‘FLAT (GENLIST (λi. hround_events (n2w lfdn) (interest [n2w lfdn])
                                    (srelabel (kv_server lfdn)) s2 (i + k1)) (k2 − k1))’ >>
  ‘k2 = (k2 − k1) + k1’ by simp[] >>
  pop_assum (fn th => CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [th]))) >>
  REWRITE_TAC[GENLIST_APPEND, FLAT_APPEND] >> simp[]
QED

Theorem kv2_rounds_handle[local]:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ∧ lfdn < dimword (:64) ∧ MEM q (KG1 lfdn s2 k) ⇒
  ∃j. j < dimword (:64) − 1 ∧ FST q = hdln lfdn j
Proof
  strip_tac >>
  ‘MAP SND (FILTER (λq'. FST q' = FST q) (KG1 lfdn s2 k)) ≼
   parse_all_b (FLAT (read (FST q) (KT1 lfdn s2 k)))’
    by metis_tac[kv2_rounds_serves] >>
  ‘FLAT (read (FST q) (KT1 lfdn s2 k)) ≠ []’
    by (strip_tac >> fs[parse_all_b_NIL] >>
        fs[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
  drule read_on_fd >> strip_tac >>
  irule kv2_query_handle >> simp[] >> metis_tac[]
QED

Theorem kv2_rounds_bytes_all[local]:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ∧ lfdn < dimword (:64) ⇒
  ∀k j. j < dimword (:64) − 1 ⇒
        ep_written j (KP2 lfdn s2 (SUC k)) =
          HttpSpec$bytes (FLAT (written (hdln lfdn j) (KT1 lfdn s2 k))) ∧
        ep_read j (KP2 lfdn s2 k) =
          HttpSpec$bytes (FLAT (read (hdln lfdn j) (KT1 lfdn s2 k)))
Proof
  metis_tac[kv2_rounds_bytes]
QED

(* ------------------------------------------------------------------------
   The theorem
   ------------------------------------------------------------------------ *)

(* MAIN: per-episode linearizability for the key-value server on the
   handle layer, in every fair version-2 world with one listener *)
Theorem kv2_safe:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ∧ lfdn < dimword (:64) ⇒
  kv_safe2 (gtrace2 (kv_server lfdn) lfdn s2)
Proof
  rw[kv_safe2_def] >>
  ‘uses_ok lfdn (kv_server lfdn) ∧ srv_eof_last (kv_server lfdn)’
    by simp[kv_server_uses_ok, kv_server_eof_last] >>
  ‘∀i. hround_events (n2w lfdn) (interest [n2w lfdn]) (srelabel (kv_server lfdn)) s2 i ≠ []’
    by (gen_tac >> simp[hround_events_alt] >> rpt (pairarg_tac >> gvs[])) >>
  drule_all LPREFIX_rounds_between >> strip_tac >>
  (* the bridge, at every round *)
  ‘lfdn < dimword (:64)’ by fs[] >>
  mp_tac kv2_rounds_bytes_all >> impl_tac >- fs[] >> strip_tac >>
  ‘∀k fd. MAP SND (FILTER (λq. FST q = fd) (KG1 lfdn s2 k)) ≼
            parse_all_b (FLAT (read fd (KT1 lfdn s2 k))) ∧
          written fd (KT1 lfdn s2 k) ≼
            MAP print_response (fd_answers fd (KG1 lfdn s2 k))’
    by metis_tac[kv2_rounds_serves] >>
  ‘∀k1 k2. k1 ≤ k2 ⇒ KG1 lfdn s2 k1 ≼ KG1 lfdn s2 k2 ∧ KP2 lfdn s2 k1 ≼ KP2 lfdn s2 k2’
    by metis_tac[kv2_rounds_mono] >>
  ‘∀k q. MEM q (KG1 lfdn s2 k) ⇒ ∃j. j < (dimword (:64) − 1) ∧ FST q = hdln lfdn j’
    by (rpt strip_tac >> irule kv2_rounds_handle >> simp[] >>
        metis_tac[]) >>
  (* episodes that did anything are below (dimword (:64) − 1) *)
  ‘LENGTH (accepted_fds evs) < (dimword (:64) − 1)’
    by (‘LENGTH (accepted_fds evs) ≤ LENGTH (accepted_fds (KP2 lfdn s2 (SUC n)))’
          by (qpat_x_assum ‘evs ≼ KP2 _ _ _’ mp_tac >> rw[IS_PREFIX_APPEND] >>
              simp[accepted_fds_APPEND]) >>
        qspecl_then [‘lfdn’, ‘kv_server lfdn’, ‘s2’] mp_tac
          (Q.GENL [‘lfdn’, ‘m’, ‘s2’] accepted_bound_gen) >>
        impl_tac >- fs[] >> disch_then (qspec_then ‘SUC n’ mp_tac) >> simp[]) >>
  ‘∀j. (dimword (:64) − 1) ≤ j ⇒ ep_read j evs = [] ∧ ep_written j evs = []’
    by (rpt gen_tac >> strip_tac >> ‘¬(j < LENGTH (accepted_fds evs))’ by fs[] >>
        ONCE_REWRITE_TAC[ep_read_def, ep_written_def] >> pop_assum (fn th => REWRITE_TAC[th])) >>
  (* what has been read in each episode *)
  ‘∀j. parse_all_b (MAP (CHR o w2n) (ep_read j evs)) = rss j’
    by (gen_tac >> irule read_brequests_parse >> simp[bytes_chars] >> metis_tac[]) >>
  ‘∀j. (dimword (:64) − 1) ≤ j ⇒ rss j = []’
    by (rpt strip_tac >> qpat_x_assum ‘∀j. parse_all_b _ = rss j’ (qspec_then ‘j’ mp_tac) >>
        simp[parse_all_b_NIL]) >>
  ‘∀k j. k ≤ n ∧ j < (dimword (:64) − 1) ⇒ parse_all_b (FLAT (read (hdln lfdn j) (KT1 lfdn s2 k))) ≼ rss j’
    by (rpt strip_tac >>
        qpat_x_assum ‘∀j. parse_all_b _ = rss j’ (qspec_then ‘j’ (SUBST1_TAC o SYM)) >>
        irule parse_all_b_prefix >> ONCE_REWRITE_TAC[GSYM bytes_prefix_iff] >>
        simp[bytes_chars] >>
        qpat_assum ‘∀k j. j < (dimword (:64) − 1) ⇒ ep_written _ _ = _ ∧ _’
          (qspecl_then [‘k’, ‘j’] mp_tac) >>
        impl_tac >- fs[] >> disch_then (SUBST1_TAC o SYM o CONJUNCT2) >>
        ‘ep_read j (KP2 lfdn s2 k) ≼ ep_read j evs’
          by (irule ep_read_mono >> metis_tac[IS_PREFIX_TRANS]) >>
        metis_tac[]) >>
  qabbrev_tac ‘Gn = KG1 lfdn s2 n’ >>
  qabbrev_tac ‘Gc = λj. MAP SND (FILTER (λq. FST q = hdln lfdn j) Gn)’ >>
  ‘∀q. MEM q Gn ⇒ ∃j. j < (dimword (:64) − 1) ∧ FST q = hdln lfdn j’ by metis_tac[] >>
  ‘∀j. Gc j ≼ rss j’
    by (gen_tac >> Cases_on ‘j < (dimword (:64) − 1)’
        >- (simp[Abbr ‘Gc’, Abbr ‘Gn’] >> irule IS_PREFIX_TRANS >>
            qexists_tac ‘parse_all_b (FLAT (read (hdln lfdn j) (KT1 lfdn s2 n)))’ >>
            simp[]) >>
        ‘Gc j = []’
          by (simp[Abbr ‘Gc’, FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >>
              first_x_assum drule >> strip_tac >> gvs[hdln_11]) >>
        simp[]) >>
  (* the order *)
  qabbrev_tac ‘CS = COUNT_LIST (dimword (:64) − 1)’ >>
  qabbrev_tac ‘L1 = MAP (λq. (unh lfdn (FST q), SND q)) Gn’ >>
  qabbrev_tac ‘pend = FLAT (MAP (λc. MAP (λr. (c, r)) (DROP (LENGTH (Gc c)) (rss c))) CS)’ >>
  qabbrev_tac ‘L = L1 ++ pend’ >>
  ‘∀j. MAP SND (FILTER (λx. FST x = j) L1) = Gc j’
    by (gen_tac >> simp[Abbr ‘L1’, Abbr ‘Gc’] >>
        DEP_REWRITE_TAC[FILTER_conn_eps] >> simp[MAP_MAP_o, combinTheory.o_DEF] >>
        metis_tac[]) >>
  ‘∀j. MAP SND (FILTER (λx. FST x = j) L) = rss j’
    by (gen_tac >> simp[Abbr ‘L’, FILTER_APPEND, Abbr ‘pend’, FILTER_pend, Abbr ‘CS’,
                        all_distinct_count_list, MEM_COUNT_LIST] >> rw[]
        >- (qpat_x_assum ‘∀j. Gc j ≼ rss j’ (qspec_then ‘j’ mp_tac) >>
            simp[MAP_MAP_o, combinTheory.o_DEF] >> strip_tac >> fs[IS_PREFIX_APPEND] >>
            simp[DROP_LENGTH_APPEND]) >>
        ‘(dimword (:64) − 1) ≤ j’ by fs[] >> ‘rss j = []’ by fs[] >>
        qpat_x_assum ‘∀j. Gc j ≼ rss j’ (qspec_then ‘j’ mp_tac) >> simp[]) >>
  (* what has been written, at evs *)
  ‘∀j. ep_written j evs ≼ reply_bytes (fd_answers (hdln lfdn j) Gn)’
    by (gen_tac >> reverse (Cases_on ‘j < (dimword (:64) − 1)’) >- (‘(dimword (:64) − 1) ≤ j’ by fs[] >> fs[]) >>
        irule IS_PREFIX_TRANS >>
        qexists_tac ‘ep_written j (KP2 lfdn s2 (SUC n))’ >>
        reverse conj_tac >- (irule ep_written_mono >> first_assum ACCEPT_TAC) >>
        qpat_assum ‘∀k j. j < (dimword (:64) − 1) ⇒ ep_written _ _ = _ ∧ _’
          (qspecl_then [‘n’, ‘j’] mp_tac) >>
        impl_tac >- fs[] >> disch_then (SUBST1_TAC o CONJUNCT1) >>
        simp[reply_bytes_def, bytes_prefix_iff, Abbr ‘Gn’] >>
        irule prefix_FLAT >> simp[]) >>
  qexists_tac ‘label L’ >>
  ‘is_order2 rss (label L)’ by (irule is_order2_label >> simp[]) >>
  simp[] >>
  (* the replies *)
  ‘∀j. ∃X. replies rss (label L) j = fd_answers (hdln lfdn j) Gn ++ X’
    by (gen_tac >> simp[replies_label] >>
        ‘MAP SND L = MAP SND (Gn ++ MAP (λx. (0:num, SND x)) pend)’
          by simp[Abbr ‘L’, Abbr ‘L1’, MAP_MAP_o, combinTheory.o_DEF, ETA_AX] >>
        qpat_x_assum ‘MAP SND L = _’ SUBST1_TAC >>
        REWRITE_TAC[kv_run_store, run_store_APPEND_FST] >>
        simp[Abbr ‘L’] >>
        DEP_REWRITE_TAC[GSYM ZIP_APPEND] >> conj_tac >- simp[Abbr ‘L1’] >>
        simp[FILTER_APPEND, Abbr ‘L1’] >>
        DEP_REWRITE_TAC[ZIP_conn_eps] >>
        conj_tac >- (simp[] >> metis_tac[]) >>
        simp[fd_answers_def, MAP_MAP_o, combinTheory.o_DEF, ETA_AX]) >>
  ‘∀j. LENGTH (replies rss (label L) j) = LENGTH (rss j)’
    by (gen_tac >> simp[replies_label] >>
        DEP_REWRITE_TAC[LENGTH_FILTER_ZIP] >> simp[] >>
        qpat_x_assum ‘∀j. MAP SND (FILTER _ L) = _’
          (qspec_then ‘j’ (SUBST1_TAC o SYM)) >> simp[]) >>
  ‘∀j. LENGTH (fd_answers (hdln lfdn j) Gn) = LENGTH (Gc j)’
    by simp[LENGTH_fd_answers, Abbr ‘Gc’] >>
  ‘∀j. reply_bytes (fd_answers (hdln lfdn j) Gn) =
       reply_bytes (TAKE (LENGTH (Gc j)) (replies rss (label L) j))’
    by (gen_tac >> qpat_x_assum ‘∀j. ∃X. _’ (qspec_then ‘j’ strip_assume_tac) >>
        qpat_x_assum ‘∀j. LENGTH (fd_answers _ _) = _’
          (qspec_then ‘j’ (SUBST1_TAC o SYM)) >>
        simp[TAKE_LENGTH_APPEND]) >>
  conj_tac
  >- ((* real time *)
      qsuff_tac ‘∃pj. commits_at2 rss (label L) evs pj’
      >- metis_tac[commits_at2_real_time] >>
      qexists_tac ‘λj. if j < LENGTH Gn
                       then LENGTH (KP2 lfdn s2 ($LEAST (λk. j < LENGTH (KG1 lfdn s2 k))))
                       else LENGTH evs’ >>
      ‘∀j. j < LENGTH Gn ⇒
           j < LENGTH (KG1 lfdn s2 ($LEAST (λk. j < LENGTH (KG1 lfdn s2 k)))) ∧
           $LEAST (λk. j < LENGTH (KG1 lfdn s2 k)) ≤ n ∧
           ∀m. m < $LEAST (λk. j < LENGTH (KG1 lfdn s2 k)) ⇒ LENGTH (KG1 lfdn s2 m) ≤ j’
        by (rpt gen_tac >> strip_tac >>
            qspecl_then [‘λk. j < LENGTH (KG1 lfdn s2 k)’, ‘n’] mp_tac
              (Q.GEN ‘P’ WhileTheory.FULL_LEAST_INTRO) >>
            simp[Abbr ‘Gn’] >> rw[] >>
            drule (Q.ISPEC ‘λk. j < LENGTH (KG1 lfdn s2 k)’ WhileTheory.LESS_LEAST) >> simp[]) >>
      ‘∀a b. a ≤ b ⇒ LENGTH (KP2 lfdn s2 a) ≤ LENGTH (KP2 lfdn s2 b)’
        by metis_tac[IS_PREFIX_LENGTH] >>
      ‘LENGTH (KP2 lfdn s2 n) ≤ LENGTH evs’ by metis_tac[IS_PREFIX_LENGTH] >>
      ‘LENGTH L1 = LENGTH Gn’ by simp[Abbr ‘L1’] >>
      simp[commits_at2_def] >> conj_tac
      >- (rw[] >> gvs[]
          >- (qpat_x_assum ‘∀a b. a ≤ b ⇒ LENGTH _ ≤ LENGTH _’ irule >>
              qspecl_then [‘λk. j < LENGTH (KG1 lfdn s2 k)’,
                           ‘$LEAST (λk. j' < LENGTH (KG1 lfdn s2 k))’] mp_tac
                (Q.GEN ‘P’ WhileTheory.FULL_LEAST_INTRO) >>
              simp[] >> impl_tac
              >- (qpat_x_assum ‘∀j. j < LENGTH Gn ⇒ _’ (qspec_then ‘j'’ mp_tac) >> simp[]) >>
              simp[])
          >> irule LESS_EQ_TRANS >> qexists_tac ‘LENGTH (KP2 lfdn s2 n)’ >> simp[] >>
          qpat_x_assum ‘∀a b. a ≤ b ⇒ LENGTH _ ≤ LENGTH _’ irule >>
          qpat_x_assum ‘∀j. j < LENGTH Gn ⇒ _’ (qspec_then ‘j’ mp_tac) >> simp[]) >>
      rpt gen_tac >> strip_tac >>
      qabbrev_tac ‘c = FST (EL j L)’ >>
      qabbrev_tac ‘i = LENGTH (FILTER (λx. FST x = c) (TAKE j L))’ >>
      ‘EL j (label L) = (c, i)’ by simp[label_def, EL_GENLIST, Abbr ‘c’, Abbr ‘i’] >>
      pop_assum SUBST1_TAC >>
      ‘i < LENGTH (rss c)’
        by (simp[Abbr ‘i’, Abbr ‘c’] >>
            qpat_x_assum ‘∀j. MAP SND (FILTER _ L) = _’
              (qspec_then ‘FST (EL j L)’ (SUBST1_TAC o SYM)) >>
            simp[] >> irule cnt_TAKE_lt >> fs[]) >>
      simp[started2_def, answered2_def] >>
      Cases_on ‘j < LENGTH Gn’ >> simp[]
      >- ((* a query, committed at the start of its first round cr *)
          qabbrev_tac ‘cr = $LEAST (λk. j < LENGTH (KG1 lfdn s2 k))’ >>
          qpat_x_assum ‘∀j. j < LENGTH Gn ⇒ _’ (qspec_then ‘j’ mp_tac) >> simp[] >> strip_tac >>
          ‘TAKE (LENGTH (KP2 lfdn s2 cr)) evs = KP2 lfdn s2 cr’
            by (irule prefix_TAKE_self >> irule IS_PREFIX_TRANS >>
                qexists_tac ‘KP2 lfdn s2 n’ >> simp[]) >>
          simp[] >>
          qabbrev_tac ‘fd = FST (EL j Gn)’ >>
          ‘∃e. e < (dimword (:64) − 1) ∧ fd = hdln lfdn e’
            by (qpat_assum ‘∀q. MEM q Gn ⇒ _’ (qspec_then ‘EL j Gn’ mp_tac) >>
                simp[Abbr ‘fd’, EL_MEM]) >>
          ‘EL j L = (e, SND (EL j Gn))’
            by simp[Abbr ‘L’, EL_APPEND1, Abbr ‘L1’, EL_MAP, unh_hdln] >>
          ‘c = e’ by simp[Abbr ‘c’] >>
          qpat_x_assum ‘c = e’ SUBST_ALL_TAC >>
          ‘LENGTH (FILTER (λq. FST q = fd) (TAKE j Gn)) = i’
            by (simp[Abbr ‘i’, Abbr ‘L’, TAKE_APPEND1, Abbr ‘L1’, GSYM MAP_TAKE] >>
                DEP_REWRITE_TAC[FILTER_conn_eps] >> simp[] >>
                metis_tac[MEM_TAKE]) >>
          ‘KG1 lfdn s2 cr ≼ Gn’ by simp[Abbr ‘Gn’] >>
          ‘TAKE (SUC j) Gn = TAKE (SUC j) (KG1 lfdn s2 cr)’
            by (irule prefix_TAKE_eq >> simp[]) >>
          conj_tac
          >- ((* started: e's first i+1 requests were read before round cr *)
              irule brequests_TAKE_SUC >> simp[] >>
              qpat_assum ‘fd = hdln lfdn e’ (fn th => REWRITE_TAC[GSYM th]) >>
              ‘parse_all_b (FLAT (read fd (KT1 lfdn s2 cr))) ≼ rss e’ by metis_tac[] >>
              ‘LENGTH (FILTER (λq. FST q = fd) (TAKE (SUC j) (KG1 lfdn s2 cr))) = SUC i’
                by (qpat_x_assum ‘TAKE (SUC j) Gn = _’ (SUBST1_TAC o SYM) >>
                    simp[TAKE_SUC_EL, FILTER_APPEND] >>
                    qpat_x_assum ‘LENGTH (FILTER _ (TAKE j Gn)) = i’ (SUBST1_TAC o SYM) >>
                    simp[Abbr ‘fd’]) >>
              ‘LENGTH (FILTER (λq. FST q = fd) (TAKE (SUC j) (KG1 lfdn s2 cr))) ≤
               LENGTH (FILTER (λq. FST q = fd) (KG1 lfdn s2 cr))’
                by (irule IS_PREFIX_LENGTH >> irule prefix_FILTER >>
                    simp[IS_PREFIX_APPEND] >> metis_tac[TAKE_DROP]) >>
              ‘SUC i ≤ LENGTH (parse_all_b (FLAT (read fd (KT1 lfdn s2 cr))))’
                by (‘LENGTH (FILTER (λq. FST q = fd) (KG1 lfdn s2 cr)) ≤
                     LENGTH (parse_all_b (FLAT (read fd (KT1 lfdn s2 cr))))’
                      by (qpat_assum ‘∀k fd. MAP SND _ ≼ _ ∧ _’
                            (qspecl_then [‘cr’, ‘fd’]
                               (mp_tac o MATCH_MP IS_PREFIX_LENGTH o CONJUNCT1)) >>
                          REWRITE_TAC[LENGTH_MAP]) >>
                    decide_tac) >>
              ‘TAKE (SUC i) (rss e) = TAKE (SUC i) (parse_all_b (FLAT (read fd (KT1 lfdn s2 cr))))’
                by (irule prefix_TAKE_eq >> simp[]) >>
              simp[brequests_def, bytes_prefix_iff] >>
              irule parse_all_b_printed >> simp[IS_PREFIX_APPEND] >>
              metis_tac[TAKE_DROP]) >>
          (* not answered: before round cr, at most e's first i answers *)
          ‘∃i'. i' ≤ i ∧ ep_written e (KP2 lfdn s2 cr) ≼
                         reply_bytes (TAKE i' (replies rss (label L) e))’
            by (Cases_on ‘cr’
                >- (qexists_tac ‘0’ >>
                    simp[ep_written_def, accepted_fds_def, bytes_written_to_def]) >>
                rename1 ‘KP2 lfdn s2 (SUC k2)’ >>
                ‘LENGTH (KG1 lfdn s2 k2) ≤ j’
                  by (qpat_x_assum ‘∀m. m < SUC k2 ⇒ _’ (qspec_then ‘k2’ mp_tac) >> simp[]) >>
                ‘KG1 lfdn s2 k2 ≼ Gn’ by simp[Abbr ‘Gn’] >>
                qexists_tac ‘LENGTH (fd_answers fd (KG1 lfdn s2 k2))’ >> conj_tac
                >- (simp[LENGTH_fd_answers] >>
                    qpat_x_assum ‘LENGTH (FILTER _ (TAKE j Gn)) = i’ (SUBST1_TAC o SYM) >>
                    qpat_assum ‘fd = hdln lfdn e’ (fn th => REWRITE_TAC[GSYM th]) >>
                    irule IS_PREFIX_LENGTH >> irule prefix_FILTER >>
                    irule prefix_shorter_TAKE >> simp[]) >>
                ‘fd_answers fd (KG1 lfdn s2 k2) =
                 TAKE (LENGTH (fd_answers fd (KG1 lfdn s2 k2))) (replies rss (label L) e)’
                  by (qpat_assum ‘fd = hdln lfdn e’ (fn th => REWRITE_TAC[th]) >>
                      irule prefix_LENGTH_eq_TAKE >> irule IS_PREFIX_TRANS >>
                      qexists_tac ‘fd_answers (hdln lfdn e) Gn’ >> conj_tac >>
                      TRY (irule fd_answers_prefix >> simp[] >> NO_TAC) >>
                      qpat_x_assum ‘∀j. ∃X. _’ (qspec_then ‘e’ strip_assume_tac) >> simp[]) >>
                pop_assum (SUBST1_TAC o SYM) >>
                qpat_assum ‘∀k j. j < (dimword (:64) − 1) ⇒ ep_written _ _ = _ ∧ _’
                  (qspecl_then [‘k2’, ‘e’] mp_tac) >>
                impl_tac >- fs[] >> disch_then (SUBST1_TAC o CONJUNCT1) >>
                simp[reply_bytes_def, bytes_prefix_iff] >> irule prefix_FLAT >>
                qpat_assum ‘fd = hdln lfdn e’ (fn th => REWRITE_TAC[th]) >>
                qpat_assum ‘∀k fd. MAP SND _ ≼ _ ∧ _’
                  (qspecl_then [‘k2’, ‘hdln lfdn e’] (ACCEPT_TAC o CONJUNCT2))) >>
          strip_tac >>
          qspecl_then [‘i’, ‘replies rss (label L) e’, ‘i'’,
                       ‘ep_written e (KP2 lfdn s2 cr)’]
            mp_tac (Q.GENL [‘i’, ‘R’, ‘j’, ‘x’] reply_bytes_TAKE) >> simp[]) >>
      (* a request not queried yet, committed at the end of evs *)
      ‘LENGTH (Gc c) ≤ i’
        by (qpat_x_assum ‘∀j. MAP SND (FILTER _ L1) = Gc j’ (qspec_then ‘c’ (SUBST1_TAC o SYM)) >>
            simp[Abbr ‘i’, Abbr ‘L’, TAKE_APPEND, TAKE_LENGTH_TOO_LONG, FILTER_APPEND]) >>
      conj_tac
      >- (irule brequests_TAKE_SUC >> simp[] >> irule IS_PREFIX_TRANS >>
          qexists_tac ‘brequests (rss c)’ >> simp[brequests_TAKE_prefix]) >>
      strip_tac >>
      qspecl_then [‘i’, ‘replies rss (label L) c’, ‘LENGTH (Gc c)’, ‘ep_written c evs’]
        mp_tac (Q.GENL [‘i’, ‘R’, ‘j’, ‘x’] reply_bytes_TAKE) >> simp[] >>
      qpat_x_assum ‘∀j. reply_bytes _ = _’ (qspec_then ‘c’ (SUBST1_TAC o SYM)) >>
      qpat_x_assum ‘∀j. ep_written j evs ≼ _’ (qspec_then ‘c’ ACCEPT_TAC)) >>
  gen_tac >> qpat_x_assum ‘∀j. ∃X. _’ (qspec_then ‘j’ strip_assume_tac) >> simp[] >>
  irule IS_PREFIX_TRANS >> qexists_tac ‘reply_bytes (fd_answers (hdln lfdn j) Gn)’ >>
  simp[reply_bytes_prefix]
QED
