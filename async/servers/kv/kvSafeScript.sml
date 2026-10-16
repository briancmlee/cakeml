(*
  KvSpec's safety (linearizability) for the loop's trace of the
  key-value server, kv_server (kvModel), in any interest function.

  At a point evs of the trace, between the starts of rounds n and n+1:
   - the order: the queries the store has answered by round n, in the
     order it answered them (kv_queries), followed by the complete
     requests not queried yet, connection by connection;
   - commit points: a query first answered in round k commits at the start
     of round k (the position LENGTH (rounds 0..k-1) in the trace); a
     request not queried yet commits at the end of evs;
   - commit points give real time (kvLabel's commits_at_real_time),
     because a query of round k reads its request in rounds < k and its
     response is written in rounds > k.

  The bridge between model rounds and trace positions is skeletonRunOk's
  gen_rounds_bytes, used at every round k ≤ n: the bytes read in rounds
  < k are those of the transcript after k rounds, the bytes written in
  rounds ≤ k those of the transcript after k rounds.
*)
Theory kvSafe
Ancestors
  words asyncCore asyncLevel1 asyncLevel2 asyncTranscript echoServer
  echoServerSafety echoServerUses relabel relabelDist
  socketWorld loopPollWorld loopRounds loopSockInv
  echoSockModel loopRoundsTrans skeletonRunOk EchoSpec HttpGetSpec
  HttpSpec KvSpec httpGetParse httpHeadersParse httpParse
  withStore skeletonK kvHandler kvModel kvOrder
  kvLabel kvTraceLemmas llist ffi
Libs
  preamble

(* ------------------------------------------------------------------------
   Lists
   ------------------------------------------------------------------------ *)

Theorem FLAT_GENLIST_prefix[local]:
  a ≤ b ⇒ FLAT (GENLIST f a) ≼ FLAT (GENLIST f b)
Proof
  Induct_on ‘b’ >> rw[] >> Cases_on ‘a = SUC b’ >> simp[] >>
  ‘a ≤ b’ by simp[] >> first_x_assum drule >>
  rw[IS_PREFIX_APPEND, GENLIST, SNOC_APPEND, FLAT_APPEND] >> metis_tac[APPEND_ASSOC]
QED

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

Theorem n2w_eq_iff[local]:
  h0 < dimword(:64) ⇒ ((n2w h0 : word64) = c ⇔ h0 = w2n c)
Proof
  rw[EQ_IMP_THM] >> simp[]
QED

(* Connections of fds below 2^64, as words *)
Theorem FILTER_conn_words[local]:
  ∀G. (∀q. MEM q G ⇒ FST q < dimword(:64)) ⇒
      FILTER (λx. FST x = c) (MAP (λq. (n2w (FST q) : word64, SND q)) G) =
      MAP (λq. (c, SND q)) (FILTER (λq. FST q = w2n c) G)
Proof
  Induct >> simp[] >> PairCases >> rpt strip_tac >>
  first_assum (qspec_then ‘(h0,h1)’ mp_tac) >> simp_tac std_ss [] >> strip_tac >>
  ‘∀q. MEM q G ⇒ FST q < dimword(:64)’ by (rw[] >> fs[]) >>
  fs[] >> simp[n2w_eq_iff] >> rw[]
QED

Theorem ZIP_conn_words[local]:
  ∀G A. (∀q. MEM q G ⇒ FST q < dimword(:64)) ∧ LENGTH A = LENGTH G ⇒
        FILTER (λp. FST (FST p) = c)
               (ZIP (MAP (λq. (n2w (FST q) : word64, SND q)) G, A)) =
        MAP (λp. ((c, SND (FST p)), SND p))
            (FILTER (λp. FST (FST p) = w2n c) (ZIP (G, A)))
Proof
  Induct >> simp[] >> PairCases >> rpt gen_tac >> Cases_on ‘A’ >> simp[] >>
  strip_tac >>
  first_assum (qspec_then ‘(h0,h1)’ mp_tac) >> simp_tac std_ss [] >> strip_tac >>
  ‘∀q. MEM q G ⇒ FST q < dimword(:64)’ by (rw[] >> fs[]) >>
  first_x_assum (qspec_then ‘t’ mp_tac) >> simp[] >> strip_tac >>
  simp[n2w_eq_iff] >> rw[]
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

(* A connection with something read appears in the trace's read events *)
Definition ev_conn_def:
  ev_conn (IO_event f conf b) = bytes_fd conf
End

Theorem conns_of_trace[local]:
  ∃CS. ALL_DISTINCT CS ∧ ∀c. bytes_read_from c evs ≠ [] ⇒ MEM c CS
Proof
  qexists_tac ‘nub (MAP ev_conn evs)’ >> simp[all_distinct_nub] >>
  rw[bytes_read_from_def] >> gs[FLAT_EQ_NIL, EVERY_MEM, MEM_MAP] >>
  rename1 ‘MEM ev evs’ >> qexists_tac ‘ev’ >> simp[] >>
  Cases_on ‘ev’ >> rename1 ‘IO_event f conf b’ >> Cases_on ‘f’ >>
  gvs[event_read_def, ev_conn_def] >> every_case_tac >> gvs[]
QED

Theorem read_on_fd[local]:
  ∀tr. FLAT (read fd tr) ≠ [] ⇒ EXISTS (on_fd fd) tr
Proof
  Induct >> simp[read_def] >> PairCases >> simp[] >>
  every_case_tac >> rw[] >> gvs[GSYM read_def, on_fd_def]
QED

(* ------------------------------------------------------------------------
   The theorem
   ------------------------------------------------------------------------ *)

(* The server's rounds, in the loop's run *)
Overload KEV = “λlfdn ifds s0. grounds_events ifds (srelabel (kv_server lfdn)) s0”
Overload KHH = “λlfdn ifds s0 k. MAP sfs (ghist ifds (srelabel (kv_server lfdn)) s0 k)”
Overload KTS = “λlfdn ifds s0 k. trans (kv_server lfdn) (KHH lfdn ifds s0 k)”
Overload KG = “λlfdn ifds s0 k. kv_queries lfdn (KHH lfdn ifds s0 k)”
Overload KP = “λlfdn ifds s0 k. FLAT (GENLIST (KEV lfdn ifds s0) k)”

(* The bridge, at every round *)
Theorem kv_rounds_bytes[local]:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  bytes_written_to c (KP lfdn ifds s0 (SUC k)) =
    HttpGetSpec$bytes (FLAT (written (w2n c) (KTS lfdn ifds s0 k))) ∧
  bytes_read_from c (KP lfdn ifds s0 k) =
    HttpGetSpec$bytes (FLAT (read (w2n c) (KTS lfdn ifds s0 k)))
Proof
  strip_tac >>
  ‘uses_ok lfdn (kv_server lfdn)’ by simp[kv_server_uses_ok] >>
  drule_all gen_rounds_bytes >>
  disch_then (qspecl_then [‘k’, ‘ifds’, ‘c’] mp_tac) >> simp[bytes_def]
QED

Theorem kv_rounds_fresh[local]:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  fresh (KTS lfdn ifds s0 k)
Proof
  strip_tac >> ‘uses_ok lfdn (kv_server lfdn)’ by simp[kv_server_uses_ok] >>
  drule_all gen_fresh >> simp[]
QED

Theorem kv_rounds_serves[local]:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  MAP SND (FILTER (λq. FST q = fd) (KG lfdn ifds s0 k)) ≼
    parse_all_b (FLAT (read fd (KTS lfdn ifds s0 k))) ∧
  written fd (KTS lfdn ifds s0 k) ≼
    MAP print_response (fd_answers fd (KG lfdn ifds s0 k))
Proof
  strip_tac >> irule kv_server_serves >> simp[kv_rounds_fresh]
QED

Theorem kv_rounds_mono[local]:
  k1 ≤ k2 ⇒
  KG lfdn ifds s0 k1 ≼ KG lfdn ifds s0 k2 ∧ KP lfdn ifds s0 k1 ≼ KP lfdn ifds s0 k2
Proof
  strip_tac >> conj_tac
  >- (‘KHH lfdn ifds s0 k1 = TAKE k1 (KHH lfdn ifds s0 k2)’
        by simp[GSYM MAP_TAKE, ghist_TAKE] >>
      pop_assum SUBST1_TAC >> simp[kv_queries_TAKE]) >>
  irule FLAT_GENLIST_prefix >> simp[]
QED

Theorem parse_all_b_NIL[local]:
  parse_all_b "" = []
Proof
  simp[Once parse_all_b_def] >> EVAL_TAC
QED

Theorem kv_rounds_bounded[local]:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ MEM q (KG lfdn ifds s0 k) ⇒
  FST q < dimword(:64)
Proof
  strip_tac >>
  ‘MAP SND (FILTER (λq'. FST q' = FST q) (KG lfdn ifds s0 k)) ≼
   parse_all_b (FLAT (read (FST q) (KTS lfdn ifds s0 k)))’
    by metis_tac[kv_rounds_serves] >>
  ‘FLAT (read (FST q) (KTS lfdn ifds s0 k)) ≠ []’
    by (strip_tac >> fs[parse_all_b_NIL] >>
        fs[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
  drule read_on_fd >> strip_tac >>
  ‘uses_ok lfdn (kv_server lfdn)’ by simp[kv_server_uses_ok] >>
  drule_all gen_fds_bounded >> simp[]
QED

(* MAIN: KvSpec's safety for the key-value server's trace: in a world
   with one listener n2w lfdn and no connections, for any interest
   function, the trace is linearizable *)
Theorem kv_comp_safe:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  kv_safe (LFLATTEN (LGENLIST
    (λi. fromList (grounds_events ifds (srelabel (kv_server lfdn)) s0 i)) NONE))
Proof
  rw[kv_safe_def] >>
  ‘∀i. KEV lfdn ifds s0 i ≠ []’ by simp[grounds_events_alt] >>
  drule_all LPREFIX_rounds_between >> strip_tac >>
  ‘∀k c. bytes_written_to c (KP lfdn ifds s0 (SUC k)) =
           HttpGetSpec$bytes (FLAT (written (w2n c) (KTS lfdn ifds s0 k))) ∧
         bytes_read_from c (KP lfdn ifds s0 k) =
           HttpGetSpec$bytes (FLAT (read (w2n c) (KTS lfdn ifds s0 k)))’
    by metis_tac[kv_rounds_bytes] >>
  ‘∀k fd. MAP SND (FILTER (λq. FST q = fd) (KG lfdn ifds s0 k)) ≼
            parse_all_b (FLAT (read fd (KTS lfdn ifds s0 k))) ∧
          written fd (KTS lfdn ifds s0 k) ≼
            MAP print_response (fd_answers fd (KG lfdn ifds s0 k))’
    by metis_tac[kv_rounds_serves] >>
  ‘∀k1 k2. k1 ≤ k2 ⇒
           KG lfdn ifds s0 k1 ≼ KG lfdn ifds s0 k2 ∧
           KP lfdn ifds s0 k1 ≼ KP lfdn ifds s0 k2’
    by metis_tac[kv_rounds_mono] >>
  ‘∀k q. MEM q (KG lfdn ifds s0 k) ⇒ FST q < dimword(:64)’
    by metis_tac[kv_rounds_bounded] >>
  (* what has been read from each connection *)
  ‘∀c. parse_all_b (MAP (CHR o w2n) (bytes_read_from c evs)) = rss c’
    by (gen_tac >> irule read_brequests_parse >> simp[bytes_chars] >> metis_tac[]) >>
  ‘∀k c. k ≤ n ⇒ parse_all_b (FLAT (read (w2n c) (KTS lfdn ifds s0 k))) ≼ rss c’
    by (rpt strip_tac >>
        first_x_assum (qspec_then ‘c’ (SUBST1_TAC o SYM)) >>
        irule parse_all_b_prefix >> ONCE_REWRITE_TAC[GSYM bytes_prefix_iff] >>
        simp[bytes_chars] >>
        qpat_assum ‘∀k c. bytes_written_to _ _ = _ ∧ _’
          (qspecl_then [‘k’, ‘c’] (SUBST1_TAC o SYM o CONJUNCT2)) >>
        qpat_assum ‘∀c. EVERY _ _ ∧ _’
          (qspec_then ‘c’ (SUBST1_TAC o SYM o last o CONJUNCTS)) >>
        irule bytes_read_from_mono >> metis_tac[IS_PREFIX_TRANS]) >>
  qabbrev_tac ‘Gn = KG lfdn ifds s0 n’ >>
  qabbrev_tac ‘Gc = λc:word64. MAP SND (FILTER (λq. FST q = w2n c) Gn)’ >>
  ‘∀c. Gc c ≼ rss c’
    by (gen_tac >> simp[Abbr ‘Gc’, Abbr ‘Gn’] >> irule IS_PREFIX_TRANS >>
        qexists_tac ‘parse_all_b (FLAT (read (w2n c) (KTS lfdn ifds s0 n)))’ >> simp[]) >>
  (* the order *)
  qspec_then ‘evs’ strip_assume_tac (GEN_ALL conns_of_trace) >>
  qabbrev_tac ‘L1 = MAP (λq. (n2w (FST q) : word64, SND q)) Gn’ >>
  qabbrev_tac ‘pend = FLAT (MAP (λc. MAP (λr. (c, r)) (DROP (LENGTH (Gc c)) (rss c))) CS)’ >>
  qabbrev_tac ‘L = L1 ++ pend’ >>
  ‘∀c. MAP SND (FILTER (λx. FST x = c) L1) = Gc c’
    by (gen_tac >> simp[Abbr ‘L1’, Abbr ‘Gc’] >>
        DEP_REWRITE_TAC[FILTER_conn_words] >> simp[MAP_MAP_o, combinTheory.o_DEF] >>
        fs[Abbr ‘Gn’] >> metis_tac[]) >>
  ‘∀c. MAP SND (FILTER (λx. FST x = c) L) = rss c’
    by (gen_tac >> simp[Abbr ‘L’, FILTER_APPEND, Abbr ‘pend’, FILTER_pend] >> rw[]
        >- (qpat_x_assum ‘∀c. Gc c ≼ rss c’ (qspec_then ‘c’ mp_tac) >>
            simp[MAP_MAP_o, combinTheory.o_DEF] >> strip_tac >> fs[IS_PREFIX_APPEND] >>
            simp[DROP_LENGTH_APPEND]) >>
        ‘rss c = []’
          by (CCONTR_TAC >>
              ‘bytes_read_from c evs ≠ []’ suffices_by metis_tac[] >>
              qpat_assum ‘∀c. EVERY _ _ ∧ _’ (qspec_then ‘c’ mp_tac) >>
              Cases_on ‘rss c’ >> fs[brequests_def, bytes_APPEND] >> rpt strip_tac >>
              qpat_x_assum ‘_ (print_brequest _) = []’
                (mp_tac o AP_TERM “LENGTH : word8 list -> num”) >>
              simp[print_brequest_NIL]) >>
        qpat_x_assum ‘∀c. Gc c ≼ rss c’ (qspec_then ‘c’ mp_tac) >> simp[]) >>
  (* what has been written, at evs *)
  ‘∀c. bytes_written_to c evs ≼ reply_bytes (fd_answers (w2n c) Gn)’
    by (gen_tac >> irule IS_PREFIX_TRANS >>
        qexists_tac ‘bytes_written_to c (KP lfdn ifds s0 (SUC n))’ >>
        simp[bytes_written_to_mono] >>
        simp[reply_bytes_def, bytes_prefix_iff, Abbr ‘Gn’] >>
        irule prefix_FLAT >> simp[]) >>
  qexists_tac ‘label L’ >>
  ‘is_order rss (label L)’ by (irule is_order_label >> simp[]) >>
  simp[] >>
  (* the replies *)
  qabbrev_tac ‘A = FST (run_store kv_delta (λk. NONE) Gn)’ >>
  ‘∀c. ∃X. replies rss (label L) c = fd_answers (w2n c) Gn ++ X’
    by (gen_tac >> simp[replies_label] >>
        ‘MAP SND L1 = MAP SND Gn’ by simp[Abbr ‘L1’, LIST_EQ_REWRITE, EL_MAP] >>
        ‘MAP SND L = MAP SND (Gn ++ MAP (λx. (0:num, SND x)) pend)’
          by (simp[Abbr ‘L’] >> simp[LIST_EQ_REWRITE, EL_MAP]) >>
        qpat_x_assum ‘MAP SND L = _’ SUBST1_TAC >>
        REWRITE_TAC[kv_run_store, run_store_APPEND_FST] >>
        simp[Abbr ‘L’] >>
        DEP_REWRITE_TAC[GSYM ZIP_APPEND] >> conj_tac >- simp[Abbr ‘L1’, Abbr ‘A’] >>
        simp[FILTER_APPEND, Abbr ‘L1’] >>
        DEP_REWRITE_TAC[ZIP_conn_words] >>
        conj_tac >- (simp[Abbr ‘A’] >> fs[Abbr ‘Gn’] >> metis_tac[]) >>
        simp[fd_answers_def, MAP_MAP_o, combinTheory.o_DEF, ETA_AX]) >>
  ‘∀c. LENGTH (replies rss (label L) c) = LENGTH (rss c)’
    by (gen_tac >> simp[replies_label] >>
        DEP_REWRITE_TAC[LENGTH_FILTER_ZIP] >> simp[] >>
        qpat_x_assum ‘∀c. MAP SND (FILTER _ L) = _’
          (qspec_then ‘c’ (SUBST1_TAC o SYM)) >> simp[]) >>
  ‘∀c. LENGTH (fd_answers (w2n c) Gn) = LENGTH (Gc c)’
    by simp[LENGTH_fd_answers, Abbr ‘Gc’] >>
  ‘∀c. reply_bytes (fd_answers (w2n c) Gn) =
       reply_bytes (TAKE (LENGTH (Gc c)) (replies rss (label L) c))’
    by (gen_tac >> qpat_x_assum ‘∀c. ∃X. _’ (qspec_then ‘c’ strip_assume_tac) >>
        qpat_x_assum ‘∀c. LENGTH (fd_answers _ _) = _’
          (qspec_then ‘c’ (SUBST1_TAC o SYM)) >>
        simp[TAKE_LENGTH_APPEND]) >>
  conj_tac
  >- ((* real time *)
      qsuff_tac ‘∃pj. commits_at rss (label L) evs pj’
      >- metis_tac[commits_at_real_time] >>
      qexists_tac ‘λj. if j < LENGTH Gn then LENGTH (KP lfdn ifds s0 ($LEAST (λk. j < LENGTH (KG lfdn ifds s0 k))))
                       else LENGTH evs’ >>
      ‘∀j. j < LENGTH Gn ⇒
           j < LENGTH (KG lfdn ifds s0 ($LEAST (λk. j < LENGTH (KG lfdn ifds s0 k)))) ∧
           $LEAST (λk. j < LENGTH (KG lfdn ifds s0 k)) ≤ n ∧
           ∀m. m < $LEAST (λk. j < LENGTH (KG lfdn ifds s0 k)) ⇒ LENGTH (KG lfdn ifds s0 m) ≤ j’
        by (rpt gen_tac >> strip_tac >>
            qspecl_then [‘λk. j < LENGTH (KG lfdn ifds s0 k)’, ‘n’] mp_tac
              (Q.GEN ‘P’ WhileTheory.FULL_LEAST_INTRO) >>
            simp[Abbr ‘Gn’] >> rw[] >>
            drule (Q.ISPEC ‘λk. j < LENGTH (KG lfdn ifds s0 k)’ WhileTheory.LESS_LEAST) >> simp[]) >>
      ‘∀a b. a ≤ b ⇒ LENGTH (KP lfdn ifds s0 a) ≤ LENGTH (KP lfdn ifds s0 b)’
        by metis_tac[IS_PREFIX_LENGTH] >>
      ‘LENGTH (KP lfdn ifds s0 n) ≤ LENGTH evs’ by metis_tac[IS_PREFIX_LENGTH] >>
      ‘LENGTH L1 = LENGTH Gn’ by simp[Abbr ‘L1’] >>
      simp[commits_at_def] >> conj_tac
      >- (rw[] >> gvs[]
          >- (qpat_x_assum ‘∀a b. a ≤ b ⇒ LENGTH _ ≤ LENGTH _’ irule >>
              qspecl_then [‘λk. j < LENGTH (KG lfdn ifds s0 k)’,
                           ‘$LEAST (λk. j' < LENGTH (KG lfdn ifds s0 k))’] mp_tac
                (Q.GEN ‘P’ WhileTheory.FULL_LEAST_INTRO) >>
              simp[] >> impl_tac
              >- (qpat_x_assum ‘∀j. j < LENGTH Gn ⇒ _’ (qspec_then ‘j'’ mp_tac) >> simp[]) >>
              simp[])
          >> irule LESS_EQ_TRANS >> qexists_tac ‘LENGTH (KP lfdn ifds s0 n)’ >> simp[] >>
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
      simp[started_def, answered_def] >>
      Cases_on ‘j < LENGTH Gn’ >> simp[]
      >- ((* a query, committed at the start of its first round cr *)
          qabbrev_tac ‘cr = $LEAST (λk. j < LENGTH (KG lfdn ifds s0 k))’ >>
          qpat_x_assum ‘∀j. j < LENGTH Gn ⇒ _’ (qspec_then ‘j’ mp_tac) >> simp[] >> strip_tac >>
          ‘TAKE (LENGTH (KP lfdn ifds s0 cr)) evs = KP lfdn ifds s0 cr’
            by (irule prefix_TAKE_self >> irule IS_PREFIX_TRANS >>
                qexists_tac ‘KP lfdn ifds s0 n’ >> simp[]) >>
          simp[] >>
          qabbrev_tac ‘fd = FST (EL j Gn)’ >>
          ‘fd < dimword(:64)’
            by (qpat_assum ‘∀k q. MEM q (KG _ _ _ k) ⇒ _’ (qspecl_then [‘n’, ‘EL j Gn’] mp_tac) >>
                simp[Abbr ‘fd’] >> disch_then irule >> simp[Abbr ‘Gn’, EL_MEM]) >>
          ‘EL j L = (n2w fd, SND (EL j Gn))’
            by simp[Abbr ‘L’, EL_APPEND1, Abbr ‘L1’, EL_MAP] >>
          ‘w2n c = fd’ by simp[Abbr ‘c’] >>
          ‘LENGTH (FILTER (λq. FST q = fd) (TAKE j Gn)) = i’
            by (simp[Abbr ‘i’, Abbr ‘L’, TAKE_APPEND1, Abbr ‘L1’, GSYM MAP_TAKE] >>
                DEP_REWRITE_TAC[FILTER_conn_words] >> simp[] >>
                rpt strip_tac >> ‘MEM q Gn’ by metis_tac[MEM_TAKE] >>
                qpat_assum ‘∀k q. MEM q (KG _ _ _ k) ⇒ _’ (qspecl_then [‘n’, ‘q’] mp_tac) >>
                fs[Abbr ‘Gn’]) >>
          ‘KG lfdn ifds s0 cr ≼ Gn’ by simp[Abbr ‘Gn’] >>
          ‘TAKE (SUC j) Gn = TAKE (SUC j) (KG lfdn ifds s0 cr)’
            by (irule prefix_TAKE_eq >> simp[]) >>
          conj_tac
          >- ((* started: c's first i+1 requests were read before round cr *)
              irule brequests_TAKE_SUC >> simp[] >>
              qabbrev_tac ‘PR = parse_all_b (FLAT (read fd (KTS lfdn ifds s0 cr)))’ >>
              ‘PR ≼ rss c’
                by (qunabbrev_tac ‘PR’ >> qpat_assum ‘w2n c = fd’ (SUBST1_TAC o SYM) >>
                    qpat_assum ‘∀k c. k ≤ n ⇒ parse_all_b _ ≼ rss c’ irule >> simp[]) >>
              ‘LENGTH (FILTER (λq. FST q = fd) (TAKE (SUC j) (KG lfdn ifds s0 cr))) = SUC i’
                by (qpat_x_assum ‘TAKE (SUC j) Gn = _’ (SUBST1_TAC o SYM) >>
                    simp[TAKE_SUC_EL, FILTER_APPEND] >> simp[Abbr ‘fd’]) >>
              ‘LENGTH (FILTER (λq. FST q = fd) (TAKE (SUC j) (KG lfdn ifds s0 cr))) ≤
               LENGTH (FILTER (λq. FST q = fd) (KG lfdn ifds s0 cr))’
                by (irule IS_PREFIX_LENGTH >> irule prefix_FILTER >>
                    simp[IS_PREFIX_APPEND] >> metis_tac[TAKE_DROP]) >>
              ‘SUC i ≤ LENGTH PR’
                by (qpat_assum ‘∀k fd. MAP SND _ ≼ _ ∧ _’
                      (qspecl_then [‘cr’, ‘fd’] (assume_tac o CONJUNCT1)) >>
                    imp_res_tac IS_PREFIX_LENGTH >> fs[Abbr ‘PR’]) >>
              ‘TAKE (SUC i) (rss c) = TAKE (SUC i) PR’ by (irule prefix_TAKE_eq >> simp[]) >>
              simp[brequests_def, bytes_prefix_iff] >>
              irule parse_all_b_printed >> simp[Abbr ‘PR’, IS_PREFIX_APPEND] >>
              metis_tac[TAKE_DROP]) >>
          (* not answered: before round cr, at most c's first i answers *)
          ‘∃i'. i' ≤ i ∧ bytes_written_to c (KP lfdn ifds s0 cr) ≼
                         reply_bytes (TAKE i' (replies rss (label L) c))’
            by (Cases_on ‘cr’
                >- (qexists_tac ‘0’ >> simp[bytes_written_to_def]) >>
                rename1 ‘KP lfdn ifds s0 (SUC k2)’ >>
                ‘LENGTH (KG lfdn ifds s0 k2) ≤ j’
                  by (qpat_x_assum ‘∀m. m < SUC k2 ⇒ _’ (qspec_then ‘k2’ mp_tac) >> simp[]) >>
                ‘KG lfdn ifds s0 k2 ≼ Gn’ by simp[Abbr ‘Gn’] >>
                qexists_tac ‘LENGTH (fd_answers fd (KG lfdn ifds s0 k2))’ >> conj_tac
                >- (simp[LENGTH_fd_answers] >>
                    qpat_x_assum ‘LENGTH (FILTER _ (TAKE j Gn)) = i’ (SUBST1_TAC o SYM) >>
                    irule IS_PREFIX_LENGTH >> irule prefix_FILTER >>
                    irule prefix_shorter_TAKE >> simp[]) >>
                ‘fd_answers fd (KG lfdn ifds s0 k2) =
                 TAKE (LENGTH (fd_answers fd (KG lfdn ifds s0 k2))) (replies rss (label L) c)’
                  by (irule prefix_LENGTH_eq_TAKE >> irule IS_PREFIX_TRANS >>
                      qexists_tac ‘fd_answers fd Gn’ >> conj_tac >>
                      TRY (irule fd_answers_prefix >> simp[] >> NO_TAC) >>
                      qpat_x_assum ‘∀c. ∃X. _’ (qspec_then ‘c’ strip_assume_tac) >> simp[]) >>
                pop_assum (SUBST1_TAC o SYM) >>
                qpat_assum ‘∀k c. bytes_written_to _ _ = _ ∧ _’
                  (qspecl_then [‘k2’, ‘c’] (SUBST1_TAC o CONJUNCT1)) >>
                simp[reply_bytes_def, bytes_prefix_iff] >> irule prefix_FLAT >>
                qpat_assum ‘∀k fd. MAP SND _ ≼ _ ∧ _’
                  (qspecl_then [‘k2’, ‘fd’] (ACCEPT_TAC o CONJUNCT2))) >>
          strip_tac >>
          qspecl_then [‘i’, ‘replies rss (label L) c’, ‘i'’,
                       ‘bytes_written_to c (KP lfdn ifds s0 cr)’]
            mp_tac (Q.GENL [‘i’, ‘R’, ‘j’, ‘x’] reply_bytes_TAKE) >> simp[]) >>
      (* a request not queried yet, committed at the end of evs *)
      ‘LENGTH (Gc c) ≤ i’
        by (qpat_x_assum ‘∀c. MAP SND (FILTER _ L1) = Gc c’ (qspec_then ‘c’ (SUBST1_TAC o SYM)) >>
            simp[Abbr ‘i’, Abbr ‘L’, TAKE_APPEND, TAKE_LENGTH_TOO_LONG, FILTER_APPEND]) >>
      conj_tac
      >- (irule brequests_TAKE_SUC >> simp[] >> irule IS_PREFIX_TRANS >>
          qexists_tac ‘brequests (rss c)’ >> simp[brequests_TAKE_prefix]) >>
      strip_tac >>
      qspecl_then [‘i’, ‘replies rss (label L) c’, ‘LENGTH (Gc c)’, ‘bytes_written_to c evs’]
        mp_tac (Q.GENL [‘i’, ‘R’, ‘j’, ‘x’] reply_bytes_TAKE) >> simp[] >>
      qpat_x_assum ‘∀c. reply_bytes _ = _’ (qspec_then ‘c’ (SUBST1_TAC o SYM)) >>
      qpat_x_assum ‘∀c. bytes_written_to c evs ≼ _’ (qspec_then ‘c’ ACCEPT_TAC)) >>
  gen_tac >> qpat_x_assum ‘∀c. ∃X. _’ (qspec_then ‘c’ strip_assume_tac) >> simp[] >>
  irule IS_PREFIX_TRANS >> qexists_tac ‘reply_bytes (fd_answers (w2n c) Gn)’ >>
  simp[reply_bytes_prefix]
QED
