(*
  HttpKvSpec's safety (linearizability) for the loop's trace of the
  key-value server, kv_server (asyncKvModel), in any interest function.

  At a point evs of the trace, between the starts of rounds n and n+1:
   - the order: the queries the store has answered by round n, in the
     order it answered them (kv_queries), followed by the complete
     requests not queried yet, connection by connection;
   - commit points: a query first answered in round k commits at the start
     of round k (the position LENGTH (rounds 0..k-1) in the trace); a
     request not queried yet commits at the end of evs;
   - commit points give real time (asyncKvLabel's commits_at_real_time),
     because a query of round k reads its request in rounds < k and its
     response is written in rounds > k.

  The bridge between model rounds and trace positions is asyncRunOkGen's
  gen_rounds_bytes, used at every round k ≤ n: the bytes read in rounds
  < k are those of the transcript after k rounds, the bytes written in
  rounds ≤ k those of the transcript after k rounds.
*)
Theory asyncKvSafe
Ancestors
  words asyncCore asyncLevel1 asyncLevel2 asyncTranscript asyncServer
  asyncServerSafety asyncM4ServerUses asyncM4Relabel asyncM4RelabelDist
  ffiSpikeSocketFFI asyncM3World asyncM4GRounds asyncM4SockInv
  asyncM4SockModel asyncM4GTrans asyncRunOkGen EchoSpec HttpSpec
  HttpSpecBodies HttpKvSpec asyncHttpParse asyncHttpParseH asyncHttpParseB
  asyncWithStore asyncServerWithK asyncKvHandler asyncKvModel asyncKvOrder
  asyncKvLabel asyncKvTraceLemmas llist ffi while
Libs
  preamble

(* ------------------------------------------------------------------------
   Lists
   ------------------------------------------------------------------------ *)

Theorem FLAT_GENLIST_prefix[local]:
  a ≤ b ⇒ FLAT (GENLIST f a) ≼ FLAT (GENLIST f b)
Proof
  strip_tac >> ‘b = a + (b - a)’ by simp[] >>
  pop_assum SUBST1_TAC >> simp[GENLIST_APPEND, FLAT_APPEND]
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

(* Connections of fds below 2^64, as words *)
Theorem FILTER_conn_words[local]:
  ∀G. (∀q. MEM q G ⇒ FST q < dimword(:64)) ⇒
      FILTER (λx. FST x = c) (MAP (λq. (n2w (FST q) : word64, SND q)) G) =
      MAP (λq. (c, SND q)) (FILTER (λq. FST q = w2n c) G)
Proof
  Induct >> simp[] >> PairCases >> rw[] >> gvs[] >>
  gvs[] >> metis_tac[w2n_n2w, n2w_w2n, LESS_MOD]
QED

Theorem ZIP_conn_words[local]:
  ∀G A. (∀q. MEM q G ⇒ FST q < dimword(:64)) ∧ LENGTH A = LENGTH G ⇒
        FILTER (λp. FST (FST p) = c)
               (ZIP (MAP (λq. (n2w (FST q) : word64, SND q)) G, A)) =
        MAP (λp. ((c, SND (FST p)), SND p))
            (FILTER (λp. FST (FST p) = w2n c) (ZIP (G, A)))
Proof
  Induct >> simp[] >> PairCases >> rpt gen_tac >> Cases_on ‘A’ >> simp[] >>
  rw[] >> gvs[] >> metis_tac[w2n_n2w, n2w_w2n, LESS_MOD]
QED

Theorem FILTER_pend[local]:
  ∀CS. ALL_DISTINCT CS ⇒
       FILTER (λx. FST x = c) (FLAT (MAP (λc. MAP (λr. (c, r)) (D c)) CS)) =
       if MEM c CS then MAP (λr. (c, r)) (D c) else []
Proof
  Induct >> simp[FILTER_APPEND] >> rw[] >> gvs[]
  >> simp[FILTER_EQ_ID, EVERY_MAP, FILTER_EQ_NIL]
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
  simp[bytes_read_from_def, FLAT_EQ_NIL, EXISTS_MEM, EVERY_MEM] >>
  rpt strip_tac >> simp[MEM_MAP] >> qexists_tac ‘e’ >> simp[] >>
  Cases_on ‘e’ >> rename1 ‘IO_event f conf b’ >> Cases_on ‘f’ >>
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

(* MAIN: HttpKvSpec's safety for the key-value server's trace: in a world
   with one listener n2w lfdn and no connections, for any interest
   function, the trace is linearizable *)
Theorem kv_comp_safe:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ⇒
  kv_safe (LFLATTEN (LGENLIST
    (λi. fromList (grounds_events ifds (srelabel (kv_server lfdn)) s0 i)) NONE))
Proof
  rw[kv_safe_def] >>
  qabbrev_tac ‘ev = grounds_events ifds (srelabel (kv_server lfdn)) s0’ >>
  ‘∀i. ev i ≠ []’ by simp[Abbr ‘ev’, grounds_events_alt] >>
  drule_all LPREFIX_rounds_between >> strip_tac >>
  ‘uses_ok lfdn (kv_server lfdn)’ by simp[kv_server_uses_ok] >>
  qabbrev_tac ‘HH = λk. MAP sfs (ghist ifds (srelabel (kv_server lfdn)) s0 k)’ >>
  qabbrev_tac ‘TS = λk. trans (kv_server lfdn) (HH k)’ >>
  qabbrev_tac ‘G = λk. kv_queries lfdn (HH k)’ >>
  qabbrev_tac ‘P = λk. FLAT (GENLIST ev k)’ >>
  (* the bridge, at every round *)
  ‘∀k c. bytes_written_to c (P (SUC k)) = bytes (FLAT (written (w2n c) (TS k))) ∧
         bytes_read_from c (P k) = bytes (FLAT (read (w2n c) (TS k)))’
    by (rpt gen_tac >> drule_all gen_rounds_bytes >>
        disch_then (qspecl_then [‘k’, ‘ifds’, ‘c’] mp_tac) >>
        simp[Abbr ‘P’, Abbr ‘ev’, Abbr ‘TS’, Abbr ‘HH’, bytes_def]) >>
  ‘∀k. fresh (TS k)’ by (simp[Abbr ‘TS’, Abbr ‘HH’] >> metis_tac[gen_fresh]) >>
  ‘∀k fd. MAP SND (FILTER (λq. FST q = fd) (G k)) ≼
            parse_all_b (FLAT (read fd (TS k))) ∧
          written fd (TS k) ≼ MAP print_response (fd_answers fd (G k))’
    by (rpt gen_tac >> simp[Abbr ‘G’, Abbr ‘TS’] >> irule kv_server_serves >>
        fs[Abbr ‘TS’]) >>
  ‘∀k1 k2. k1 ≤ k2 ⇒ G k1 ≼ G k2 ∧ P k1 ≼ P k2’
    by (rw[Abbr ‘G’, Abbr ‘P’, FLAT_GENLIST_prefix] >>
        ‘HH k1 = TAKE k1 (HH k2)’ by simp[Abbr ‘HH’, MAP_TAKE, ghist_TAKE] >>
        simp[kv_queries_TAKE]) >>
  ‘∀k q. MEM q (G k) ⇒ FST q < dimword(:64)’
    by (rpt strip_tac >>
        first_x_assum (qspecl_then [‘k’, ‘FST q’] (strip_assume_tac o CONJUNCT1)) >>
        ‘FLAT (read (FST q) (TS k)) ≠ []’
          by (strip_tac >> gvs[] >>
              qpat_x_assum ‘_ ≼ parse_all_b ""’ mp_tac >>
              simp[Once parse_all_b_def, parse_brequest_def] >>
              EVAL_TAC >> simp[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
        drule read_on_fd >> simp[Abbr ‘TS’, Abbr ‘HH’] >> strip_tac >>
        drule_all gen_fds_bounded >> simp[]) >>
  (* what has been read from each connection *)
  ‘∀c. parse_all_b (MAP (CHR o w2n) (bytes_read_from c evs)) = rss c’
    by (gen_tac >> irule read_brequests_parse >> simp[bytes_chars] >> metis_tac[]) >>
  ‘∀k c. k ≤ n ⇒ parse_all_b (FLAT (read (w2n c) (TS k))) ≼ rss c’
    by (rpt strip_tac >>
        first_x_assum (qspec_then ‘c’ (SUBST1_TAC o SYM)) >>
        irule parse_all_b_prefix >> ONCE_REWRITE_TAC[GSYM bytes_prefix_iff] >>
        simp[bytes_chars] >>
        qpat_x_assum ‘∀k c. bytes_written_to _ _ = _ ∧ _’
          (qspecl_then [‘k’, ‘c’] (SUBST1_TAC o SYM o CONJUNCT2)) >>
        irule bytes_read_from_mono >> irule IS_PREFIX_TRANS >>
        qexists_tac ‘P n’ >> simp[]) >>
  qabbrev_tac ‘Gn = G n’ >>
  qabbrev_tac ‘Gc = λc. MAP SND (FILTER (λq. FST q = w2n c) Gn)’ >>
  ‘∀c. Gc c ≼ rss c’
    by (gen_tac >> simp[Abbr ‘Gc’, Abbr ‘Gn’] >> irule IS_PREFIX_TRANS >>
        qexists_tac ‘parse_all_b (FLAT (read (w2n c) (TS n)))’ >> simp[]) >>
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
    by (gen_tac >> simp[Abbr ‘L’, FILTER_APPEND, Abbr ‘pend’, FILTER_pend] >>
        rw[]
        >- (first_x_assum (qspec_then ‘c’ mp_tac) >> rw[IS_PREFIX_APPEND] >>
            simp[MAP_MAP_o, combinTheory.o_DEF, DROP_LENGTH_APPEND])
        >> ‘rss c = []’
             by (CCONTR_TAC >>
                 ‘bytes_read_from c evs ≠ []’
                   by (first_x_assum (qspec_then ‘c’ mp_tac) >>
                       Cases_on ‘rss c’ >> simp[brequests_def, bytes_APPEND] >>
                       metis_tac[print_brequest_NIL, LENGTH_NIL, LENGTH_bytes]) >>
                 metis_tac[]) >>
        first_x_assum (qspec_then ‘c’ mp_tac) >> simp[]) >>
  qexists_tac ‘label L’ >>
  ‘is_order rss (label L)’ by (irule is_order_label >> simp[]) >>
  simp[] >>
  (* the replies *)
  qabbrev_tac ‘A = FST (run_store kv_delta (λk. NONE) Gn)’ >>
  ‘∀c. ∃X. replies rss (label L) c = fd_answers (w2n c) Gn ++ X’
    by (gen_tac >> simp[replies_label] >>
        ‘MAP SND L = MAP SND (Gn ++ MAP (λx. (0, SND x)) pend)’
          by simp[Abbr ‘L’, Abbr ‘L1’, MAP_MAP_o, combinTheory.o_DEF] >>
        simp[kv_run_store, run_store_APPEND_FST] >>
        ‘LENGTH L1 = LENGTH A’ by simp[Abbr ‘L1’, Abbr ‘A’] >>
        simp[Abbr ‘L’, ZIP_APPEND, FILTER_APPEND] >>
        DEP_REWRITE_TAC[ZIP_conn_words |> Q.GEN ‘c’ |> Q.SPEC ‘c’] >>
        conj_tac >- (simp[Abbr ‘A’] >> fs[Abbr ‘Gn’] >> metis_tac[]) >>
        simp[fd_answers_def, MAP_MAP_o, combinTheory.o_DEF, Abbr ‘A’]) >>
  ‘∀c. LENGTH (replies rss (label L) c) = LENGTH (rss c)’
    by (gen_tac >> simp[replies_label] >>
        simp[LENGTH_FILTER_ZIP] >>
        first_x_assum (qspec_then ‘c’ (SUBST1_TAC o SYM)) >> simp[]) >>
  ‘∀c. LENGTH (fd_answers (w2n c) Gn) = LENGTH (Gc c)’
    by simp[LENGTH_fd_answers, Abbr ‘Gc’] >>
  ‘∀c. reply_bytes (fd_answers (w2n c) Gn) =
       reply_bytes (TAKE (LENGTH (Gc c)) (replies rss (label L) c))’
    by (gen_tac >> first_x_assum (qspec_then ‘c’ strip_assume_tac) >>
        last_x_assum (qspec_then ‘c’ strip_assume_tac) >>
        simp[TAKE_LENGTH_APPEND] >> metis_tac[TAKE_LENGTH_APPEND]) >>
  (* what has been written, at evs *)
  ‘∀c. bytes_written_to c evs ≼ reply_bytes (fd_answers (w2n c) Gn)’
    by (gen_tac >> irule IS_PREFIX_TRANS >>
        qexists_tac ‘bytes_written_to c (P (SUC n))’ >>
        simp[bytes_written_to_mono] >>
        simp[reply_bytes_def, bytes_prefix_iff, Abbr ‘Gn’] >>
        irule prefix_FLAT >> simp[]) >>
  conj_tac
  >- ((* real time *)
      irule commits_at_real_time >> simp[] >>
      qexists_tac ‘λj. if j < LENGTH Gn then LENGTH (P ($LEAST (λk. j < LENGTH (G k))))
                       else LENGTH evs’ >>
      ‘∀j. j < LENGTH Gn ⇒
           j < LENGTH (G ($LEAST (λk. j < LENGTH (G k)))) ∧
           $LEAST (λk. j < LENGTH (G k)) ≤ n ∧
           ∀m. m < $LEAST (λk. j < LENGTH (G k)) ⇒ LENGTH (G m) ≤ j’
        by (rpt gen_tac >> strip_tac >>
            qspecl_then [‘λk. j < LENGTH (G k)’, ‘n’] mp_tac
              (Q.GENL [‘P’, ‘x’] FULL_LEAST_INTRO) >>
            simp[Abbr ‘Gn’] >> rw[] >>
            drule (Q.ISPEC ‘λk. j < LENGTH (G k)’ LESS_LEAST) >> simp[]) >>
      ‘∀a b. a ≤ b ⇒ LENGTH (P a) ≤ LENGTH (P b)’
        by metis_tac[IS_PREFIX_LENGTH] >>
      ‘LENGTH (P n) ≤ LENGTH evs’ by metis_tac[IS_PREFIX_LENGTH] >>
      ‘LENGTH L1 = LENGTH Gn’ by simp[Abbr ‘L1’] >>
      simp[commits_at_def] >> conj_tac
      >- (rw[] >> gvs[]
          >- (first_x_assum irule >>
              qspecl_then [‘λk. j < LENGTH (G k)’,
                           ‘$LEAST (λk'. k < LENGTH (G k'))’] mp_tac
                (Q.GENL [‘P’, ‘x’] FULL_LEAST_INTRO) >>
              simp[] >> impl_tac >- (first_x_assum (qspec_then ‘k’ mp_tac) >> simp[]) >>
              simp[])
          >> irule LESS_EQ_TRANS >> qexists_tac ‘LENGTH (P n)’ >> simp[]) >>
      rpt gen_tac >> strip_tac >>
      simp[label_def, EL_GENLIST] >>
      qabbrev_tac ‘c = FST (EL j L)’ >>
      qabbrev_tac ‘i = LENGTH (FILTER (λx. FST x = c) (TAKE j L))’ >>
      ‘i < LENGTH (rss c)’
        by (simp[Abbr ‘i’, Abbr ‘c’] >>
            first_x_assum (qspec_then ‘FST (EL j L)’ (SUBST1_TAC o SYM o
                             (fn th => th) )) >>
            simp[] >> irule cnt_TAKE_lt >> fs[]) >>
      simp[started_def, answered_def] >>
      Cases_on ‘j < LENGTH Gn’ >> simp[]
      >- ((* a query, committed at the start of its first round *)
          qabbrev_tac ‘cr = $LEAST (λk. j < LENGTH (G k))’ >>
          first_x_assum (qspec_then ‘j’ mp_tac) >> simp[] >> strip_tac >>
          ‘TAKE (LENGTH (P cr)) evs = P cr’
            by (irule prefix_TAKE_self >> irule IS_PREFIX_TRANS >>
                qexists_tac ‘P n’ >> simp[]) >>
          simp[] >>
          qabbrev_tac ‘fd = FST (EL j Gn)’ >>
          ‘fd < dimword(:64)’ by (simp[Abbr ‘fd’, Abbr ‘Gn’] >> metis_tac[MEM_EL]) >>
          ‘EL j L = (n2w fd, SND (EL j Gn))’
            by simp[Abbr ‘L’, EL_APPEND1, Abbr ‘L1’, EL_MAP] >>
          ‘c = n2w fd ∧ w2n c = fd’ by simp[Abbr ‘c’] >>
          ‘i = LENGTH (FILTER (λq. FST q = fd) (TAKE j Gn))’
            by (simp[Abbr ‘i’, Abbr ‘L’, TAKE_APPEND1, Abbr ‘L1’, GSYM MAP_TAKE] >>
                DEP_REWRITE_TAC[FILTER_conn_words] >> simp[] >>
                fs[Abbr ‘Gn’] >> metis_tac[MEM_TAKE]) >>
          ‘G cr ≼ Gn’ by simp[Abbr ‘Gn’] >>
          ‘TAKE (SUC j) Gn = TAKE (SUC j) (G cr)’ by (irule prefix_TAKE_eq >> simp[]) >>
          conj_tac
          >- ((* started: c's first i+1 requests were read before round cr *)
              irule brequests_TAKE_SUC >> simp[] >>
              qabbrev_tac ‘PR = parse_all_b (FLAT (read fd (TS cr)))’ >>
              ‘PR ≼ rss c’ by (simp[Abbr ‘PR’] >> metis_tac[]) >>
              ‘SUC i ≤ LENGTH PR’
                by (irule LESS_EQ_TRANS >>
                    qexists_tac ‘LENGTH (MAP SND (FILTER (λq. FST q = fd) (G cr)))’ >>
                    reverse conj_tac >- metis_tac[IS_PREFIX_LENGTH] >>
                    simp[] >> irule LESS_EQ_TRANS >>
                    qexists_tac ‘LENGTH (FILTER (λq. FST q = fd) (TAKE (SUC j) (G cr)))’ >>
                    reverse conj_tac
                    >- (irule IS_PREFIX_LENGTH >> irule prefix_FILTER >>
                        simp[IS_PREFIX_APPEND] >> metis_tac[TAKE_DROP]) >>
                    qpat_x_assum ‘TAKE (SUC j) Gn = _’ (SUBST1_TAC o SYM) >>
                    simp[TAKE_SUC_EL, FILTER_APPEND, Abbr ‘fd’]) >>
              ‘TAKE (SUC i) (rss c) = TAKE (SUC i) PR’ by (irule prefix_TAKE_eq >> simp[]) >>
              simp[brequests_def] >>
              qpat_x_assum ‘∀k c. bytes_written_to _ _ = _ ∧ _’
                (qspecl_then [‘cr’, ‘c’] (SUBST1_TAC o CONJUNCT2)) >>
              simp[bytes_prefix_iff] >> irule parse_all_b_printed >>
              simp[Abbr ‘PR’, IS_PREFIX_APPEND] >> metis_tac[TAKE_DROP]) >>
          (* not answered: before round cr, at most c's first i answers *)
          ‘∃i'. i' ≤ i ∧ bytes_written_to c (P cr) ≼
                         reply_bytes (TAKE i' (replies rss (label L) c))’
            by (Cases_on ‘cr’
                >- (qexists_tac ‘0’ >> simp[Abbr ‘P’, bytes_written_to_def]) >>
                rename1 ‘P (SUC k2)’ >>
                ‘k2 < SUC k2’ by simp[] >>
                ‘LENGTH (G k2) ≤ j’ by metis_tac[] >>
                ‘G k2 ≼ Gn’ by simp[Abbr ‘Gn’] >>
                qexists_tac ‘LENGTH (fd_answers fd (G k2))’ >>
                conj_tac
                >- (simp[LENGTH_fd_answers, Abbr ‘i’] >> irule IS_PREFIX_LENGTH >>
                    irule prefix_FILTER >> irule prefix_shorter_TAKE >> simp[]) >>
                qpat_x_assum ‘∀k c. bytes_written_to _ _ = _ ∧ _’
                  (qspecl_then [‘k2’, ‘c’] (SUBST1_TAC o CONJUNCT1)) >>
                ‘fd_answers fd (G k2) =
                 TAKE (LENGTH (fd_answers fd (G k2))) (replies rss (label L) c)’
                  by (irule prefix_LENGTH_eq_TAKE >> irule IS_PREFIX_TRANS >>
                      qexists_tac ‘fd_answers fd Gn’ >> simp[fd_answers_prefix] >>
                      last_x_assum (qspec_then ‘c’ strip_assume_tac) >> gvs[]) >>
                pop_assum (SUBST1_TAC o SYM) >>
                simp[reply_bytes_def, bytes_prefix_iff] >>
                irule prefix_FLAT >> simp[]) >>
          strip_tac >> drule_at (Pos last) reply_bytes_TAKE >> simp[] >>
          qexists_tac ‘i'’ >> simp[]) >>
      (* a request not queried yet, committed at the end of evs *)
      ‘LENGTH (Gc c) ≤ i’
        by (simp[Abbr ‘i’, Abbr ‘L’, TAKE_APPEND, TAKE_LENGTH_TOO_LONG, FILTER_APPEND] >>
            first_x_assum (qspec_then ‘c’ (SUBST1_TAC o SYM)) >> simp[]) >>
      conj_tac
      >- (irule brequests_TAKE_SUC >> simp[] >>
          first_x_assum (qspec_then ‘c’ strip_assume_tac) >> simp[] >>
          irule IS_PREFIX_TRANS >> qexists_tac ‘brequests (rss c)’ >>
          simp[brequests_TAKE_prefix]) >>
      strip_tac >> drule_at (Pos last) reply_bytes_TAKE >> simp[] >>
      qexists_tac ‘LENGTH (Gc c)’ >> simp[] >> metis_tac[]) >>
  gen_tac >> irule IS_PREFIX_TRANS >> first_assum (irule_at Any) >>
  first_x_assum (qspec_then ‘c’ strip_assume_tac) >>
  simp[] >> irule reply_bytes_prefix >> simp[]
QED
