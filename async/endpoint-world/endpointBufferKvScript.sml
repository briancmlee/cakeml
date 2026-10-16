(*
  A linearizable key-value server stays linearizable behind a relay
  (kv_relay_closed): HttpKvSpec's kv_safe survives buffer closure.

  The setting is a RELAY RUN: the inside trace (the server) and the
  outside trace (the system), observed at the same instants t of a joint
  run, monotonely, every outside prefix being observed; at each instant,
  on each connection, the server has read a prefix of what was read
  outside, and what was written outside is a prefix of what the server
  wrote (endpointBuffer's relays, for all connections at once).

  At an outside point, the server has read a prefix of each connection's
  requests (parse_mono); kv_safe inside gives an order of those; it is
  extended by the requests the server has not read yet, at the end.  The
  store is sequential, so the earlier replies are unchanged.  Real time
  transfers: if x was answered outside before y was read outside, then at
  that instant the same held inside (a relay only widens request
  intervals); and an appended request cannot have been answered outside,
  since what is written outside is a prefix of what the server wrote.
*)
Theory endpointBufferKv
Ancestors
  EchoSpec HttpSpec HttpSpecBodies HttpKvSpec rich_list endpointBuffer
  endpointBufferHttp
Libs
  preamble

(* Inside and outside traces at the instants of a joint run *)
Definition relay_run_def:
  relay_run (ins : num -> io_event list) (outs : num -> io_event list) io io' ⇔
    (∀t t'. t ≤ t' ⇒ ins t ≼ ins t' ∧ outs t ≼ outs t') ∧
    (∀t. LPREFIX (fromList (ins t)) io) ∧
    (∀evs'. LPREFIX (fromList evs') io' ⇒ ∃t. outs t = evs') ∧
    (∀t c. relays (bytes_read_from c (ins t), bytes_written_to c (ins t))
                  (bytes_read_from c (outs t), bytes_written_to c (outs t)))
End

(* ------------------------------------------------------------------------
   The store, run in pieces
   ------------------------------------------------------------------------ *)

Definition kv_final_def:
  kv_final st [] = st ∧
  kv_final st (r :: rs) = kv_final (SND (kv_step st r)) rs
End

Theorem kv_run_APPEND:
  ∀l1 st. kv_run st (l1 ++ l2) = kv_run st l1 ++ kv_run (kv_final st l1) l2
Proof
  Induct >> simp[kv_run_def, kv_final_def] >> rpt gen_tac >>
  Cases_on ‘kv_step st h’ >> simp[]
QED

Theorem LENGTH_kv_run[simp]:
  ∀l st. LENGTH (kv_run st l) = LENGTH l
Proof
  Induct >> simp[kv_run_def] >> rpt gen_tac >> Cases_on ‘kv_step st h’ >> simp[]
QED

Definition ord_reqs_def:
  ord_reqs rss order = MAP (λ(d, i). EL i (rss d)) order
End

Theorem FILTER_ZIP_APPEND:
  ∀a b. LENGTH a = LENGTH b ⇒
        FILTER P (ZIP (a ++ c, b ++ d)) = FILTER P (ZIP (a, b)) ++ FILTER P (ZIP (c, d))
Proof
  Induct >> simp[] >> gen_tac >> Cases >> simp[] >> rw[]
QED

Theorem replies_APPEND:
  replies rss (order ++ ex) c =
    replies rss order c ++
    MAP SND (FILTER (λ((d, i), a). d = c)
              (ZIP (ex, kv_run (kv_final (λk. NONE) (ord_reqs rss order))
                                 (ord_reqs rss ex))))
Proof
  REWRITE_TAC[replies_def, ord_reqs_def, MAP_APPEND, kv_run_APPEND] >>
  ‘LENGTH order = LENGTH (kv_run (λk. NONE) (MAP (λ(d,i). EL i (rss d)) order))’
    by simp[] >>
  drule FILTER_ZIP_APPEND >> disch_then (fn th => REWRITE_TAC[th, MAP_APPEND])
QED

(* The inside order's indices are within the inside requests *)
Theorem is_order_MEM:
  is_order rss order ∧ MEM (d, i) order ⇒ i < LENGTH (rss d)
Proof
  rw[is_order_def] >> first_x_assum (qspec_then ‘d’ mp_tac) >> strip_tac >>
  ‘MEM i (MAP SND (FILTER (λx. FST x = d) order))’
    by (simp[MEM_MAP, MEM_FILTER] >> qexists_tac ‘(d, i)’ >> simp[]) >>
  rfs[MEM_COUNT_LIST]
QED

Theorem replies_ext:
  is_order rss order ∧ (∀c. rss c ≼ rss' c) ⇒ replies rss' order c = replies rss order c
Proof
  rw[replies_def] >>
  ‘MAP (λ(d, i). EL i (rss' d)) order = MAP (λ(d, i). EL i (rss d)) order’
    by (irule MAP_CONG >> simp[FORALL_PROD] >> rpt strip_tac >>
        drule_all is_order_MEM >> strip_tac >>
        first_x_assum (qspec_then ‘p_1’ mp_tac) >> rw[IS_PREFIX_APPEND] >>
        simp[EL_APPEND1]) >>
  simp[]
QED

Theorem LENGTH_replies:
  is_order rss order ⇒ LENGTH (replies rss order c) = LENGTH (rss c)
Proof
  rw[replies_def, is_order_def] >>
  first_x_assum (qspec_then ‘c’ mp_tac) >>
  qmatch_goalsub_abbrev_tac ‘ZIP (order, ans)’ >>
  ‘LENGTH ans = LENGTH order’ by simp[Abbr ‘ans’] >>
  ‘∀(l1 : (word64 # num) list) (l2 : response list). LENGTH l1 = LENGTH l2 ⇒
     LENGTH (FILTER (λ((d,i),a). d = c) (ZIP (l1, l2))) =
     LENGTH (FILTER (λx. FST x = c) l1)’
    by (Induct >> simp[] >> gen_tac >> Cases >> simp[] >>
        Cases_on ‘h’ >> rw[]) >>
  strip_tac >>
  ‘LENGTH (MAP SND (FILTER (λx. FST x = c) order)) = LENGTH (rss c)’
    by (qpat_x_assum ‘MAP SND _ = _’ (fn th => REWRITE_TAC[th]) >>
        simp[LENGTH_COUNT_LIST]) >>
  first_x_assum (qspecl_then [‘order’, ‘ans’] mp_tac) >> fs[]
QED

Theorem print_response_nonempty:
  print_response a ≠ []
Proof
  Cases_on ‘a’ >> simp[print_response_def]
QED

Theorem reply_bytes_APPEND:
  reply_bytes (a ++ b) = reply_bytes a ++ reply_bytes b
Proof
  simp[reply_bytes_def, bytes_def]
QED

Theorem reply_bytes_nil:
  reply_bytes c = [] ⇔ c = []
Proof
  Cases_on ‘c’ >> simp[reply_bytes_def, bytes_def, print_response_nonempty]
QED

Theorem reply_bytes_more:
  c ≠ [] ⇒ ¬(reply_bytes (a ++ c) ≼ reply_bytes a)
Proof
  rw[reply_bytes_APPEND] >> strip_tac >> imp_res_tac IS_PREFIX_LENGTH >>
  fs[] >> ‘reply_bytes c = []’ by (Cases_on ‘reply_bytes c’ >> fs[]) >>
  fs[reply_bytes_nil]
QED

(* ------------------------------------------------------------------------
   Orders, extended
   ------------------------------------------------------------------------ *)

Theorem earlier_APPEND:
  (earlier order x y ⇒ earlier (order ++ ex) x y) ∧
  (MEM x order ∧ MEM y ex ⇒ earlier (order ++ ex) x y)
Proof
  rw[earlier_def] >- (qexistsl_tac [‘l1’, ‘l2’, ‘l3 ++ ex’] >> simp[]) >>
  fs[MEM_SPLIT] >> qexistsl_tac [‘l1’, ‘l2 ++ l1'’, ‘l2'’] >> simp[]
QED

(* The extra requests of connection c, after its first n *)
Definition extra_def:
  extra (rss : word64 -> brequest list) rss' cs =
    FLAT (MAP (λc. GENLIST (λk. (c, LENGTH (rss c) + k))
                           (LENGTH (rss' c) − LENGTH (rss c))) cs)
End

Theorem FILTER_extra:
  ∀cs. ALL_DISTINCT cs ⇒
       FILTER (λx. FST x = c) (extra rss rss' cs) =
       if MEM c cs then GENLIST (λk. (c, LENGTH (rss c) + k))
                                (LENGTH (rss' c) − LENGTH (rss c))
       else []
Proof
  Induct >> simp[extra_def] >> rw[] >> fs[extra_def, FILTER_APPEND] >>
  simp[FILTER_EQ_NIL, EVERY_GENLIST] >>
  ‘FILTER (λx. FST x = c) (GENLIST (λk. (c, LENGTH (rss c) + k))
                                   (LENGTH (rss' c) − LENGTH (rss c))) =
   GENLIST (λk. (c, LENGTH (rss c) + k)) (LENGTH (rss' c) − LENGTH (rss c))’
    by simp[FILTER_EQ_ID, EVERY_GENLIST] >>
  simp[] >> rw[] >> fs[] >> metis_tac[]
QED

Theorem MEM_extra:
  MEM (c, i) (extra rss rss' cs) ⇒ LENGTH (rss c) ≤ i ∧ i < LENGTH (rss' c)
Proof
  rw[extra_def, MEM_FLAT, MEM_MAP, MEM_GENLIST] >> fs[MEM_GENLIST]
QED

Theorem COUNT_LIST_GENLIST_ADD:
  n ≤ m ⇒ COUNT_LIST n ++ GENLIST (λk. k + n) (m − n) = COUNT_LIST m
Proof
  rw[LIST_EQ_REWRITE, EL_APPEND_EQN, LENGTH_COUNT_LIST, EL_COUNT_LIST] >> rw[]
QED

Theorem bytes_written_prefix:
  evs1 ≼ evs ⇒ bytes_written_to c evs1 ≼ bytes_written_to c evs ∧
               bytes_read_from c evs1 ≼ bytes_read_from c evs
Proof
  rw[IS_PREFIX_APPEND] >> simp[bytes_written_to_def, bytes_read_from_def]
QED

(* The fds events name; a connection read from is among them *)
Definition evs_fds_def:
  evs_fds evs = MAP (λev. case ev of IO_event n conf b => bytes_fd conf) evs
End

Theorem read_fd_MEM:
  bytes_read_from c evs ≠ [] ⇒ MEM c (evs_fds evs)
Proof
  Induct_on ‘evs’ >> simp[bytes_read_from_def, evs_fds_def] >> Cases >>
  rename1 ‘IO_event nm _ _’ >> Cases_on ‘nm’ >>
  rw[event_read_def] >> fs[bytes_read_from_def, evs_fds_def]
QED

Theorem brequests_nil:
  brequests rs = [] ⇔ rs = []
Proof
  Cases_on ‘rs’ >> simp[brequests_def, bytes_def] >>
  Cases_on ‘h’ >> simp[print_brequest_def]
QED

Theorem TAKE_prefix_eq:
  a ≼ b ∧ j ≤ LENGTH a ⇒ TAKE j b = TAKE j a
Proof
  rw[IS_PREFIX_APPEND] >> simp[TAKE_APPEND1]
QED

Theorem LPREFIX_fromList_prefix:
  LPREFIX (fromList evs) io ∧ evs1 ≼ evs ⇒ LPREFIX (fromList evs1) io
Proof
  rw[] >> irule LPREFIX_TRANS >> qexists_tac ‘fromList evs’ >>
  simp[LPREFIX_fromList, from_toList]
QED

Theorem is_order_extend:
  is_order rss order ∧ (∀c. rss c ≼ rss' c) ∧ ALL_DISTINCT cs ∧
  (∀c. ¬MEM c cs ⇒ rss' c = []) ⇒
  is_order rss' (order ++ extra rss rss' cs)
Proof
  rw[is_order_def, FILTER_APPEND, FILTER_extra] >>
  first_x_assum (qspec_then ‘c’ assume_tac) >>
  first_x_assum (qspec_then ‘c’ assume_tac) >>
  imp_res_tac IS_PREFIX_LENGTH >> rw[MAP_GENLIST, combinTheory.o_DEF]
  >- (irule COUNT_LIST_GENLIST_ADD >> simp[]) >>
  res_tac >> fs[]
QED

(* MAIN: a linearizable key-value server stays linearizable behind a
   relay *)
Theorem kv_relay_closed:
  relay_run ins outs io io' ∧ kv_safe io ⇒ kv_safe io'
Proof
  rw[kv_safe_def] >> rename1 ‘LPREFIX (fromList evs) io'’ >>
  qpat_x_assum ‘relay_run _ _ _ _’ (strip_assume_tac o REWRITE_RULE [relay_run_def]) >>
  ‘∃t. outs t = evs’ by metis_tac[] >>
  ‘∀c. ∃rs rest. rs ≼ rss c ∧ EVERY valid_brequest rs ∧
                 bytes_read_from c (ins t) = brequests rs ++ rest ∧ no_full_brequest rest’
    by (gen_tac >> irule parse_mono >> conj_tac >- metis_tac[] >>
        qexists_tac ‘rests c’ >>
        qpat_x_assum ‘∀t c. relays _ _’ (qspecl_then [‘t’, ‘c’] mp_tac) >>
        simp[relays_def] >> metis_tac[]) >>
  qpat_x_assum ‘∀c. ∃rs rest. _’ (strip_assume_tac o SIMP_RULE std_ss [SKOLEM_THM]) >>
  qpat_x_assum ‘∀evs rss rests. _’ (qspecl_then [‘ins t’, ‘f’, ‘f'’] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qpat_x_assum ‘outs t = evs’ (SUBST_ALL_TAC o SYM) >>
  ‘∀c. ¬MEM c (nub (evs_fds (outs t))) ⇒ rss c = []’
    by (rw[MEM_nub] >>
        ‘bytes_read_from c (outs t) = []’ by metis_tac[read_fd_MEM] >>
        qpat_x_assum ‘∀c. EVERY valid_brequest (rss c) ∧ _’ (qspec_then ‘c’ mp_tac) >>
        simp[brequests_nil]) >>
  ‘∀c. f c ≼ rss c’ by metis_tac[] >>
  ‘is_order rss (order ++ extra f rss (nub (evs_fds (outs t))))’
    by (irule is_order_extend >> simp[all_distinct_nub]) >>
  qexists_tac ‘order ++ extra f rss (nub (evs_fds (outs t)))’ >>
  qabbrev_tac ‘ex = extra f rss (nub (evs_fds (outs t)))’ >>
  ‘∀c. ∃X. replies rss (order ++ ex) c = replies f order c ++ X’
    by (simp[replies_APPEND] >> metis_tac[replies_ext]) >>
  ‘∀c. bytes_written_to c (outs t) ≼ reply_bytes (replies f order c)’
    by (gen_tac >> irule IS_PREFIX_TRANS >>
        qexists_tac ‘bytes_written_to c (ins t)’ >> simp[] >>
        qpat_x_assum ‘∀t c. relays _ _’ (qspecl_then [‘t’, ‘c’] mp_tac) >>
        simp[relays_def]) >>
  rpt conj_tac >- fs[]
  >- (* real time *)
   (rpt gen_tac >> PairCases_on ‘x’ >> PairCases_on ‘y’ >>
    rename1 ‘precedes _ _ _ (c, i) (d, j)’ >>
    strip_tac >>
    ‘MEM (c, i) order’
      by (CCONTR_TAC >>
          ‘MEM (c, i) ex’ by fs[] >>
          ‘LENGTH (f c) ≤ i ∧ i < LENGTH (rss c)’
            by (fs[Abbr ‘ex’] >> metis_tac[MEM_extra]) >>
          qpat_x_assum ‘∀c. ∃X. _’ (qspec_then ‘c’ strip_assume_tac) >>
          ‘LENGTH (replies f order c) = LENGTH (f c)’ by metis_tac[LENGTH_replies] >>
          ‘LENGTH (replies rss (order ++ ex) c) = LENGTH (rss c)’
            by metis_tac[LENGTH_replies] >>
          ‘LENGTH X = LENGTH (rss c) − LENGTH (f c)’
            by (qpat_x_assum ‘replies rss _ c = _’ (fn th => fs[th])) >>
          ‘TAKE (SUC i) (replies rss (order ++ ex) c) =
           replies f order c ++ TAKE (SUC i − LENGTH (f c)) X’
            by (qpat_x_assum ‘replies rss _ c = _’ SUBST1_TAC >> fs[TAKE_APPEND2]) >>
          ‘TAKE (SUC i − LENGTH (f c)) X ≠ []’
            by (fs[TAKE_EQ_NIL] >> strip_tac >> fs[]) >>
          qpat_x_assum ‘precedes _ _ _ _ _’
            (strip_assume_tac o REWRITE_RULE [precedes_def]) >>
          ‘reply_bytes (replies f order c ++ TAKE (SUC i − LENGTH (f c)) X) ≼
           reply_bytes (replies f order c)’
            by metis_tac[IS_PREFIX_TRANS, bytes_written_prefix] >>
          metis_tac[reply_bytes_more]) >>
    reverse (Cases_on ‘MEM (d, j) order’) >- metis_tac[earlier_APPEND, MEM_APPEND] >>
    irule (CONJUNCT1 earlier_APPEND) >>
    qpat_x_assum ‘∀x y. _ ⇒ earlier order x y’ irule >> simp[] >>
    qpat_x_assum ‘precedes _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [precedes_def]) >>
    simp[precedes_def] >>
    ‘∃t1. t1 ≤ t ∧ outs t1 = evs1’
      by (‘∃t1. outs t1 = evs1’ by metis_tac[LPREFIX_fromList_prefix] >>
          Cases_on ‘t1 ≤ t’ >- metis_tac[] >>
          qexists_tac ‘t’ >> simp[] >>
          ‘outs t ≼ outs t1’ by fs[] >> metis_tac[IS_PREFIX_ANTISYM]) >>
    qexists_tac ‘ins t1’ >>
    qpat_assum ‘∀t c. relays _ _’
      (qspecl_then [‘t1’, ‘c’] (strip_assume_tac o REWRITE_RULE [relays_def])) >>
    qpat_assum ‘∀t c. relays _ _’
      (qspecl_then [‘t1’, ‘d’] (strip_assume_tac o REWRITE_RULE [relays_def])) >>
    rpt conj_tac
    >- fs[]
    >- (qpat_x_assum ‘∀c. ∃X. _’ (qspec_then ‘c’ strip_assume_tac) >>
        ‘i < LENGTH (replies f order c)’ by metis_tac[LENGTH_replies, is_order_MEM] >>
        ‘TAKE (SUC i) (replies rss (order ++ ex) c) = TAKE (SUC i) (replies f order c)’
          by (qpat_x_assum ‘replies rss _ c = _’ SUBST1_TAC >>
              irule TAKE_APPEND1 >> fs[]) >>
        metis_tac[IS_PREFIX_TRANS])
    >- (‘j ≤ LENGTH (f d)’ by metis_tac[is_order_MEM, LESS_IMP_LESS_OR_EQ] >>
        ‘TAKE j (rss d) = TAKE j (f d)’ by metis_tac[TAKE_prefix_eq] >>
        metis_tac[IS_PREFIX_TRANS])) >>
  (* writes *)
  gen_tac >> qpat_x_assum ‘∀c. ∃X. _’ (qspec_then ‘c’ strip_assume_tac) >>
  qpat_x_assum ‘replies rss _ c = _’ SUBST1_TAC >>
  simp[reply_bytes_APPEND] >> metis_tac[IS_PREFIX_TRANS, IS_PREFIX_APPEND3]
QED
