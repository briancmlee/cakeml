(*
  A pending query makes the next round act (design/37 §5, step C3): if a
  computation's last round emitted a query, and the next snapshot answers
  its actions, it performs a socket action in the next round.

  - NA_emit_*, NA_rd_*: the new actions of emit and readable, then a
    continuation, on any history;
  - proto_v_qreacts: the query handler (a query, once answered, is
    followed by the write);
  - sv_qreacts: the skeleton server_v, from its handlers;
  - store_qreacts: the store server: with_store answers the queries
    itself, so a pending query (kv_pending) makes the store server act in
    the next round, whatever the world does, as long as it answers the
    socket actions.

  For the store server with query handlers (KV's shape):
  store_proto_qreacts (a pending query), store_proto_reacts (a ready
  event the Level 2 store server waits for).

  MAIN: proto_v_qreacts, sv_qreacts, store_qreacts, store_proto_qreacts,
  store_proto_reacts.
*)
Theory storePending
Ancestors
  pair list rich_list arithmetic option pred_set
  asyncCore asyncLevel1 asyncTranscript echoServer echoProgress
  echoCause skeletonV skeletonVProgress skeletonVLive
  protoV withStore withStore2 skeletonVKv skeletonVActs
  protoVActs wrapActs storeReact asyncLevel2 proto2
  echoBlockingWaits
Libs
  preamble

(* ------------------------------------------------------------------------
   New actions of emit and readable
   ------------------------------------------------------------------------ *)

Theorem NA_NIL[local]:
  NA m [] = (m []).actions
Proof
  simp[new_actions_def, log_of_def]
QED

Theorem NA_emit_NIL:
  NA (bind (emit a) f) [] = [a]
Proof
  simp[NA_NIL, bind_emit_NIL]
QED

(* The emit answered by s1: the continuation's new actions *)
Theorem NA_emit_CONS:
  oHD (s1 : ('zev, 'zres) snapshot).results = SOME r ⇒
  NA (bind (emit (a : 'zact))
           (f : 'zres -> ('zev, 'zres) snapshot list -> ('zact, 'zz option) asyncCore$outcome))
     (s1 :: g) = NA (f r) g
Proof
  strip_tac >>
  qpat_assum ‘oHD _ = _’ (fn th => assume_tac (MATCH_MP bind_emit_CONS th)) >>
  Cases_on ‘g’ using SNOC_CASES
  >- (qpat_x_assum ‘oHD _ = _’ (fn th =>
        simp[new_actions_def, log_of_def, bind_emit_NIL,
             GEN_ALL (MATCH_MP bind_emit_CONS th)]))
  >> REWRITE_TAC[SNOC_APPEND, GSYM (CONJUNCT2 APPEND), new_actions_SNOC] >>
  qpat_x_assum ‘oHD _ = _’ (fn th =>
    simp[log_of_def, GEN_ALL (MATCH_MP bind_emit_CONS th)])
QED

(* The emit unanswered: nothing new *)
Theorem NA_emit_unans:
  oHD s1.results = NONE ⇒ NA (bind (emit a) f) (s1 :: g) = []
Proof
  strip_tac >> Cases_on ‘g’ using SNOC_CASES
  >- simp[new_actions_def, log_of_def, bind_emit_NIL, bind_emit_unanswered]
  >> REWRITE_TAC[SNOC_APPEND, GSYM (CONJUNCT2 APPEND), new_actions_SNOC] >>
  simp[log_of_def, bind_emit_unanswered]
QED

(* Both, as one rewrite *)
Theorem NA_emit_CONS_case:
  NA (bind (emit a) f) (s1 :: g) =
  case oHD s1.results of NONE => [] | SOME r => NA (f r) g
Proof
  Cases_on ‘oHD s1.results’ >> simp[NA_emit_unans] >>
  irule NA_emit_CONS >> simp[]
QED

Theorem bind_rd_running[local]:
  (∀n. n ≤ LENGTH h ⇒
       ((readable fd : (event, 'r) snapshot list -> ('a, unit option) asyncCore$outcome)
          (TAKE n h)).result = NONE) ⇒
  (bind (readable fd : (event, 'r) snapshot list -> ('a, unit option) asyncCore$outcome) g h).actions = []
Proof
  strip_tac >>
  ‘bind (readable fd) g h = <| actions := (readable fd h).actions; result := NONE |>’
    by (irule bind_running >> first_assum ACCEPT_TAC) >>
  simp[readable_def, wait_def]
QED

Theorem rd_after[local]:
  first_rd fd h1 ⇒ (bind (readable fd) g (h1 ++ q)).actions = (g () q).actions
Proof
  rw[] >> ‘first_done (readable fd) h1 ()’ by simp[first_done_readable] >>
  drule_then (fn th => REWRITE_TAC[th]) bind_continues_actions >>
  simp[readable_def, wait_def, new_actions_def, log_of_def]
QED

(* After the wait for fd: the continuation's new actions *)
Theorem NA_rd_after:
  first_rd fd h1 ⇒ NA (bind (readable fd) G) (h1 ++ g) = NA (G ()) g
Proof
  strip_tac >> Cases_on ‘g’ using SNOC_CASES
  >- (‘h1 ≠ []’ by (strip_tac >> gvs[first_rd_def, first_some_def]) >>
      ‘h1 = FRONT h1 ++ [LAST h1]’ by simp[APPEND_FRONT_LAST] >>
      pop_assum (fn th => ONCE_REWRITE_TAC[th] >> assume_tac (GSYM th)) >>
      simp[new_actions_SNOC, log_of_def, NA_NIL] >>
      ‘(bind (readable fd) G (FRONT h1)).actions = []’
        by (irule bind_rd_running >> rpt strip_tac >>
            ‘TAKE n (FRONT h1) = TAKE n h1’
              by (qpat_x_assum ‘FRONT h1 ++ _ = h1’
                    (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM th]))) >>
                  simp[TAKE_APPEND1]) >>
            ‘n < LENGTH h1’ by (Cases_on ‘h1’ >> gvs[LENGTH_FRONT]) >>
            gvs[first_rd_def] >> first_x_assum drule >>
            simp[readable_def, wait_def]) >>
      simp[] >>
      ‘h1 = h1 ++ []’ by simp[] >> pop_assum SUBST1_TAC >>
      irule rd_after >> simp[])
  >> REWRITE_TAC[SNOC_APPEND, APPEND_ASSOC] >>
  simp[new_actions_SNOC, log_of_def] >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >>
  qmatch_goalsub_abbrev_tac ‘bind RDY G’ >>
  ‘(bind RDY G (h1 ++ l)).actions = (G () l).actions ∧
   (bind RDY G (h1 ++ (l ++ [x]))).actions = (G () (l ++ [x])).actions’
    by (simp[Abbr ‘RDY’] >> REWRITE_TAC[GSYM APPEND_ASSOC] >>
        conj_tac >> irule rd_after >> simp[]) >>
  ASM_REWRITE_TAC[]
QED

(* Still waiting for fd: nothing new *)
Theorem NA_rd_waiting:
  (∀n. n ≤ LENGTH g ⇒
       ((readable fd : (event, 'r) snapshot list -> ('a, unit option) asyncCore$outcome)
          (TAKE n g)).result = NONE) ⇒
  NA (bind (readable fd : (event, 'r) snapshot list -> ('a, unit option) asyncCore$outcome) G) g = []
Proof
  strip_tac >> Cases_on ‘g’ using SNOC_CASES
  >- (simp[NA_NIL] >> irule bind_rd_running >> simp[])
  >> REWRITE_TAC[SNOC_APPEND] >> simp[new_actions_SNOC, log_of_def] >>
  qmatch_goalsub_abbrev_tac ‘bind RDY G’ >>
  ‘(bind RDY G (l ++ [x])).actions = []’
    by (simp[Abbr ‘RDY’] >> irule bind_rd_running >> fs[SNOC_APPEND]) >>
  simp[]
QED

Theorem NA_return[local]:
  NA (return x) h = []
Proof
  simp[new_actions_def, log_of_def, return_def]
QED

(* ------------------------------------------------------------------------
   The query handler
   ------------------------------------------------------------------------ *)

(* MAIN: a query of the handler, answered by the next snapshot, is
   followed by the write *)
Theorem proto_v_qreacts:
  vocab_ok V ∧ vocab_qok V ⇒
  ∀g buf s q.
    MEM (V.qry q) (NA (proto_handler_v V P ansq fin (fd, buf)) g) ∧ s.results ≠ [] ⇒
    ∃a. MEM a (NA (proto_handler_v V P ansq fin (fd, buf)) (g ++ [s])) ∧ V.sact a ≠ NONE
Proof
  strip_tac >> gen_tac >> measureInduct_on ‘LENGTH g’ >> rpt gen_tac >> strip_tac >>
  ‘∀d. V.qry q ≠ V.wr fd d ∧ V.qry q ≠ V.rd fd’
    by (fs[vocab_ok_def, vocab_qok_def] >> rpt strip_tac >>
        first_x_assum (qspec_then ‘q’ mp_tac) >> simp[]) >>
  qpat_x_assum ‘MEM _ _’ mp_tac >> ONCE_REWRITE_TAC[proto_handler_v_unfold] >>
  Cases_on ‘P.parse buf’ >> simp[NA_return]
  (* a complete request *)
  >- (rename1 ‘PComplete req rest’ >> Cases_on ‘ansq req’ >> simp[]
      (* no query: the write, then the rest *)
      >- (Cases_on ‘g’ >> simp[NA_emit_NIL] >>
          Cases_on ‘oHD h.results’ >> simp[NA_emit_CONS_case] >>
          strip_tac >> first_x_assum (qspec_then ‘t’ mp_tac) >> simp[] >>
          disch_then drule >> simp[])
      (* the query, then the write, then the rest *)
      >> Cases_on ‘g’ >> simp[NA_emit_NIL]
      >- (Cases_on ‘s.results’ >> gvs[] >> simp[NA_emit_CONS_case, NA_emit_NIL] >>
          fs[vocab_ok_def])
      >> Cases_on ‘oHD h.results’ >> simp[NA_emit_CONS_case]
      >> Cases_on ‘t’ >> simp[NA_emit_NIL]
      >> Cases_on ‘oHD h'.results’ >> simp[NA_emit_CONS_case]
      >> strip_tac >> first_x_assum (qspec_then ‘t'’ mp_tac) >> simp[]
      >> disch_then drule >> simp[])
  (* incomplete: the wait, the read, then by its response *)
  >> qmatch_goalsub_abbrev_tac ‘bind RDY G’
  >> qspecl_then [‘RDY’, ‘g’] strip_assume_tac history_split
  >- (‘NA (bind RDY G) g = []’ by (fs[Abbr ‘RDY’] >> irule NA_rd_waiting >> fs[]) >>
      simp[])
  >> ‘x = ()’ by simp[oneTheory.one]
  >> ‘first_rd fd h1’ by gvs[Abbr ‘RDY’, first_done_readable]
  >> ‘h1 ≠ []’ by metis_tac[first_rd_nonempty]
  >> gvs[] >> REWRITE_TAC[GSYM APPEND_ASSOC]
  >> simp[Abbr ‘RDY’, NA_rd_after, Abbr ‘G’]
  >> Cases_on ‘h2’ >> simp[NA_emit_NIL]
  >> Cases_on ‘oHD h.results’ >> simp[NA_emit_CONS_case]
  >> ‘LENGTH t < LENGTH h1 + SUC (LENGTH t)’ by (Cases_on ‘h1’ >> gvs[])
  >> rpt CASE_TAC >> simp[NA_return]
  >> strip_tac >> first_x_assum (qspec_then ‘t’ mp_tac) >> simp[]
  >> disch_then drule >> simp[]
QED

(* ------------------------------------------------------------------------
   The skeleton
   ------------------------------------------------------------------------ *)

Theorem both_NA[local]:
  ∀t. NA (both m1 m2) t = NA m1 (left_view m1 m2 t) ++ NA m2 (right_view m1 m2 t)
Proof
  gen_tac >> Cases_on ‘t’ using SNOC_CASES
  >- simp[NA_NIL, both_def, par_log_def, par_actions_NIL, log_of_def]
  >> REWRITE_TAC[SNOC_APPEND, both_new_actions]
QED

(* The handler facts sv_qreacts needs *)
Definition hqreacts_def:
  hqreacts V hf ⇔
    ∀fd g s q. MEM (V.qry q) (NA (hf fd) g) ∧ s.results ≠ [] ⇒
               sacts_new V (hf fd) (g ++ [s])
End

(* MAIN: a query of the skeleton (one of its handlers'), with the next
   snapshot answering its actions, is followed by a socket action *)
Theorem sv_qreacts:
  vocab_ok V ∧ vocab_qok V ∧ hqreacts V hf ⇒
  ∀h s q. MEM (V.qry q) (NA (server_v V hf lfd) h) ∧
          LENGTH (NA (server_v V hf lfd) h) ≤ LENGTH s.results ⇒
          sacts_new V (server_v V hf lfd) (h ++ [s])
Proof
  strip_tac >>
  ‘∀q l. V.qry q ≠ V.acc l’
    by (fs[vocab_ok_def, vocab_qok_def] >> rpt strip_tac >>
        first_x_assum (qspec_then ‘q’ mp_tac) >> simp[]) >>
  gen_tac >> measureInduct_on ‘LENGTH h’ >> rpt gen_tac >>
  ONCE_REWRITE_TAC[sv_steps] >>
  qmatch_goalsub_abbrev_tac ‘bind RDY G’ >>
  qspecl_then [‘RDY’, ‘h’] strip_assume_tac history_split
  (* still waiting for the listener: nothing *)
  >- (‘NA (bind RDY G) h = []’ by (fs[Abbr ‘RDY’] >> irule NA_rd_waiting >> fs[]) >>
      simp[])
  >> ‘x = ()’ by simp[oneTheory.one]
  >> ‘first_rd lfd h1’ by gvs[Abbr ‘RDY’, first_done_readable]
  >> ‘h1 ≠ []’ by metis_tac[first_rd_nonempty]
  >> gvs[] >> REWRITE_TAC[GSYM APPEND_ASSOC]
  >> simp[Abbr ‘RDY’, NA_rd_after, Abbr ‘G’]
  (* the accept *)
  >> Cases_on ‘h2’
  >- (simp[NA_emit_NIL] >> metis_tac[])
  >> simp[NA_emit_CONS_case] >> Cases_on ‘oHD h.results’ >> simp[]
  >> rename1 ‘oHD s1.results = SOME r’
  >> ‘LENGTH t < LENGTH h1 + SUC (LENGTH t)’ by (Cases_on ‘h1’ >> gvs[])
  >> Cases_on ‘vaccd V r’
  (* no new connection: the server again *)
  >- (simp[sv_after_accept_other] >> strip_tac >>
      first_x_assum (qspec_then ‘t’ mp_tac) >> simp[] >> metis_tac[])
  (* a new connection fd: its handler, beside the rest of the server *)
  >> rename1 ‘vaccd V r = SOME fd’
  >> ‘sv_after_accept V hf lfd r = map (λp. ()) (both (hf fd) (server_v V hf lfd))’
       by (irule sv_after_accept_acc >> simp[])
  >> pop_assum SUBST1_TAC
  >> simp[both_NA, left_view_SNOC_eq, right_view_SNOC_eq]
  >> qabbrev_tac ‘L = left_view (hf fd) (server_v V hf lfd) t’
  >> qabbrev_tac ‘R = right_view (hf fd) (server_v V hf lfd) t’
  >> strip_tac
  (* the handler's query *)
  >- (‘(s with results := TAKE (LENGTH (NA (hf fd) L)) s.results).results ≠ []’
        by (simp[] >> Cases_on ‘NA (hf fd) L’ >> gvs[] >>
            Cases_on ‘s.results’ >> gvs[]) >>
      fs[hqreacts_def] >>
      first_x_assum (qspecl_then [‘fd’, ‘L’,
                                  ‘s with results := TAKE (LENGTH (NA (hf fd) L)) s.results’,
                                  ‘q’] mp_tac) >>
      simp[] >> metis_tac[])
  (* the rest of the server's *)
  >> ‘LENGTH R < LENGTH h1 + SUC (LENGTH t)’ by simp[Abbr ‘R’]
  >> first_x_assum (qspec_then ‘R’ mp_tac) >> simp[]
  >> disch_then (qspecl_then [‘s with results := DROP (LENGTH (NA (hf fd) L)) s.results’, ‘q’]
                   mp_tac)
  >> simp[] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The store
   ------------------------------------------------------------------------ *)

Theorem LENGTH_merge_full[local]:
  ∀acts rs ans.
    LENGTH (socks acts) ≤ LENGTH rs ∧ LENGTH (queries acts) ≤ LENGTH ans ⇒
    LENGTH acts ≤ LENGTH (merge acts rs ans)
Proof
  Induct >> simp[merge_def] >> Cases >> rpt gen_tac >> simp[merge_def, socks_def, queries_def]
  >- (Cases_on ‘rs’ >> simp[] >> fs[GSYM socks_def, GSYM queries_def])
  >> Cases_on ‘ans’ >> simp[] >> fs[GSYM socks_def, GSYM queries_def]
QED

Theorem MEM_socks[local]:
  ∀acts. MEM (Sock x) acts ⇒ socks acts ≠ []
Proof
  Induct >> simp[socks_def] >> rw[] >> fs[GSYM socks_def] >>
  Cases_on ‘h’ >> simp[]
QED

(* MAIN: a pending query makes the store server act in the next round, if
   the world answers its socket actions *)
Theorem store_qreacts:
  asyncLevel1$wf m ∧
  (∀h s q. MEM (Kv q) (NA m h) ∧ LENGTH (NA m h) ≤ LENGTH s.results ⇒
           ∃b. MEM b (NA m (h ++ [s])) ∧
               (sockV : ((echoServer$action, num # 'q) kact, 'b, num # 'q,
                         ('b, echoServer$response) kres) vocab).sact b ≠ NONE) ∧
  kv_pending δ st m h ∧
  LENGTH (socks (NA m (inner_hist δ st m h))) ≤ LENGTH s.results ⇒
  NA (with_store δ st m) (h ++ [s]) ≠ []
Proof
  strip_tac >>
  qabbrev_tac ‘IH = inner_hist δ st m h’ >>
  qabbrev_tac ‘acts = NA m IH’ >>
  ‘∃q. MEM (Kv q) acts’
    by (gvs[kv_pending_def, Abbr ‘acts’, Abbr ‘IH’] >>
        qpat_x_assum ‘queries _ ≠ []’ mp_tac >>
        qspec_tac (‘NA m (inner_hist δ st m h)’, ‘l’) >>
        Induct >> simp[queries_def] >> Cases >> simp[] >> fs[GSYM queries_def] >>
        metis_tac[]) >>
  qabbrev_tac ‘s' = s with results := merge acts s.results
                                        (store_answers δ st (m IH).actions acts)’ >>
  ‘inner_hist δ st m (h ++ [s]) = IH ++ [s']’
    by simp[inner_hist_SNOC, Abbr ‘IH’, Abbr ‘s'’, Abbr ‘acts’] >>
  ‘LENGTH acts ≤ LENGTH s'.results’
    by (simp[Abbr ‘s'’] >> irule LENGTH_merge_full >> simp[] >>
        drule_then (qspec_then ‘IH’ strip_assume_tac) log_new_actions >>
        simp[Abbr ‘acts’, LENGTH_store_answers]) >>
  first_x_assum (qspecl_then [‘IH’, ‘s'’, ‘q’] mp_tac) >> simp[] >> strip_tac >>
  simp[new_actions_with_store] >>
  Cases_on ‘b’ >> fs[sockV_def] >> metis_tac[MEM_socks]
QED

(* ------------------------------------------------------------------------
   The store server with query handlers
   ------------------------------------------------------------------------ *)

(* MAIN: a pending query makes the store server with query handlers act in
   the next round, if the world answers its socket actions *)
Theorem store_proto_qreacts:
  kv_pending δ st (server_v (sockV : ((echoServer$action, num # 'q) kact, 'b, num # 'q,
                   ('b, echoServer$response) kres) vocab)
                     (λfd. proto_handler_v sockV P (ansq fd) (fin fd) (fd, "")) lfd) h ∧
  LENGTH (socks (NA (server_v sockV (λfd. proto_handler_v sockV P (ansq fd) (fin fd) (fd, "")) lfd)
                    (inner_hist δ st
                       (server_v sockV (λfd. proto_handler_v sockV P (ansq fd) (fin fd) (fd, "")) lfd)
                       h))) ≤ LENGTH s.results ⇒
  NA (with_store δ st
        (server_v sockV (λfd. proto_handler_v sockV P (ansq fd) (fin fd) (fd, "")) lfd))
     (h ++ [s]) ≠ []
Proof
  strip_tac >> match_mp_tac store_qreacts >> simp[] >> rpt conj_tac
  >- (irule wf_server_v >> simp[wf_proto_handler_v])
  >> rpt strip_tac >>
  ‘vocab_ok (sockV : ((echoServer$action, num # 'q) kact, 'b, num # 'q,
                   ('b, echoServer$response) kres) vocab) ∧ vocab_qok (sockV : ((echoServer$action, num # 'q) kact, 'b, num # 'q,
                   ('b, echoServer$response) kres) vocab)’ by simp[vocab_ok_sockV, vocab_qok_sockV] >>
  ‘hqreacts (sockV : ((echoServer$action, num # 'q) kact, 'b, num # 'q,
                   ('b, echoServer$response) kres) vocab) (λfd. proto_handler_v sockV P (ansq fd) (fin fd) (fd, ""))’
    by (rw[hqreacts_def] >> irule proto_v_qreacts >> simp[] >> metis_tac[]) >>
  irule sv_qreacts >> simp[] >> qexists_tac ‘q’ >> fs[sockV_def]
QED

Theorem server_v2_run[local]:
  (∀fd. (h2 fd).run = hf fd) ⇒ (server_v2 V h2 lfd).run = server_v V hf lfd
Proof
  strip_tac >>
  ‘∀fd. erase (h2 fd) = hf fd’ by simp[erase_def] >>
  drule erase_server_v2 >> simp[erase_def]
QED

(* MAIN: the store server with query handlers acts in the next round if
   something the Level 2 store server waits for is ready in it *)
Theorem store_proto_reacts:
  Readable x ∈
    waiting_on (with_store2 Always δ st
                  (server_v2 (sockV : ((echoServer$action, num # 'q) kact, 'b, num # 'q,
                   ('b, echoServer$response) kres) vocab)
                     (λfd. proto_handler_v2 sockV P (ansq fd) (fin fd) (fd, "")) lfd)) h ∧
  Readable x ∈ s.ready ⇒
  NA (with_store δ st
        (server_v sockV (λfd. proto_handler_v sockV P (ansq fd) (fin fd) (fd, "")) lfd))
     (h ++ [s]) ≠ []
Proof
  strip_tac >> drule waiting_on_interest >> strip_tac >>
  qmatch_asmsub_abbrev_tac ‘server_v2 sockV H2 lfd’ >>
  qabbrev_tac ‘HF = λfd. proto_handler_v sockV P (ansq fd) (fin fd) (fd, "")’ >>
  ‘(server_v2 sockV H2 lfd).run = server_v sockV HF lfd’
    by (irule server_v2_run >>
        simp[Abbr ‘H2’, Abbr ‘HF’, GSYM erase_def, erase_proto_handler_v2]) >>
  ‘asyncLevel1$wf (server_v sockV HF lfd)’
    by (irule wf_server_v >> simp[Abbr ‘HF’, wf_proto_handler_v]) >>
  qabbrev_tac ‘IH = inner_hist δ st (server_v sockV HF lfd) h’ >>
  (* the skeleton waits for x on the inner history *)
  ‘Readable x ∈ waiting_on (server_v2 sockV H2 lfd) IH’
    by (qpat_x_assum ‘Readable x ∈ (with_store2 _ _ _ _).interest h’ mp_tac >>
        qpat_x_assum ‘((with_store2 _ _ _ _).run h).result = NONE’ mp_tac >>
        simp[with_store2_def, with_store_def, waiting_on_def, Abbr ‘IH’] >> rw[]) >>
  qabbrev_tac ‘acts = NA (server_v sockV HF lfd) IH’ >>
  qabbrev_tac ‘s' = s with results := merge acts s.results
                     (store_answers δ st (server_v sockV HF lfd IH).actions acts)’ >>
  ‘inner_hist δ st (server_v sockV HF lfd) (h ++ [s]) = IH ++ [s']’
    by simp[inner_hist_SNOC, Abbr ‘IH’, Abbr ‘s'’, Abbr ‘acts’] >>
  ‘Readable x ∈ s'.ready’ by simp[Abbr ‘s'’] >>
  ‘vocab_ok (sockV : ((echoServer$action, num # 'q) kact, 'b, num # 'q,
                   ('b, echoServer$response) kres) vocab)’ by simp[vocab_ok_sockV] >>
  ‘hreacts_v (sockV : ((echoServer$action, num # 'q) kact, 'b, num # 'q,
                   ('b, echoServer$response) kres) vocab) H2’
    by (rw[hreacts_v_def, Abbr ‘H2’] >> irule proto2_reacts_s >> simp[] >> metis_tac[]) >>
  ‘sacts_new (sockV : ((echoServer$action, num # 'q) kact, 'b, num # 'q,
                   ('b, echoServer$response) kres) vocab) (server_v2 sockV H2 lfd).run (IH ++ [s'])’
    by (irule sv2_reacts_s >> simp[] >> metis_tac[]) >>
  gvs[] >>
  simp[new_actions_with_store] >>
  Cases_on ‘a’ >> fs[sockV_def] >> metis_tac[MEM_socks]
QED
