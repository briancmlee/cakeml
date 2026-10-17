(*
  KV liveness through the library (design/34, principled version).

   (with_store answers every query with a store answer: asyncKvLiveStore.)
   The KV handler is the query handler proto_handler_v (asyncProtoV) for
      the bodies parser P_b, the Sock/Kv vocabulary sockV, the query
      Kv (fd, req) and the printed answer, on every history in which its
      queries are answered by the store (kv_proto_agree).  The two differ
      only when a query gets a non-store answer: the KV handler stops,
      proto_handler_v writes regardless.
*)
Theory asyncKvLive
Ancestors
  pair list rich_list arithmetic option pred_set string words
  asyncCore asyncLevel1 asyncTranscript asyncProgress asyncServer
  asyncServerSafety asyncWithStore asyncServerWithK asyncKvHandler
  HttpSpec HttpSpecBodies asyncHttpParseB
  asyncServerV asyncServerVProgress asyncServerVLive asyncServerVLiveA
  asyncServerVLiveP asyncServerVKv asyncProto asyncProtoV asyncProtoB
  asyncKvLiveStore asyncProtoMachineV asyncKvModel HttpKvSpec llist
  asyncProtoLiveV
Libs
  preamble

(* ------------------------------------------------------------------------
   2. The KV handler, as the query handler
   ------------------------------------------------------------------------ *)

(* The response written for a request, given its query's answer *)
Definition kfin_def:
  kfin (req : brequest) (k : HttpSpec$response option) =
    case k of SOME ans => print_response ans | NONE => ""
End

(* The query handler of fd for KV: ask the store Kv (fd, req) *)
Overload kvq = “λfd. proto_handler_v sockV P_b (λreq. SOME (fd, req)) kfin”

(* Two binds of the same computation have the same transcript if their
   continuations do, after each way m can finish *)
Theorem trans_bind_cong:
  asyncLevel1$wf (m : ('ee, 'rr) snapshot list -> ('aa, 'xx option) asyncCore$outcome) ∧
  settled m ∧
  (∀h1 h2 x. g = h1 ++ h2 ∧ first_done m h1 x ∧
             trans (bind m f1) g = trans m h1 ++ trans (f1 x) h2 ⇒
             trans (f1 x) h2 = trans (f2 x) h2) ⇒
  trans (bind m f1) g = trans (bind m f2) g
Proof
  strip_tac >> qspecl_then [‘m’, ‘g’] strip_assume_tac history_split
  >- (‘trans (bind m f1) g = trans m g ∧ trans (bind m f2) g = trans m g’
        by (conj_tac >> irule trans_bind_running >> simp[]) >>
      simp[])
  >> gvs[] >>
  ‘trans (bind m f1) (h1 ++ h2) = trans m h1 ++ trans (f1 x) h2 ∧
   trans (bind m f2) (h1 ++ h2) = trans m h1 ++ trans (f2 x) h2’
    by (conj_tac >> irule trans_bind_continues >> simp[]) >>
  simp[]
QED

Theorem kans_ok_APPEND[local]:
  kans_ok V (l1 ++ l2) ⇔ kans_ok V l1 ∧ kans_ok V l2
Proof
  simp[kans_ok_def] >> metis_tac[]
QED

Theorem kans_ok_CONS[local]:
  kans_ok V (e :: l) ⇔ kans_ok V [e] ∧ kans_ok V l
Proof
  simp[kans_ok_def] >> metis_tac[]
QED

(* sockV's fields, and P_b's parser, applied *)
Theorem sockV_simps[local]:
  sockV.qry q = Kv q ∧ sockV.rd fd = Sock (Read fd) ∧
  sockV.wr fd d = Sock (Write fd d) ∧
  sockV.sact (Kv q) = NONE ∧ sockV.sact (Sock x) = SOME x ∧
  sockV.sres (SockR y) = SOME y ∧ sockV.sres (KvR b) = NONE ∧
  sockV.kans (KvR b) = SOME b ∧ sockV.kans (SockR y) = NONE
Proof
  simp[sockV_def]
QED

Theorem P_b_parse[local]:
  P_b.parse s = b_presult (parse_brequest s)
Proof
  simp[P_b_def]
QED

(* MAIN: on a history in which its queries are answered by the store, the
   KV handler has the query handler's transcript *)
Theorem kv_proto_agree:
  ∀g buf. kans_ok sockV (trans (kv_handler (fd, buf)) g) ⇒
          trans (kv_handler (fd, buf)) g = trans (kvq fd (fd, buf)) g
Proof
  gen_tac >> completeInduct_on ‘LENGTH g’ >> rw[] >>
  pop_assum mp_tac >> ONCE_REWRITE_TAC[kv_handler_unfold, proto_handler_v_unfold] >>
  simp[P_b_parse] >> Cases_on ‘parse_brequest buf’ >> simp[b_presult_def, sockV_simps]
  (* a complete request: the query, then the write *)
  >- (strip_tac >> irule trans_bind_cong >> simp[wf_emit, settled_emit] >>
      rpt strip_tac >> drule first_done_emit >> strip_tac >> gvs[trans_emit] >>
      Cases_on ‘x’ >> fs[Once kans_ok_CONS]
      >- fs[kans_ok_def, sockV_simps] >>
      simp[kfin_def, sockV_simps] >> irule trans_bind_cong >> simp[wf_emit, settled_emit] >>
      rpt strip_tac >> drule first_done_emit >> strip_tac >> gvs[trans_emit] >>
      fs[Once kans_ok_CONS] >> fs[Once kans_ok_CONS] >>
      first_x_assum irule >> simp[])
  (* incomplete: wait, read, continue *)
  >- (strip_tac >> irule trans_bind_cong >> simp[readable_def, wf_wait, settled_wait] >>
      rpt strip_tac >> drule first_done_wait_nonempty >> strip_tac >>
      irule trans_bind_cong >> simp[wf_emit, settled_emit] >>
      rpt strip_tac >> drule first_done_emit >> strip_tac >> gvs[trans_emit] >>
      fs[Once kans_ok_CONS] >>
      ‘LENGTH h2' < LENGTH h1 + SUC (LENGTH h2')’ by (Cases_on ‘h1’ >> fs[]) >>
      Cases_on ‘x’ >> simp[sockV_simps] >>
      TRY (rename1 ‘SockR rr’ >> Cases_on ‘rr’) >> simp[] >>
      qpat_x_assum ‘∀m. _’ irule >> simp[] >>
      qpat_x_assum ‘trans (bind (wait _) _) _ = _’
        (assume_tac o REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
      qpat_x_assum ‘kans_ok _ (trans (bind _ _) _)’ mp_tac >>
      REWRITE_TAC[readable_def] >>
      pop_assum (fn th => REWRITE_TAC [th]) >> simp[Once kans_ok_CONS])
QED

(* ------------------------------------------------------------------------
   3. The KV handler is well behaved
   ------------------------------------------------------------------------ *)

Theorem on_fdk_sock_owner[local]:
  on_fdk fd p ⇔ sock_owner (FST p) = SOME fd
Proof
  PairCases_on ‘p’ >> Cases_on ‘p0’ >> simp[on_fdk_def, on_fd_def]
  >- (rename1 ‘Sock a’ >> Cases_on ‘a’ >> simp[sock_owner_def] >> metis_tac[])
  >> rename1 ‘Kv q’ >> PairCases_on ‘q’ >> simp[sock_owner_def] >> metis_tac[]
QED

(* The KV handler is well behaved: it only touches its own fd *)
Theorem hokv_kv:
  hokv sockV (λfd. kv_handler (fd, ""))
Proof
  rw[hokv_def, wf_kv_handler, settled_kv_handler, on_fd_v_sockV] >>
  qspecl_then [‘g’, ‘""’] mp_tac (Q.GEN ‘fd’ kv_handler_serves |> Q.SPEC ‘fd’) >>
  simp[EVERY_MEM, on_fdk_sock_owner]
QED


(* ------------------------------------------------------------------------
   4. The KV handler's obligation, from the query handler's liveness
   ------------------------------------------------------------------------ *)

(* The query handler of fd answers all of D's complete requests: within
   B D rounds, it has received an answer to each of their queries and
   written the responses (the form of cf-actions' proto_handler_live_va
   with the answer count, for one fd) *)
Definition qfull_def:
  qfull V P ansq fin fd B ⇔
    ∀g j0 D.
      prompt (proto_handler_v V P ansq fin (fd, "")) g ∧
      henv_t fd (λq. sproj V (trans (proto_handler_v V P ansq fin (fd, "")) q)) g j0 D ∧
      j0 + B D ≤ LENGTH g ⇒
      ∃j. j ≤ LENGTH g ∧
          resps ansq fin (proto_all P D)
            (kanswers V (trans (proto_handler_v V P ansq fin (fd, "")) (TAKE j g))) ≼
            written fd (sproj V (trans (proto_handler_v V P ansq fin (fd, "")) (TAKE j g))) ∧
          nq ansq (proto_all P D) ≤
            LENGTH (kanswers V (trans (proto_handler_v V P ansq fin (fd, "")) (TAKE j g)))
End

(* Two computations with the same transcripts on the prefixes of g are
   answered promptly on g together *)
Theorem prompt_cong:
  asyncLevel1$wf (m1 : ('ee, 'rr) snapshot list -> ('aa, 'xx option) asyncCore$outcome) ∧
  asyncLevel1$wf (m2 : ('ee, 'rr) snapshot list -> ('aa, 'yy option) asyncCore$outcome) ∧
  (∀j. j ≤ LENGTH g ⇒ trans m1 (TAKE j g) = trans m2 (TAKE j g)) ⇒
  (prompt m1 g ⇔ prompt m2 g)
Proof
  strip_tac >>
  ‘∀j. j ≤ LENGTH g ⇒ (m1 (TAKE j g)).actions = (m2 (TAKE j g)).actions’
    by metis_tac[MAP_FST_trans] >>
  ‘∀i. i < LENGTH g ⇒
       new_actions (log_of m1) (TAKE i g) = new_actions (log_of m2) (TAKE i g)’
    by (rpt strip_tac >> Cases_on ‘i’
        >- (qpat_x_assum ‘∀j. _ ⇒ (m1 _).actions = _’ (qspec_then ‘0’ mp_tac) >>
            simp[new_actions_def, log_of_def]) >>
        ‘FRONT (TAKE (SUC n) g) = TAKE n g’
          by (‘TAKE (SUC n) g = TAKE n g ++ [EL n g]’ by simp[TAKE_SUC_EL] >>
              simp[FRONT_APPEND]) >>
        ‘(m1 (TAKE (SUC n) g)).actions = (m2 (TAKE (SUC n) g)).actions ∧
         (m1 (TAKE n g)).actions = (m2 (TAKE n g)).actions’ by simp[] >>
        ‘g ≠ []’ by (strip_tac >> fs[]) >>
        simp[new_actions_def, log_of_def]) >>
  simp[prompt_def]
QED

(* With store answers, every received answer is a value *)
Theorem kans_ok_kanswers:
  ∀tr. kans_ok V tr ⇒ EVERY IS_SOME (kanswers V tr)
Proof
  Induct >> simp[kanswers_def] >> PairCases >> rw[] >>
  fs[Once kans_ok_CONS] >> fs[GSYM kanswers_def] >>
  every_case_tac >> fs[kans_ok_def] >> Cases_on ‘V.kans x’ >> fs[]
QED

Theorem nq_kv[local]:
  ∀rs. nq (λreq. SOME (fd, req)) rs = LENGTH rs
Proof
  Induct >> simp[nq_def] >> fs[nq_def]
QED

(* With an answer for each request, the KV responses are printed answers *)
Theorem resps_kv:
  ∀rs ks. LENGTH rs ≤ LENGTH ks ∧ EVERY IS_SOME ks ⇒
          resps (λreq. SOME (fd, req)) kfin rs ks =
          MAP print_response (MAP THE (TAKE (LENGTH rs) ks))
Proof
  Induct >> simp[resps_def] >> rpt gen_tac >> Cases_on ‘ks’ >> simp[] >>
  strip_tac >> fs[IS_SOME_EXISTS, kfin_def]
QED

(* MAIN: the KV handler meets the library's obligation for the KV goal,
   given the query handler's full liveness at every fd *)
Theorem kv_handler_live:
  (∀fd. qfull sockV P_b (λreq. SOME (fd, req)) kfin fd B) ⇒
  handler_live_vp sockV (λfd. kv_handler (fd, "")) kv_goal B
Proof
  rw[handler_live_vp_def] >>
  qpat_x_assum ‘∀fd. qfull _ _ _ _ _ _’ (qspec_then ‘fd’ mp_tac) >> rw[qfull_def] >>
  ‘∀j. j ≤ LENGTH g ⇒
       trans (kv_handler (fd, "")) (TAKE j g) = trans (kvq fd (fd, "")) (TAKE j g)’
    by (rpt strip_tac >> irule kv_proto_agree >> simp[]) >>
  first_x_assum (qspecl_then [‘g’, ‘j0’, ‘D’] mp_tac) >>
  impl_tac
  >- (rpt conj_tac
      >- (‘prompt (kv_handler (fd, "")) g ⇔ prompt (kvq fd (fd, "")) g’
            suffices_by metis_tac[] >>
          irule prompt_cong >> simp[wf_kv_handler, wf_proto_handler_v])
      >- (qpat_x_assum ‘henv_t _ _ _ _ _’ mp_tac >> simp[henv_t_def, hread_t_def])
      >> simp[]) >>
  strip_tac >> qexists_tac ‘j’ >> simp[kv_goal_def] >>
  ‘kans_ok sockV (trans (kvq fd (fd, "")) (TAKE j g))’ by metis_tac[] >>
  drule kans_ok_kanswers >> strip_tac >>
  fs[nq_kv] >>
  qexists_tac ‘MAP THE (TAKE (LENGTH (proto_all P_b D))
                 (kanswers sockV (trans (kvq fd (fd, "")) (TAKE j g))))’ >>
  simp[] >> fs[resps_kv]
QED

(* ------------------------------------------------------------------------
   5. KV liveness
   ------------------------------------------------------------------------ *)

(* MAIN: the KV server is live (HttpKvSpec's kv_live) on the event loop's
   trace, given that the query handler answers all complete requests
   (qfull, at every fd: cf-actions' proto_handler_live_va_full) *)
Theorem kv_live_rounds_qfull:
  (∀fd. qfull sockV P_b (λreq. SOME (fd, req)) kfin fd B) ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ⇒
  kv_live s0
    (LFLATTEN (LGENLIST (λi. fromList (grounds_events (EI lfdn)
       (srelabel (kv_server lfdn)) s0 i)) NONE))
Proof
  rw[kv_server_def, kv_inner_def] >> irule kv_live_from_goal >>
  simp[hokv_kv] >> qexists_tac ‘B’ >> simp[kv_handler_live]
QED

(* The query handler's full liveness, at every fd (from
   proto_handler_live_va_full) *)
Theorem qfull_kv:
  qfull sockV P_b (λreq. SOME (fd, req)) kfin fd
        (λD. (LENGTH D + 2) * (2 * LENGTH (proto_all P_b D) + 3))
Proof
  rw[qfull_def] >>
  metis_tac[proto_handler_live_va_full, proto_ok_b, vocab_ok_sockV, vocab_qok_sockV]
QED

(* MAIN: the KV server is live (HttpKvSpec's kv_live) on the event loop's
   trace, in every fair socket world with one listener *)
Theorem kv_live_rounds:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ⇒
  kv_live s0
    (LFLATTEN (LGENLIST (λi. fromList (grounds_events (EI lfdn)
       (srelabel (kv_server lfdn)) s0 i)) NONE))
Proof
  strip_tac >> irule kv_live_rounds_qfull >> simp[] >>
  qexists_tac ‘λD. (LENGTH D + 2) * (2 * LENGTH (proto_all P_b D) + 3)’ >>
  simp[qfull_kv]
QED
