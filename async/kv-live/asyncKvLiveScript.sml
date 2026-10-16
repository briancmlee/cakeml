(*
  KV liveness through the library (design/34, principled version).

   1. with_store answers every query with a store answer (KvR):
      wrap_kans_with_store.
   2. The KV handler is the query handler proto_handler_v (asyncProtoV) for
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
Libs
  preamble

(* ------------------------------------------------------------------------
   1. The store answers queries
   ------------------------------------------------------------------------ *)

Theorem zipr_NIL_NONE[local]:
  ∀acts. ¬MEM (a, SOME x) (zipr acts [])
Proof
  Induct >> simp[zipr_def]
QED

(* In a round of the inner history, a query's response is the store's *)
Theorem zipr_merge_kv:
  ∀acts rs ans q x.
    MEM (Kv q, SOME x) (zipr acts (merge acts rs ans)) ⇒ ∃b. x = KvR b
Proof
  Induct >> simp[zipr_def, merge_def] >> Cases >> rpt gen_tac >> simp[merge_def]
  >- (Cases_on ‘rs’ >> simp[zipr_def, zipr_NIL_NONE] >> metis_tac[])
  >> Cases_on ‘ans’ >> simp[zipr_def, zipr_NIL_NONE] >> rw[] >> metis_tac[]
QED

(* MAIN: with_store answers every query of the inner computation with a
   store answer *)
Theorem wrap_kans_with_store:
  wrap_kans sockV (with_store δ s0) (inner_hist δ s0)
Proof
  rw[wrap_kans_def, kans_ok_def, trans_def, MEM_FLAT, MEM_GENLIST] >>
  Cases_on ‘a’ >> fs[sockV_def] >>
  gvs[round_trans_def, responses_at_def] >>
  Cases_on ‘n < LENGTH h’ >> fs[zipr_NIL_NONE] >>
  gvs[EL_inner_hist] >> drule zipr_merge_kv >> strip_tac >> simp[]
QED

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

(* MAIN: on a history in which its queries are answered by the store, the
   KV handler has the query handler's transcript *)
Theorem kv_proto_agree:
  ∀g buf. kans_ok sockV (trans (kv_handler (fd, buf)) g) ⇒
          trans (kv_handler (fd, buf)) g = trans (kvq fd (fd, buf)) g
Proof
  gen_tac >> completeInduct_on ‘LENGTH g’ >> rw[] >>
  pop_assum mp_tac >> ONCE_REWRITE_TAC[kv_handler_unfold, proto_handler_v_unfold] >>
  simp[P_b_def] >> Cases_on ‘parse_brequest buf’ >> simp[b_presult_def, sockV_def]
  (* a complete request: the query, then the write *)
  >- (strip_tac >> irule trans_bind_cong >> simp[wf_emit, settled_emit] >>
      rpt strip_tac >> drule first_done_emit >> strip_tac >> gvs[trans_emit] >>
      Cases_on ‘x’ >> fs[kans_ok_APPEND]
      >- fs[kans_ok_def] >>
      simp[kfin_def] >> irule trans_bind_cong >> simp[wf_emit, settled_emit] >>
      rpt strip_tac >> drule first_done_emit >> strip_tac >> gvs[trans_emit] >>
      fs[kans_ok_APPEND] >>
      first_x_assum irule >> simp[sockV_def])
  (* incomplete: wait, read, continue *)
  >- (strip_tac >> irule trans_bind_cong >> simp[readable_def, wf_wait, settled_wait] >>
      rpt strip_tac >> drule first_done_wait_nonempty >> strip_tac >>
      irule trans_bind_cong >> simp[wf_emit, settled_emit] >>
      rpt strip_tac >> drule first_done_emit >> strip_tac >> gvs[trans_emit] >>
      fs[kans_ok_APPEND] >>
      ‘LENGTH h2' < LENGTH h1 + SUC (LENGTH h2')’ by (Cases_on ‘h1’ >> fs[]) >>
      Cases_on ‘x’ >> simp[]
      >- (rename1 ‘SockR rr’ >> Cases_on ‘rr’ >> simp[] >>
          first_x_assum irule >> simp[sockV_def])
      >> first_x_assum irule >> simp[sockV_def])
QED
