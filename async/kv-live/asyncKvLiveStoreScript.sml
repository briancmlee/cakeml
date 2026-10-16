(*
  KV liveness through the library, the parts that do not depend on the KV
  handler (design/34, principled version).

   - wrap_kans_with_store: with_store answers every query of the inner
     computation with a store answer (KvR).
   - server_with_k_eq_v: the KV skeleton is the library's, for sockV.
   - kv_live_from_goal (MAIN): kv_live for the loop's trace of
     with_store δ st0 (server_with_k hf lfdn), for ANY handler hf that only
     touches its own fd and meets the KV goal kv_goal (as many printed
     answers written as D has complete requests) in the library's sense
     (handler_live_vp).
*)
Theory asyncKvLiveStore
Ancestors
  pair list rich_list arithmetic option pred_set string words llist
  asyncCore asyncLevel1 asyncTranscript asyncProgress asyncServer
  asyncServerSafety asyncWithStore asyncServerWithK EchoSpec
  HttpSpec HttpSpecBodies HttpKvSpec asyncHttpParseB asyncM4GRounds
  asyncM4GTrans asyncM4Drain asyncServerWithLive
  asyncServerV asyncServerVProgress asyncServerVLive asyncServerVLiveA
  asyncServerVLiveP asyncServerVKv asyncProto asyncProtoB
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
  rename1 ‘TAKE k (inner_hist _ _ _ _)’ >>
  Cases_on ‘k < LENGTH h’ >> fs[zipr_NIL_NONE] >>
  gvs[EL_inner_hist] >> drule zipr_merge_kv >> strip_tac >> simp[]
QED


(* ------------------------------------------------------------------------
   3. The KV server is the library's skeleton
   ------------------------------------------------------------------------ *)

(* MAIN: server_with_k is the skeleton for the Sock/Kv vocabulary *)
Theorem server_with_k_eq_v:
  server_with_k h = server_v sockV h
Proof
  simp[server_with_k_def, server_v_def] >> AP_TERM_TAC >>
  simp[FUN_EQ_THM, server_with_k_body_def, server_v_body_def, sockV_def] >> rpt gen_tac >>
  AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM] >> rpt gen_tac >>
  AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM] >> Cases >> simp[vaccd_def, sockV_def] >>
  CASE_TAC >> simp[]
QED

(* ------------------------------------------------------------------------
   4. kv_live, from the per-handler goal
   ------------------------------------------------------------------------ *)

(* What kv_live asks of a handler for data D: as many printed answers
   written as D has complete requests *)
Definition kv_goal_def:
  kv_goal D (ks : HttpSpec$response option list) ws ⇔
    ∃ans. LENGTH ans = LENGTH (proto_all P_b D) ∧ MAP print_response ans ≼ ws
End

Theorem proto_all_b_NIL[local]:
  proto_all P_b [] = []
Proof
  simp[Once proto_all_def] >> CASE_TAC >> simp[]
QED

Theorem kv_goal_NIL[local]:
  kv_goal "" [] []
Proof
  simp[kv_goal_def, proto_all_b_NIL]
QED

(* The library theorem for the KV vocabulary, the store and the KV goal *)
Theorem kv_server_v_goal:
  hokv sockV (hf : num -> ((asyncServer$action, num # brequest) kact,
                           (HttpSpec$response, asyncServer$response) kres, 'kz) vmach) ∧
  handler_live_vp sockV hf kv_goal B ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ⇒
  ∀δ st0 c n D. HttpSpec$bytes D ≼ sent_upto c n s0 ⇒
  ∃N ks ws. kv_goal D ks ws ∧
     HttpSpec$bytes (FLAT ws) =
       bytes_written_to c
         (FLAT (GENLIST (grounds_events (EI lfdn)
                  (srelabel (with_store δ st0 (server_v sockV hf lfdn))) s0) N))
Proof
  rpt strip_tac >>
  qspecl_then [‘sockV : ((asyncServer$action, num # brequest) kact, HttpSpec$response,
                         num # brequest, (HttpSpec$response, asyncServer$response) kres) vocab’,
               ‘with_store δ st0’, ‘inner_hist δ st0’, ‘hf’, ‘kv_goal’, ‘B’,
               ‘D’, ‘s0’, ‘lfdn’, ‘c’, ‘n’] mp_tac
    (Q.GENL [‘V’, ‘Wr’, ‘inner’, ‘hf’, ‘Q’, ‘B’, ‘D’, ‘s0’, ‘lfdn’, ‘c’, ‘n’]
       server_v_live_p) >>
  simp[vocab_ok_sockV, kv_goal_NIL, wrap_ok_with_store, wrap_kans_with_store] >>
  impl_tac
  >- (fs[hokv_def, on_fd_v_sockV, bytes_def]) >>
  strip_tac >> qexistsl [‘N’, ‘ks’, ‘ws’] >> fs[bytes_def]
QED

(* MAIN: kv_live for the loop's trace of the store-wrapped skeleton, for
   any handler meeting the KV goal *)
Theorem kv_live_from_goal:
  hokv sockV (hf : num -> ((asyncServer$action, num # brequest) kact,
                           (HttpSpec$response, asyncServer$response) kres, 'kz) vmach) ∧
  handler_live_vp sockV hf kv_goal B ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ⇒
  kv_live s0
    (LFLATTEN (LGENLIST (λi. fromList (grounds_events (EI lfdn)
       (srelabel (with_store δ st0 (server_with_k hf lfdn))) s0 i)) NONE))
Proof
  rw[kv_live_def, server_with_k_eq_v] >>
  ‘∃N ks ws. kv_goal (FLAT (MAP print_brequest rs)) ks ws ∧
     HttpSpec$bytes (FLAT ws) =
       bytes_written_to c
         (FLAT (GENLIST (grounds_events (EI lfdn)
                  (srelabel (with_store δ st0 (server_v sockV hf lfdn))) s0) N))’
    by (irule kv_server_v_goal >> fs[brequests_def, bytes_def] >> metis_tac[]) >>
  ‘P_b.print = print_brequest ∧ P_b.valid = valid_brequest’ by simp[P_b_def] >>
  ‘proto_all P_b (FLAT (MAP print_brequest rs)) = rs’
    by (mp_tac (Q.GEN ‘P’ proto_all_printed |> Q.ISPEC ‘P_b’) >>
        simp[proto_ok_b]) >>
  fs[kv_goal_def] >>
  qexistsl [‘FLAT (GENLIST (grounds_events (EI lfdn)
               (srelabel (with_store δ st0 (server_v sockV hf lfdn))) s0) N)’, ‘ans’] >>
  simp[rounds_LPREFIX, reply_bytes_def] >>
  qpat_x_assum ‘HttpSpec$bytes _ = _’ (SUBST1_TAC o SYM) >>
  REWRITE_TAC[bytes_prefix_sw] >>
  fs[IS_PREFIX_APPEND] >> simp[FLAT_APPEND]
QED
