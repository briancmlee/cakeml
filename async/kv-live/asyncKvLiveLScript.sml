(*
  KV liveness through the library (asyncKvLiveStore, asyncKvLive) for the
  loop polled through the live interest list (D26, asyncM4LiveInterest),
  by asyncServerVLiveL's server_v_live_p_l and server_v_queue_progress_l.
  The statements are asyncKvLive's with EI replaced by the live list
  KLV lfdn = live [n2w lfdn] (log_of (srelabel (kv_server lfdn))); they
  have no new premise (the KV server never reads its listener, by uses_ok).

  MAIN: kv_live_from_goal_l, kv_live_rounds_l, kv_queue_progress_l.
*)
Theory asyncKvLiveL
Ancestors
  pair list rich_list arithmetic option pred_set string words llist
  asyncCore asyncLevel1 asyncTranscript asyncProgress asyncServer
  asyncServerSafety asyncWithStore asyncServerWithK asyncKvHandler EchoSpec
  HttpSpec HttpSpecBodies HttpKvSpec asyncHttpParseB asyncM4GRounds
  asyncM4GTrans asyncM4Drain asyncM4Queue asyncServerWithLive
  asyncServerV asyncServerVProgress asyncServerVLive asyncServerVLiveA
  asyncServerVLiveP asyncServerVLiveL asyncServerVKv asyncProto asyncProtoB
  asyncProtoV asyncKvLiveStore asyncKvLive asyncKvModel asyncM4LiveInterest
Libs
  preamble

Overload KLV = “λlfdn. asyncM4LiveInterest$live [n2w lfdn : word64]
                         (log_of (srelabel (kv_server lfdn)))”
Overload KM = “λlfdn. srelabel (kv_server lfdn)”

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

(* kv_server_v_goal on the live list *)
Theorem kv_server_v_goal_l:
  hokv sockV (hf : num -> ((asyncServer$action, num # brequest) kact,
                           (HttpSpec$response, asyncServer$response) kres, 'kz) vmach) ∧
  handler_live_vp sockV hf kv_goal B ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ⇒
  ∀δ st0 c n D. HttpSpec$bytes D ≼ sent_upto c n s0 ⇒
  ∃N ks ws. kv_goal D ks ws ∧
     HttpSpec$bytes (FLAT ws) =
       bytes_written_to c
         (FLAT (GENLIST (grounds_events (LVg (with_store δ st0 (server_v sockV hf lfdn)) lfdn)
                  (srelabel (with_store δ st0 (server_v sockV hf lfdn))) s0) N))
Proof
  rpt strip_tac >>
  qspecl_then [‘sockV : ((asyncServer$action, num # brequest) kact, HttpSpec$response,
                         num # brequest, (HttpSpec$response, asyncServer$response) kres) vocab’,
               ‘with_store δ st0’, ‘inner_hist δ st0’, ‘hf’, ‘kv_goal’, ‘B’,
               ‘D’, ‘s0’, ‘lfdn’, ‘c’, ‘n’] mp_tac
    (Q.GENL [‘V’, ‘Wr’, ‘inner’, ‘hf’, ‘Q’, ‘B’, ‘D’, ‘s0’, ‘lfdn’, ‘c’, ‘n’]
       server_v_live_p_l) >>
  simp[vocab_ok_sockV, kv_goal_NIL, wrap_ok_with_store, wrap_kans_with_store] >>
  impl_tac
  >- (fs[hokv_def, on_fd_v_sockV, bytes_def]) >>
  strip_tac >> qexistsl [‘N’, ‘ks’, ‘ws’] >> fs[bytes_def]
QED

(* MAIN: kv_live_from_goal on the live list *)
Theorem kv_live_from_goal_l:
  hokv sockV (hf : num -> ((asyncServer$action, num # brequest) kact,
                           (HttpSpec$response, asyncServer$response) kres, 'kz) vmach) ∧
  handler_live_vp sockV hf kv_goal B ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ⇒
  kv_live s0
    (LFLATTEN (LGENLIST (λi. fromList (grounds_events
       (LVg (with_store δ st0 (server_with_k hf lfdn)) lfdn)
       (srelabel (with_store δ st0 (server_with_k hf lfdn))) s0 i)) NONE))
Proof
  rw[kv_live_def, server_with_k_eq_v] >>
  ‘∃N ks ws. kv_goal (FLAT (MAP print_brequest rs)) ks ws ∧
     HttpSpec$bytes (FLAT ws) =
       bytes_written_to c
         (FLAT (GENLIST (grounds_events (LVg (with_store δ st0 (server_v sockV hf lfdn)) lfdn)
                  (srelabel (with_store δ st0 (server_v sockV hf lfdn))) s0) N))’
    by (irule kv_server_v_goal_l >> fs[brequests_def, bytes_def] >> metis_tac[]) >>
  ‘P_b.print = print_brequest ∧ P_b.valid = valid_brequest’ by simp[P_b_def] >>
  ‘proto_all P_b (FLAT (MAP print_brequest rs)) = rs’
    by (mp_tac (Q.GEN ‘P’ proto_all_printed |> Q.ISPEC ‘P_b’) >>
        simp[proto_ok_b]) >>
  fs[kv_goal_def] >>
  qexistsl [‘FLAT (GENLIST (grounds_events (LVg (with_store δ st0 (server_v sockV hf lfdn)) lfdn)
               (srelabel (with_store δ st0 (server_v sockV hf lfdn))) s0) N)’, ‘ans’] >>
  simp[rounds_LPREFIX, reply_bytes_def] >>
  qpat_x_assum ‘HttpSpec$bytes _ = _’ (SUBST1_TAC o SYM) >>
  REWRITE_TAC[bytes_prefix_sw] >>
  fs[IS_PREFIX_APPEND] >> simp[FLAT_APPEND]
QED

(* kv_live_rounds_qfull on the live list *)
Theorem kv_live_rounds_qfull_l:
  (∀fd. qfull sockV P_b (λreq. SOME (fd, req)) kfin fd B) ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ⇒
  kv_live s0
    (LFLATTEN (LGENLIST (λi. fromList (grounds_events (KLV lfdn) (KM lfdn) s0 i)) NONE))
Proof
  rw[kv_server_def, kv_inner_def] >> irule kv_live_from_goal_l >>
  simp[hokv_kv] >> qexists_tac ‘B’ >> simp[kv_handler_live]
QED

(* MAIN: the KV server is live (HttpKvSpec's kv_live) on the trace of the
   loop polled through the live list, in every fair socket world with one
   listener *)
Theorem kv_live_rounds_l:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  sched_wf s0 ⇒
  kv_live s0
    (LFLATTEN (LGENLIST (λi. fromList (grounds_events (KLV lfdn) (KM lfdn) s0 i)) NONE))
Proof
  strip_tac >> irule kv_live_rounds_qfull_l >> simp[] >>
  qexists_tac ‘λD. (LENGTH D + 2) * (2 * LENGTH (proto_all P_b D) + 3)’ >>
  simp[qfull_kv]
QED

(* MAIN: a pending connection is eventually handed out to the KV server *)
Theorem kv_queue_progress_l:
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ⇒
  ∀k n. queued (n2w lfdn) c k (gstate (KLV lfdn) (KM lfdn) s0 n) ⇒
        ∃N. MEM c (wacc (gperf (KLV lfdn) (KM lfdn) s0 N))
Proof
  rpt strip_tac >>
  fs[kv_server_def, kv_inner_def, server_with_k_eq_v] >>
  irule server_v_queue_progress_l >>
  simp[vocab_ok_sockV, hokv_kv] >>
  conj_tac >- (qexists_tac ‘inner_hist kv_delta (λk. NONE)’ >> simp[wrap_ok_with_store]) >>
  qexistsl [‘k’, ‘n’] >> first_assum ACCEPT_TAC
QED
