(*
  The store server's run becomes stable after the last arrival (design/37
  §5, step C: proto_stable's analogue for stateful servers), for every
  protocol P with proto_ok P and query handlers that tag their queries
  with their fd (KV's shape).

  - From some round on, the polling run performs no actions
    (storeSafe's store_acts_stop).
  - Then no query is pending: a pending query would be answered by the
    store in the next round, and the handler would write
    (storePending's store_proto_qreacts).
  - And nothing the Level 2 store server waits for is ready: what it waits
    for is polled (the listener, or a connection the server accepted,
    storeAcc's store_acc), would stay ready (no actions, no
    arrivals), and would make the server act in the next round
    (store_proto_reacts).

  With R1's loop variant (design/37 §4), the first two facts say the loop
  stops polling Always, and the third that it then sleeps.

  MAIN: store_stable.
*)
Theory storeStable
Ancestors
  pair list rich_list arithmetic option pred_set llist alist words
  asyncCore asyncLevel1 asyncLevel2 asyncTranscript echoServer
  echoServerSafety socketWorld socketFair loopPollWorld
  loopRounds loopRoundsTrans loopSockInv relabel
  relabelDist echoSockModel echoRunOk loopPollDyn
  echoLiveSched echoLiveProg echoBlockingWaits skeletonRunOk
  quietRounds echoStable skeletonV skeletonVProgress
  skeletonVLive protoInterface protoV proto2 protoMeasure
  withStore withStore2 skeletonVKv skeletonVActs
  protoVActs wrapActs stableGen storeSafe
  storeReact storeAcc storePending QuietSpec
Libs
  preamble

(* The store server with query handlers, at Level 1 and at Level 2 *)
Overload HQ = “λP ansq fin fd. proto_handler_v sockV P (ansq fd) (fin fd) (fd, "")”
Overload SM = “λδ st P ansq fin lfdn.
  with_store δ st (server_v sockV (λfd. proto_handler_v sockV P (ansq fd) (fin fd) (fd, "")) lfdn)”
Overload SM2 = “λδ st P ansq fin lfdn.
  with_store2 Always δ st
    (server_v2 sockV (λfd. proto_handler_v2 sockV P (ansq fd) (fin fd) (fd, "")) lfdn)”

Theorem gres_idle[local]:
  gacts ifds m s0 n = [] ⇒ gres ifds m s0 n = []
Proof
  simp[gres_def, sock_acts_tot_def, sock_acts_def]
QED

Theorem gstate_idle[local]:
  gacts ifds m s0 n = [] ⇒ gstate ifds m s0 (SUC n) = tick (gstate ifds m s0 n)
Proof
  simp[gstate_SUC, gmid_def, sock_acts_tot_def, sock_acts_def]
QED

Theorem is_ready_tick[local]:
  next_step s = [] ⇒ (is_ready (tick s) w ⇔ is_ready s w)
Proof
  strip_tac >> drule tick_static >> simp[is_ready_def]
QED

(* The store server uses the socket API correctly *)
Theorem store_uses_ok:
  (∀fd req q. ansq fd req = SOME q ⇒ FST q = fd) ⇒
  uses_ok lfdn (SM δ st P ansq fin lfdn)
Proof
  strip_tac >> irule uses_ok_wrap >> simp[vocab_ok_sockV] >>
  rpt conj_tac >>
  TRY (qexists_tac ‘inner_hist δ st’ >> simp[wrap_ok_with_store] >> NO_TAC) >>
  rw[hokv_def, wf_proto_handler_v, settled_proto_handler_v] >>
  irule proto_v_own >> simp[vocab_ok_sockV] >>
  rw[sockV_def] >> PairCases_on ‘q’ >> simp[sock_owner_def] >> res_tac >> fs[]
QED

(* Round n's actions, from the store server's on the run's history *)
Theorem store_gacts:
  gacts ifds (srelabel m) s0 n = MAP sfa (NA m (MAP sfs (ghist ifds (srelabel m) s0 n)))
Proof
  simp[gacts_def, new_actions_relabel]
QED

(* What the Level 2 store server waits for is polled *)
Theorem store_waiting_polled:
  (∀fd req q. ansq fd req = SOME q ⇒ FST q = fd) ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  Readable x ∈ waiting_on (SM2 δ st P ansq fin lfdn)
                 (MAP sfs (ghist (EI lfdn) (srelabel (SM δ st P ansq fin lfdn)) s0 n)) ⇒
  x < dimword (:64) ∧
  MEM (n2w x) (EI lfdn (ghist (EI lfdn) (srelabel (SM δ st P ansq fin lfdn)) s0 n))
Proof
  strip_tac >>
  ‘uses_ok lfdn (SM δ st P ansq fin lfdn)’ by metis_tac[store_uses_ok] >>
  ‘grun_ok (EI lfdn) (srelabel (SM δ st P ansq fin lfdn)) s0’
    by (irule gen_grun_ok >> metis_tac[]) >>
  drule store_acc >> strip_tac
  >- (gvs[] >> metis_tac[interest_accepted, MEM])
  >> qabbrev_tac ‘TT = TSg (SM δ st P ansq fin lfdn) (EI lfdn) s0 n’ >>
  ‘MEM x (accepted TT)’
    by (CCONTR_TAC >>
        ‘FILTER ($= x) (accepted TT) = []’
          by (simp[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
        gvs[accs_accepted, Abbr ‘TT’]) >>
  ‘MEM x (MAP w2n (wacc (gperf (EI lfdn) (srelabel (SM δ st P ansq fin lfdn)) s0 n)))’
    by (drule_all gen_sinv >>
        disch_then (qspecl_then [‘EI lfdn’, ‘n’] strip_assume_tac) >>
        drule gen_trans_split >> strip_tac >>
        drule TREL_accepted >> drule TREL_NONE >> rpt strip_tac >>
        gvs[Abbr ‘TT’, accepted_NONE]) >>
  gvs[MEM_MAP] >> conj_tac >- (qspec_then ‘y’ mp_tac w2n_lt >> simp[]) >>
  metis_tac[interest_accepted]
QED

(* MAIN (Q1 for stateful servers): in a world where only finitely many
   things arrive, the polling run of the store server reaches a round after
   which it performs no actions, no query is pending, and nothing the
   Level 2 store server waits for is ready *)
Theorem store_stable:
  proto_ok P ∧ (∀fd req q. ansq fd req = SOME q ⇒ FST q = fd) ∧
  s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧ lfdn < dimword (:64) ∧
  arrivals_finite s0 ⇒
  ∃n1. ∀n. n1 ≤ n ⇒
    gacts (EI lfdn) (srelabel (SM δ st P ansq fin lfdn)) s0 n = [] ∧
    ¬kv_pending δ st (server_v sockV (HQ P ansq fin) lfdn)
       (MAP sfs (ghist (EI lfdn) (srelabel (SM δ st P ansq fin lfdn)) s0 n)) ∧
    ∀x. Readable x ∈ waiting_on (SM2 δ st P ansq fin lfdn)
                       (MAP sfs (ghist (EI lfdn) (srelabel (SM δ st P ansq fin lfdn)) s0 n)) ⇒
        ¬is_ready (gstate (EI lfdn) (srelabel (SM δ st P ansq fin lfdn)) s0 n) (n2w x)
Proof
  strip_tac >>
  drule_all_then (Q.ISPECL_THEN [‘δ’, ‘st’, ‘fin’] strip_assume_tac) store_acts_stop >>
  qexists_tac ‘n1’ >> rpt gen_tac >> strip_tac >>
  qabbrev_tac ‘SW = SM δ st P ansq fin lfdn’ >>
  qabbrev_tac ‘HH = MAP sfs (ghist (EI lfdn) (srelabel SW) s0 n)’ >>
  ‘gacts (EI lfdn) (srelabel SW) s0 n = [] ∧
   gacts (EI lfdn) (srelabel SW) s0 (SUC n) = []’ by simp[Abbr ‘SW’] >>
  ‘gres (EI lfdn) (srelabel SW) s0 n = []’ by (irule gres_idle >> fs[]) >>
  qabbrev_tac ‘SS = sfs (ssnap (FILTER (is_ready (gstate (EI lfdn) (srelabel SW) s0 (SUC n)))
                                       (EI lfdn (ghist (EI lfdn) (srelabel SW) s0 n))) [])’ >>
  (* round n + 1 has no actions: the server does nothing with SS *)
  ‘NA SW (HH ++ [SS]) = []’
    by (qpat_x_assum ‘gacts _ _ _ (SUC n) = []’ mp_tac >>
        REWRITE_TAC[gen_gacts_SUC] >>
        qpat_x_assum ‘gres _ _ _ n = []’ (fn th => REWRITE_TAC[th]) >>
        simp[Abbr ‘SS’, Abbr ‘HH’]) >>
  rpt conj_tac
  >- simp[Abbr ‘SW’]
  (* no pending query *)
  >- (strip_tac >>
      ‘NA SW (HH ++ [SS]) ≠ []’ suffices_by simp[] >>
      qunabbrev_tac ‘SW’ >> match_mp_tac store_proto_qreacts >> simp[] >>
      ‘asyncLevel1$wf (server_v sockV (HQ P ansq fin) lfdn)’
        by (irule wf_server_v >> simp[wf_proto_handler_v]) >>
      ‘NA (SM δ st P ansq fin lfdn) HH = []’
        by (qpat_x_assum ‘gacts _ _ _ n = []’ mp_tac >> REWRITE_TAC[store_gacts] >>
            simp[Abbr ‘HH’]) >>
      qpat_x_assum ‘NA _ HH = []’ mp_tac >>
      simp[new_actions_with_store])
  (* nothing waited for is ready *)
  >> rpt strip_tac >>
  ‘x < dimword (:64) ∧ MEM (n2w x) (EI lfdn (ghist (EI lfdn) (srelabel SW) s0 n))’
    by (qpat_x_assum ‘Readable x ∈ _’ mp_tac >> simp[Abbr ‘HH’, Abbr ‘SW’] >>
        strip_tac >> drule_at (Pos last) store_waiting_polled >>
        impl_tac >- (simp[] >> metis_tac[]) >> simp[]) >>
  ‘next_step (gstate (EI lfdn) (srelabel SW) s0 n) = []’ by fs[] >>
  ‘is_ready (gstate (EI lfdn) (srelabel SW) s0 (SUC n)) (n2w x)’
    by (‘gstate (EI lfdn) (srelabel SW) s0 (SUC n) = tick (gstate (EI lfdn) (srelabel SW) s0 n)’
          by (irule gstate_idle >> fs[]) >>
        simp[is_ready_tick]) >>
  ‘NA SW (HH ++ [SS]) ≠ []’ suffices_by simp[] >>
  qunabbrev_tac ‘SW’ >> match_mp_tac store_proto_reacts >>
  simp[Abbr ‘SS’, snap_map_def, ssnap_def, sfe_def, MEM_FILTER] >>
  qexists_tac ‘n2w x’ >> simp[]
QED
