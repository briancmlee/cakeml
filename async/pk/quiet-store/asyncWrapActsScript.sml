(*
  The per-action cause through a wrapper (design/37 §5, step B): if Wr is
  a wrapper for V (asyncServerVLive's wrap_ok), every new action of Wr m
  is the socket part of a new action of m, on the inner history, whose
  last snapshot has the outer one's ready set (wrap_new_actions).

  Instance: the skeleton over the Sock/Kv vocabulary, run with a store
  (with_store δ s0 (server_v sockV hf lfd)), accepts only when the
  listener is readable in the new snapshot, and reads g only when g is
  readable in it and g's handler has not finished (store_sv_new_actions).

  KV's shape: the query handlers proto_handler_v sockV P ansq fin under
  the store (store_proto_new_actions).

  MAIN: wrap_new_actions, store_sv_new_actions, store_proto_new_actions.
*)
Theory asyncWrapActs
Ancestors
  pair list rich_list arithmetic option pred_set
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncWithStore asyncServerV asyncServerVProgress asyncServerVLive
  asyncServerVKv asyncSVActs asyncProtoV asyncProtoVActs
Libs
  preamble

Theorem sacts_APPEND:
  ∀l1 l2. sacts V (l1 ++ l2) = sacts V l1 ++ sacts V l2
Proof
  simp[sacts_def]
QED

Theorem MEM_sacts:
  ∀l. MEM x (sacts V l) ⇔ ∃b. MEM b l ∧ V.sact b = SOME x
Proof
  Induct >> simp[] >> rw[] >> every_case_tac >> simp[] >>
  metis_tac[optionTheory.SOME_11, optionTheory.NOT_SOME_NONE]
QED

Theorem TAKE_EL_LAST[local]:
  ∀l. LENGTH l = SUC n ⇒ l = TAKE n l ++ [EL n l]
Proof
  gen_tac >> Cases_on ‘l’ using SNOC_CASES >>
  simp[SNOC_APPEND, TAKE_LENGTH_APPEND, EL_LENGTH_APPEND] >>
  strip_tac >> gvs[TAKE_LENGTH_APPEND, EL_LENGTH_APPEND]
QED

(* The inner history grows by one snapshot, with the outer one's ready set *)
Theorem wrap_inner_SNOC:
  wrap_ok V Wr inner ∧ wf m ⇒
  ∃s'. inner m (q ++ [s]) = inner m q ++ [s'] ∧ s'.ready = s.ready
Proof
  rw[wrap_ok_def] >>
  first_x_assum (qspecl_then [‘m’, ‘q ++ [s]’] strip_assume_tac) >> gvs[] >>
  qexists_tac ‘EL (LENGTH q) (inner m (q ++ [s]))’ >>
  ‘inner m q = TAKE (LENGTH q) (inner m (q ++ [s]))’
    by (first_x_assum (qspec_then ‘LENGTH q’ mp_tac) >>
        simp[TAKE_LENGTH_APPEND]) >>
  conj_tac
  >- (pop_assum SUBST1_TAC >> irule TAKE_EL_LAST >> simp[])
  >> first_x_assum (qspec_then ‘LENGTH q’ mp_tac) >>
  simp[EL_APPEND2]
QED

(* MAIN: Wr m's new actions are socket parts of m's, on the inner history *)
Theorem wrap_new_actions:
  wrap_ok V Wr inner ∧ wf m ∧ MEM a (NA (Wr m) (q ++ [s])) ⇒
  ∃s' b. inner m (q ++ [s]) = inner m q ++ [s'] ∧ s'.ready = s.ready ∧
         V.sact b = SOME a ∧ MEM b (NA m (inner m q ++ [s']))
Proof
  strip_tac >>
  drule_all wrap_inner_SNOC >> disch_then (qspecl_then [‘s’, ‘q’] strip_assume_tac) >>
  qexists_tac ‘s'’ >> simp[] >>
  ‘∀h. (Wr m h).actions = sacts V (m (inner m h)).actions’ by fs[wrap_ok_def] >>
  qpat_x_assum ‘MEM _ _’ mp_tac >>
  simp[new_actions_SNOC, log_of_def] >>
  drule_then (qspecl_then [‘inner m q’, ‘s'’] SUBST1_TAC) wf_log_SNOC >>
  simp[sacts_APPEND, DROP_LENGTH_APPEND, log_of_def, MEM_sacts] >> metis_tac[]
QED

Theorem wrap_new_actions_all[local]:
  ∀V Wr inner. wrap_ok V Wr inner ⇒ ∀m a q s.
  wf m ∧ MEM a (NA (Wr m) (q ++ [s])) ⇒
  ∃s' b. inner m (q ++ [s]) = inner m q ++ [s'] ∧ s'.ready = s.ready ∧
         V.sact b = SOME a ∧ MEM b (NA m (inner m q ++ [s']))
Proof
  rpt strip_tac >> irule wrap_new_actions >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The skeleton over sockV, run with a store
   ------------------------------------------------------------------------ *)

(* Below, sockV is annotated with its type wherever nothing else fixes its
   answer type (under hacts_v, before .sact); the type variables 'zb, 'zq
   are distinctive so that drule cannot capture a goal's *)
(* wrap_new_actions for the store wrapper *)
Theorem store_new_actions:
  asyncLevel1$wf (m : (event, ('zb, asyncServer$response) kres) snapshot list ->
          ((asyncServer$action, num # 'zq) kact, 'zz option) asyncCore$outcome) ∧
  MEM a (NA (with_store (δ : 'zst -> num # 'zq -> 'zb # 'zst) s0 m) (q ++ [s : (event, asyncServer$response) snapshot])) ⇒
  ∃s' b. inner_hist δ s0 m (q ++ [s]) = inner_hist δ s0 m q ++ [s'] ∧
         s'.ready = s.ready ∧
         (sockV : ((asyncServer$action, num # 'zq) kact, 'zb, num # 'zq,
                     ('zb, asyncServer$response) kres) vocab).sact b = SOME a ∧
         MEM b (NA m (inner_hist δ s0 m q ++ [s']))
Proof
  strip_tac >>
  drule_all_then strip_assume_tac
    (MATCH_MP wrap_new_actions_all wrap_ok_with_store) >>
  metis_tac[]
QED

(* sv_new_actions for the Sock/Kv vocabulary *)
Theorem sockV_sv_new_actions:
  hcounts_v (sockV : ((asyncServer$action, num # 'zq) kact, 'zb, num # 'zq,
                     ('zb, asyncServer$response) kres) vocab) hf ∧ hacts_v (sockV : ((asyncServer$action, num # 'zq) kact, 'zb, num # 'zq,
                     ('zb, asyncServer$response) kres) vocab) hf ∧
  MEM a (NA (server_v sockV hf lfd) (q ++ [s])) ⇒
  (∀l. (sockV : ((asyncServer$action, num # 'zq) kact, 'zb, num # 'zq,
                     ('zb, asyncServer$response) kres) vocab).sact a = SOME (Accept l) ⇒
       l = lfd ∧ Readable lfd ∈ s.ready) ∧
  ∀g. (sockV : ((asyncServer$action, num # 'zq) kact, 'zb, num # 'zq,
                     ('zb, asyncServer$response) kres) vocab).sact a = SOME (Read g) ⇒
      Readable g ∈ s.ready ∧
      eofs_v sockV g (trans (server_v sockV hf lfd) (q ++ [s])) <
      accs_v sockV g (trans (server_v sockV hf lfd) (q ++ [s]))
Proof
  strip_tac >>
  ‘vocab_ok (sockV : ((asyncServer$action, num # 'zq) kact, 'zb, num # 'zq,
                     ('zb, asyncServer$response) kres) vocab)’ by simp[vocab_ok_sockV] >>
  drule_all sv_new_actions >> simp[]
QED

(* MAIN: with a store, the skeleton accepts only when the listener is
   readable in the new snapshot, and reads g only when g is readable in it
   and g's handler has not finished *)
Theorem store_sv_new_actions:
  hcounts_v (sockV : ((asyncServer$action, num # 'zq) kact, 'zb, num # 'zq,
                     ('zb, asyncServer$response) kres) vocab) hf ∧
  hacts_v (sockV : ((asyncServer$action, num # 'zq) kact, 'zb, num # 'zq,
                     ('zb, asyncServer$response) kres) vocab) hf ∧
  MEM a (NA (with_store δ s0 (server_v sockV hf lfd))
            (q ++ [s : (event, asyncServer$response) snapshot])) ⇒
  (∀l. a = Accept l ⇒ l = lfd ∧ Readable lfd ∈ s.ready) ∧
  ∀g. a = Read g ⇒
      Readable g ∈ s.ready ∧
      eofs g (trans (with_store δ s0 (server_v sockV hf lfd)) (q ++ [s])) <
      accs g (trans (with_store δ s0 (server_v sockV hf lfd)) (q ++ [s]))
Proof
  strip_tac >>
  ‘asyncLevel1$wf (server_v sockV hf lfd)’ by (irule wf_server_v >> fs[hacts_v_def]) >>
  drule_all store_new_actions >> strip_tac >>
  drule_all sockV_sv_new_actions >> strip_tac >>
  gvs[trans_with_store, sproj_sockV]
QED

(* MAIN: the same for the protocol server with query handlers (KV's
   shape), for every protocol *)
Theorem store_proto_new_actions:
  MEM a (NA (with_store δ s0
               (server_v (sockV : ((asyncServer$action, num # 'zq) kact, 'zb, num # 'zq,
                     ('zb, asyncServer$response) kres) vocab)
                  (λfd. proto_handler_v sockV P ansq fin (fd, "")) lfd))
            (q ++ [s : (event, asyncServer$response) snapshot])) ⇒
  (∀l. a = Accept l ⇒ l = lfd ∧ Readable lfd ∈ s.ready) ∧
  ∀g. a = Read g ⇒
      Readable g ∈ s.ready ∧
      eofs g (trans (with_store δ s0
                       (server_v sockV (λfd. proto_handler_v sockV P ansq fin (fd, "")) lfd))
                    (q ++ [s])) <
      accs g (trans (with_store δ s0
                       (server_v sockV (λfd. proto_handler_v sockV P ansq fin (fd, "")) lfd))
                    (q ++ [s]))
Proof
  strip_tac >> irule store_sv_new_actions >>
  simp[proto_v_hcounts, proto_v_hacts, vocab_ok_sockV, vocab_qok_sockV]
QED
