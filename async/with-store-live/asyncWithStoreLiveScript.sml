(*
  with_store answers promptly (design/34 §2.5), the fact that liveness of
  a server under with_store needs: if the world answers with_store δ s0 m
  promptly, then every Kv query that m emits in round n is answered by the
  store, in the snapshot that ends round n of m's (inner) history, with a
  KvR answer at the query's position; every Sock action with a SockR one.

  So m runs on a prompt history (as prompt_with_store says), and its queries never
  wait: under the event loop, a handler of server_with_k sees each answer
  one round after its query, exactly as for a socket action.
*)
Theory asyncWithStoreLive
Ancestors
  list rich_list arithmetic asyncCore asyncLevel1 asyncTranscript
  asyncProgress asyncWithStore
Libs
  BasicProvers

(* merge puts a KvR answer at every query and a SockR result at every
   socket action, when there are enough of both *)
Theorem merge_EL:
  ∀acts rs ans k.
    LENGTH (socks acts) ≤ LENGTH rs ∧ LENGTH (queries acts) ≤ LENGTH ans ∧
    k < LENGTH acts ⇒
    (∀q. EL k acts = Kv q ⇒ ∃b. EL k (merge acts rs ans) = KvR b) ∧
    (∀x. EL k acts = Sock x ⇒ ∃r. EL k (merge acts rs ans) = SockR r)
Proof
  Induct >> simp[] >> Cases >> rpt gen_tac >> strip_tac >>
  simp[merge_def]
  >- (Cases_on ‘rs’ >> fs[] >> Cases_on ‘k’ >> fs[])
  >> Cases_on ‘ans’ >> fs[] >> Cases_on ‘k’ >> fs[]
QED

(* MAIN: with a prompt world, the store answers each query of round n in
   the next snapshot of the inner history *)
Theorem with_store_answers:
  wf m ∧ prompt (with_store δ s0 m) h ∧ n < LENGTH h ∧
  k < LENGTH (new_actions (log_of m) (inner_hist δ s0 m (TAKE n h))) ⇒
  (∀q. EL k (new_actions (log_of m) (inner_hist δ s0 m (TAKE n h))) = Kv q ⇒
       ∃b. EL k (EL n (inner_hist δ s0 m h)).results = KvR b) ∧
  (∀x. EL k (new_actions (log_of m) (inner_hist δ s0 m (TAKE n h))) = Sock x ⇒
       ∃r. EL k (EL n (inner_hist δ s0 m h)).results = SockR r)
Proof
  strip_tac >>
  qabbrev_tac ‘acts = new_actions (log_of m) (inner_hist δ s0 m (TAKE n h))’ >>
  ‘(EL n (inner_hist δ s0 m h)).results =
     merge acts (EL n h).results
       (store_answers δ s0 (m (inner_hist δ s0 m (TAKE n h))).actions acts)’
    by gs[EL_inner_hist, GSYM inner_hist_TAKE, Abbr ‘acts’] >>
  pop_assum SUBST1_TAC >>
  irule merge_EL >> simp[] >>
  (* the world answered with_store's (= m's socket) actions *)
  conj_tac
  >- (qpat_x_assum ‘prompt _ _’ mp_tac >> simp[prompt_def] >>
      disch_then (qspec_then ‘n’ mp_tac) >>
      simp[new_actions_with_store, GSYM inner_hist_TAKE, Abbr ‘acts’, responses_at_def]) >>
  (* the store answered all of the round's queries *)
  drule_then (qspec_then ‘inner_hist δ s0 m (TAKE n h)’ strip_assume_tac) log_new_actions >>
  simp[Abbr ‘acts’] >> pop_assum SUBST1_TAC >> simp[LENGTH_store_answers]
QED
