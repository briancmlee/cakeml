(*
  G2, top: kv_peer_valid_sys's hypotheses from per-trace clauses of the
  three programs' claims, for an infinite run of client 0, proxy 1, KV 2:
   - ¬free0 and no_fd0 for client and proxy, from "the trace starts with
     the check of fd 0 (D33 stdio_open) and never closes fd 0" (free0_stdio;
     moonshotW2.l0sys_no_fd0 through irun_steps);
   - the topology (no_conn_to) from "every connect is to a" (client, T4),
     "every connect episode is to b" (proxy; with ¬free0, its socketless
     connects may go anywhere) and "no connect" (KV);
   - relay_ok and csend_ok from the proxy's and the client's clauses
     (relay_ok_of_ep, csend_ok_of_client).
*)
Theory moonshotLiveG2
Ancestors
  moonshotLiveRelayWorld moonshotLiveRelay moonshotLiveAccepts moonshotW2 moonshotProxyGlue
  moonshotLiveProjInf moonshotLiveStmts l0sysFair l0sys l0sysEpisodes Marshalling
Libs
  preamble

(* A finite stretch of an infinite run *)
Theorem irun_steps_from:
  (∀n. sys_step (ss n) (rs n) (ss (SUC n))) ⇒
  ∀n m. sys_steps (ss m) (GENLIST (λi. rs (m + i)) n) (GENLIST (λi. ss (m + i)) (SUC n))
Proof
  strip_tac >> Induct >- simp[sys_steps_def] >> gen_tac >>
  ‘GENLIST (λi. rs (m + i)) (SUC n) = rs m :: GENLIST (λi. rs (SUC m + i)) n’
    by (rewrite_tac[GENLIST_CONS] >> simp[GENLIST_FUN_EQ, ADD_CLAUSES]) >>
  ‘GENLIST (λi. ss (m + i)) (SUC (SUC n)) = ss m :: GENLIST (λi. ss (SUC m + i)) (SUC n)’
    by (CONV_TAC (LAND_CONV (REWR_CONV GENLIST_CONS)) >> simp[GENLIST_FUN_EQ, ADD_CLAUSES]) >>
  ntac 2 (pop_assum SUBST1_TAC) >> rewrite_tac[sys_steps_def] >>
  qexistsl_tac [‘ss (SUC m)’, ‘GENLIST (λi. ss (SUC m + i)) (SUC n)’] >> simp[]
QED

Theorem irun_steps:
  l0sys_irun ps ss rs ⇒ sys_init ps (ss 0) ∧ sys_steps (ss 0) (GENLIST rs n) (GENLIST ss (SUC n))
Proof
  rw[l0sysFairTheory.l0sys_irun_def] >>
  drule irun_steps_from >> disch_then (qspecl_then [‘n’, ‘0’] mp_tac) >>
  simp[ETA_THM]
QED

(* The trace starts with the check of fd 0 *)
Definition start0_def:
  start0 evs ⇔ evs = [] ∨ ∃i rest. evs = IO_event (ExtCall «sys_fdok») [0w] [(i, 1w)] :: rest
End

Theorem fd0_checked_start0:
  start0 evs ⇒ fd0_checked evs
Proof
  rw[start0_def, fd0_checked_def] >> Cases_on ‘pre’ >> gvs[] >> metis_tac[MEM]
QED

Theorem irun_no_fd0:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ∧ start0 (ptr rs k n) ∧ no_close0 (ptr rs k n) ⇒
  no_fd0 (ptr rs k n)
Proof
  strip_tac >> drule irun_steps >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  rewrite_tac[no_fd0_def, ptr_def] >> irule l0sys_no_fd0 >>
  fs[ptr_def, fd0_checked_start0] >>
  qexistsl_tac [‘ps’, ‘ss 0’, ‘GENLIST ss (SUC n)’] >> simp[]
QED

(* Every connect is to port x *)
Definition conns_only_def:
  conns_only x evs ⇔ ∀conf bs. MEM (IO_event (ExtCall «sys_connect») conf bs) evs ⇒ conf = pbytes x
End

Definition no_conns_def:
  no_conns evs ⇔ ∀conf bs. ¬MEM (IO_event (ExtCall «sys_connect») conf bs) evs
End

Theorem conns_only_conn_to:
  conns_only x evs ∧ x < 65536 ∧ conn_to q evs ⇒ q = x
Proof
  rw[conns_only_def, conn_to_def] >> res_tac >> gvs[w22n_pbytes]
QED

Theorem no_conns_conn_to:
  no_conns evs ⇒ ¬conn_to q evs
Proof
  rw[no_conns_def, conn_to_def] >> metis_tac[]
QED

(* Every connect that opened an episode was to port x (the proxy's form,
   proxy_safe_l0 constrains only connects that got a socket; the text of
   moonshotStep12Stmts.connects_only) *)
Definition eps_only_def:
  eps_only x evs ⇔ ∀ev f q. MEM ev evs ∧ ev_new ev = SOME (f, INL q) ⇒ q = x
End

Theorem eps_only_no_conn_to:
  eps_only x evs ∧ ¬free0 evs ∧ q ≠ x ⇒ no_conn_to q evs
Proof
  rw[no_conn_to_def, eps_only_def] >> strip_tac >>
  drule roles_connected_ev >> strip_tac >> res_tac
QED

Theorem conns_only_no_conn_to:
  conns_only x evs ∧ x < 65536 ∧ q ≠ x ⇒ no_conn_to q evs
Proof
  rpt strip_tac >> irule no_conn_to_of >> strip_tac >>
  drule_all conns_only_conn_to >> simp[]
QED

Theorem no_conns_no_conn_to:
  no_conns evs ⇒ no_conn_to q evs
Proof
  metis_tac[no_conn_to_of, no_conns_conn_to]
QED

(* MAIN: G2 at every instant n, from the programs' clauses on ptr rs k n *)
Theorem kv_peer_valid_run:
  l0sys_irun ps ss rs ∧ LENGTH ps = 3 ∧ isolated [a; b] ss rs ∧
  a < 65536 ∧ b < 65536 ∧ a ≠ b ∧
  (ss m).peer (2, jk) = SOME e ∧ (ss m).target e = SOME b ∧ is_end (ss n) (2, jk) ∧
  start0 (ptr rs 0 n) ∧ no_close0 (ptr rs 0 n) ∧ start0 (ptr rs 1 n) ∧ no_close0 (ptr rs 1 n) ∧
  conns_only a (ptr rs 0 n) ∧ eps_only b (ptr rs 1 n) ∧ no_conns (ptr rs 2 n) ∧
  (* the proxy: proxy_safe_ep's cover and relay clauses at ptr rs 1 n *)
  (∀c. l0_ep_role c (ptr rs 1 n) = SOME (Connected b) ⇒
       ∃f. prx f = SOME c ∧ l0_ep_role f (ptr rs 1 n) = SOME (Accepted a)) ∧
  (∀f c. prx f = SOME c ⇒ l0_ep_sent c (ptr rs 1 n) ≼ l0_ep_recvd f (ptr rs 1 n)) ∧
  (* the client: client_safe_l0's connect clause at ptr rs 0 n *)
  (∀i. EVERY valid_brequest (rqs i)) ∧
  (∀j p. l0_ep_role j (ptr rs 0 n) = SOME (Connected p) ⇒
         lc j < (N : num) ∧ l0_ep_sent j (ptr rs 0 n) ≼ brequests (rqs (lc j))) ⇒
  ∃rqs. EVERY valid_brequest rqs ∧ (sys_chan (ss n) (2, jk)).peer_sent ≼ brequests rqs
Proof
  strip_tac >>
  ‘relay_ok a b rs n’
    by (irule relay_ok_of_ep >>
        qexistsl_tac [‘ptr rs 1 n’, ‘prx’, ‘λj. l0_ep_role j (ptr rs 1 n)’] >> simp[]) >>
  ‘csend_ok a rs n’ by (irule csend_ok_of_client >> qexistsl_tac [‘N’, ‘lc’, ‘rqs’] >> simp[]) >>
  ‘no_fd0 (ptr rs 0 n) ∧ no_fd0 (ptr rs 1 n)’
    by (conj_tac >> irule irun_no_fd0 >> simp[] >> qexistsl_tac [‘ps’, ‘ss’] >> simp[]) >>
  ‘¬free0 (ptr rs 0 n) ∧ ¬free0 (ptr rs 1 n)’
    by (conj_tac >> irule free0_stdio >> fs[start0_def]) >>
  ‘∀k. k < 3 ∧ k ≠ 0 ⇒ no_conn_to a (ptr rs k n)’
    by (rpt strip_tac >> ‘k = 1 ∨ k = 2’ by decide_tac >> rveq
        >- (irule eps_only_no_conn_to >> conj_tac >- first_assum ACCEPT_TAC >>
            qexists_tac ‘b’ >> conj_tac >> first_assum ACCEPT_TAC) >>
        irule no_conns_no_conn_to >> first_assum ACCEPT_TAC) >>
  ‘∀k. k < 3 ∧ k ≠ 1 ⇒ no_conn_to b (ptr rs k n)’
    by (rpt strip_tac >> ‘k = 0 ∨ k = 2’ by decide_tac >> rveq
        >- (irule conns_only_no_conn_to >> qexists_tac ‘a’ >> rpt conj_tac >>
            FIRST [first_assum ACCEPT_TAC, qpat_x_assum ‘a ≠ b’ (ACCEPT_TAC o GSYM)]) >>
        irule no_conns_no_conn_to >> first_assum ACCEPT_TAC) >>
  irule kv_peer_valid_sys >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [‘a’, ‘b’, ‘e’, ‘m’, ‘ps’, ‘rs’] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
