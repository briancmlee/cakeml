(*
  G2 lifts: the per-trace clauses of moonshotLiveG2.kv_peer_valid_run from
  the three programs' claims (the safety line's forms), on every prefix of
  each program's L0 trace:
   - client: client_safe_l0 (T4 and the connect clause) and stdio_open
     (moonshotClientL0Stmts, honestL0Outcome);
   - proxy: proxy_safe_l0, stdio_open and no_close_stdio; the cover and relay
     clauses through moonshotProxyGlue.proxy_safe_bridge, with prx_of;
   - KV: l0_topology (honestHttpKvL0SpecCopy: no connect at all).
  kv_peer_valid_claims then gives G2 at every instant of an infinite run whose
  processes' traces are prefixes of traces with those claims (l0sys_proj_inf).
*)
Theory moonshotLiveClaims
Ancestors
  moonshotLiveG2 moonshotLiveRelay moonshotLiveAccepts moonshotClientL0Stmts honestL0Outcome
  moonshotProxyGlue moonshotPairGlue proxyL0StmtsCopy honestHttpKvL0SpecCopy moonshotWorldFacts moonshotW2 moonshotLiveStmts
  l0sysFair l0sysEpisodes llist
Libs
  preamble

(* As moonshotKvBridge.LPREFIX_LNTH *)
Theorem lprefix_lnth:
  LPREFIX (fromList evs) tr ∧ n < LENGTH evs ⇒ LNTH n tr = SOME (EL n evs)
Proof
  rw[LPREFIX_fromList] >> every_case_tac >> gvs[]
  >- (irule LTAKE_LNTH_EL >> metis_tac[]) >>
  ‘LFINITE tr’ by (CCONTR_TAC >> gvs[toList]) >>
  ‘tr = fromList x’ by metis_tac[to_fromList, THE_DEF] >>
  gvs[LNTH_fromList] >> imp_res_tac IS_PREFIX_LENGTH >>
  ‘n < LENGTH x’ by simp[] >> simp[] >> metis_tac[is_prefix_el]
QED

Theorem stdio_start0:
  stdio_open tr ∧ LPREFIX (fromList evs) tr ⇒ start0 evs
Proof
  rw[stdio_open_def, start0_def] >> Cases_on ‘evs’ >> fs[LPREFIX_LCONS]
QED

Theorem stdio_no_close0:
  no_close_stdio evs ⇒ no_close0 evs
Proof
  rw[no_close_stdio_def] >> irule no_close0_stdio >> metis_tac[]
QED

(* The client *)
Theorem client_trace_clauses:
  client_safe_l0 a c N rqs lc tr ∧ stdio_open tr ∧ LPREFIX (fromList evs) tr ⇒
  start0 evs ∧ no_close0 evs ∧ conns_only a evs ∧
  ∀j p. l0_ep_role j evs = SOME (Connected p) ⇒ lc j < N ∧ l0_ep_sent j evs ≼ brequests (rqs (lc j))
Proof
  strip_tac >> drule_all stdio_start0 >> strip_tac >>
  qpat_x_assum ‘client_safe_l0 _ _ _ _ _ _’ (mp_tac o REWRITE_RULE [client_safe_l0_def]) >>
  disch_then drule >> strip_tac >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (irule stdio_no_close0 >> first_assum ACCEPT_TAC)
  >- (rewrite_tac[conns_only_def] >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

(* The proxy: every connect episode is to b (as moonshotStep12.proxy_ports) *)
Theorem proxy_eps_only:
  proxy_safe_l0 kt hw a b pr tr ∧ LPREFIX (fromList ft) tr ∧ EVERY opens_ok ft ∧ b < 65536 ⇒
  eps_only b ft
Proof
  rw[eps_only_def] >>
  ‘opens_ok ev’ by fs[EVERY_MEM] >>
  drule_all new_INL_connected >> strip_tac >>
  qpat_x_assum ‘proxy_safe_l0 _ _ _ _ _ _’ (mp_tac o REWRITE_RULE [proxy_safe_l0_def]) >>
  disch_then (drule o CONJUNCT2) >> strip_tac >>
  fs[MEM_EL] >> rveq >>
  qpat_x_assum ‘∀q. q < LENGTH ft ∧ _ ⇒ _’ (qspec_then ‘n’ mp_tac) >> simp[] >> strip_tac >>
  drule ev_new_INL_ev >> strip_tac >> gvs[connect_port_def, w22n_pbytes]
QED

Theorem proxy_trace_clauses:
  proxy_safe_l0 kt hw a b pr tr ∧ stdio_open tr ∧ (∀evs. LPREFIX (fromList evs) tr ⇒ no_close_stdio evs) ∧
  LPREFIX (fromList ft) tr ∧ ep_ok ft ∧ a < 65536 ∧ b < 65536 ⇒
  start0 ft ∧ no_close0 ft ∧ eps_only b ft ∧
  (∀c. l0_ep_role c ft = SOME (Connected b) ⇒
       ∃f. prx_of pr ft f = SOME c ∧ l0_ep_role f ft = SOME (Accepted a)) ∧
  (∀f c. prx_of pr ft f = SOME c ⇒ l0_ep_sent c ft ≼ l0_ep_recvd f ft)
Proof
  strip_tac >>
  ‘proxy_safe_ep (prx_of pr ft) (λpx j. l0_ep_role j ft) (λpx t. ft) 1 a b’
    by (irule proxy_safe_bridge >> simp[] >> qexistsl_tac [‘hw’, ‘tr’, ‘kt’] >> simp[]) >>
  rpt conj_tac
  >- (irule stdio_start0 >> qexists_tac ‘tr’ >> simp[])
  >- (irule stdio_no_close0 >> first_x_assum irule >> first_assum ACCEPT_TAC)
  >- (irule proxy_eps_only >> fs[ep_ok_def] >> metis_tac[])
  >- fs[proxy_safe_ep_def] >>
  fs[proxy_safe_ep_def] >> metis_tac[]
QED

(* KV *)
Theorem kv_no_conns:
  l0_topology b tr ∧ LPREFIX (fromList evs) tr ⇒ no_conns evs
Proof
  rw[no_conns_def, MEM_EL] >> strip_tac >>
  ‘LNTH n tr = SOME (EL n evs)’ by metis_tac[lprefix_lnth] >>
  fs[l0_topology_def] >> first_x_assum drule >>
  qpat_x_assum ‘_ = EL n evs’ (SUBST1_TAC o SYM) >> simp[l0_topo_ev_def]
QED

(* MAIN: G2 at every instant, from the three claims *)
Theorem kv_peer_valid_claims:
  l0sys_irun ps ss rs ∧ LENGTH ps = 3 ∧ isolated [a; b] ss rs ∧
  a < 65536 ∧ b < 65536 ∧ a ≠ b ∧
  (ss m).peer (2, jk) = SOME e ∧ (ss m).target e = SOME b ∧ is_end (ss n) (2, jk) ∧
  client_safe_l0 a c N rqs lc io0 ∧ stdio_open io0 ∧ (∀i. EVERY valid_brequest (rqs i)) ∧
  (∀t. LPREFIX (fromList (ptr rs 0 t)) io0) ∧
  proxy_safe_l0 kt hw a b pr io1 ∧ stdio_open io1 ∧
  (∀evs. LPREFIX (fromList evs) io1 ⇒ no_close_stdio evs) ∧ (∀t. LPREFIX (fromList (ptr rs 1 t)) io1) ∧
  l0_topology b io2 ∧ (∀t. LPREFIX (fromList (ptr rs 2 t)) io2) ⇒
  ∃rqs. EVERY valid_brequest rqs ∧ (sys_chan (ss n) (2, jk)).peer_sent ≼ brequests rqs
Proof
  strip_tac >>
  ‘start0 (ptr rs 0 n) ∧ no_close0 (ptr rs 0 n) ∧ conns_only a (ptr rs 0 n) ∧
   ∀j p. l0_ep_role j (ptr rs 0 n) = SOME (Connected p) ⇒
         lc j < N ∧ l0_ep_sent j (ptr rs 0 n) ≼ brequests (rqs (lc j))’
    by (irule client_trace_clauses >> qexistsl_tac [‘c’, ‘io0’] >> simp[]) >>
  ‘start0 (ptr rs 1 n) ∧ no_close0 (ptr rs 1 n)’
    by (conj_tac
        >- (irule stdio_start0 >> qexists_tac ‘io1’ >> simp[]) >>
        irule stdio_no_close0 >> first_x_assum irule >> simp[]) >>
  ‘no_fd0 (ptr rs 1 n)’ by (irule irun_no_fd0 >> simp[] >> qexistsl_tac [‘ps’, ‘ss’] >> simp[]) >>
  ‘ep_ok (ptr rs 1 n)’
    by (drule irun_steps >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
        rewrite_tac[ptr_def] >> irule l0sys_ep_ok >>
        fs[no_fd0_def, ptr_def] >>
        qexistsl_tac [‘ps’, ‘ss 0’, ‘GENLIST ss (SUC n)’] >> simp[]) >>
  ‘eps_only b (ptr rs 1 n) ∧
   (∀c. l0_ep_role c (ptr rs 1 n) = SOME (Connected b) ⇒
        ∃f. prx_of pr (ptr rs 1 n) f = SOME c ∧ l0_ep_role f (ptr rs 1 n) = SOME (Accepted a)) ∧
   (∀f c. prx_of pr (ptr rs 1 n) f = SOME c ⇒
          l0_ep_sent c (ptr rs 1 n) ≼ l0_ep_recvd f (ptr rs 1 n))’
    by (qspecl_then [‘kt’, ‘hw’, ‘a’, ‘b’, ‘pr’, ‘io1’, ‘ptr rs 1 n’] mp_tac
          (Q.GENL [‘kt’, ‘hw’, ‘a’, ‘b’, ‘pr’, ‘tr’, ‘ft’] proxy_trace_clauses) >>
        impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, first_x_assum (qspec_then ‘n’ ACCEPT_TAC)]) >>
        simp[]) >>
  ‘no_conns (ptr rs 2 n)’ by (irule kv_no_conns >> qexistsl_tac [‘b’, ‘io2’] >> simp[]) >>
  irule kv_peer_valid_run >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [‘N’, ‘a’, ‘b’, ‘e’, ‘lc’, ‘m’, ‘prx_of pr (ptr rs 1 n)’, ‘ps’, ‘rqs’, ‘rs’] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
