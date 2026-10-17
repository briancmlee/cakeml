(*
  Moonshot step 12: THE HEADLINE, moonshot_safe_stmt (moonshotStep12Stmts),
  from B2's isolated variant b2_iso_stmt (m4-server's).

  - Each claim's early outcomes (stdio_closed, l0_listen_failed) run only
    sys_fdok and failed listens (early_ev): no episodes, so they meet the
    proxy's and KV's safe forms vacuously (early_proxy_safe with no pairing,
    early_kv_safe) and every port clause (early_ports).
  - Past them, the claims give the port clauses on each process's trace
    (B1/G2: g2_one_io), and the proxy's W2 (stdio_open + no_close_stdio,
    moonshotW2); the proxy's connects are to b by its claim's connect
    clause (opens_ok, W1, ties ev_new's connects to l0_event_connected).
  - topology_stmt_holds turns the port clauses into topology, and
    moonshot_sys_safe gives the conclusion.
*)
Theory moonshotStep12
Ancestors
  moonshotStep12Stmts moonshotTopology moonshotSysGlue moonshotSafeGlue moonshotW2
  moonshotWorldFacts moonshotProxyGlue moonshotClientL0Stmts proxyL0StmtsCopy
  honestL0Outcome moonshotKvClient l0sysBridges l0sys l0sysEpisodes l0sysInv
  honestEchoL0SpecCopy HttpKvSpec2 Marshalling llist rich_list
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* The early outcomes *)

(* An event of an early outcome: a stdio check, or a failed listen *)
Definition early_ev_def:
  early_ev ev ⇔
    (∃conf bs. ev = IO_event (ExtCall «sys_fdok») conf bs) ∨
    ∃conf bs. ev = IO_event (ExtCall «sys_listen») conf bs ∧ ∀k. l0_ev_res bs ≠ SOME (Ok k)
End

Definition early_def:
  early b ⇔ stdio_closed b ∨ l0_listen_failed b
End

Theorem LPREFIX_fromList_MEM:
  LPREFIX (fromList evs) (fromList l) ∧ MEM e evs ⇒ MEM e l
Proof
  rw[cfTheory.LPREFIX_fromList_fromList] >> drule_all IS_PREFIX_MEM >> simp[]
QED

Theorem early_prefix:
  early b ∧ LPREFIX (fromList evs) (beh_io b) ⇒ EVERY early_ev evs
Proof
  rw[early_def, EVERY_MEM] >>
  fs[stdio_closed_def, l0_listen_failed_def] >> rveq >>
  qpat_x_assum ‘LPREFIX _ _’ mp_tac >> rewrite_tac[beh_io_def] >> strip_tac >>
  drule_all LPREFIX_fromList_MEM >> rw[] >> simp[early_ev_def]
QED

Theorem early_ev_facts:
  early_ev ev ⇒
  ev_new ev = NONE ∧ ev_listen ev = NONE ∧ l0_event_accepted ev = NONE ∧
  l0_event_connected ev = NONE
Proof
  rw[early_ev_def] >>
  simp[ev_new_def, ev_listen_def, l0_event_accepted_def, l0_event_connected_def, LET_THM] >>
  every_case_tac >> gvs[l0_ev_res_def]
QED

Theorem early_no_eps:
  ∀evs. EVERY early_ev evs ⇒ ep_fds evs = []
Proof
  Induct >> simp[ep_fds_def] >> rpt strip_tac >> drule early_ev_facts >> simp[] >>
  fs[GSYM ep_fds_def]
QED

Theorem early_role:
  EVERY early_ev evs ⇒ l0_ep_role j evs = NONE
Proof
  strip_tac >> drule early_no_eps >> strip_tac >>
  ‘ep_roles [] evs = []’
    by (‘LENGTH (ep_roles [] evs) = 0’ suffices_by simp[] >>
        rewrite_tac[ep_roles_LENGTH] >> simp[]) >>
  simp[l0_ep_role_def]
QED

Theorem early_ports:
  EVERY early_ev evs ⇒
  listens_only p evs ∧ connects_only q evs ∧ no_connects evs ∧ no_close_stdio evs ∧
  EVERY (λev. ∀r. ev_new ev ≠ SOME (0w, r)) evs
Proof
  strip_tac >> fs[EVERY_MEM] >>
  ‘∀ev. MEM ev evs ⇒ ev_new ev = NONE’ by metis_tac[early_ev_facts] >>
  rw[listens_only_def, connects_only_def, no_connects_def, no_close_stdio_def] >>
  CCONTR_TAC >> fs[] >> res_tac >> fs[early_ev_def]
QED

Theorem early_proxy_safe:
  early b ⇒ proxy_safe_l0 kt hw pa pb (K NONE) (beh_io b)
Proof
  simp[proxy_safe_l0_def] >> rpt strip_tac >> drule_all early_prefix >> strip_tac >>
  ‘∀n. n < LENGTH evs ⇒ l0_event_connected (EL n evs) = NONE ∧
                        l0_event_accepted (EL n evs) = NONE’
    by (rpt strip_tac >> fs[EVERY_EL] >> res_tac >> imp_res_tac early_ev_facts) >>
  ‘listens_only pa evs’ by metis_tac[early_ports] >>
  fs[listens_only_def, is_front_def] >> metis_tac[]
QED

Theorem early_kv_safe:
  early b ⇒ kv_safe_g l0_ep_recvd l0_ep_sent (beh_io b)
Proof
  rw[kv_safe_g_def] >> drule_all early_prefix >> strip_tac >>
  ‘∀j. l0_ep_recvd j evs = [] ∧ l0_ep_sent j evs = []’
    by (gen_tac >> ‘l0_ep_role j evs = NONE’ by metis_tac[early_role] >>
        drule role_none_unborn >> simp[]) >>
  ‘∀j. rss j = []’
    by (gen_tac >> first_x_assum (qspec_then ‘j’ mp_tac) >> simp[]) >>
  qexists_tac ‘[]’ >> simp[is_order2_def, COUNT_LIST_def]
QED

(*---------------------------------------------------------------------------*)
(* The ports, past the early outcomes *)

Theorem new_INL_port:
  ev_new ev = SOME (f, INL q) ⇒
  ∃conf bs. ev = IO_event (ExtCall «sys_connect») conf bs ∧ q = w22n conf
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bl’ >> Cases_on ‘nm’ >>
  rw[ev_new_def, LET_THM] >> every_case_tac >> gvs[]
QED

Theorem client_ports:
  client_safe_l0 a c N rqs lc io ∧ LPREFIX (fromList evs) io ∧ a < 65536 ⇒
  listens_only c evs ∧ connects_only a evs
Proof
  rw[client_safe_l0_def] >> first_x_assum drule >> strip_tac >>
  rw[listens_only_def, connects_only_def]
  >- metis_tac[] >>
  drule new_INL_port >> strip_tac >> gvs[] >>
  ‘conf = pbytes a’ by metis_tac[] >> simp[w22n_pbytes]
QED

Theorem proxy_ports:
  proxy_safe_l0 kt hw a b pr io ∧ LPREFIX (fromList evs) io ∧ b < 65536 ∧
  EVERY opens_ok evs ⇒
  listens_only a evs ∧ connects_only b evs
Proof
  rw[proxy_safe_l0_def] >> first_x_assum drule >> strip_tac >>
  rw[listens_only_def, connects_only_def]
  >- metis_tac[] >>
  ‘opens_ok ev’ by fs[EVERY_MEM] >>
  drule_all new_INL_connected >> strip_tac >>
  fs[MEM_EL] >> rveq >>
  qpat_x_assum ‘∀q. q < LENGTH evs ∧ _ ⇒ _’ (qspec_then ‘n’ mp_tac) >> simp[] >> strip_tac >>
  drule new_INL_port >> strip_tac >> gvs[connect_port_def, w22n_pbytes]
QED

(* The proxy's W2, past its stdio check *)
Theorem proxy_w2:
  sys_init ps s0 ∧ sys_steps s0 rs ss ∧ k < LENGTH ps ∧
  stdio_open io ∧ LPREFIX (fromList (proc_events k rs)) io ∧
  no_close_stdio (proc_events k rs) ⇒
  EVERY (λev. ∀r. ev_new ev ≠ SOME (0w, r)) (proc_events k rs)
Proof
  strip_tac >> irule l0sys_no_fd0 >> rpt conj_tac
  >- (qpat_x_assum ‘stdio_open _’ (strip_assume_tac o REWRITE_RULE [stdio_open_def]) >>
      irule fd0_checked_stdio >> metis_tac[])
  >- (irule no_close0_stdio >> fs[no_close_stdio_def])
  >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* THE HEADLINE, from b2_iso_stmt *)

Theorem moonshot_safe:
  b2_iso_stmt ⇒ moonshot_safe_stmt kt hw cprog pprog kprog
Proof
  rewrite_tac[moonshot_safe_stmt_def] >> rpt strip_tac >>
  qabbrev_tac ‘sy = moonshot_sys cprog pprog kprog a b c N rqs’ >>
  ‘LENGTH sy = 3 ∧ EL 0 sy = cprog a c N rqs ∧ EL 1 sy = pprog a b ∧ EL 2 sy = kprog b’
    by simp[Abbr ‘sy’, moonshot_sys_def] >>
  qpat_x_assum ‘l0sys_iso_run _ _ _ _’ (strip_assume_tac o REWRITE_RULE [l0sys_iso_run_def]) >>
  ‘l0sys_run sy rs’
    by (rewrite_tac[l0sys_run_def] >> qexistsl_tac [‘s0’, ‘ss’] >> asm_rewrite_tac[]) >>
  (* the client's ports *)
  ‘listens_only c (proc_events 0 rs) ∧ connects_only a (proc_events 0 rs)’
    by (qspecl_then [‘sy’, ‘rs’, ‘0’,
          ‘λbeh. stdio_closed beh ∨ l0_listen_failed beh ∨
             stdio_open (beh_io beh) ∧ ∃lc. client_safe_l0 a c N rqs lc (beh_io beh)’]
          mp_tac (Q.GENL [‘ps’, ‘rs’, ‘k’, ‘Q’] g2_one_io) >>
        impl_tac
        >- (simp[] >> rpt strip_tac >>
            qpat_x_assum ‘l0_client_claim _’ mp_tac >> rewrite_tac[l0_client_claim_def] >>
            disch_then (qspecl_then [‘a’, ‘c’, ‘N’, ‘rqs’, ‘w0’] mp_tac) >>
            impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
        simp[] >> strip_tac
        >- (‘early b'’ by simp[early_def] >> drule_all early_prefix >> simp[early_ports])
        >- (‘early b'’ by simp[early_def] >> drule_all early_prefix >> simp[early_ports]) >>
        drule_all client_ports >> simp[]) >>
  (* the proxy: its ports and W2, and its safe form *)
  ‘∀w0. l0_rely w0 ∧ l0_fresh w0 ∧ fds_lt w0 ⇒
        ∃bp. semantics_prog (init_state (l0_ffi w0)) init_env (pprog a b) bp ∧ bp ≠ Fail ∧
             (early bp ∨
              stdio_open (beh_io bp) ∧ (∃pr. proxy_safe_l0 kt hw a b pr (beh_io bp)) ∧
              ∀evs. LPREFIX (fromList evs) (beh_io bp) ⇒ no_close_stdio evs)’
    by (rpt strip_tac >> qpat_x_assum ‘proxy_claim_safe _ _ _’ mp_tac >>
        rewrite_tac[proxy_claim_safe_def] >>
        disch_then (qspecl_then [‘a’, ‘b’, ‘w0’] mp_tac) >>
        impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
        disch_then (qx_choose_then ‘beh’ assume_tac) >> qexists_tac ‘beh’ >>
        pop_assum mp_tac >> rewrite_tac[early_def, GSYM DISJ_ASSOC]) >>
  ‘EVERY (λev. ∀r. ev_new ev ≠ SOME (0w, r)) (proc_events 1 rs) ∧
   listens_only a (proc_events 1 rs) ∧ connects_only b (proc_events 1 rs)’
    by (qspecl_then [‘sy’, ‘rs’, ‘1’,
          ‘λbp. early bp ∨
             stdio_open (beh_io bp) ∧ (∃pr. proxy_safe_l0 kt hw a b pr (beh_io bp)) ∧
             ∀evs. LPREFIX (fromList evs) (beh_io bp) ⇒ no_close_stdio evs’]
          mp_tac (Q.GENL [‘ps’, ‘rs’, ‘k’, ‘Q’] g2_one_io) >>
        impl_tac >- simp[] >>
        simp[] >> strip_tac
        >- (drule_all early_prefix >> simp[early_ports]) >>
        ‘no_close_stdio (proc_events 1 rs)’ by (first_x_assum drule >> simp[]) >>
        ‘EVERY (λev. ∀r. ev_new ev ≠ SOME (0w, r)) (proc_events 1 rs)’
          by (qspecl_then [‘sy’, ‘s0’, ‘rs’, ‘ss’, ‘1’, ‘beh_io b'’] mp_tac
                (Q.GENL [‘ps’, ‘s0’, ‘rs’, ‘ss’, ‘k’, ‘io’] proxy_w2) >>
              asm_rewrite_tac[] >> simp[]) >>
        ‘ep_ok (proc_events 1 rs)’
          by (qspecl_then [‘sy’, ‘s0’, ‘rs’, ‘ss’, ‘1’] mp_tac
                (Q.GENL [‘ps’, ‘s0’, ‘rs’, ‘ss’, ‘k’] l0sys_ep_ok) >>
              asm_rewrite_tac[] >> simp[]) >>
        ‘EVERY opens_ok (proc_events 1 rs)’ by fs[ep_ok_def] >>
        drule_all proxy_ports >> simp[]) >>
  (* KV *)
  ‘∀w0. l0_rely w0 ∧ l0_fresh w0 ∧ fds_lt w0 ⇒
        ∃bk. semantics_prog (init_state (l0_ffi w0)) init_env (kprog b) bk ∧ bk ≠ Fail ∧
             (early bk ∨
              stdio_open (beh_io bk) ∧ kv_safe_g l0_ep_recvd l0_ep_sent (beh_io bk) ∧
              ∀evs. LPREFIX (fromList evs) (beh_io bk) ⇒
                    listens_only b evs ∧ no_connects evs ∧ no_close_stdio evs)’
    by (rpt strip_tac >> qpat_x_assum ‘kv_claim_safe _’ mp_tac >>
        rewrite_tac[kv_claim_safe_def] >>
        disch_then (qspecl_then [‘b’, ‘w0’] mp_tac) >>
        impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
        disch_then (qx_choose_then ‘beh’ assume_tac) >> qexists_tac ‘beh’ >>
        pop_assum mp_tac >> rewrite_tac[early_def, GSYM DISJ_ASSOC]) >>
  ‘listens_only b (proc_events 2 rs) ∧ no_connects (proc_events 2 rs)’
    by (qspecl_then [‘sy’, ‘rs’, ‘2’,
          ‘λbk. early bk ∨
             stdio_open (beh_io bk) ∧ kv_safe_g l0_ep_recvd l0_ep_sent (beh_io bk) ∧
             ∀evs. LPREFIX (fromList evs) (beh_io bk) ⇒
                   listens_only b evs ∧ no_connects evs ∧ no_close_stdio evs’]
          mp_tac (Q.GENL [‘ps’, ‘rs’, ‘k’, ‘Q’] g2_one_io) >>
        impl_tac >- simp[] >>
        simp[] >> strip_tac
        >- (drule_all early_prefix >> simp[early_ports]) >>
        first_x_assum drule >> simp[]) >>
  (* topology *)
  ‘topology (sys_rl rs) 0 1 2 a b’
    by (mp_tac topology_stmt_holds >> rewrite_tac[topology_stmt_def] >>
        disch_then (qspecl_then [‘cprog’, ‘pprog’, ‘kprog’, ‘a’, ‘b’, ‘c’, ‘N’, ‘rqs’, ‘rs’]
                    mp_tac) >>
        rewrite_tac[client_ix_def, proxy_ix_def, kv_ix_def] >> disch_then irule >>
        qpat_x_assum ‘Abbrev _’ (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
        qpat_x_assum ‘sy = _’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
        asm_rewrite_tac[]) >>
  (* B2 *)
  ‘∃cn. (∀e e'. cn e = SOME e' ⇔ cn e' = SOME e) ∧
        (∀k j k' j'. cn (k, j) = SOME (k', j') ⇒
           (∃p. l0_ep_role j (proc_events k rs) = SOME (Connected p) ∧
                l0_ep_role j' (proc_events k' rs) = SOME (Accepted p) ∨
                l0_ep_role j (proc_events k rs) = SOME (Accepted p) ∧
                l0_ep_role j' (proc_events k' rs) = SOME (Connected p)) ∧
           ∀t. l0_ep_recvd j' (proc_events k' (TAKE t rs)) ≼
               l0_ep_sent j (proc_events k (TAKE t rs))) ∧
        b2_quiet_ab a b rs cn’
    by (qpat_x_assum ‘b2_iso_stmt’ mp_tac >> rewrite_tac[b2_iso_stmt_def] >>
        disch_then (qspecl_then [‘sy’, ‘a’, ‘b’, ‘rs’] mp_tac) >>
        impl_tac >- (rewrite_tac[l0sys_iso_run_def] >> qexistsl_tac [‘s0’, ‘ss’] >>
                     asm_rewrite_tac[]) >>
        strip_tac >> qexists_tac ‘cn’ >> rpt conj_tac
        >- first_assum ACCEPT_TAC
        >- (rpt strip_tac >> qpat_x_assum ‘∀k j k' j'. _’ drule >> simp[]) >>
        first_assum ACCEPT_TAC) >>
  (* the composed corollary (no rewriting with B2's symmetric iff from here) *)
  rewrite_tac[client_ix_def] >> irule moonshot_sys_safe >>
  qexistsl_tac [‘cn’, ‘hw’, ‘kt’, ‘2’, ‘a’, ‘b’, ‘sy’, ‘1’] >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (qpat_assum ‘LENGTH sy = 3’ (fn th => rewrite_tac [th]) >> simp[] >> NO_TAC) >>
  TRY (rpt strip_tac >>
       qpat_x_assum ‘∀w0. _ ⇒ ∃bp. semantics_prog _ _ (pprog a b) _ ∧ _’ (qspec_then ‘w0’ mp_tac) >>
       impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
       strip_tac >> qexists_tac ‘bp’ >> qpat_assum ‘EL 1 sy = _’ (fn th => rewrite_tac [th]) >>
       rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
       TRY (qexists_tac ‘K NONE’ >> irule early_proxy_safe >> first_assum ACCEPT_TAC >> NO_TAC) >>
       qexists_tac ‘pr’ >> first_assum ACCEPT_TAC >> NO_TAC) >>
  rpt strip_tac >>
  qpat_x_assum ‘∀w0. _ ⇒ ∃bk. semantics_prog _ _ (kprog b) _ ∧ _’ (qspec_then ‘w0’ mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> qexists_tac ‘bk’ >> qpat_assum ‘EL 2 sy = _’ (fn th => rewrite_tac [th]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  irule early_kv_safe >> first_assum ACCEPT_TAC
QED
