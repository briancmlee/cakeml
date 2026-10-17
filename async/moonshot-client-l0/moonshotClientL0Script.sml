(*
  Moonshot step 12, C1 (close-v2): l0_client_claim for the client binary
  client_prog (e1ClientSem), with N < 2^63 (D42).

  The binary's four outcomes (e1ClientSem): stdio closed, the listen on c
  failed, it finished after n rounds of E1, or it runs E1 for ever.  In
  the last two its trace is the three fdok events, the listen, then the
  rounds' events, and every finite prefix of it lies within the start and
  finitely many rounds (e1TracePrefix).  One episode map lc serves every
  round boundary (client_rounds_safe), so it serves every prefix
  (client_prefix_safe): the start has no episodes, no sends and no close,
  and its one listen is on c.
*)
Theory moonshotClientL0
Ancestors
  moonshotClientL0Rounds moonshotClientL0Stmts e1ClientSem e1World e1TracePrefix
  e1TraceEvents moonshotSentGlue moonshotClientTotal moonshotClientSpec
  honestL0Fdok e1DriverSpec e1DriverMain e1DriverProg e1DriverLoop honestL0Part
  honestL0Outcome l0sysBridges honestL1PFRound honestL1EPModel proxyL0StmtsCopy
  honestL1Model honestEchoL0SpecCopy honestL0World
Libs
  preamble

(* The two copies of fds_lt *)
Theorem fds_lt_eq[local]:
  l0sysInv$fds_lt w ⇔ honestL0WorldProps$fds_lt w
Proof
  simp[l0sysInvTheory.fds_lt_def, honestL0WorldPropsTheory.fds_lt_def]
QED

(* ------------------------------------------------------------------------
   Prefixes of start ++ rounds
   ------------------------------------------------------------------------ *)

Theorem prefix_mem[local]:
  evs ≼ l ∧ MEM x evs ⇒ MEM x l
Proof
  rw[IS_PREFIX_APPEND] >> simp[]
QED

(* The start's events open no episode and send nothing *)
Theorem start_quiet[local]:
  EVERY (λev. ev_name ev = ExtCall «sys_fdok») pre ⇒
  EVERY (λev. ev_new ev = NONE ∧ l0sysEpisodes$ev_sent ev = NONE)
        (pre ++ [IO_event (ExtCall «sys_listen») conf bs])
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  TRY (irule name_new) >> TRY (irule name_sent) >> res_tac >> simp[ev_name_def]
QED

Theorem start_noaccept[local]:
  EVERY (λev. ev_name ev = ExtCall «sys_fdok») pre ∧
  EVERY (λev. ev_name ev ≠ ExtCall «sys_accept») R ⇒
  EVERY (λev. ev_name ev ≠ ExtCall «sys_accept»)
        (pre ++ [IO_event (ExtCall «sys_listen») conf bs] ++ R)
Proof
  simp[EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[ev_name_def]
QED

(* From one round boundary to every prefix before it *)
Theorem client_prefix_safe:
  client_round_safe a N rqs lc R ∧ (∀j. lc j < N) ∧
  EVERY (λev. ev_name ev = ExtCall «sys_fdok») pre ∧
  evs ≼ pre ++ [IO_event (ExtCall «sys_listen») (port_bytes c) bs] ++ R ⇒
  (∀conf bs k. MEM (IO_event (ExtCall «sys_listen») conf bs) evs ∧
               l0_ev_res bs = SOME (Ok k) ⇒ conf = pbytes c) ∧
  (∀conf bs. MEM (IO_event (ExtCall «sys_connect») conf bs) evs ⇒ conf = pbytes a) ∧
  (∀j p. l0_ep_role j evs = SOME (Accepted p) ⇒ l0_ep_sent j evs = []) ∧
  (∀j p. l0_ep_role j evs = SOME (Connected p) ⇒
         lc j < N ∧ l0_ep_sent j evs ≼ brequests (rqs (lc j))) ∧
  (∀j j'. l0_ep_sent j evs ≠ [] ∧ l0_ep_sent j' evs ≠ [] ∧ lc j = lc j' ⇒ j = j') ∧
  no_close_stdio evs
Proof
  REWRITE_TAC[client_round_safe_def] >> strip_tac >>
  qabbrev_tac ‘lev = IO_event (ExtCall «sys_listen») (port_bytes c) bs’ >>
  ‘∀j. l0_ep_sent j evs ≼ l0_ep_sent j R’
    by (gen_tac >>
        ‘l0_ep_sent j (pre ++ [lev] ++ R) = l0_ep_sent j R’
          by (REWRITE_TAC[GSYM APPEND_ASSOC] >>
              REWRITE_TAC[APPEND_ASSOC] >> irule l0_ep_sent_quiet >>
              simp[Abbr ‘lev’, start_quiet]) >>
        pop_assum (SUBST1_TAC o SYM) >> irule l0_ep_sent_mono >> first_assum ACCEPT_TAC) >>
  ‘∀x. MEM x evs ⇒ MEM x pre ∨ x = lev ∨ MEM x R’
    by (rpt strip_tac >>
        qspecl_then [‘evs’, ‘pre ++ [lev] ++ R’, ‘x’] mp_tac
          (Q.GENL [‘evs’, ‘l’, ‘x’] prefix_mem) >>
        impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
        rewrite_tac[MEM_APPEND, MEM] >> rpt strip_tac >> asm_rewrite_tac[]) >>
  rpt conj_tac
  >- (rpt strip_tac >> first_x_assum drule >> strip_tac
      >- (qpat_x_assum ‘EVERY (λev. ev_name ev = _) pre’ mp_tac >> simp[EVERY_MEM] >>
          disch_then drule >> simp[ev_name_def])
      >- gvs[Abbr ‘lev’, pbytes_def, port_bytes_def] >>
      qpat_x_assum ‘EVERY (e1ev_ok _) R’ mp_tac >> simp[EVERY_MEM] >>
      disch_then drule >> simp[e1TraceEventsTheory.e1ev_ok_def])
  >- (rpt strip_tac >> first_x_assum drule >> strip_tac
      >- (qpat_x_assum ‘EVERY (λev. ev_name ev = _) pre’ mp_tac >> simp[EVERY_MEM] >>
          disch_then drule >> simp[ev_name_def])
      >- gvs[Abbr ‘lev’] >>
      qpat_x_assum ‘EVERY (e1ev_ok _) R’ mp_tac >> simp[EVERY_MEM] >>
      disch_then drule >> simp[e1TraceEventsTheory.e1ev_ok_def, pbytes_def, port_bytes_def])
  >- (rpt strip_tac >>
      ‘l0_ep_role j (pre ++ [lev] ++ R) = SOME (Accepted p)’
        by (irule l0_ep_role_mono >> qexists_tac ‘evs’ >> simp[]) >>
      ‘EVERY (λev. ev_name ev ≠ ExtCall «sys_accept») (pre ++ [lev] ++ R)’
        by simp[Abbr ‘lev’, start_noaccept] >>
      drule noaccept_role >> disch_then (qspecl_then [‘p’, ‘j’] mp_tac) >> asm_rewrite_tac[])
  >- (rpt strip_tac >- simp[] >>
      irule IS_PREFIX_TRANS >> qexists_tac ‘l0_ep_sent j R’ >> simp[])
  >- (rpt strip_tac >>
      first_x_assum (qspecl_then [‘j’, ‘j'’] match_mp_tac) >> simp[] >>
      metis_tac[prefix_nonnil]) >>
  rewrite_tac[no_close_stdio_def] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac
  >- (qpat_x_assum ‘EVERY (λev. ev_name ev = _) pre’ mp_tac >> simp[EVERY_MEM] >>
          disch_then drule >> simp[ev_name_def])
  >- gvs[Abbr ‘lev’] >>
  qpat_x_assum ‘no_close_stdio R’ mp_tac >> rewrite_tac[no_close_stdio_def] >>
  disch_then drule >> simp[]
QED

(* The client's io is safe once each of its prefixes lies within the start
   and some safe round boundary *)
Theorem client_safe_io:
  (∀j. lc j < N) ∧
  EVERY (λev. ev_name ev = ExtCall «sys_fdok») pre ∧
  (∀evs. LPREFIX (fromList evs) io ⇒
         ∃R. client_round_safe a N rqs lc R ∧
             evs ≼ pre ++ [IO_event (ExtCall «sys_listen») (port_bytes c) bs] ++ R) ⇒
  client_safe_l0 a c N rqs lc io
Proof
  rewrite_tac[client_safe_l0_def] >> strip_tac >> gen_tac >> strip_tac >>
  qpat_x_assum ‘∀evs. LPREFIX _ _ ⇒ _’ drule >> strip_tac >>
  qspecl_then [‘a’, ‘N’, ‘rqs’, ‘lc’, ‘R’, ‘pre’, ‘evs’, ‘c’, ‘bs’] mp_tac
    (Q.GENL [‘a’, ‘N’, ‘rqs’, ‘lc’, ‘R’, ‘pre’, ‘evs’, ‘c’, ‘bs’] client_prefix_safe) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* ------------------------------------------------------------------------
   The rounds' events
   ------------------------------------------------------------------------ *)

Theorem erun_SOME:
  erounds lfd pol ifds m ws0 n ≠ NONE ⇒
  erounds lfd pol ifds m ws0 n = SOME (erun lfd pol ifds m ws0 n)
Proof
  Cases_on ‘erounds lfd pol ifds m ws0 n’ >> simp[erun_def]
QED

Theorem erun_evs_FLAT:
  ∀n. erounds lfd pol ifds m ws0 n ≠ NONE ⇒
      FST (SND (SND (erun lfd pol ifds m ws0 n))) =
      FLAT (GENLIST (eround_evs lfd pol ifds m ws0) n)
Proof
  Induct >- simp[] >> strip_tac >>
  ‘erounds lfd pol ifds m ws0 n ≠ NONE’
    by (irule erounds_LE_SOME >> qexists_tac ‘SUC n’ >> simp[]) >>
  first_x_assum drule >> drule erun_SUC >> strip_tac >>
  simp[GENLIST, SNOC_APPEND]
QED

(* ------------------------------------------------------------------------
   The startup
   ------------------------------------------------------------------------ *)

Theorem listen_SOME[local]:
  ∃out w' ev. sys_listen_port c w = SOME (out, w', ev)
Proof
  simp[sys_listen_port_def, l0_do_def, l0_ffi_fn_def, l0_call_def,
       port_bytes_def, l0_hdr_def] >>
  every_case_tac >> gvs[]
QED

Theorem listen_ev[local]:
  sys_listen_port c w = SOME (out, w', ev) ⇒
  ev = IO_event (ExtCall «sys_listen») (port_bytes c) (ZIP (REPLICATE 13 0w, out))
Proof
  simp[sys_listen_port_def, l0_do_def, AllCaseEqs()] >> rw[] >> simp[]
QED

Theorem listen_failed_res[local]:
  LENGTH out = 13 ∧ listen_fd out = NONE ⇒
  ∀k. l0_ev_res (ZIP (REPLICATE 13 (0w : word8), out)) ≠ SOME (Ok k)
Proof
  rpt strip_tac >> gvs[l0_ev_res_def, MAP_ZIP, listen_fd_def, l0_res_of_def]
QED

Theorem fdok_name[local]:
  l0_do «sys_fdok» [f] 1 w = SOME (out, w', ev) ⇒ ev_name ev = ExtCall «sys_fdok»
Proof
  simp[fdok_do] >> rw[] >> simp[ev_name_def]
QED

Theorem start_reach[local]:
  l0_rely w0 ∧ w0.hist = [] ∧ FDOK3 w0 w1 w2 w3 o0 o1 o2 e0 e1 e2 ⇒ l0_reach w0 w3
Proof
  strip_tac >>
  ‘l0_reach w0 w0’ by (irule l0_reach_init >> conj_tac >> first_assum ACCEPT_TAC) >>
  ‘l0_reach w0 w1’
    by (irule l0_do_reach >> qpat_assum ‘l0_do _ [0w] _ w0 = _’ (irule_at Any) >>
        first_assum ACCEPT_TAC) >>
  ‘l0_reach w0 w2’
    by (irule l0_do_reach >> qpat_assum ‘l0_do _ [1w] _ w1 = _’ (irule_at Any) >>
        first_assum ACCEPT_TAC) >>
  irule l0_do_reach >> qpat_assum ‘l0_do _ [2w] _ w2 = _’ (irule_at Any) >>
  first_assum ACCEPT_TAC
QED

(* The answers of three open fds *)
Theorem fdok_open_evs[local]:
  FDOK3 w0 w1 w2 w3 o0 o1 o2 e0 e1 e2 ∧ fdok_all o0 o1 o2 ⇒
  e0 = IO_event (ExtCall «sys_fdok») [0w] [(0w, 1w)] ∧
  e1 = IO_event (ExtCall «sys_fdok») [1w] [(0w, 1w)] ∧
  e2 = IO_event (ExtCall «sys_fdok») [2w] [(0w, 1w)]
Proof
  rewrite_tac[fdok_all_def] >> strip_tac >> gvs[fdok_do]
QED

Theorem fdok_open_io[local]:
  stdio_open (LAPPEND (fromList [IO_event (ExtCall «sys_fdok») [0w] [(0w, 1w)];
                                 IO_event (ExtCall «sys_fdok») [1w] [(0w, 1w)];
                                 IO_event (ExtCall «sys_fdok») [2w] [(0w, 1w)]]) rest)
Proof
  rewrite_tac[stdio_open_def] >> qexistsl_tac [‘0w’, ‘0w’, ‘0w’, ‘rest’] >> rewrite_tac[]
QED

Theorem erun_SOME_parts[local]:
  erounds lfd pol ifds m (w0, es0) n ≠ NONE ⇒
  ∃h w es evs logs. erounds lfd pol ifds m (w0, es0) n = SOME (h, (w, es), evs, logs) ∧
                    erun lfd pol ifds m (w0, es0) n = (h, (w, es), evs, logs)
Proof
  strip_tac >> drule erun_SOME >>
  Cases_on ‘erun lfd pol ifds m (w0, es0) n’ >> PairCases_on ‘r’ >> simp[]
QED

(* Every round boundary of a total run is safe *)
Theorem rounds_safe_all[local]:
  (∀n. erounds lfd pol ifds m ws0 n ≠ NONE) ∧
  (∀n h ws evs logs. erounds lfd pol ifds m ws0 n = SOME (h, ws, evs, logs) ⇒ P evs) ⇒
  ∀n. P (FST (SND (SND (erun lfd pol ifds m ws0 n))))
Proof
  rpt strip_tac >>
  qpat_x_assum ‘∀n. _ ≠ NONE’ (qspec_then ‘n’ (assume_tac o MATCH_MP erun_SOME)) >>
  Cases_on ‘erun lfd pol ifds m ws0 n’ >> PairCases_on ‘r’ >> gvs[] >>
  first_x_assum drule >> simp[]
QED

(* ------------------------------------------------------------------------
   The claim
   ------------------------------------------------------------------------ *)

Theorem client_prog_l0_claim:
  l0_client_claim client_prog
Proof
  rewrite_tac[l0_client_claim_def] >> rpt strip_tac >>
  ‘w0.hist = []’ by fs[l0_fresh_def] >>
  ‘honestL0WorldProps$fds_lt w0’ by fs[fds_lt_eq] >>
  ‘∃o0 w1 e0. l0_do «sys_fdok» [0w] 1 w0 = SOME (o0, w1, e0)’ by simp[fdok_do] >>
  ‘∃o1 w2 e1. l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1)’ by simp[fdok_do] >>
  ‘∃o2 w3 e2. l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2)’ by simp[fdok_do] >>
  ‘EVERY (λev. ev_name ev = ExtCall «sys_fdok») [e0; e1; e2]’
    by (simp[] >> rpt conj_tac >> irule fdok_name >> rpt (first_assum (irule_at Any))) >>
  Cases_on ‘fdok_all o0 o1 o2’
  >- (‘∃out w4 ev. sys_listen_port c w3 = SOME (out, w4, ev)’ by simp[listen_SOME] >>
      ‘l0_reach w0 w3’ by (irule start_reach >> rpt (first_assum (irule_at Any))) >>
      ‘LENGTH out = 13’
        by (qpat_assum ‘sys_listen_port _ _ = _’
              (assume_tac o REWRITE_RULE [sys_listen_port_def]) >>
            drule_all e1DriverSpecTheory.l0_do_length >> simp[]) >>
      ‘ev = IO_event (ExtCall «sys_listen») (port_bytes c) (ZIP (REPLICATE 13 0w, out))’
        by (drule listen_ev >> simp[]) >>
      drule_all fdok_open_evs >> strip_tac >>
      Cases_on ‘listen_fd out’
      >- (qexists_tac ‘Terminate Success [e0; e1; e2; ev]’ >> rpt conj_tac
          >- (irule client_nolisten_semantics >> rpt (first_assum (irule_at Any)))
          >- simp[] >>
          disj2_tac >> disj1_tac >> rewrite_tac[l0_listen_failed_def] >>
          qexistsl_tac [‘0w’, ‘0w’, ‘0w’, ‘port_bytes c’, ‘ZIP (REPLICATE 13 0w, out)’] >>
          asm_rewrite_tac[] >> irule listen_failed_res >> conj_tac >> first_assum ACCEPT_TAC)
      >> rename1 ‘listen_fd out = SOME k’ >>
      drule_all e1_start_world >> strip_tac >>
      drule_all e1_start_stdio_used >> strip_tac >>
      ‘N < cbound’
        by (qpat_assum ‘N < 2 ** 63’ mp_tac >> rewrite_tac[moonshotClientSpecTheory.cbound_def]) >>
      qspecl_then [‘N’, ‘rqs’, ‘a’, ‘w4’, ‘n2w k’, ‘pol_never’] mp_tac
        (Q.GENL [‘N’, ‘rqs’, ‘a’, ‘w0’, ‘lfd’, ‘pol’] client_rounds_safe) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then (qx_choose_then ‘lc’ strip_assume_tac) >>
      qspecl_then [‘a’, ‘N’, ‘w4’, ‘n2w k’, ‘pol_never’, ‘rqs’] mp_tac
        (Q.GENL [‘a’, ‘N’, ‘w0’, ‘lfd’, ‘pol’, ‘rqs’] client_l1_total) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then (assume_tac o CONJUNCT1) >>
      qspecl_then [‘client_round_safe a N rqs lc’, ‘n2w k’, ‘pol_never’, ‘cifds a N rqs’,
                   ‘cprog a N rqs’, ‘(w4, einit)’] mp_tac
        (Q.GENL [‘P’, ‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘ws0’] rounds_safe_all) >>
      impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
      BETA_TAC >> strip_tac >>
      Cases_on ‘∃n. call_done (cstate a N rqs
                   (FST (erun (n2w k) pol_never (cifds a N rqs) (cprog a N rqs) (w4, einit) n)))’
      >- (pop_assum (strip_assume_tac o HO_MATCH_MP arithmeticTheory.WOP) >>
          qspecl_then [‘n2w k’, ‘pol_never’, ‘cifds a N rqs’, ‘cprog a N rqs’, ‘w4’, ‘einit’, ‘n’]
            mp_tac (Q.GENL [‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘es0’, ‘n’] erun_SOME_parts) >>
          impl_tac >- (qpat_assum ‘∀n. erounds _ _ _ _ _ n ≠ NONE’ (qspec_then ‘n’ ACCEPT_TAC)) >>
          strip_tac >>
          qexists_tac ‘Terminate Success ([e0; e1; e2; ev] ++ evs)’ >> rpt conj_tac
          >- (irule client_term_n_semantics >> rpt (first_assum (irule_at Any)) >>
              conj_tac >- (qpat_assum ‘erun _ _ _ _ _ n = _’ (fn th =>
                             qpat_assum ‘call_done _’ (ACCEPT_TAC o REWRITE_RULE [th, FST]))) >>
              first_assum ACCEPT_TAC)
          >- simp[] >>
          disj2_tac >> disj2_tac >> conj_tac
          >- (rewrite_tac[beh_io_def] >>
              ‘[e0; e1; e2; ev] ++ evs = [e0; e1; e2] ++ ev :: evs’ by simp[] >>
              pop_assum SUBST1_TAC >> rewrite_tac[GSYM LAPPEND_fromList] >>
              qpat_x_assum ‘e0 = _’ SUBST1_TAC >> qpat_x_assum ‘e1 = _’ SUBST1_TAC >>
              qpat_x_assum ‘e2 = _’ SUBST1_TAC >> rewrite_tac[fdok_open_io]) >>
          qexists_tac ‘lc’ >> rewrite_tac[beh_io_def] >>
          qspecl_then [‘lc’, ‘N’, ‘[e0; e1; e2]’, ‘fromList ([e0; e1; e2; ev] ++ evs)’, ‘a’, ‘rqs’,
                       ‘c’, ‘ZIP (REPLICATE 13 0w, out)’] mp_tac
            (Q.GENL [‘lc’, ‘N’, ‘pre’, ‘io’, ‘a’, ‘rqs’, ‘c’, ‘bs’] client_safe_io) >>
          impl_tac
          >- (rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
              rpt strip_tac >> qexists_tac ‘evs’ >> conj_tac
              >- (qpat_x_assum ‘∀n. client_round_safe _ _ _ _ _’ (qspec_then ‘n’ mp_tac) >>
                  qpat_assum ‘erun _ _ _ _ _ n = _’ SUBST1_TAC >> simp[]) >>
              qpat_x_assum ‘LPREFIX _ _’ mp_tac >> rewrite_tac[e1_lprefix_fromList] >>
              qpat_assum ‘ev = _’ (SUBST1_TAC o SYM) >> simp[]) >>
          disch_then ACCEPT_TAC)
      >> pop_assum (assume_tac o SIMP_RULE bool_ss [NOT_EXISTS_THM]) >>
      qexists_tac ‘Diverge (LAPPEND (fromList [e0; e1; e2; ev]) (LFLATTEN (LGENLIST
         (λi. fromList (eround_evs (n2w k) pol_never (cifds a N rqs) (cprog a N rqs) (w4, einit) i)) NONE)))’ >>
      rpt conj_tac
      >- (irule client_div_n_semantics >> rpt (first_assum (irule_at Any)) >>
          conj_tac >> first_assum ACCEPT_TAC)
      >- simp[] >>
      disj2_tac >> disj2_tac >> conj_tac
      >- (rewrite_tac[beh_io_def] >>
          ‘fromList [e0; e1; e2; ev] = LAPPEND (fromList [e0; e1; e2]) (fromList [ev])’
            by rewrite_tac[LAPPEND_fromList, APPEND] >>
          pop_assum SUBST1_TAC >> rewrite_tac[LAPPEND_ASSOC] >>
          qpat_x_assum ‘e0 = _’ SUBST1_TAC >> qpat_x_assum ‘e1 = _’ SUBST1_TAC >>
          qpat_x_assum ‘e2 = _’ SUBST1_TAC >> rewrite_tac[fdok_open_io]) >>
      qexists_tac ‘lc’ >> rewrite_tac[beh_io_def] >>
      qspecl_then [‘lc’, ‘N’, ‘[e0; e1; e2]’,
                   ‘LAPPEND (fromList [e0; e1; e2; ev]) (LFLATTEN (LGENLIST
                      (λi. fromList (eround_evs (n2w k) pol_never (cifds a N rqs) (cprog a N rqs) (w4, einit) i)) NONE))’, ‘a’, ‘rqs’,
                   ‘c’, ‘ZIP (REPLICATE 13 0w, out)’] mp_tac
        (Q.GENL [‘lc’, ‘N’, ‘pre’, ‘io’, ‘a’, ‘rqs’, ‘c’, ‘bs’] client_safe_io) >>
      impl_tac
      >- (rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
          rpt strip_tac >> drule e1_lprefix_rounds >> strip_tac >>
          qexists_tac ‘FST (SND (SND (erun (n2w k) pol_never (cifds a N rqs) (cprog a N rqs) (w4, einit) n)))’ >> conj_tac
          >- (qpat_x_assum ‘∀n. client_round_safe _ _ _ _ _’ (qspec_then ‘n’ ACCEPT_TAC)) >>
          ‘FST (SND (SND (erun (n2w k) pol_never (cifds a N rqs) (cprog a N rqs) (w4, einit) n))) = FLAT (GENLIST (eround_evs (n2w k) pol_never (cifds a N rqs) (cprog a N rqs) (w4, einit)) n)’
            by (irule erun_evs_FLAT >>
                qpat_assum ‘∀n. erounds _ _ _ _ _ n ≠ NONE’ (qspec_then ‘n’ ACCEPT_TAC)) >>
          pop_assum SUBST1_TAC >>
          qpat_x_assum ‘_ ≼ _ ++ FLAT _’ mp_tac >>
          qpat_assum ‘ev = _’ (SUBST1_TAC o SYM) >> simp[]) >>
      disch_then ACCEPT_TAC) >>
  qexists_tac ‘Terminate Success [e0; e1; e2]’ >>
  conj_tac
  >- (irule client_closed_semantics >> rpt conj_tac >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC >>
      qexistsl [‘o0’, ‘o1’, ‘o2’, ‘w1’, ‘w2’, ‘w3’] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[stdio_closed_def] >> gvs[fdok_do, fdok_all_def] >> every_case_tac >> gvs[]
QED
