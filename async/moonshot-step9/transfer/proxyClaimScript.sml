(*
  Moonshot step 9: the proxy run's hypotheses discharged.  After the
  proxy's start (proxy_start), its E1 rounds never fail (proxy-e1's
  proxy_l1_total), the program diverges with the run's trace
  (proxy_div_n_semantics), and every prefix of that trace is ep_ok
  (proxyLone.lone_ep_ok: fd 0 is checked first, and E1 never closes
  stdio, moonshotStdioClose).  So proxy_safe_l0 holds of the run given
  only the buffering bound (proxy_bound_ok).
*)
Theory proxyClaim
Ancestors
  proxySafeRun proxyLone proxySem proxyTotal moonshotStdioClose moonshotW2 proxyStart proxyL0Run
  e1World e1DriverMain e1DriverProg honestL0Fdok e1DriverLoop llist
Libs
  preamble

Theorem proxy_start_unfold:
  proxy_start a w0 pre w4 k ⇒
  ∃w1 w2 w3 e0 e1 e2 out ev.
    l0_proxy_world w0 ∧
    FDOK3 w0 w1 w2 w3 [1w] [1w] [1w] e0 e1 e2 ∧ fdok_all [1w] [1w] [1w] ∧
    sys_listen_port a w3 = SOME (out, w4, ev) ∧ listen_fd out = SOME k ∧
    pre = [e0; e1; e2; ev] ∧
    e0 = IO_event (ExtCall «sys_fdok») [0w] [(0w, 1w)] ∧
    e1 = IO_event (ExtCall «sys_fdok») [1w] [(0w, 1w)] ∧
    e2 = IO_event (ExtCall «sys_fdok») [2w] [(0w, 1w)]
Proof
  rw[proxy_start_def] >>
  rpt (qpat_x_assum ‘l0_do «sys_fdok» _ _ _ = _’
         (strip_assume_tac o REWRITE_RULE [fdok_do])) >>
  gvs[] >>
  simp[fdok_do, fdok_all_def, sys_listen_port_def, listen_fd_def]
QED

Theorem proxy_ptot:
  proxy_start a w0 pre w4 k ∧ b < 65536 ⇒
  ptot k b hw w4 ∧
  ∀n. SND (ecm (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) w4 n) + 1 < dimword (:64)
Proof
  strip_tac >> drule proxy_start_facts >> strip_tac >>
  qspecl_then [‘b’, ‘w4’, ‘plfd k’, ‘pol_never’, ‘hw’] mp_tac
    (Q.GENL [‘b’, ‘w0’, ‘lfd’, ‘pol’, ‘hw’] proxy_l1_total) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[]
QED

Theorem proxy_run_semantics:
  proxy_start a w0 pre w4 k ∧ b < 65536 ⇒
  semantics_prog (init_state (l0_ffi w0)) init_env (proxy_prog a b hw)
    (Diverge (proxy_run_io b hw k w4 pre))
Proof
  strip_tac >> drule_all proxy_ptot >> disch_then (qspec_then ‘hw’ strip_assume_tac) >>
  drule proxy_start_unfold >> strip_tac >>
  rewrite_tac[proxy_run_io_def] >> qpat_x_assum ‘pre = _’ SUBST1_TAC >>
  irule proxy_div_n_semantics >>
  qpat_x_assum ‘l0_proxy_world _’ (strip_assume_tac o REWRITE_RULE [proxyL0StmtsTheory.l0_proxy_world_def]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl_tac [‘[1w]’, ‘[1w]’, ‘[1w]’, ‘out’, ‘w1’, ‘w2’, ‘w3’] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* The run's events after the start close no stdio fd *)
Theorem proxy_run_no_close0:
  proxy_start a w0 pre w4 k ∧ b < 65536 ∧
  LPREFIX (fromList ft) (proxy_run_io b hw k w4 pre) ⇒ no_close0 ft
Proof
  strip_tac >> drule_all proxy_ptot >> disch_then (qspec_then ‘hw’ strip_assume_tac) >>
  drule_all proxy_run_cover >> strip_tac >>
  drule proxy_start_facts >> strip_tac >>
  drule proxy_start_unfold >> strip_tac >>
  ‘MEM (1w : word64) (l0_used w4) ∧ MEM (2w : word64) (l0_used w4)’
    by (drule_all e1_start_stdio_used >> simp[]) >>
  qabbrev_tac ‘PEn = erun (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4, einit) n’ >>
  ‘erounds (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4, einit) n =
     SOME (FST PEn, FST (SND PEn), FST (SND (SND PEn)), SND (SND (SND PEn)))’
    by (qunabbrev_tac ‘PEn’ >> irule erounds_erun >>
        qpat_x_assum ‘ptot _ _ _ _’ (fn th => ACCEPT_TAC (SPEC “n:num” th))) >>
  ‘no_close_stdio (FST (SND (SND PEn)))’
    by (qspecl_then [‘w4’, ‘plfd k’, ‘pol_never’, ‘pifds_k b hw k’, ‘pprog_k b hw k’] mp_tac
          (Q.GENL [‘w0’, ‘lfd’, ‘pol’, ‘ifds’, ‘m’] erounds_no_close_stdio) >>
        impl_tac >- (simp[GSYM fds_lt_copy] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
        disch_then drule >> simp[]) >>
  irule no_close0_stdio >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘no_close_stdio _’ mp_tac >> rewrite_tac[honestL0OutcomeTheory.no_close_stdio_def] >>
  disch_then irule >> simp[] >>
  ‘MEM (IO_event (ExtCall «sys_close») conf bs) (pre ++ FST (SND (SND PEn)))’
    by (qunabbrev_tac ‘PEn’ >> metis_tac[IS_PREFIX_MEM]) >>
  qexists_tac ‘bs’ >>
  qpat_x_assum ‘sys_listen_port _ _ = _’ (strip_assume_tac o MATCH_MP honestL1PFRoundTheory.l0_do_cases o
                                          REWRITE_RULE [sys_listen_port_def]) >>
  qpat_x_assum ‘MEM _ (pre ++ _)’ mp_tac >> simp[]
QED

Theorem proxy_run_ep_ok:
  proxy_start a w0 pre w4 k ∧ b < 65536 ∧
  LPREFIX (fromList ft) (proxy_run_io b hw k w4 pre) ⇒ ep_ok ft
Proof
  strip_tac >>
  ‘no_close0 ft’ by (irule proxy_run_no_close0 >> metis_tac[]) >>
  drule_all proxy_run_semantics >> disch_then (qspec_then ‘hw’ assume_tac) >>
  drule proxy_start_unfold >> strip_tac >>
  ‘fd0_checked ft’
    by (irule fd0_checked_stdio >> qpat_x_assum ‘LPREFIX _ _’ mp_tac >>
        simp[proxy_run_io_def] >> strip_tac >>
        qexistsl_tac [‘0w’, ‘0w’, ‘0w’, ‘LAPPEND (fromList [ev]) (LFLATTEN (LGENLIST
           (λi. fromList (eround_evs (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4, einit) i))
           NONE))’] >>
        simp[] >> ‘[e0; e1; e2; ev] = [e0; e1; e2] ++ [ev]’ by simp[] >>
        fs[GSYM LAPPEND_fromList, LAPPEND_ASSOC]) >>
  irule lone_ep_ok >> fs[proxyL0StmtsTheory.l0_proxy_world_def] >>
  qexistsl_tac [‘Diverge (proxy_run_io b hw k w4 pre)’, ‘proxy_prog a b hw’, ‘w0’] >>
  fs[l0sysBridgesTheory.beh_io_def, fds_lt_copy]
QED

(* proxy_safe_l0 for the run, given the buffering bound *)
Theorem proxy_run_safe:
  proxy_start a w0 pre w4 k ∧ b < 65536 ∧
  proxy_bound_ok kt hw (proxy_pr a b hw k w4 (proxy_run_io b hw k w4 pre)) (proxy_run_io b hw k w4 pre) ⇒
  proxy_safe_l0 kt hw a b (proxy_pr a b hw k w4 (proxy_run_io b hw k w4 pre)) (proxy_run_io b hw k w4 pre)
Proof
  strip_tac >>
  ‘∀ft. LPREFIX (fromList ft) (proxy_run_io b hw k w4 pre) ⇒ ep_ok ft’
    by (rpt strip_tac >> drule_all proxy_run_ep_ok >> simp[]) >>
  drule_all proxy_ptot >> disch_then (qspec_then ‘hw’ strip_assume_tac) >>
  drule_all proxy_safe_run_bound >> simp[]
QED
