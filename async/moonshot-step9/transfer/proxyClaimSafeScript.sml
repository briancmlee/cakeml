(*
  Moonshot step 9: the proxy's safety claim in the form step 12 consumes
  (moonshotStep12Stmts.proxy_claim_safe, the safety half of l0_proxy_claim,
  with D37's stdio_open / no_close_stdio), for the proxy program, given the
  buffering bound of every run (proxy_bound_ok).  No liveness.

  proxy_claim_safe is stated on proxyL0StmtsCopy (a verbatim copy of the
  statement's safety half); the copy's proxy_safe_l0 is the real one.
*)
Theory proxyClaimSafe
Ancestors
  proxyClaim moonshotStep12Stmts moonshotClientL0Stmts proxyL0StmtsCopy proxyL0Stmts honestL1BStmts
  proxySafeRun proxySem proxyStart proxyL0Run e1DriverMain e1DriverProg honestL0Fdok honestL0Outcome
  honestL1PFRound l0sysBridges llist
Libs
  preamble

(* ------------------------------------------------------------------------
   The copy's proxy_safe_l0 is the real one
   ------------------------------------------------------------------------ *)

Theorem pos_open_copy:
  proxyL0StmtsCopy$pos_open = proxyL0Stmts$pos_open
Proof
  simp[FUN_EQ_THM, proxyL0StmtsCopyTheory.pos_open_def, proxyL0StmtsTheory.pos_open_def,
       pos_fd_copy, pos_ends_copy]
QED

Theorem poll_ev_copy:
  proxyL0StmtsCopy$poll_ev = honestL1BStmts$poll_ev
Proof
  simp[FUN_EQ_THM, proxyL0StmtsCopyTheory.poll_ev_def, honestL1BStmtsTheory.poll_ev_def]
QED

Theorem out_poll_copy:
  proxyL0StmtsCopy$out_poll = honestL1BStmts$out_poll
Proof
  simp[FUN_EQ_THM, proxyL0StmtsCopyTheory.out_poll_def, honestL1BStmtsTheory.out_poll_def]
QED

Theorem n_out_polls_copy:
  proxyL0StmtsCopy$n_out_polls = honestL1BStmts$n_out_polls
Proof
  simp[FUN_EQ_THM, proxyL0StmtsCopyTheory.n_out_polls_def, honestL1BStmtsTheory.n_out_polls_def,
       out_poll_copy]
QED

Theorem send_took_copy:
  proxyL0StmtsCopy$send_took = honestL1BStmts$send_took
Proof
  simp[FUN_EQ_THM] >> Cases_on ‘x'’ >>
  simp[proxyL0StmtsCopyTheory.send_took_def, honestL1BStmtsTheory.send_took_def, l0_ev_res_copy]
QED

Theorem pos_timed_out_copy:
  proxyL0StmtsCopy$pos_timed_out = proxyL0Stmts$pos_timed_out
Proof
  simp[FUN_EQ_THM, proxyL0StmtsCopyTheory.pos_timed_out_def, proxyL0StmtsTheory.pos_timed_out_def,
       pos_open_copy, pos_fd_copy, n_out_polls_copy, poll_ev_copy, out_poll_copy, send_took_copy,
       pos_ends_copy]
QED

Theorem proxy_bnd_copy:
  proxyL0StmtsCopy$proxy_bnd = proxyL0Stmts$proxy_bnd
Proof
  simp[FUN_EQ_THM, proxyL0StmtsCopyTheory.proxy_bnd_def, proxyL0StmtsTheory.proxy_bnd_def]
QED

Theorem proxy_safe_l0_copy:
  proxyL0StmtsCopy$proxy_safe_l0 = proxyL0Stmts$proxy_safe_l0
Proof
  simp[FUN_EQ_THM, proxyL0StmtsCopyTheory.proxy_safe_l0_def, proxyL0StmtsTheory.proxy_safe_l0_def,
       pbytes_copy, l0_ev_res_copy, l0_event_connected_copy, connect_port_copy, is_front_copy,
       pos_sent_copy, pos_read_copy, pos_timed_out_copy, proxy_bnd_copy]
QED

(* ------------------------------------------------------------------------
   The start
   ------------------------------------------------------------------------ *)

Theorem sys_listen_port_SOME:
  ∃out w1 ev. sys_listen_port a w = SOME (out, w1, ev)
Proof
  simp[sys_listen_port_def, honestL1ModelTheory.l0_do_def, honestL0WorldTheory.l0_ffi_fn_def, honestL0WorldTheory.l0_call_def,
       honestL1EPModelTheory.port_bytes_def, honestL0WorldTheory.l0_hdr_def] >>
  every_case_tac >> gvs[]
QED

Theorem fdok_SOME:
  ∃out w1 ev. l0_do «sys_fdok» [f] 1 w = SOME (out, w1, ev)
Proof
  simp[fdok_do]
QED

Theorem l0_deliver_rely:
  l0_rely w ⇒ l0_rely (l0_deliver w x)
Proof
  strip_tac >> irule honestL0RelyTheory.l0_rely_ch >> qexists_tac ‘w’ >>
  Cases_on ‘x’ >> rw[honestL0WorldTheory.l0_deliver_def] >> every_case_tac >>
  simp[honestL0WorldTheory.upd_lchan_def]
QED

Theorem l0_tick_rely:
  l0_rely w ⇒ l0_rely (l0_tick nm w)
Proof
  simp[honestL0WorldTheory.l0_tick_def] >>
  ‘∀as w. l0_rely w ⇒ l0_rely (FOLDL l0_deliver w as)’
    by (Induct >> simp[] >> metis_tac[l0_deliver_rely]) >>
  rw[] >> first_x_assum irule >> irule honestL0RelyTheory.l0_rely_ch >>
  qexists_tac ‘w’ >> simp[]
QED

(* A failed listen's event has no Ok result *)
Theorem listen_failed_res:
  l0_rely w ∧ sys_listen_port a w = SOME (out, w1, ev) ∧ listen_fd out = NONE ⇒
  ∃conf bs. ev = IO_event (ExtCall «sys_listen») conf bs ∧ ∀k. l0_ev_res bs ≠ SOME (Ok k)
Proof
  rw[sys_listen_port_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  ‘l0_rely (l0_tick «sys_listen» w)’ by simp[l0_tick_rely] >>
  ‘LENGTH out = 13’ by (drule_all honestL0WorldPropsTheory.l0_call_length >> simp[]) >>
  gvs[honestEchoL0SpecTheory.l0_ev_res_def, MAP_ZIP, listen_fd_def, honestL1ModelTheory.l0_res_of_def,
      AllCaseEqs()] >>
  every_case_tac >> gvs[]
QED

(* ------------------------------------------------------------------------
   The claim
   ------------------------------------------------------------------------ *)

Theorem proxy_claim_safe_holds:
  (∀a b w0 pre w4 k.
     proxy_start a w0 pre w4 k ∧ b < 65536 ⇒
     proxy_bound_ok kt hw (proxy_pr a b hw k w4 (proxy_run_io b hw k w4 pre)) (proxy_run_io b hw k w4 pre)) ⇒
  proxy_claim_safe kt hw (λa b. proxy_prog a b hw)
Proof
  rw[proxy_claim_safe_def] >>
  qspecl_then [‘0w’, ‘w0’] (qx_choosel_then [‘o0’, ‘w1’, ‘e0’] assume_tac) (Q.GENL [‘f’, ‘w’] fdok_SOME) >>
  qspecl_then [‘1w’, ‘w1’] (qx_choosel_then [‘o1’, ‘w2’, ‘e1’] assume_tac) (Q.GENL [‘f’, ‘w’] fdok_SOME) >>
  qspecl_then [‘2w’, ‘w2’] (qx_choosel_then [‘o2’, ‘w3’, ‘e2’] assume_tac) (Q.GENL [‘f’, ‘w’] fdok_SOME) >>
  qspecl_then [‘a’, ‘w3’] (qx_choosel_then [‘out’, ‘w4’, ‘ev’] assume_tac) (Q.GENL [‘a’, ‘w’] sys_listen_port_SOME) >>
  ‘w0.hist = []’ by fs[l0_fresh_def] >>
  Cases_on ‘fdok_all o0 o1 o2’
  >- (Cases_on ‘listen_fd out’
      >- ((* the listen failed *)
          qexists_tac ‘Terminate Success [e0; e1; e2; ev]’ >> conj_tac
          >- (irule proxy_nolisten_semantics >> simp[] >>
              qexistsl_tac [‘o0’, ‘o1’, ‘o2’, ‘out’, ‘w1’, ‘w2’, ‘w3’, ‘w4’] >> simp[]) >>
          simp[] >> disj2_tac >> disj1_tac >>
          ‘l0_rely w3’ by metis_tac[honestL1PFRefineTheory.l0_do_rely] >>
          drule_all listen_failed_res >> strip_tac >>
          gvs[l0_listen_failed_def, fdok_all_def, fdok_do, l0_ev_res_copy]) >>
      (* the listener k: E1's rounds *)
      rename1 ‘listen_fd out = SOME k’ >>
      ‘proxy_start a w0 [e0; e1; e2; ev] w4 k’
        by (fs[proxy_start_def, proxyL0StmtsTheory.l0_proxy_world_def, l0_fresh_def, fdok_all_def,
               sys_listen_port_def, listen_fd_def, AllCaseEqs(), fds_lt_copy]) >>
      qexists_tac ‘Diverge (proxy_run_io b hw k w4 [e0; e1; e2; ev])’ >>
      conj_tac >- (drule_all proxy_run_semantics >> simp[]) >>
      simp[beh_io_def] >> disj2_tac >> disj2_tac >> rpt conj_tac
      >- (drule proxy_start_unfold >> strip_tac >> gvs[] >>
          simp[stdio_open_def, proxy_run_io_def] >>
          qexistsl_tac [‘0w’, ‘0w’, ‘0w’] >> simp[])
      >- (qexists_tac ‘proxy_pr a b hw k w4 (proxy_run_io b hw k w4 [e0; e1; e2; ev])’ >>
          rewrite_tac[proxy_safe_l0_copy] >> irule proxy_run_safe
          >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, qexists_tac ‘w0’ >> first_assum ACCEPT_TAC,
            first_x_assum (qspecl_then [‘a’, ‘b’, ‘w0’, ‘[e0; e1; e2; ev]’, ‘w4’, ‘k’] mp_tac) >> simp[]])
      >> rpt strip_tac >> drule_all proxy_run_no_close_stdio >> simp[]) >>
  (* stdio closed *)
  qexists_tac ‘Terminate Success [e0; e1; e2]’ >> conj_tac
  >- (irule proxy_closed_semantics >> simp[] >>
      qexistsl_tac [‘o0’, ‘o1’, ‘o2’, ‘w1’, ‘w2’, ‘w3’] >> simp[]) >>
  simp[] >> disj1_tac >> irule fdok_closed >>
  qexistsl_tac [‘o0’, ‘o1’, ‘o2’, ‘w0’, ‘w1’, ‘w2’, ‘w3’] >> fs[fdok_all_def]
QED
