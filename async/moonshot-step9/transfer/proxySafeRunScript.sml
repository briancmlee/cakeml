(*
  Moonshot step 9, item 5: the proxy's safety on its raw L0 trace
  (proxy_safe_l0) for the run proxy_run_io, from the handle-layer guarantee
  (moonshotProxySafe) carried down by E1's trace lemmas (e1TraceLag), with
  episodes named by position through moonshotProxyGlue.pos_ep_prefix.

  ep_ok (honest L0 answers on the trace) is a hypothesis here, discharged
  at the claim from the lone-program trace lemmas (moonshotLoneTrace).
*)
Theory proxySafeRun
Ancestors
  honestL1PFRefine moonshotSentGlue honestEchoL0Spec l0sysInv l0sysEpisodes e1DriverLoop moonshotProxySafe proxyHLStmts
  moonshotProxyGlue e1TraceLag e1TracePrefix e1TraceRound proxyStart proxyL0Run proxyL1Claim
  llist
Libs
  preamble

(* ------------------------------------------------------------------------
   The glue's copies are the real definitions
   ------------------------------------------------------------------------ *)

Theorem l0_ev_res_copy:
  honestEchoL0SpecCopy$l0_ev_res = honestEchoL0Spec$l0_ev_res
Proof
  simp[FUN_EQ_THM, honestEchoL0SpecCopyTheory.l0_ev_res_def, honestEchoL0SpecTheory.l0_ev_res_def]
QED

Theorem l0_event_accepted_copy:
  honestEchoL0SpecCopy$l0_event_accepted = honestEchoL0Spec$l0_event_accepted
Proof
  simp[FUN_EQ_THM] >> Cases >> rename1 ‘IO_event nm _ _’ >> Cases_on ‘nm’ >>
  simp[honestEchoL0SpecCopyTheory.l0_event_accepted_def, honestEchoL0SpecTheory.l0_event_accepted_def,
       l0_ev_res_copy]
QED

Theorem l0_event_closed_copy:
  honestEchoL0SpecCopy$l0_event_closed = honestEchoL0Spec$l0_event_closed
Proof
  simp[FUN_EQ_THM] >> Cases >> rename1 ‘IO_event nm _ _’ >> Cases_on ‘nm’ >>
  simp[honestEchoL0SpecCopyTheory.l0_event_closed_def, honestEchoL0SpecTheory.l0_event_closed_def,
       l0_ev_res_copy]
QED

Theorem l0_event_sent_copy:
  honestEchoL0SpecCopy$l0_event_sent f = honestEchoL0Spec$l0_event_sent f
Proof
  simp[FUN_EQ_THM] >> Cases >> rename1 ‘IO_event nm _ _’ >> Cases_on ‘nm’ >>
  simp[honestEchoL0SpecCopyTheory.l0_event_sent_def, honestEchoL0SpecTheory.l0_event_sent_def,
       l0_ev_res_copy]
QED

Theorem l0_event_recv_copy:
  honestEchoL0SpecCopy$l0_event_recv f = honestEchoL0Spec$l0_event_recv f
Proof
  simp[FUN_EQ_THM] >> Cases >> rename1 ‘IO_event nm _ _’ >> Cases_on ‘nm’ >>
  simp[honestEchoL0SpecCopyTheory.l0_event_recv_def, honestEchoL0SpecTheory.l0_event_recv_def,
       l0_ev_res_copy]
QED

Theorem l0_event_connected_copy:
  proxyL0StmtsCopy$l0_event_connected = proxyL0Stmts$l0_event_connected
Proof
  simp[FUN_EQ_THM] >> Cases >> rename1 ‘IO_event nm _ _’ >> Cases_on ‘nm’ >>
  simp[proxyL0StmtsCopyTheory.l0_event_connected_def, proxyL0StmtsTheory.l0_event_connected_def]
QED

Theorem connect_port_copy:
  proxyL0StmtsCopy$connect_port = proxyL0Stmts$connect_port
Proof
  simp[FUN_EQ_THM] >> Cases >> rename1 ‘IO_event nm _ _’ >> Cases_on ‘nm’ >>
  simp[proxyL0StmtsCopyTheory.connect_port_def, proxyL0StmtsTheory.connect_port_def]
QED

Theorem pbytes_copy:
  proxyL0StmtsCopy$pbytes = proxyL0Stmts$pbytes
Proof
  simp[FUN_EQ_THM, proxyL0StmtsCopyTheory.pbytes_def, proxyL0StmtsTheory.pbytes_def]
QED

Theorem l0_event_opened_copy:
  proxyL0StmtsCopy$l0_event_opened = proxyL0Stmts$l0_event_opened
Proof
  simp[FUN_EQ_THM, proxyL0StmtsCopyTheory.l0_event_opened_def, proxyL0StmtsTheory.l0_event_opened_def,
       l0_event_accepted_copy, l0_event_connected_copy]
QED

Theorem pos_fd_copy:
  proxyL0StmtsCopy$pos_fd = proxyL0Stmts$pos_fd
Proof
  simp[FUN_EQ_THM, proxyL0StmtsCopyTheory.pos_fd_def, proxyL0StmtsTheory.pos_fd_def,
       l0_event_opened_copy]
QED

Theorem pos_ends_copy:
  proxyL0StmtsCopy$pos_ends = proxyL0Stmts$pos_ends
Proof
  simp[FUN_EQ_THM, proxyL0StmtsCopyTheory.pos_ends_def, proxyL0StmtsTheory.pos_ends_def,
       l0_event_opened_copy, l0_event_closed_copy]
QED

Theorem pos_events_copy:
  proxyL0StmtsCopy$pos_events = proxyL0Stmts$pos_events
Proof
  simp[FUN_EQ_THM, proxyL0StmtsCopyTheory.pos_events_def, proxyL0StmtsTheory.pos_events_def,
       pos_fd_copy, pos_ends_copy]
QED

Theorem pos_sent_copy:
  proxyL0StmtsCopy$pos_sent = proxyL0Stmts$pos_sent
Proof
  simp[FUN_EQ_THM, proxyL0StmtsCopyTheory.pos_sent_def, proxyL0StmtsTheory.pos_sent_def,
       pos_fd_copy, pos_events_copy, l0_event_sent_copy]
QED

Theorem pos_read_copy:
  proxyL0StmtsCopy$pos_read = proxyL0Stmts$pos_read
Proof
  simp[FUN_EQ_THM, proxyL0StmtsCopyTheory.pos_read_def, proxyL0StmtsTheory.pos_read_def,
       pos_fd_copy, pos_events_copy, l0_event_recv_copy]
QED

Theorem is_front_copy:
  proxyL0StmtsCopy$is_front = proxyL0Stmts$is_front
Proof
  simp[FUN_EQ_THM, proxyL0StmtsCopyTheory.is_front_def, proxyL0StmtsTheory.is_front_def,
       l0_event_accepted_copy]
QED

(* pos_ep_prefix on the real definitions *)
Theorem pos_ep_real:
  ep_ok ft ∧ evs ≼ ft ∧ ep_at ft p ⇒
  l0_ep_sent (ep_idx ft p) evs = proxyL0Stmts$pos_sent p evs ∧
  l0_ep_recvd (ep_idx ft p) evs = proxyL0Stmts$pos_read p evs
Proof
  rewrite_tac[GSYM pos_sent_copy, GSYM pos_read_copy, pos_ep_prefix]
QED

(* ------------------------------------------------------------------------
   The trace: pre, then E1's rounds
   ------------------------------------------------------------------------ *)

Theorem flat_eround_evs:
  (∀n. erounds lfd pol ifds m ws0 n ≠ NONE) ⇒
  ∀n. FLAT (GENLIST (eround_evs lfd pol ifds m ws0) n) = FST (SND (SND (erun lfd pol ifds m ws0 n)))
Proof
  strip_tac >> Induct >> simp[GENLIST, SNOC_APPEND, FLAT_APPEND] >>
  first_x_assum (qspec_then ‘SUC n’ assume_tac) >> drule erun_SUC >> strip_tac >>
  simp[eround_evs_def, DROP_APPEND, DROP_LENGTH_NIL]
QED

Theorem run_prefix_cases:
  (∀n. erounds lfd pol ifds m ws0 n ≠ NONE) ∧
  LPREFIX (fromList evs)
    (LAPPEND (fromList pre) (LFLATTEN (LGENLIST (λi. fromList (eround_evs lfd pol ifds m ws0 i)) NONE))) ⇒
  evs ≼ pre ∨
  ∃i X. evs = pre ++ X ∧ FST (SND (SND (erun lfd pol ifds m ws0 i))) ≼ X ∧
        X ≼ FST (SND (SND (erun lfd pol ifds m ws0 (SUC i))))
Proof
  strip_tac >> drule e1_lprefix_rounds >> strip_tac >>
  drule round_sandwich >> strip_tac >> simp[] >> disj2_tac >>
  ‘pre ≼ evs’ by metis_tac[IS_PREFIX_TRANS, IS_PREFIX_APPEND3] >>
  gvs[IS_PREFIX_APPEND] >>
  drule flat_eround_evs >> disch_then (assume_tac o GSYM) >> simp[] >>
  qexists_tac ‘i’ >> simp[]
QED

Theorem LNTH_LTAKE_SUC[local]:
  ∀n. LNTH n io ≠ NONE ⇒ ∃l. LTAKE (SUC n) io = SOME l
Proof
  Induct >> rpt strip_tac >> ONCE_REWRITE_TAC[LTAKE_SNOC_LNTH]
  >- (Cases_on ‘LNTH 0 io’ >> gvs[]) >>
  ‘LNTH n io ≠ NONE’ by metis_tac[LNTH_NONE_MONO, DECIDE “n ≤ SUC n”] >>
  first_x_assum drule >> strip_tac >> simp[] >> Cases_on ‘LNTH (SUC n) io’ >> gvs[]
QED

Theorem LPREFIX_long:
  LPREFIX (fromList evs) io ∧ LNTH q io ≠ NONE ⇒
  ∃ft. LPREFIX (fromList ft) io ∧ evs ≼ ft ∧ q < LENGTH ft
Proof
  strip_tac >> drule LNTH_LTAKE_SUC >> strip_tac >>
  drule LTAKE_IMP_LDROP >> strip_tac >> imp_res_tac LTAKE_LENGTH >>
  ‘LPREFIX (fromList l) io’ by (simp[LPREFIX_APPEND] >> metis_tac[]) >>
  Cases_on ‘LENGTH evs ≤ LENGTH l’
  >- (qexists_tac ‘l’ >> simp[] >> irule LPREFIX_comparable >> simp[] >> qexists_tac ‘io’ >> simp[]) >>
  qexists_tac ‘evs’ >> simp[]
QED

Theorem io_ep_ft:
  LPREFIX (fromList ft) io ∧ p < LENGTH ft ⇒
  (io_ep_at io p ⇔ ep_at ft p) ∧ io_ep_idx io p = ep_idx ft p
Proof
  rw[LPREFIX_APPEND] >>
  simp[io_ep_at_def, io_ep_idx_def, ep_at_def, ep_idx_def, LNTH_LAPPEND, LNTH_fromList] >>
  ‘fromList ft ++ₗ ll = fromList (TAKE p ft) ++ₗ (fromList (DROP p ft) ++ₗ ll)’
    by simp[GSYM LAPPEND_ASSOC, LAPPEND_fromList] >>
  pop_assum SUBST1_TAC >>
  qspecl_then [‘fromList (DROP p ft) ++ₗ ll’, ‘TAKE p ft’, ‘0’] mp_tac LTAKE_LAPPEND_fromList >>
  simp[LENGTH_TAKE]
QED

(* ------------------------------------------------------------------------
   The start's four events
   ------------------------------------------------------------------------ *)

Theorem proxy_start_pre:
  proxy_start a w0 pre w4 k ⇒
  EVERY (λe. ev_new e = NONE ∧ ev_sent e = NONE ∧ ev_recvd e = NONE ∧
             honestEchoL0Spec$l0_event_accepted e = NONE ∧
             proxyL0Stmts$l0_event_connected e = NONE) pre
Proof
  rw[proxy_start_def, proxyL0StmtsTheory.l0_proxy_world_def] >>
  ‘l0_rely w1 ∧ l0_rely w2 ∧ l0_rely w3’ by metis_tac[honestL1PFRefineTheory.l0_do_rely] >>
  imp_res_tac moonshotSentGlueTheory.l0_do_ev >> gvs[] >>
  simp[ev_new_def, ev_sent_def, ev_recvd_def, honestEchoL0SpecTheory.l0_event_accepted_def,
       proxyL0StmtsTheory.l0_event_connected_def]
QED

Theorem ep_io_quiet:
  ∀pre opn n. EVERY (λe. sel e = NONE ∧ ev_new e = NONE) pre ⇒
              ep_io sel j opn n (pre ++ X) = ep_io sel j opn n X
Proof
  Induct >> simp[ep_io_def]
QED

Theorem proxy_start_ep:
  proxy_start a w0 pre w4 k ⇒
  l0_ep_sent j (pre ++ X) = l0_ep_sent j X ∧ l0_ep_recvd j (pre ++ X) = l0_ep_recvd j X
Proof
  strip_tac >> drule proxy_start_pre >> strip_tac >>
  simp[l0_ep_sent_def, l0_ep_recvd_def] >> conj_tac >> irule ep_io_quiet >>
  gvs[EVERY_MEM]
QED

Theorem proxy_start_no_front:
  proxy_start a w0 pre w4 k ∧ evs ≼ pre ⇒ ¬proxyL0Stmts$is_front p evs
Proof
  rpt strip_tac >> drule proxy_start_pre >> fs[proxyL0StmtsTheory.is_front_def] >>
  ‘EL p evs = EL p pre ∧ p < LENGTH pre’
    by (imp_res_tac IS_PREFIX_LENGTH >> fs[IS_PREFIX_APPEND] >> simp[EL_APPEND1]) >>
  simp[EXISTS_MEM] >> qexists_tac ‘EL p pre’ >> gvs[EL_MEM]
QED

(* ------------------------------------------------------------------------
   The pairing, unfolded
   ------------------------------------------------------------------------ *)

Overload ptot = “λk b hw w4. ∀n. erounds (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4, einit) n ≠ NONE”

Theorem proxy_chan_hdl_SOME:
  proxy_chan_hdl a b hw k w4 j = SOME hd ⇒
  ∃N. ALOOKUP (ehbinds (plfd k) (elv (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) w4)
                 (pifds_k b hw k) (pprog_k b hw k)
                 (pew (plfd k) a pol_never (pifds_k b hw k) (pprog_k b hw k) w4 []) N) j = SOME hd
Proof
  simp[proxy_chan_hdl_def, proxy_lv_def, proxy_pew_def] >> DEEP_INTRO_TAC some_intro >> rw[] >>
  metis_tac[]
QED

Theorem proxy_pr_SOME:
  proxy_pr a b hw k w4 io p = SOME q ⇒
  ∃hd c. io_ep_at io p ∧ io_ep_at io q ∧
         proxy_chan_hdl a b hw k w4 (io_ep_idx io p) = SOME hd ∧
         ppair (plfd k) b hw (proxy_lv b hw k w4) (proxy_pew a b hw k w4) hd = SOME c ∧
         proxy_chan_hdl a b hw k w4 (io_ep_idx io q) = SOME c
Proof
  simp[proxy_pr_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum ‘$some _ = SOME _’ mp_tac >> DEEP_INTRO_TAC some_intro >> rw[] >>
  metis_tac[]
QED

Theorem erounds_erun:
  erounds lfd pol ifds m ws0 n ≠ NONE ⇒
  erounds lfd pol ifds m ws0 n =
    SOME (FST (erun lfd pol ifds m ws0 n), FST (SND (erun lfd pol ifds m ws0 n)),
          FST (SND (SND (erun lfd pol ifds m ws0 n))), SND (SND (SND (erun lfd pol ifds m ws0 n))))
Proof
  Cases_on ‘erounds lfd pol ifds m ws0 n’ >> simp[erun_def] >> rename1 ‘SOME r’ >>
  PairCases_on ‘r’ >> simp[]
QED

Theorem e1_relay_erun:
  e1run_ok lfd a pol ifds m w0 calls ∧ (∀n. erounds lfd pol ifds m (w0, einit) n ≠ NONE) ∧
  (∀k. hl_sent c (hl_pairs m (ehhist lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) k)) ≼
       hl_read hd (hl_pairs m (ehhist lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) k))) ∧
  ALOOKUP (ehbinds lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) N) jq = SOME c ∧
  ALOOKUP (ehbinds lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) N') jp = SOME hd ∧
  FST (SND (SND (erun lfd pol ifds m (w0, einit) i))) ≼ X ∧
  X ≼ FST (SND (SND (erun lfd pol ifds m (w0, einit) (SUC i)))) ⇒
  l0_ep_sent jq X ≼ l0_ep_recvd jp X
Proof
  strip_tac >> irule e1_relay_raw >>
  qpat_x_assum ‘∀n. erounds _ _ _ _ _ _ ≠ NONE’ (fn th =>
    assume_tac (MATCH_MP erounds_erun (SPEC “i:num” th)) >>
    assume_tac (MATCH_MP erounds_erun (SPEC “SUC i” th))) >>
  metis_tac[]
QED

Theorem proxy_e1run_ok:
  proxy_start a w0 pre w4 k ∧ ptot k b hw w4 ⇒
  e1run_ok (plfd k) a pol_never (pifds_k b hw k) (pprog_k b hw k) w4 []
Proof
  strip_tac >> drule proxy_start_facts >> strip_tac >>
  rewrite_tac[e1run_ok_def] >> simp[honestL1EPRefineTheory.pew_props] >>
  conj_tac
  >- (‘∀n. SND (ecm (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) w4 n) + 1 < dimword (:64)’
        suffices_by simp[] >>
      irule proxy_ecm_bound >> simp[]) >>
  ‘proxy_guar_hl b hw (plfd k) (elv (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) w4)
     (pifds_k b hw k) (pprog_k b hw k) (pew (plfd k) a pol_never (pifds_k b hw k) (pprog_k b hw k) w4 [])’
    by (irule proxy_l1_guar >> simp[]) >>
  pop_assum mp_tac >> simp_tac std_ss [proxy_guar_hl_def, LET_THM] >> strip_tac >> first_assum ACCEPT_TAC
QED

(* ------------------------------------------------------------------------
   proxy_safe_l0, the relay clause
   ------------------------------------------------------------------------ *)

Theorem proxy_relay_l0:
  proxy_start a w0 pre w4 k ∧ ptot k b hw w4 ∧
  (∀ft. LPREFIX (fromList ft) (proxy_run_io b hw k w4 pre) ⇒ ep_ok ft) ∧
  LPREFIX (fromList evs) (proxy_run_io b hw k w4 pre) ∧ proxyL0Stmts$is_front p evs ∧
  proxy_pr a b hw k w4 (proxy_run_io b hw k w4 pre) p = SOME q ⇒
  proxyL0Stmts$pos_sent q evs ≼ proxyL0Stmts$pos_read p evs ∧
  proxyL0Stmts$pos_sent p evs ≼ proxyL0Stmts$pos_read q evs
Proof
  strip_tac >> qabbrev_tac ‘io = proxy_run_io b hw k w4 pre’ >>
  drule proxy_pr_SOME >> strip_tac >>
  ‘p < LENGTH evs’ by fs[proxyL0StmtsTheory.is_front_def] >>
  ‘LNTH q io ≠ NONE’ by fs[io_ep_at_def] >>
  drule_all LPREFIX_long >> strip_tac >>
  ‘p < LENGTH ft’ by (imp_res_tac IS_PREFIX_LENGTH >> decide_tac) >>
  ‘ep_ok ft’ by (qpat_x_assum ‘∀ft. _ ⇒ ep_ok _’ irule >> first_assum ACCEPT_TAC) >>
  ‘ep_at ft p ∧ io_ep_idx io p = ep_idx ft p’ by metis_tac[io_ep_ft] >>
  ‘ep_at ft q ∧ io_ep_idx io q = ep_idx ft q’ by metis_tac[io_ep_ft] >>
  ‘proxyL0Stmts$pos_sent q evs = l0_ep_sent (io_ep_idx io q) evs ∧
   proxyL0Stmts$pos_read q evs = l0_ep_recvd (io_ep_idx io q) evs ∧
   proxyL0Stmts$pos_sent p evs = l0_ep_sent (io_ep_idx io p) evs ∧
   proxyL0Stmts$pos_read p evs = l0_ep_recvd (io_ep_idx io p) evs’
    by metis_tac[pos_ep_real] >>
  ntac 4 (pop_assum SUBST1_TAC) >>
  qpat_x_assum ‘LPREFIX (fromList evs) io’ mp_tac >>
  simp[Abbr ‘io’, proxy_run_io_def] >> strip_tac >>
  drule_at (Pos last) run_prefix_cases >> impl_tac >- first_assum ACCEPT_TAC >> strip_tac
  >- (drule_all proxy_start_no_front >> disch_then (qspec_then ‘p’ mp_tac) >> simp[]) >>
  drule proxy_e1run_ok >> disch_then drule >> strip_tac >>
  gvs[proxy_start_ep] >>
  imp_res_tac proxy_chan_hdl_SOME >>
  ‘proxy_world (plfd k) a (proxy_pew a b hw k w4)’ by simp[proxy_pew_def, pew_proxy_world] >>
  drule proxy_relay >> disch_then drule >> strip_tac >>
  drule proxy_start_ep >> strip_tac >> simp[] >>
  qpat_x_assum ‘∀n. hl_sent _ _ ≼ _ ∧ _’ (strip_assume_tac o REWRITE_RULE [proxy_lv_def, proxy_pew_def] o
                                          SIMP_RULE std_ss [FORALL_AND_THM]) >>
  conj_tac >> irule (INST_TYPE [alpha |-> “:unit option”] e1_relay_erun) >>
  FIRST [qexistsl_tac [‘N'’, ‘N’, ‘a’, ‘hd’, ‘[]’, ‘c’, ‘i’, ‘pifds_k b hw k’, ‘plfd k’, ‘pprog_k b hw k’,
                       ‘pol_never’, ‘w4’] >> rpt conj_tac >> first_assum ACCEPT_TAC >> NO_TAC,
         qexistsl_tac [‘N’, ‘N'’, ‘a’, ‘c’, ‘[]’, ‘hd’, ‘i’, ‘pifds_k b hw k’, ‘plfd k’, ‘pprog_k b hw k’,
                       ‘pol_never’, ‘w4’] >> rpt conj_tac >> first_assum ACCEPT_TAC]
QED
