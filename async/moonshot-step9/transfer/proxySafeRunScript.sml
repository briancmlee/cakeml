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
  moonshotProxyGlue e1TraceChan e1TraceEvents e1TraceKind e1TraceLag e1TracePrefix e1TraceRound proxyStart proxyL0Run proxyL1Claim
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

(* ------------------------------------------------------------------------
   Kinds and bindings, on the proxy's run
   ------------------------------------------------------------------------ *)

Overload PW[local] = “λa b hw k w4. pew (plfd k) a pol_never (pifds_k b hw k) (pprog_k b hw k) w4 []”
Overload PL[local] = “λb hw k w4. elv (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) w4”
Overload PB[local] = “λa b hw k w4 n. ehbinds (plfd k) (PL b hw k w4) (pifds_k b hw k) (pprog_k b hw k) (PW a b hw k w4) n”
Overload PP[local] = “λa b hw k w4 n. hl_pairs (pprog_k b hw k) (ehhist (plfd k) (PL b hw k w4) (pifds_k b hw k) (pprog_k b hw k) (PW a b hw k w4) n)”
Overload PE[local] = “λb hw k w4 n. FST (SND (SND (erun (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4, einit) n)))”

Theorem accepted_new_real:
  honestEchoL0Spec$l0_event_accepted ev ≠ NONE ⇔ ∃f l. ev_new ev = SOME (f, INR l)
Proof
  rewrite_tac[GSYM l0_event_accepted_copy, accepted_new]
QED

Theorem acc_hdls_eq:
  acc_hdls = hl_acc_handles
Proof
  simp[FUN_EQ_THM, acc_hdls_def, hl_acc_handles_def]
QED

Theorem proxy_ehrounds:
  proxy_start a w0 pre w4 k ∧ ptot k b hw w4 ⇒
  (PW a b hw k w4).chans = [] ∧ (PW a b hw k w4).open_fds = [] ∧ alloc_ok (PW a b hw k w4).alloc ∧
  LENGTH (PW a b hw k w4).listening ≤ 1 ∧ EVERY (λ(l, a, q). q = []) (PW a b hw k w4).listening ∧
  ∀n. ehacts (plfd k) (PL b hw k w4) n 0
        (ehst (plfd k) (PL b hw k w4) (pifds_k b hw k) (pprog_k b hw k) (PW a b hw k w4) n)
        (new_actions (log_of (pprog_k b hw k))
           (ehhist (plfd k) (PL b hw k w4) (pifds_k b hw k) (pprog_k b hw k) (PW a b hw k w4) n)) ≠ NONE
Proof
  strip_tac >> drule_all proxy_e1run_ok >> strip_tac >>
  drule e1run_ok_ehrounds >> simp[]
QED

Theorem proxy_kinds:
  proxy_start a w0 pre w4 k ∧ ptot k b hw w4 ∧ MEM (j, hd) (PB a b hw k w4 n) ⇒
  j < LENGTH (ep_conn (PE b hw k w4 n)) ∧
  (MEM hd (hl_conn_handles (PP a b hw k w4 n)) ⇔ EL j (ep_conn (PE b hw k w4 n))) ∧
  (MEM hd (hl_acc_handles (PP a b hw k w4 n)) ⇔ ¬EL j (ep_conn (PE b hw k w4 n)))
Proof
  strip_tac >> drule_all proxy_e1run_ok >> rewrite_tac[e1run_ok_def] >> strip_tac >>
  rewrite_tac[GSYM acc_hdls_eq] >>
  ‘erounds (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4, einit) n ≠ NONE’ by simp[] >>
  drule erounds_erun >> strip_tac >>
  irule (INST_TYPE [alpha |-> “:unit option”] e1_kinds) >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl_tac [‘a’, ‘[]’, ‘FST (erun (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4,einit) n)’,
                ‘SND (SND (SND (erun (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4,einit) n)))’,
                ‘pol_never’, ‘w4’,
                ‘FST (SND (erun (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4,einit) n))’] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]
QED

Theorem proxy_conn_bound:
  proxy_start a w0 pre w4 k ∧ ptot k b hw w4 ∧
  (MEM c (hl_conn_handles (PP a b hw k w4 n)) ∨ MEM c (hl_acc_handles (PP a b hw k w4 n))) ⇒
  ∃j. MEM (j, c) (PB a b hw k w4 n)
Proof
  strip_tac >> drule_all proxy_ehrounds >> strip_tac >>
  drule_all ehrounds_kinv >> disch_then (qspec_then ‘n’ mp_tac) >>
  rewrite_tac[kinv_def, acc_hdls_eq] >> strip_tac >>
  ‘MEM c (MAP SND (PB a b hw k w4 n))’ by metis_tac[] >>
  fs[MEM_MAP] >> qexists_tac ‘FST y’ >> Cases_on ‘y’ >> fs[]
QED

Theorem proxy_bound_lookup:
  proxy_start a w0 pre w4 k ∧ ptot k b hw w4 ∧ MEM (j, c) (PB a b hw k w4 n) ⇒
  ALOOKUP (PB a b hw k w4 n) j = SOME c
Proof
  strip_tac >> drule_all proxy_ehrounds >> strip_tac >>
  drule_all ehrounds_gchinv >> disch_then (qspec_then ‘n’ assume_tac) >>
  drule gchinv_distinct >> strip_tac >> irule ALOOKUP_ALL_DISTINCT_MEM >> simp[]
QED

(* ------------------------------------------------------------------------
   Trace helpers: kinds by position, prefixes
   ------------------------------------------------------------------------ *)

Theorem quiet_ep:
  ∀l. EVERY (λe. ev_new e = NONE) l ⇒ ep_conn l = [] ∧ ep_fds l = []
Proof
  Induct >> rw[e1TraceRoleTheory.ep_conn_def, ep_fds_def] >> fs[ep_fds_def]
QED

Theorem proxy_start_conn:
  proxy_start a w0 pre w4 k ⇒
  ep_conn (pre ++ X) = ep_conn X ∧ ep_fds (pre ++ X) = ep_fds X
Proof
  strip_tac >> drule proxy_start_pre >> strip_tac >>
  ‘EVERY (λe. ev_new e = NONE) pre’ by fs[EVERY_MEM] >>
  drule quiet_ep >> fs[ep_fds_def]
QED

Theorem conn_front:
  ep_at ft p ∧ ev_new (EL p ft) = SOME (f, INR l) ⇒
  ep_idx ft p < LENGTH (ep_conn ft) ∧ ¬EL (ep_idx ft p) (ep_conn ft)
Proof
  strip_tac >> ‘p < LENGTH ft’ by fs[ep_at_def] >>
  ‘ep_conn ft = ep_conn (TAKE p ft) ++ [F] ++ ep_conn (DROP (SUC p) ft)’
    by (‘ft = TAKE p ft ++ [EL p ft] ++ DROP (SUC p) ft’
          by metis_tac[TAKE_SUC_EL, TAKE_DROP] >>
        pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
        simp[e1TraceRoleTheory.ep_conn_def]) >>
  simp[ep_idx_def, GSYM LENGTH_ep_conn, EL_APPEND1, EL_APPEND2, EL_LENGTH_APPEND]
QED

Theorem EL_prefix:
  xs ≼ ys ∧ j < LENGTH xs ⇒ EL j xs = EL j ys
Proof
  rw[IS_PREFIX_APPEND] >> simp[EL_APPEND1]
QED

Theorem ep_conn_mono:
  xs ≼ ys ⇒ ep_conn xs ≼ ep_conn ys
Proof
  rw[IS_PREFIX_APPEND] >> simp[]
QED

Theorem run_LPREFIX:
  ptot k b hw w4 ⇒ LPREFIX (fromList (pre ++ PE b hw k w4 n)) (proxy_run_io b hw k w4 pre)
Proof
  strip_tac >> drule flat_eround_evs >> disch_then (assume_tac o GSYM) >>
  simp[proxy_run_io_def] >>
  REWRITE_TAC[e1TracePrefixTheory.LPREFIX_LAPPEND_fromList, e1TracePrefixTheory.rounds_LPREFIX]
QED

Theorem hl_sent_ehhist_mono:
  ∀d. hl_sent c (hl_pairs m (ehhist lfd lv ifds m W0 n)) ≼
      hl_sent c (hl_pairs m (ehhist lfd lv ifds m W0 (n + d)))
Proof
  Induct >> simp[] >>
  irule IS_PREFIX_TRANS >> qexists_tac ‘hl_sent c (hl_pairs m (ehhist lfd lv ifds m W0 (n + d)))’ >>
  simp[] >> ‘n + SUC d = SUC (n + d)’ by decide_tac >> pop_assum SUBST1_TAC >>
  qspecl_then [‘lfd’, ‘lv’, ‘ifds’, ‘m’, ‘W0’, ‘n + d’] strip_assume_tac moonshotClientTheory.ehhist_SUC >>
  simp[moonshotClientTheory.hl_pairs_SNOC, moonshotClientSpecTheory.hl_sent_def, IS_PREFIX_APPEND3]
QED

Theorem hl_sent_ehhist_le:
  n ≤ n' ⇒
  hl_sent c (hl_pairs m (ehhist lfd lv ifds m W0 n)) ≼ hl_sent c (hl_pairs m (ehhist lfd lv ifds m W0 n'))
Proof
  strip_tac >> ‘n' = n + (n' - n)’ by decide_tac >> pop_assum SUBST1_TAC >>
  simp[hl_sent_ehhist_mono]
QED

Theorem proxy_chan_hdl_of:
  ALOOKUP (PB a b hw k w4 N) j = SOME c ⇒ proxy_chan_hdl a b hw k w4 j = SOME c
Proof
  strip_tac >> simp[proxy_chan_hdl_def, proxy_lv_def, proxy_pew_def] >>
  DEEP_INTRO_TAC some_intro >> rw[]
  >- metis_tac[ehbinds_lookup_same] >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------
   proxy_safe_l0, an unpaired front
   ------------------------------------------------------------------------ *)

(* A front's handle with no backend is never written *)
Theorem proxy_unpaired_all:
  proxy_start a w0 pre w4 k ∧ ptot k b hw w4 ∧
  LPREFIX (fromList evs) (proxy_run_io b hw k w4 pre) ∧
  ep_at evs p ∧ ev_new (EL p evs) = SOME (f, INR l) ∧
  ALOOKUP (PB a b hw k w4 N) (ep_idx evs p) = SOME c ∧
  ppair (plfd k) b hw (PL b hw k w4) (PW a b hw k w4) c = NONE ⇒
  ∀n. hl_sent c (PP a b hw k w4 n) = []
Proof
  strip_tac >> gen_tac >> qabbrev_tac ‘KK = MAX n N’ >>
  ‘hl_sent c (PP a b hw k w4 n) ≼ hl_sent c (PP a b hw k w4 KK)’
    by (irule hl_sent_ehhist_le >> simp[Abbr ‘KK’]) >>
  ‘ALOOKUP (PB a b hw k w4 KK) (ep_idx evs p) = SOME c’
    by (irule ehbinds_lookup_mono >> qexists_tac ‘N’ >> simp[Abbr ‘KK’]) >>
  ‘MEM (ep_idx evs p, c) (PB a b hw k w4 KK)’ by (imp_res_tac ALOOKUP_MEM) >>
  ‘ep_idx evs p < LENGTH (ep_conn (PE b hw k w4 KK)) ∧
   (MEM c (hl_acc_handles (PP a b hw k w4 KK)) ⇔ ¬EL (ep_idx evs p) (ep_conn (PE b hw k w4 KK)))’
    by metis_tac[proxy_kinds] >>
  ‘ep_idx evs p < LENGTH (ep_conn evs) ∧ ¬EL (ep_idx evs p) (ep_conn evs)’
    by (irule conn_front >> metis_tac[]) >>
  ‘LPREFIX (fromList (pre ++ PE b hw k w4 KK)) (proxy_run_io b hw k w4 pre)’ by simp[run_LPREFIX] >>
  ‘ep_conn (pre ++ PE b hw k w4 KK) = ep_conn (PE b hw k w4 KK)’ by metis_tac[proxy_start_conn] >>
  ‘¬EL (ep_idx evs p) (ep_conn (PE b hw k w4 KK))’
    by (Cases_on ‘LENGTH evs ≤ LENGTH (pre ++ PE b hw k w4 KK)’
        >- (‘evs ≼ pre ++ PE b hw k w4 KK’
              by (irule LPREFIX_comparable >> conj_tac >- decide_tac >>
                  qexists_tac ‘proxy_run_io b hw k w4 pre’ >> simp[]) >>
            drule ep_conn_mono >> strip_tac >> metis_tac[EL_prefix]) >>
        ‘pre ++ PE b hw k w4 KK ≼ evs’
          by (irule LPREFIX_comparable >> conj_tac >- decide_tac >>
                  qexists_tac ‘proxy_run_io b hw k w4 pre’ >> simp[]) >>
        drule ep_conn_mono >> strip_tac >> metis_tac[EL_prefix]) >>
  ‘MEM c (hl_acc_handles (PP a b hw k w4 KK))’ by metis_tac[] >>
  ‘proxy_world (plfd k) a (PW a b hw k w4)’ by simp[pew_proxy_world] >>
  ‘hl_sent c (PP a b hw k w4 KK) = []’
    by (irule proxy_unpaired >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, qexists_tac ‘a’ >> first_assum ACCEPT_TAC]) >>
  qpat_x_assum ‘hl_sent c (PP a b hw k w4 n) ≼ _’ mp_tac >> simp[]
QED

(* A paired front's backend handle has a position *)
Theorem proxy_q_exists:
  proxy_start a w0 pre w4 k ∧ ptot k b hw w4 ∧
  ppair (plfd k) b hw (PL b hw k w4) (PW a b hw k w4) c = SOME c' ⇒
  ∃q. io_ep_at (proxy_run_io b hw k w4 pre) q ∧
      proxy_chan_hdl a b hw k w4 (io_ep_idx (proxy_run_io b hw k w4 pre) q) = SOME c'
Proof
  strip_tac >>
  ‘proxy_world (plfd k) a (PW a b hw k w4)’ by simp[pew_proxy_world] >>
  drule proxy_pair_roles >> disch_then drule >> strip_tac >>
  ‘∃j. MEM (j, c') (PB a b hw k w4 n)’ by (irule proxy_conn_bound >> metis_tac[]) >>
  ‘j < LENGTH (ep_conn (PE b hw k w4 n))’ by metis_tac[proxy_kinds] >>
  ‘j < LENGTH (ep_fds (pre ++ PE b hw k w4 n))’ by metis_tac[proxy_start_conn, LENGTH_ep_conn] >>
  drule ep_pos_exists >> strip_tac >>
  ‘LPREFIX (fromList (pre ++ PE b hw k w4 n)) (proxy_run_io b hw k w4 pre)’ by simp[run_LPREFIX] >>
  ‘p < LENGTH (pre ++ PE b hw k w4 n)’ by fs[ep_at_def] >>
  qexists_tac ‘p’ >> drule_all io_ep_ft >> strip_tac >> simp[] >>
  irule proxy_chan_hdl_of >> qexists_tac ‘n’ >> irule proxy_bound_lookup >> metis_tac[]
QED

Theorem e1_sent_nil_erun:
  e1run_ok lfd a pol ifds m w0 calls ∧ (∀n. erounds lfd pol ifds m (w0, einit) n ≠ NONE) ∧
  X ≼ FST (SND (SND (erun lfd pol ifds m (w0, einit) i))) ∧
  (∀N c k. ALOOKUP (ehbinds lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) N) j = SOME c ⇒
           hl_sent c (hl_pairs m (ehhist lfd (elv lfd pol ifds m w0) ifds m
                                    (pew lfd a pol ifds m w0 calls) k)) = []) ⇒
  l0_ep_sent j X = []
Proof
  strip_tac >> irule e1_sent_nil >>
  qpat_x_assum ‘∀n. erounds _ _ _ _ _ _ ≠ NONE’ (fn th =>
    assume_tac (MATCH_MP erounds_erun (SPEC “i:num” th))) >>
  metis_tac[]
QED

Theorem proxy_unpaired_l0:
  proxy_start a w0 pre w4 k ∧ ptot k b hw w4 ∧
  (∀ft. LPREFIX (fromList ft) (proxy_run_io b hw k w4 pre) ⇒ ep_ok ft) ∧
  LPREFIX (fromList evs) (proxy_run_io b hw k w4 pre) ∧ proxyL0Stmts$is_front p evs ∧
  proxy_pr a b hw k w4 (proxy_run_io b hw k w4 pre) p = NONE ⇒
  proxyL0Stmts$pos_sent p evs = []
Proof
  strip_tac >> qabbrev_tac ‘io = proxy_run_io b hw k w4 pre’ >>
  ‘p < LENGTH evs ∧ ∃f l. ev_new (EL p evs) = SOME (f, INR l)’
    by fs[proxyL0StmtsTheory.is_front_def, accepted_new_real] >>
  ‘ep_at evs p’ by simp[ep_at_def] >>
  ‘ep_ok evs’ by (qpat_x_assum ‘∀ft. _ ⇒ ep_ok _’ irule >> first_assum ACCEPT_TAC) >>
  ‘io_ep_at io p ∧ io_ep_idx io p = ep_idx evs p’ by metis_tac[io_ep_ft] >>
  ‘proxyL0Stmts$pos_sent p evs = l0_ep_sent (ep_idx evs p) evs’ by metis_tac[pos_ep_real, IS_PREFIX_REFL] >>
  pop_assum SUBST1_TAC >>
  ‘∀N c n. ALOOKUP (PB a b hw k w4 N) (ep_idx evs p) = SOME c ⇒ hl_sent c (PP a b hw k w4 n) = []’
    by (rpt strip_tac >>
        ‘proxy_chan_hdl a b hw k w4 (ep_idx evs p) = SOME c’ by metis_tac[proxy_chan_hdl_of] >>
        Cases_on ‘ppair (plfd k) b hw (PL b hw k w4) (PW a b hw k w4) c’
        >- (irule proxy_unpaired_all >> simp[Abbr ‘io’] >> metis_tac[]) >>
        rename1 ‘_ = SOME c'’ >>
        drule_at (Pos last) proxy_q_exists >> disch_then drule_all >> strip_tac >>
        qpat_x_assum ‘proxy_pr _ _ _ _ _ _ _ = NONE’ mp_tac >>
        simp[proxy_pr_def, proxy_lv_def, proxy_pew_def] >>
        DEEP_INTRO_TAC some_intro >> simp[] >> metis_tac[]) >>
  qpat_x_assum ‘LPREFIX (fromList evs) io’ mp_tac >> simp[Abbr ‘io’, proxy_run_io_def] >> strip_tac >>
  drule_at (Pos last) run_prefix_cases >> impl_tac >- first_assum ACCEPT_TAC >> strip_tac
  >- (drule_all proxy_start_no_front >> disch_then (qspec_then ‘p’ mp_tac) >> simp[]) >>
  drule proxy_start_ep >> strip_tac >> simp[] >>
  drule_all proxy_e1run_ok >> strip_tac >>
  qpat_x_assum ‘evs = _’ SUBST_ALL_TAC >>
  irule (INST_TYPE [alpha |-> “:unit option”] e1_sent_nil_erun) >>
  qexistsl_tac [‘a’, ‘[]’, ‘SUC i’, ‘pifds_k b hw k’, ‘plfd k’, ‘pprog_k b hw k’, ‘pol_never’, ‘w4’] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* ------------------------------------------------------------------------
   proxy_safe_l0, pr is injective and a backend is a connect
   ------------------------------------------------------------------------ *)

Theorem ALL_DISTINCT_SND_MEM[local]:
  ∀l. ALL_DISTINCT (MAP SND l) ∧ MEM (j, c) l ∧ MEM (j', c) l ⇒ j = j'
Proof
  Induct >> simp[FORALL_PROD] >> rw[] >> fs[MEM_MAP, FORALL_PROD] >> metis_tac[]
QED

Theorem MEM_prefix[local]:
  xs ≼ ys ∧ MEM x xs ⇒ MEM x ys
Proof
  rw[IS_PREFIX_APPEND] >> simp[]
QED

Theorem ehbinds_le:
  n ≤ n' ⇒ ehbinds lfd lv ifds m W0 n ≼ ehbinds lfd lv ifds m W0 n'
Proof
  strip_tac >> qspecl_then [‘n' - n’, ‘n’] mp_tac ehbinds_prefix >> simp[]
QED

Theorem proxy_bind_inj:
  proxy_start a w0 pre w4 k ∧ ptot k b hw w4 ∧
  MEM (j, c) (PB a b hw k w4 n) ∧ MEM (j', c) (PB a b hw k w4 n') ⇒ j = j'
Proof
  strip_tac >> qabbrev_tac ‘MX = MAX n n'’ >>
  ‘PB a b hw k w4 n ≼ PB a b hw k w4 MX ∧ PB a b hw k w4 n' ≼ PB a b hw k w4 MX’
    by (conj_tac >> irule ehbinds_le >> simp[Abbr ‘MX’]) >>
  ‘MEM (j, c) (PB a b hw k w4 MX) ∧ MEM (j', c) (PB a b hw k w4 MX)’
    by metis_tac[MEM_prefix] >>
  drule_all proxy_ehrounds >> strip_tac >>
  drule_all ehrounds_gchinv >> disch_then (qspec_then ‘MX’ assume_tac) >>
  drule gchinv_distinct >> strip_tac >>
  metis_tac[ALL_DISTINCT_SND_MEM]
QED

Theorem proxy_chan_hdl_inj:
  proxy_start a w0 pre w4 k ∧ ptot k b hw w4 ∧
  proxy_chan_hdl a b hw k w4 j = SOME c ∧ proxy_chan_hdl a b hw k w4 j' = SOME c ⇒ j = j'
Proof
  strip_tac >> imp_res_tac proxy_chan_hdl_SOME >> imp_res_tac ALOOKUP_MEM >>
  irule proxy_bind_inj >> metis_tac[]
QED

Theorem io_ep_inj:
  io_ep_at io p ∧ io_ep_at io p' ∧ io_ep_idx io p = io_ep_idx io p' ⇒ p = p'
Proof
  strip_tac >>
  ‘LNTH p io ≠ NONE ∧ LNTH p' io ≠ NONE’ by fs[io_ep_at_def] >>
  ‘LPREFIX (fromList []) io’ by simp[] >>
  ‘∃ft1. LPREFIX (fromList ft1) io ∧ p < LENGTH ft1’ by metis_tac[LPREFIX_long] >>
  ‘∃ft. LPREFIX (fromList ft) io ∧ ft1 ≼ ft ∧ p' < LENGTH ft’ by metis_tac[LPREFIX_long] >>
  ‘p < LENGTH ft’ by (imp_res_tac IS_PREFIX_LENGTH >> decide_tac) >>
  ‘ep_at ft p ∧ ep_at ft p' ∧ ep_idx ft p = ep_idx ft p'’ by metis_tac[io_ep_ft] >>
  metis_tac[ep_idx_inj]
QED

Theorem proxy_pr_inj:
  proxy_start a w0 pre w4 k ∧ ptot k b hw w4 ∧
  proxy_pr a b hw k w4 io p = SOME q ∧ proxy_pr a b hw k w4 io p' = SOME q ⇒ p = p'
Proof
  strip_tac >>
  qpat_x_assum ‘proxy_pr _ _ _ _ _ _ p = _’ (strip_assume_tac o MATCH_MP proxy_pr_SOME) >>
  qpat_x_assum ‘proxy_pr _ _ _ _ _ _ p' = _’ (strip_assume_tac o MATCH_MP proxy_pr_SOME) >>
  ‘c' = c’ by fs[] >> pop_assum SUBST_ALL_TAC >>
  ‘proxy_world (plfd k) a (PW a b hw k w4)’ by simp[pew_proxy_world] >>
  ‘hd' = hd’ by (drule proxy_pair_inj >> fs[proxy_lv_def, proxy_pew_def] >> metis_tac[]) >>
  pop_assum SUBST_ALL_TAC >>
  ‘io_ep_idx io p = io_ep_idx io p'’ by metis_tac[proxy_chan_hdl_inj] >>
  metis_tac[io_ep_inj]
QED

Theorem new_front:
  ep_at ft p ∧ ev_new (EL p ft) = SOME (f, x) ⇒
  ep_idx ft p < LENGTH (ep_conn ft) ∧ EL (ep_idx ft p) (ep_conn ft) = ISL x
Proof
  strip_tac >> ‘p < LENGTH ft’ by fs[ep_at_def] >>
  ‘ep_conn ft = ep_conn (TAKE p ft) ++ [ISL x] ++ ep_conn (DROP (SUC p) ft)’
    by (‘ft = TAKE p ft ++ [EL p ft] ++ DROP (SUC p) ft’
          by metis_tac[TAKE_SUC_EL, TAKE_DROP] >>
        pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
        simp[e1TraceRoleTheory.ep_conn_def]) >>
  simp[ep_idx_def, GSYM LENGTH_ep_conn, EL_APPEND1, EL_APPEND2, EL_LENGTH_APPEND]
QED

(* Two prefixes of the run agree on episode kinds *)
Theorem ep_conn_agree:
  LPREFIX (fromList xs) io ∧ LPREFIX (fromList ys) io ∧
  j < LENGTH (ep_conn xs) ∧ j < LENGTH (ep_conn ys) ⇒
  EL j (ep_conn xs) = EL j (ep_conn ys)
Proof
  strip_tac >> Cases_on ‘LENGTH xs ≤ LENGTH ys’
  >- (‘xs ≼ ys’ by (irule LPREFIX_comparable >> conj_tac >- decide_tac >>
                    qexists_tac ‘io’ >> simp[]) >>
      drule ep_conn_mono >> strip_tac >> metis_tac[EL_prefix]) >>
  ‘ys ≼ xs’ by (irule LPREFIX_comparable >> conj_tac >- decide_tac >>
                qexists_tac ‘io’ >> simp[]) >>
  drule ep_conn_mono >> strip_tac >> metis_tac[EL_prefix]
QED

Theorem new_connected:
  opens_ok ev ∧ ev_new ev = SOME (f, INL port) ⇒ proxyL0Stmts$l0_event_connected ev ≠ NONE
Proof
  rewrite_tac[GSYM l0_event_connected_copy] >> strip_tac >>
  fs[opens_ok_def, proxyL0StmtsCopyTheory.l0_event_opened_def] >>
  every_case_tac >> fs[] >>
  ‘∃f l. ev_new ev = SOME (f, INR l)’ by metis_tac[accepted_new, NOT_NONE_SOME] >>
  fs[]
QED

Theorem proxy_pr_connected:
  proxy_start a w0 pre w4 k ∧ ptot k b hw w4 ∧
  (∀ft. LPREFIX (fromList ft) (proxy_run_io b hw k w4 pre) ⇒ ep_ok ft) ∧
  LPREFIX (fromList evs) (proxy_run_io b hw k w4 pre) ∧
  proxy_pr a b hw k w4 (proxy_run_io b hw k w4 pre) p = SOME q ∧ q < LENGTH evs ⇒
  proxyL0Stmts$l0_event_connected (EL q evs) ≠ NONE
Proof
  strip_tac >> qabbrev_tac ‘io = proxy_run_io b hw k w4 pre’ >>
  qpat_x_assum ‘proxy_pr _ _ _ _ _ _ p = _’ (strip_assume_tac o MATCH_MP proxy_pr_SOME) >>
  ‘proxy_world (plfd k) a (PW a b hw k w4)’ by simp[pew_proxy_world] >>
  ‘∃n. MEM c (hl_conn_handles (PP a b hw k w4 n))’
    by (drule proxy_pair_roles >> fs[proxy_lv_def, proxy_pew_def] >> metis_tac[]) >>
  ‘∃j. MEM (j, c) (PB a b hw k w4 n)’ by (irule proxy_conn_bound >> metis_tac[]) >>
  ‘j < LENGTH (ep_conn (PE b hw k w4 n)) ∧ EL j (ep_conn (PE b hw k w4 n))’ by metis_tac[proxy_kinds] >>
  ‘proxy_chan_hdl a b hw k w4 j = SOME c’
    by (irule proxy_chan_hdl_of >> qexists_tac ‘n’ >> irule proxy_bound_lookup >> metis_tac[]) >>
  ‘io_ep_idx io q = j’ by metis_tac[proxy_chan_hdl_inj] >>
  ‘ep_at evs q ∧ ep_idx evs q = j’ by metis_tac[io_ep_ft] >>
  ‘∃f x. ev_new (EL q evs) = SOME (f, x)’ by (fs[ep_at_def] >> Cases_on ‘ev_new (EL q evs)’ >> fs[] >> metis_tac[pair_CASES]) >>
  ‘j < LENGTH (ep_conn evs) ∧ EL j (ep_conn evs) = ISL x’ by metis_tac[new_front] >>
  ‘LPREFIX (fromList (pre ++ PE b hw k w4 n)) io’ by simp[run_LPREFIX, Abbr ‘io’] >>
  ‘ep_conn (pre ++ PE b hw k w4 n) = ep_conn (PE b hw k w4 n)’ by metis_tac[proxy_start_conn] >>
  ‘EL j (ep_conn evs) = EL j (ep_conn (pre ++ PE b hw k w4 n))’
    by (mp_tac (Q.INST [‘xs’ |-> ‘evs’, ‘ys’ |-> ‘pre ++ PE b hw k w4 n’] ep_conn_agree) >>
        impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
                     qpat_x_assum ‘ep_conn (pre ++ _) = _’ SUBST1_TAC >> first_assum ACCEPT_TAC) >>
        simp[]) >>
  ‘ISL x’ by metis_tac[] >> Cases_on ‘x’ >> fs[] >>
  ‘ep_ok evs’ by (qpat_x_assum ‘∀ft. _ ⇒ ep_ok _’ irule >> first_assum ACCEPT_TAC) >>
  ‘opens_ok (EL q evs)’ by fs[ep_ok_def, EVERY_EL] >>
  metis_tac[new_connected]
QED

(* ------------------------------------------------------------------------
   proxy_safe_l0, a connect is a front's backend
   ------------------------------------------------------------------------ *)

Theorem proxy_roles:
  proxy_start a w0 pre w4 k ∧ ptot k b hw w4 ⇒
  MAP cpa (FST (ehst (plfd k) (PL b hw k w4) (pifds_k b hw k) (pprog_k b hw k) (PW a b hw k w4) n)).chans =
  ep_conn (PE b hw k w4 n)
Proof
  strip_tac >> drule_all proxy_e1run_ok >> rewrite_tac[e1run_ok_def] >> strip_tac >>
  ‘erounds (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4, einit) n ≠ NONE’ by simp[] >>
  drule erounds_erun >> strip_tac >>
  qspecl_then [‘w4’, ‘plfd k’, ‘pol_never’, ‘pifds_k b hw k’, ‘pprog_k b hw k’, ‘a’, ‘[]’] mp_tac
    (Q.GENL [‘w0’, ‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘a’, ‘calls’]
       (INST_TYPE [alpha |-> “:unit option”] e1TraceRoleTheory.e1_roles)) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then drule >> simp[]
QED

Theorem proxy_conn_ep_bound:
  proxy_start a w0 pre w4 k ∧ ptot k b hw w4 ∧
  j < LENGTH (ep_conn (PE b hw k w4 n)) ∧ EL j (ep_conn (PE b hw k w4 n)) ⇒
  ∃hd. MEM (j, hd) (PB a b hw k w4 n)
Proof
  strip_tac >> drule_all proxy_ehrounds >> strip_tac >>
  drule_all ehrounds_kinv >> disch_then (qspec_then ‘n’ mp_tac) >> rewrite_tac[kinv_def] >> strip_tac >>
  drule_all proxy_roles >> disch_then (qspec_then ‘n’ assume_tac) >>
  qabbrev_tac ‘cs = (FST (ehst (plfd k) (PL b hw k w4) (pifds_k b hw k) (pprog_k b hw k) (PW a b hw k w4) n)).chans’ >>
  ‘j < LENGTH cs ∧ cpa (EL j cs)’
    by (qpat_x_assum ‘MAP cpa cs = _’ (assume_tac o SYM) >>
        qpat_x_assum ‘j < LENGTH _’ mp_tac >> qpat_x_assum ‘EL j _’ mp_tac >>
        pop_assum SUBST1_TAC >> rewrite_tac[LENGTH_MAP] >> rpt strip_tac >- first_assum ACCEPT_TAC >>
        qpat_x_assum ‘EL j (MAP _ _)’ mp_tac >> simp[EL_MAP]) >>
  ‘MEM j (MAP FST (PB a b hw k w4 n))’
    by (qpat_x_assum ‘∀j. j < LENGTH cs ∧ _ ⇒ _’ (qspec_then ‘j’ mp_tac) >>
        impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> rewrite_tac[]) >>
  pop_assum mp_tac >> rewrite_tac[MEM_MAP] >> strip_tac >> Cases_on ‘y’ >>
  qexists_tac ‘r’ >> qpat_x_assum ‘j = _’ (SUBST1_TAC o SIMP_RULE std_ss []) >> first_assum ACCEPT_TAC
QED

Theorem proxy_conn_at0:
  ¬MEM c (hl_conn_handles (PP a b hw k w4 0))
Proof
  simp[endpointHLModelTheory.ehhist_def, endpointHLModelTheory.ehrounds_def,
       moonshotClientSpecTheory.hl_pairs_def]
QED

Theorem proxy_first_conn:
  ∀n. MEM c (hl_conn_handles (PP a b hw k w4 n)) ⇒
      ∃r. MEM c (hl_conn_handles (PP a b hw k w4 (SUC r))) ∧ ¬MEM c (hl_conn_handles (PP a b hw k w4 r))
Proof
  Induct >- simp[proxy_conn_at0] >> strip_tac >>
  Cases_on ‘MEM c (hl_conn_handles (PP a b hw k w4 n))’ >- (first_x_assum drule >> simp[]) >>
  qexists_tac ‘n’ >> simp[]
QED

(* The order: a front is bound before its backend *)
Theorem proxy_front_before:
  proxy_start a w0 pre w4 k ∧ ptot k b hw w4 ∧
  ppair (plfd k) b hw (PL b hw k w4) (PW a b hw k w4) hd = SOME c ∧
  MEM (jp, hd) (PB a b hw k w4 n) ∧ MEM (jq, c) (PB a b hw k w4 n') ⇒ jp < jq
Proof
  strip_tac >>
  ‘proxy_world (plfd k) a (PW a b hw k w4)’ by simp[pew_proxy_world] >>
  ‘∃n1. MEM c (hl_conn_handles (PP a b hw k w4 n1))’ by (drule proxy_pair_roles >> metis_tac[]) >>
  drule proxy_first_conn >> strip_tac >>
  ‘∃hd'. ppair (plfd k) b hw (PL b hw k w4) (PW a b hw k w4) hd' = SOME c ∧
         MEM hd' (hl_acc_handles (PP a b hw k w4 (SUC r)))’ by (drule proxy_conn_front >> metis_tac[]) >>
  ‘hd' = hd’ by (drule proxy_pair_inj >> metis_tac[]) >> pop_assum SUBST_ALL_TAC >>
  ‘∃jp'. MEM (jp', hd) (PB a b hw k w4 (SUC r))’ by (irule proxy_conn_bound >> metis_tac[]) >>
  ‘∃jq'. MEM (jq', c) (PB a b hw k w4 (SUC r))’ by (irule proxy_conn_bound >> metis_tac[]) >>
  ‘jp' = jp ∧ jq' = jq’ by metis_tac[proxy_bind_inj] >> fs[] >>
  drule_all proxy_ehrounds >> strip_tac >>
  irule (INST_TYPE [alpha |-> “:unit option”] ehrounds_order) >> rewrite_tac[acc_hdls_eq] >>
  qexistsl_tac [‘PW a b hw k w4’, ‘c’, ‘hd’, ‘pifds_k b hw k’, ‘plfd k’, ‘PL b hw k w4’, ‘pprog_k b hw k’, ‘r’] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem proxy_pr_of:
  proxy_start a w0 pre w4 k ∧ ptot k b hw w4 ∧
  io_ep_at io p ∧ proxy_chan_hdl a b hw k w4 (io_ep_idx io p) = SOME hd ∧
  ppair (plfd k) b hw (PL b hw k w4) (PW a b hw k w4) hd = SOME c ∧
  io_ep_at io q ∧ proxy_chan_hdl a b hw k w4 (io_ep_idx io q) = SOME c ⇒
  proxy_pr a b hw k w4 io p = SOME q
Proof
  strip_tac >> simp[proxy_pr_def, proxy_lv_def, proxy_pew_def] >>
  DEEP_INTRO_TAC some_intro >> rw[]
  >- (irule io_ep_inj >> qexists_tac ‘io’ >> simp[] >> metis_tac[proxy_chan_hdl_inj]) >>
  metis_tac[]
QED

Theorem ep_idx_mono:
  p ≤ p' ⇒ ep_idx ft p ≤ ep_idx ft p'
Proof
  strip_tac >> simp[ep_idx_def] >>
  ‘TAKE p' ft = TAKE p ft ++ DROP p (TAKE p' ft)’
    by (‘MIN p p' = p’ by fs[MIN_DEF] >>
        ‘TAKE p ft = TAKE p (TAKE p' ft)’ by asm_simp_tac std_ss [TAKE_TAKE_MIN] >>
        pop_assum SUBST1_TAC >> simp[TAKE_DROP]) >>
  pop_assum SUBST1_TAC >> simp[ep_fds_def]
QED

(* ------------------------------------------------------------------------
   proxy_safe_l0, listens and connect ports
   ------------------------------------------------------------------------ *)

Theorem pbytes_port_bytes:
  proxyL0Stmts$pbytes p = port_bytes p
Proof
  simp[proxyL0StmtsTheory.pbytes_def, honestL1EPModelTheory.port_bytes_def]
QED

Theorem proxy_start_listen:
  proxy_start a w0 pre w4 k ∧ MEM (IO_event (ExtCall «sys_listen») conf bs) pre ⇒
  conf = proxyL0Stmts$pbytes a
Proof
  rw[proxy_start_def, proxyL0StmtsTheory.l0_proxy_world_def] >>
  ‘l0_rely w1 ∧ l0_rely w2 ∧ l0_rely w3’ by metis_tac[honestL1PFRefineTheory.l0_do_rely] >>
  imp_res_tac moonshotSentGlueTheory.l0_do_ev >> gvs[pbytes_port_bytes]
QED

Theorem pstate_last_pacts:
  ∃st rdy. (pstate lfd b hw h).last = pacts lfd b hw st rdy
Proof
  Cases_on ‘h’ using SNOC_CASES >>
  simp[moonshotProxyTheory.pstate_def, FOLDL_SNOC, moonshotProxyTheory.pinit_def,
       moonshotProxyTheory.pstep_def] >> metis_tac[]
QED

Theorem proxy_connects_b:
  MEM (EConnect p) (new_actions (log_of (pprog lfd b hw)) h) ⇒ p = b
Proof
  rewrite_tac[moonshotProxyTheory.pprog_new_actions] >> strip_tac >>
  ‘∃st rdy. (pstate lfd b hw h).last = pacts lfd b hw st rdy’ by metis_tac[pstate_last_pacts] >>
  fs[] >> drule moonshotProxyTheory.MEM_pacts >> simp[]
QED

Theorem proxy_rounds_ok:
  ptot k b hw w4 ⇒ EVERY (e1TraceEvents$e1ev_ok (λp. p = b)) (PE b hw k w4 n)
Proof
  strip_tac >>
  ‘erounds (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4, einit) n ≠ NONE’ by simp[] >>
  drule erounds_erun >> strip_tac >>
  mp_tac (Q.INST [‘P’ |-> ‘λp. p = b’, ‘m’ |-> ‘pprog_k b hw k’, ‘lfd’ |-> ‘plfd k’, ‘pol’ |-> ‘pol_never’,
                   ‘ifds’ |-> ‘pifds_k b hw k’, ‘ws0’ |-> ‘(w4, einit)’]
            (INST_TYPE [alpha |-> “:unit option”] e1TraceEventsTheory.erounds_evs_ok)) >>
  impl_tac >- (rpt strip_tac >> drule proxy_connects_b >> simp[]) >>
  disch_then drule >> simp[]
QED

(* An event of a prefix of the run is in the start or in some round *)
Theorem proxy_run_mem:
  ptot k b hw w4 ∧ LPREFIX (fromList evs) (proxy_run_io b hw k w4 pre) ∧ MEM e evs ⇒
  MEM e pre ∨ ∃n. MEM e (PE b hw k w4 n)
Proof
  strip_tac >> qpat_x_assum ‘LPREFIX _ _’ mp_tac >> simp[proxy_run_io_def] >> strip_tac >>
  drule_at (Pos last) run_prefix_cases >> impl_tac >- first_assum ACCEPT_TAC >> strip_tac
  >- (disj1_tac >> metis_tac[MEM_prefix]) >>
  qpat_x_assum ‘evs = _’ SUBST_ALL_TAC >> fs[] >> disj2_tac >>
  qexists_tac ‘SUC i’ >> metis_tac[MEM_prefix]
QED

Theorem proxy_listen_l0:
  proxy_start a w0 pre w4 k ∧ ptot k b hw w4 ∧
  LPREFIX (fromList evs) (proxy_run_io b hw k w4 pre) ∧
  MEM (IO_event (ExtCall «sys_listen») conf bs) evs ⇒
  conf = proxyL0Stmts$pbytes a
Proof
  strip_tac >> drule_all proxy_run_mem >> strip_tac
  >- (drule_all proxy_start_listen >> simp[]) >>
  drule proxy_rounds_ok >> disch_then (qspec_then ‘n’ mp_tac) >>
  simp[EVERY_MEM] >> disch_then drule >> simp[e1TraceEventsTheory.e1ev_ok_def]
QED

Theorem connected_name:
  proxyL0Stmts$l0_event_connected ev ≠ NONE ⇒ ∃conf bs. ev = IO_event (ExtCall «sys_connect») conf bs
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bl’ >> Cases_on ‘nm’ >>
  simp[proxyL0StmtsTheory.l0_event_connected_def] >> rw[]
QED

Theorem proxy_connect_port:
  proxy_start a w0 pre w4 k ∧ ptot k b hw w4 ∧
  LPREFIX (fromList evs) (proxy_run_io b hw k w4 pre) ∧ q < LENGTH evs ∧
  proxyL0Stmts$l0_event_connected (EL q evs) ≠ NONE ⇒
  proxyL0Stmts$connect_port (EL q evs) = SOME (proxyL0Stmts$pbytes b)
Proof
  strip_tac >> ‘MEM (EL q evs) evs’ by metis_tac[MEM_EL] >>
  drule_all proxy_run_mem >> strip_tac
  >- (drule proxy_start_pre >> simp[EVERY_MEM] >> disch_then drule >> simp[]) >>
  drule connected_name >> strip_tac >> fs[] >>
  drule proxy_rounds_ok >> disch_then (qspec_then ‘n’ mp_tac) >>
  simp[EVERY_MEM] >> disch_then drule >>
  simp[e1TraceEventsTheory.e1ev_ok_def, proxyL0StmtsTheory.connect_port_def, pbytes_port_bytes]
QED

Theorem proxy_run_cover:
  ptot k b hw w4 ∧ LPREFIX (fromList evs) (proxy_run_io b hw k w4 pre) ⇒
  ∃n. evs ≼ pre ++ PE b hw k w4 n
Proof
  strip_tac >> qpat_x_assum ‘LPREFIX _ _’ mp_tac >> simp[proxy_run_io_def] >> strip_tac >>
  drule_at (Pos last) run_prefix_cases >> impl_tac >- first_assum ACCEPT_TAC >> strip_tac
  >- (qexists_tac ‘0’ >> irule IS_PREFIX_TRANS >> qexists_tac ‘pre’ >> simp[]) >>
  qexists_tac ‘SUC i’ >> simp[]
QED

Theorem proxy_connect_front_l0:
  proxy_start a w0 pre w4 k ∧ ptot k b hw w4 ∧
  (∀ft. LPREFIX (fromList ft) (proxy_run_io b hw k w4 pre) ⇒ ep_ok ft) ∧
  LPREFIX (fromList evs) (proxy_run_io b hw k w4 pre) ∧ q < LENGTH evs ∧
  proxyL0Stmts$l0_event_connected (EL q evs) ≠ NONE ⇒
  ∃p. p < q ∧ proxyL0Stmts$is_front p evs ∧ proxy_pr a b hw k w4 (proxy_run_io b hw k w4 pre) p = SOME q
Proof
  strip_tac >> qabbrev_tac ‘io = proxy_run_io b hw k w4 pre’ >>
  ‘ep_ok evs’ by (qpat_x_assum ‘∀ft. _ ⇒ ep_ok _’ irule >> first_assum ACCEPT_TAC) >>
  ‘opens_ok (EL q evs)’ by fs[ep_ok_def, EVERY_EL] >>
  ‘proxyL0StmtsCopy$l0_event_connected (EL q evs) ≠ NONE’ by simp[l0_event_connected_copy] >>
  ‘∃f port. ev_new (EL q evs) = SOME (f, INL port)’ by (drule_all connected_new >> simp[]) >>
  ‘ep_at evs q’ by simp[ep_at_def] >>
  qabbrev_tac ‘jq = ep_idx evs q’ >>
  ‘jq < LENGTH (ep_conn evs) ∧ EL jq (ep_conn evs)’
    by (drule_all new_front >> simp[Abbr ‘jq’]) >>
  ‘∃n. evs ≼ pre ++ PE b hw k w4 n’ by (irule proxy_run_cover >> simp[Abbr ‘io’]) >>
  ‘ep_conn evs ≼ ep_conn (PE b hw k w4 n)’ by metis_tac[ep_conn_mono, proxy_start_conn] >>
  ‘jq < LENGTH (ep_conn (PE b hw k w4 n)) ∧ EL jq (ep_conn (PE b hw k w4 n))’
    by (imp_res_tac IS_PREFIX_LENGTH >> conj_tac >- decide_tac >> metis_tac[EL_prefix]) >>
  ‘∃c. MEM (jq, c) (PB a b hw k w4 n)’ by (irule proxy_conn_ep_bound >> metis_tac[]) >>
  ‘MEM c (hl_conn_handles (PP a b hw k w4 n))’ by metis_tac[proxy_kinds] >>
  ‘proxy_world (plfd k) a (PW a b hw k w4)’ by simp[pew_proxy_world] >>
  ‘∃hd. ppair (plfd k) b hw (PL b hw k w4) (PW a b hw k w4) hd = SOME c ∧
        MEM hd (hl_acc_handles (PP a b hw k w4 n))’ by (drule proxy_conn_front >> metis_tac[]) >>
  ‘∃jp. MEM (jp, hd) (PB a b hw k w4 n)’ by (irule proxy_conn_bound >> metis_tac[]) >>
  ‘jp < LENGTH (ep_conn (PE b hw k w4 n)) ∧ ¬EL jp (ep_conn (PE b hw k w4 n))’ by metis_tac[proxy_kinds] >>
  ‘jp < jq’ by (irule proxy_front_before >> metis_tac[]) >>
  ‘jp < LENGTH (ep_fds evs)’ by (fs[LENGTH_ep_conn] >> decide_tac) >>
  ‘∃p. ep_at evs p ∧ ep_idx evs p = jp’ by metis_tac[ep_pos_exists] >>
  ‘p < q’ by (CCONTR_TAC >> ‘q ≤ p’ by decide_tac >>
              ‘ep_idx evs q ≤ ep_idx evs p’ by metis_tac[ep_idx_mono] >> fs[Abbr ‘jq’]) >>
  qexists_tac ‘p’ >> conj_tac >- first_assum ACCEPT_TAC >>
  ‘p < LENGTH evs’ by fs[ep_at_def] >>
  conj_tac
  >- (simp[proxyL0StmtsTheory.is_front_def, accepted_new_real] >>
      ‘∃f' x. ev_new (EL p evs) = SOME (f', x)’
        by (fs[ep_at_def] >> Cases_on ‘ev_new (EL p evs)’ >> fs[] >> metis_tac[pair_CASES]) >>
      ‘EL jp (ep_conn evs) = ISL x’ by metis_tac[new_front] >>
      ‘EL jp (ep_conn evs) = EL jp (ep_conn (PE b hw k w4 n))’
        by (irule EL_prefix >> fs[LENGTH_ep_conn]) >>
      Cases_on ‘x’ >> fs[]) >>
  ‘io_ep_at io p ∧ io_ep_idx io p = jp ∧ io_ep_at io q ∧ io_ep_idx io q = jq’
    by metis_tac[io_ep_ft] >>
  ‘proxy_chan_hdl a b hw k w4 jp = SOME hd ∧ proxy_chan_hdl a b hw k w4 jq = SOME c’
    by (conj_tac >> irule proxy_chan_hdl_of >> qexists_tac ‘n’ >> irule proxy_bound_lookup >> metis_tac[]) >>
  qpat_x_assum ‘io_ep_idx io p = jp’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th])) >>
  qpat_x_assum ‘io_ep_idx io q = jq’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th])) >>
  drule_all proxy_pr_of >> disch_then ACCEPT_TAC
QED

(* ------------------------------------------------------------------------
   proxy_safe_l0 for the run, given the buffering bound (still open)
   ------------------------------------------------------------------------ *)

(* proxy_safe_l0's last two conjuncts for a paired front (rev 7 bound) *)
Definition proxy_bound_ok_def:
  proxy_bound_ok kt hw (pr : num -> num option) io ⇔
    ∀evs p q. LPREFIX (fromList evs) io ∧ proxyL0Stmts$is_front p evs ∧ pr p = SOME q ⇒
      (pos_timed_out kt q (fromList evs) ∨
       LENGTH (proxyL0Stmts$pos_read p evs) ≤ LENGTH (proxyL0Stmts$pos_sent q evs) + proxy_bnd hw) ∧
      (pos_timed_out kt p (fromList evs) ∨
       LENGTH (proxyL0Stmts$pos_read q evs) ≤ LENGTH (proxyL0Stmts$pos_sent p evs) + proxy_bnd hw)
End

Theorem proxy_safe_run_bound:
  proxy_start a w0 pre w4 k ∧ ptot k b hw w4 ∧
  (∀ft. LPREFIX (fromList ft) (proxy_run_io b hw k w4 pre) ⇒ ep_ok ft) ∧
  proxy_bound_ok kt hw (proxy_pr a b hw k w4 (proxy_run_io b hw k w4 pre)) (proxy_run_io b hw k w4 pre) ⇒
  proxy_safe_l0 kt hw a b (proxy_pr a b hw k w4 (proxy_run_io b hw k w4 pre)) (proxy_run_io b hw k w4 pre)
Proof
  strip_tac >> rewrite_tac[proxyL0StmtsTheory.proxy_safe_l0_def] >> conj_tac
  >- (rpt strip_tac >> irule proxy_pr_inj >>
      qexistsl_tac [‘a’, ‘b’, ‘hw’, ‘proxy_run_io b hw k w4 pre’, ‘k’, ‘pre’, ‘q’, ‘w0’, ‘w4’] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  gen_tac >> strip_tac >> rpt conj_tac
  >- (rpt strip_tac >> drule_all proxy_listen_l0 >> simp[])
  >- (gen_tac >> strip_tac >> conj_tac
      >- (drule_all proxy_connect_port >> simp[]) >>
      drule_all proxy_connect_front_l0 >> simp[])
  >- (rpt strip_tac >> drule_all proxy_pr_connected >> simp[]) >>
  gen_tac >> strip_tac >>
  Cases_on ‘proxy_pr a b hw k w4 (proxy_run_io b hw k w4 pre) p’ >> simp[]
  >- (drule_all proxy_unpaired_l0 >> simp[]) >>
  rename1 ‘_ = SOME q’ >>
  drule_all proxy_relay_l0 >> strip_tac >> simp[] >>
  qpat_x_assum ‘proxy_bound_ok _ _ _ _’ mp_tac >> rewrite_tac[proxy_bound_ok_def] >>
  disch_then drule_all >> simp[]
QED
