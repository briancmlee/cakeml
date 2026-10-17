(*
  The proxy's liveness parts of l0_proxy_claim (proxyL0Stmts, rev 10),
  STATED over m4-server's run (proxyL0Run): from the start proxy_start
  and E1's rounds never failing (totality), on the proxy's whole trace
  proxy_run_io and its pairing proxy_pr, under the claim's live-block
  hypotheses (F1_io, F2, accepts_below):
   - proxy_live_run: proxy_live_l0 (relay, conditional on draining);
   - proxy_pairs_run: under accepts_lt (2 ** 62 + 1), proxy_pairs_l0
     (every front gets a backend).  Without it the (2^62 + 1)-th accept
     waits in L1's acq forever (the program's accept cap is 2^62 pairs),
     unpaired and unexcused;
   - conn_live_run: under accepts_lt (2 ** 62 + 1) (plain prefix form, as
     moonshot-live's accepts_lt_lift concludes; at most 2^62 accepts,
     which implies the claim's 2 ** 62 form), conn_live_l0.
  K is L1's write timeout pf_sendwait (D23), as l0_proxy_claim's header
  has it.  Statements only; proofs to come.
*)
Theory proxyLiveLift
Ancestors
  proxyStart proxyL1Claim proxyL0Run proxyL0Stmts honestL1BStmts honestL1PFModel e1DriverLoop
  moonshotProxyLive moonshotProxySafe moonshotProxyRel proxyHLStmts e1TraceAccBind e1TraceKind
  e1TraceRole e1TraceChan moonshotProxy moonshotClientSpec endpointHLModel endpointWorld
  honestEchoL0Spec l0sysEpisodes e1TracePrefix
Libs
  preamble

Overload PS[local] = “λlfd b hw lv W0 n. pstate lfd b hw (ehhist lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n)”

(* ------------------------------------------------------------------------
   The handle layer's pairing, without connect fairness: an accepted front
   gets a backend that the history connected, or connects return no socket
   without bound
   ------------------------------------------------------------------------ *)

Theorem proxy_pairs_hl:
  proxy_world lfd a W0 ∧
  MEM hd (hl_acc_handles (hl_pairs (pprog lfd b hw)
            (ehhist lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n))) ⇒
  (∃c n'. ppair lfd b hw lv W0 hd = SOME c ∧
          MEM c (hl_conn_handles (hl_pairs (pprog lfd b hw)
                   (ehhist lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n')))) ∨
  ∀k. ∃n'. k ≤ hl_nosock (hl_pairs (pprog lfd b hw)
                            (ehhist lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n'))
Proof
  strip_tac >>
  drule PS_prel_n >> disch_then (qspecl_then [‘n’, ‘lv’, ‘hw’, ‘b’] assume_tac) >>
  ‘∃p. MEM p (PS lfd b hw lv W0 n).pc ∧ p.fh = hd’
    by (drule prel_acc >> disch_then (fn th => fs[GSYM th])) >>
  qpat_x_assum ‘MEM p _’ (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  rename1 ‘i < LENGTH (PS lfd b hw lv W0 n).pc’ >>
  ‘∀m. n ≤ m ⇒ i < LENGTH (PS lfd b hw lv W0 m).pc’
    by (rpt strip_tac >> irule (cj 1 pkeep_EL) >>
        qexists_tac ‘(PS lfd b hw lv W0 n).pc’ >> simp[] >>
        irule pc_mono >> simp[] >> qexists_tac ‘a’ >> simp[]) >>
  Cases_on ‘∃m c. n ≤ m ∧ (EL i (PS lfd b hw lv W0 m).pc).bh = SOME c’
  >- (disj1_tac >> pop_assum strip_assume_tac >>
      ‘i < LENGTH (PS lfd b hw lv W0 m).pc’ by simp[] >>
      qexistsl_tac [‘c’, ‘m’] >> conj_tac
      >- (drule ppair_SOME >> disch_then (fn th => REWRITE_TAC [th]) >>
          qexistsl_tac [‘m’, ‘i’] >> simp[] >>
          mp_tac (Q.INST [‘n'’ |-> ‘m’] PS_slot_const) >>
          impl_tac >- asm_rewrite_tac [] >> strip_tac >> gvs[]) >>
      drule PS_prel_n >> disch_then (qspecl_then [‘m’, ‘lv’, ‘hw’, ‘b’] assume_tac) >>
      qpat_x_assum ‘prel _ (PS _ _ _ _ _ m) _ _ _ _’
        (fn th => REWRITE_TAC [REWRITE_RULE [prel_def] th]) >>
      qexists_tac ‘EL i (PS lfd b hw lv W0 m).pc’ >> simp[EL_MEM]) >>
  disj2_tac >> irule proxy_connect_forever >>
  conj_tac >- (qexistsl_tac [‘i’, ‘n’] >> asm_rewrite_tac [] >> rpt strip_tac >>
                Cases_on ‘(EL i (PS lfd b hw lv W0 m).pc).bh’ >> fs[] >> metis_tac[]) >>
  qexists_tac ‘a’ >> first_assum ACCEPT_TAC
QED

(* ------------------------------------------------------------------------
   A queued front is accepted while the program's accept cap is open
   ------------------------------------------------------------------------ *)

(* The fds in use: the listener and one per open handle, at most two per
   pair, so fewer than 2^64 *)
Theorem prel_used_lt:
  prel lfd st rdy ps w hs ⇒ LENGTH (ep_used w) < dimword (:64)
Proof
  rewrite_tac [prel_def] >> strip_tac >>
  ‘LENGTH (MAP FST w.open_fds) = CARD (set (MAP FST w.open_fds))’
    by simp[ALL_DISTINCT_CARD_LIST_TO_SET] >>
  ‘set (MAP FST w.open_fds) = set (MAP SND hs.tbl)’ by simp[EXTENSION] >>
  ‘CARD (set (MAP SND hs.tbl)) ≤ LENGTH (MAP SND hs.tbl)’ by simp[CARD_LIST_TO_SET] >>
  ‘LENGTH (MAP FST hs.tbl) = CARD (set (MAP FST hs.tbl))’
    by simp[ALL_DISTINCT_CARD_LIST_TO_SET] >>
  ‘set (MAP FST hs.tbl) ⊆ set (FLAT (MAP phds st.pc))’
    by (simp[SUBSET_DEF, MEM_FLAT, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
        qpat_x_assum ‘∀h. MEM h (MAP FST hs.tbl) ⇒ _’ (qspec_then ‘FST y’ mp_tac) >>
        impl_tac >- (simp[MEM_MAP] >> qexists_tac ‘y’ >> simp[]) >>
        strip_tac >> qexists_tac ‘p’ >> simp[] >> irule popen_phds >> simp[]) >>
  ‘CARD (set (MAP FST hs.tbl)) ≤ CARD (set (FLAT (MAP phds st.pc)))’
    by (irule CARD_SUBSET >> simp[]) >>
  ‘CARD (set (FLAT (MAP phds st.pc))) ≤ LENGTH (FLAT (MAP phds st.pc))’
    by simp[CARD_LIST_TO_SET] >>
  mp_tac (Q.INST [‘pc’ |-> ‘st.pc’] LENGTH_phds_le) >>
  qpat_x_assum ‘2 * LENGTH st.pc ≤ cbound’ mp_tac >>
  qpat_x_assum ‘LENGTH (MAP FST w.open_fds) = _’ mp_tac >>
  qpat_x_assum ‘set (MAP FST w.open_fds) = _’ SUBST1_TAC >>
  qpat_x_assum ‘CARD (set (MAP SND hs.tbl)) ≤ _’ mp_tac >>
  qpat_x_assum ‘LENGTH (MAP FST hs.tbl) = _’ mp_tac >>
  qpat_x_assum ‘CARD (set (MAP FST hs.tbl)) ≤ _’ mp_tac >>
  qpat_x_assum ‘CARD (set (FLAT _)) ≤ _’ mp_tac >>
  qpat_x_assum ‘w.reserved = []’ mp_tac >>
  qpat_x_assum ‘w.listening = _’ mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp[ep_used_def, cbound_def, dimword_def]
QED

Theorem prel_accept_bind:
  prel lfd st rdy ps w hs ∧ 2 * LENGTH st.pc + 2 ≤ cbound ∧
  w.listening = [(lfd, a, j :: q)] ⇒
  ∃r st1. ehdo lfd v (w, hs) (EAccept lfd) = SOME (r, st1) ∧
          ebind w (EAccept lfd) r = [(j, hdl lfd hs.nxt)]
Proof
  strip_tac >> drule_all prel_accept >>
  disch_then (qspecl_then [‘v’, ‘0’] strip_assume_tac) >>
  drule prel_used_lt >> rewrite_tac [wordsTheory.dimword_64] >> strip_tac >>
  qexistsl_tac [‘r’, ‘(w1, hs1)’] >> simp[] >>
  qpat_x_assum ‘ehdo _ _ _ _ = _’ mp_tac >>
  asm_simp_tac (srw_ss()) [ehdo_def, ep_accept_def, ep_alloc_def, LET_THM] >>
  rw[] >> simp[ebind_def]
QED

Theorem ehbacts_APPEND:
  ∀xs k st rs st1.
    ehacts lfd lv n k st xs = SOME (rs, st1) ⇒
    ehbacts lfd lv n k st (xs ++ ys) =
      ehbacts lfd lv n k st xs ++ ehbacts lfd lv n (k + LENGTH xs) st1 ys
Proof
  Induct >> simp[ehacts_def, ehbacts_def] >> rpt gen_tac >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[ADD1]
QED

(* MAIN of this part: a front queued at round n with the cap open is bound
   in round n *)
Theorem proxy_queued_bound:
  proxy_world lfd a W0 ∧
  (FST (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n)).listening = [(lfd, a', j :: q)] ∧
  2 * LENGTH (PS lfd b hw lv W0 n).pc + 2 ≤ cbound ⇒
  MEM j (MAP FST (ehbinds lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 (SUC n)))
Proof
  strip_tac >> drule pinv_all >> disch_then (qspecl_then [‘lv’, ‘hw’, ‘b’, ‘n’] mp_tac) >>
  simp_tac (srw_ss()) [pinv_def, LET_THM] >>
  qabbrev_tac ‘h = ehhist lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n’ >>
  qabbrev_tac ‘SW = ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n’ >>
  PairCases_on ‘SW’ >> rename1 ‘(w, hs)’ >> gvs[] >> strip_tac >>
  qabbrev_tac ‘st = pstate lfd b hw h’ >>
  simp[ehbinds_def, pprog_new_actions] >> disj2_tac >>
  ‘MAP SND (pacts lfd b hw st' (prdy h)) = MAP SND (pall plevels st.pc) ++
     EAccept lfd :: MAP SND (pall (pone b hw st'.lv (MAP SND st'.last)
                                     (FLAT (MAP pwrites st.pc)) (prdy h)) st.pc)’
    by simp[pacts_def] >>
  pop_assum SUBST1_TAC >>
  qspecl_then [‘pall plevels st.pc’, ‘st’, ‘hl_pairs (pprog lfd b hw) h’, ‘0’] mp_tac
    (Q.INST [‘w’ |-> ‘w’, ‘hs’ |-> ‘hs’, ‘rdy’ |-> ‘prdy h’] prel_levels) >>
  simp[pall_plevels] >> strip_tac >>
  drule ehbacts_APPEND >> simp[] >> disch_then kall_tac >>
  simp[ehbacts_def] >>
  drule_all prel_accept_bind >>
  disch_then (qspec_then ‘lv n (LENGTH (pall plevels st.pc))’ strip_assume_tac) >>
  simp[]
QED

(* ------------------------------------------------------------------------
   The cap: a closed accept cap with a front queued means more than 2^62
   accepted channels
   ------------------------------------------------------------------------ *)

Theorem hl_acc_handles_acc_hdls:
  hl_acc_handles ps = acc_hdls ps
Proof
  simp[hl_acc_handles_def, acc_hdls_def]
QED

Theorem phds_fh_distinct:
  ∀pc. ALL_DISTINCT (FLAT (MAP phds pc)) ⇒ ALL_DISTINCT (MAP (λp. p.fh) pc)
Proof
  Induct >> simp[phds_def] >> rpt gen_tac >> strip_tac >> conj_tac
  >- (simp[MEM_MAP] >> rpt strip_tac >>
      qpat_x_assum ‘¬MEM h.fh (FLAT _)’ mp_tac >>
      simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> qexists_tac ‘p’ >> simp[phds_def]) >>
  first_x_assum irule >>
  qpat_x_assum ‘ALL_DISTINCT (_ ++ _)’ mp_tac >> simp[ALL_DISTINCT_APPEND]
QED

Theorem FILTER_COUNT_LIST_LENGTH:
  LENGTH (FILTER (λi. P (EL i l)) (COUNT_LIST (LENGTH l))) = LENGTH (FILTER P l)
Proof
  ‘MAP (λi. EL i l) (FILTER (λi. P (EL i l)) (COUNT_LIST (LENGTH l))) =
   FILTER P (MAP (λi. EL i l) (COUNT_LIST (LENGTH l)))’
    by simp[FILTER_MAP, combinTheory.o_DEF] >>
  ‘MAP (λi. EL i l) (COUNT_LIST (LENGTH l)) = l’
    by simp[COUNT_LIST_GENLIST, MAP_GENLIST, combinTheory.o_DEF, GENLIST_EL] >>
  metis_tac[LENGTH_MAP]
QED

(* The pairs' fronts are bound to distinct channels without a peer
   address, and the queued front is one more *)
Theorem cap_count:
  prel lfd st rdy ps w hs ∧ gchinv lfd B ps (w, hs) ∧ kinv B ps w ∧
  w.listening = [(lfd, a, j :: q)] ⇒
  LENGTH st.pc + 1 ≤ LENGTH (FILTER (λc. ¬cpa c) w.chans)
Proof
  strip_tac >>
  qabbrev_tac ‘idx = FILTER (λi. ¬cpa (EL i w.chans)) (COUNT_LIST (LENGTH w.chans))’ >>
  ‘LENGTH idx = LENGTH (FILTER (λc. ¬cpa c) w.chans)’
    by simp[Abbr ‘idx’, FILTER_COUNT_LIST_LENGTH] >>
  pop_assum (SUBST1_TAC o SYM) >>
  ‘ALL_DISTINCT idx’ by simp[Abbr ‘idx’, FILTER_ALL_DISTINCT, all_distinct_count_list] >>
  ‘∀i. MEM i idx ⇔ i < LENGTH w.chans ∧ ¬cpa (EL i w.chans)’
    by simp[Abbr ‘idx’, MEM_FILTER, MEM_COUNT_LIST, CONJ_COMM] >>
  qpat_x_assum ‘prel _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [prel_def]) >>
  qpat_x_assum ‘gchinv _ _ _ _’ (strip_assume_tac o REWRITE_RULE [gchinv_def]) >>
  qpat_x_assum ‘kinv _ _ _’ (strip_assume_tac o REWRITE_RULE [kinv_def]) >>
  ‘ALL_DISTINCT (MAP (λp. p.fh) st.pc)’ by (simp[] >> irule phds_fh_distinct >> first_assum ACCEPT_TAC) >>
  ‘∀hd. MEM hd (MAP (λp. p.fh) st.pc) ⇒ ∃i. MEM (i, hd) B’
    by (simp[MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
        ‘MEM p.fh (acc_hdls ps)’
          by (simp[GSYM hl_acc_handles_acc_hdls] >>
              qpat_x_assum ‘∀hd. MEM hd (hl_acc_handles ps) ⇔ _’ (qspec_then ‘p.fh’ SUBST1_TAC) >>
              qexists_tac ‘p’ >> simp[]) >>
        qpat_x_assum ‘∀hd. MEM hd (hl_conn_handles ps) ∨ MEM hd (acc_hdls ps) ⇒ _’
          (qspec_then ‘p.fh’ mp_tac) >>
        simp[MEM_MAP, EXISTS_PROD]) >>
  qabbrev_tac ‘ch = λhd. @i. MEM (i, hd) B’ >>
  ‘∀hd. MEM hd (MAP (λp. p.fh) st.pc) ⇒ MEM (ch hd, hd) B’
    by (rpt strip_tac >> simp[Abbr ‘ch’] >> SELECT_ELIM_TAC >> simp[] >>
        first_x_assum irule >> first_assum ACCEPT_TAC) >>
  ‘LENGTH (MAP ch (MAP (λp. p.fh) st.pc)) = LENGTH st.pc’ by simp[] >>
  ‘ALL_DISTINCT (MAP ch (MAP (λp. p.fh) st.pc))’
    by (irule ALL_DISTINCT_MAP_INJ >> conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >> rpt strip_tac >>
        ‘MEM (ch x, x) B’ by (qpat_assum ‘∀hd. MEM hd (MAP (λp. p.fh) st.pc) ⇒ MEM (ch hd, hd) B’ irule >> first_assum ACCEPT_TAC) >>
        ‘MEM (ch y, y) B’ by (qpat_assum ‘∀hd. MEM hd (MAP (λp. p.fh) st.pc) ⇒ MEM (ch hd, hd) B’ irule >> first_assum ACCEPT_TAC) >>
        qpat_x_assum ‘ch x = ch y’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
        qspecl_then [‘B’, ‘ch y’, ‘y’, ‘x’] mp_tac (Q.GENL [‘B’, ‘j’, ‘h’, ‘h'’] bind_fun) >>
        impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  ‘¬MEM j (MAP FST B) ∧ j < LENGTH w.chans’
    by (qpat_x_assum ‘EVERY (λ(l, a, q). ALL_DISTINCT q ∧ _) w.listening’ mp_tac >>
        qpat_assum ‘w.listening = [(_, _, _ :: _)]’ (fn th => REWRITE_TAC [th]) >> simp[]) >>
  ‘¬cpa (EL j w.chans)’
    by (qpat_x_assum ‘EVERY (λ(l, a, q). EVERY _ q) w.listening’ mp_tac >>
        qpat_assum ‘w.listening = [(_, _, _ :: _)]’ (fn th => REWRITE_TAC [th]) >> simp[]) >>
  ‘∀hd. MEM hd (MAP (λp. p.fh) st.pc) ⇒ MEM (ch hd) (MAP FST B) ∧ ch hd < LENGTH w.chans ∧ ¬cpa (EL (ch hd) w.chans)’
    by (gen_tac >> strip_tac >>
        ‘MEM (ch hd, hd) B’ by (qpat_assum ‘∀hd. MEM hd (MAP (λp. p.fh) st.pc) ⇒ MEM (ch hd, hd) B’ irule >> first_assum ACCEPT_TAC) >>
        ‘MEM hd (acc_hdls ps)’
          by (rewrite_tac [GSYM hl_acc_handles_acc_hdls] >>
              qpat_x_assum ‘∀hd. MEM hd (hl_acc_handles ps) ⇔ _’ (fn th => REWRITE_TAC [th]) >>
              qpat_x_assum ‘MEM hd (MAP (λp. p.fh) st.pc)’ mp_tac >> simp[MEM_MAP] >> strip_tac >>
              qexists_tac ‘p’ >> simp[]) >>
        rpt conj_tac
        >- (simp[MEM_MAP, EXISTS_PROD] >> qexists_tac ‘hd’ >> first_assum ACCEPT_TAC)
        >- (qpat_x_assum ‘∀j hd. MEM (j, hd) B ⇒ j < _ ∧ _’ drule >> simp[])
        >> qpat_x_assum ‘∀j hd. MEM (j, hd) B ⇒ (_ ⇔ _) ∧ _’ drule >> simp[]) >>
  ‘¬MEM j (MAP ch (MAP (λp. p.fh) st.pc))’
    by (simp[MEM_MAP] >> rpt strip_tac >>
        qpat_x_assum ‘∀hd. MEM hd (MAP (λp. p.fh) st.pc) ⇒ MEM (ch hd) (MAP FST B) ∧ _’
          (qspec_then ‘y’ mp_tac) >>
        impl_tac >- (simp[MEM_MAP] >> qexists_tac ‘p’ >> simp[]) >> strip_tac >>
        qpat_x_assum ‘MEM (ch _) (MAP FST B)’ mp_tac >>
        qpat_x_assum ‘¬MEM j (MAP FST B)’ mp_tac >> simp[]) >>
  ‘ALL_DISTINCT (j :: MAP ch (MAP (λp. p.fh) st.pc))’ by (rewrite_tac [ALL_DISTINCT] >> conj_tac >> first_assum ACCEPT_TAC) >>
  ‘set (j :: MAP ch (MAP (λp. p.fh) st.pc)) ⊆ set idx’
    by (rewrite_tac [SUBSET_DEF, LIST_TO_SET_THM, IN_INSERT] >> gen_tac >> strip_tac
        >- (qpat_x_assum ‘x = j’ SUBST1_TAC >>
            qpat_x_assum ‘∀i. MEM i idx ⇔ _’ (fn th => REWRITE_TAC [th]) >>
            conj_tac >> first_assum ACCEPT_TAC) >>
        qpat_x_assum ‘MEM x (MAP ch _)’ (strip_assume_tac o ONCE_REWRITE_RULE [MEM_MAP]) >>
        qpat_x_assum ‘∀hd. MEM hd (MAP (λp. p.fh) st.pc) ⇒ MEM (ch hd) (MAP FST B) ∧ _’ drule >>
        strip_tac >> qpat_x_assum ‘x = ch _’ SUBST1_TAC >>
        qpat_x_assum ‘∀i. MEM i idx ⇔ _’ (fn th => REWRITE_TAC [th]) >>
        conj_tac >> first_assum ACCEPT_TAC) >>
  ‘CARD (set (j :: MAP ch (MAP (λp. p.fh) st.pc))) ≤ CARD (set idx)’ by (irule CARD_SUBSET >> simp[]) >>
  ‘CARD (set (j :: MAP ch (MAP (λp. p.fh) st.pc))) = LENGTH (j :: MAP ch (MAP (λp. p.fh) st.pc))’
    by (irule ALL_DISTINCT_CARD_LIST_TO_SET >> first_assum ACCEPT_TAC) >>
  ‘CARD (set idx) = LENGTH idx’ by (irule ALL_DISTINCT_CARD_LIST_TO_SET >> first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘CARD (set (j :: _)) ≤ _’ mp_tac >>
  qpat_x_assum ‘CARD (set (j :: _)) = _’ SUBST1_TAC >>
  qpat_x_assum ‘CARD (set idx) = _’ SUBST1_TAC >>
  qpat_x_assum ‘LENGTH (MAP ch (MAP (λp. p.fh) st.pc)) = _’ mp_tac >>
  rewrite_tac [LENGTH] >> decide_tac
QED

(* The raw side: channels without a peer address are the accepts *)
Theorem accepted_new_local:
  honestEchoL0Spec$l0_event_accepted ev ≠ NONE ⇔ ∃f l. ev_new ev = SOME (f, INR l)
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bl’ >> Cases_on ‘nm’ >>
  rw[honestEchoL0SpecTheory.l0_event_accepted_def, ev_new_def,
     honestEchoL0SpecTheory.l0_ev_res_def] >> every_case_tac >> gvs[]
QED

Theorem ep_conn_accepted:
  ∀evs. LENGTH (FILTER $¬ (ep_conn evs)) = LENGTH (honestEchoL0Spec$l0_accepted evs)
Proof
  Induct >> simp[ep_conn_def, honestEchoL0SpecTheory.l0_accepted_def] >> rpt strip_tac >>
  fs[honestEchoL0SpecTheory.l0_accepted_def] >>
  Cases_on ‘honestEchoL0Spec$l0_event_accepted h’ >> simp[]
  >- (‘∀f l. ev_new h ≠ SOME (f, INR l)’ by metis_tac[accepted_new_local] >>
      Cases_on ‘ev_new h’ >> simp[] >> PairCases_on ‘x’ >> Cases_on ‘x1’ >> gvs[]) >>
  ‘∃f l. ev_new h = SOME (f, INR l)’ by metis_tac[accepted_new_local, optionTheory.NOT_NONE_SOME] >>
  simp[]
QED

(* ------------------------------------------------------------------------
   The socketless connects: each HL connect that got no socket is an L0
   sys_connect event whose value field is 0 (l0_nosock)
   ------------------------------------------------------------------------ *)

Theorem edo_ch:
  edo lfd pol (w, es) x = SOME (r, (w', es'), evs) ⇒ w'.ch = w.ch
Proof
  Cases_on ‘x’ >> simp[honestL1EPModelTheory.edo_def, AllCaseEqs()] >> rw[] >> gvs[] >>
  TRY (PairCases_on ‘z’) >> gvs[] >>
  metis_tac[honestL1PFFlushTheory.pdo_ch, honestL1PFFlushTheory.l1_close_ch,
            honestL1StepsTheory.l0_do_env, honestL1EPModelTheory.sys_connect_def]
QED

Theorem connect_out_nosock:
  LENGTH out = 13 ∧ honestL1EPModel$res_val out = 0 ⇒
  proxyL0Stmts$l0_nosock (IO_event (ExtCall «sys_connect») conf (ZIP (REPLICATE 13 0w, out)))
Proof
  Cases_on ‘out’ >>
  simp[proxyL0StmtsTheory.l0_nosock_def, proxyL0StmtsTheory.l0_event_connected_def,
       proxyL0StmtsTheory.connect_port_def, honestL1EPModelTheory.res_val_def, MAP_ZIP]
QED

Theorem edo_nosock:
  edo lfd pol (w, es) x = SOME (EConnected NONE, ws', evs) ∧ (∀h. LENGTH (w.ch.errno_of h) = 4) ⇒
  ∃ev. evs = [ev] ∧ proxyL0Stmts$l0_nosock ev
Proof
  Cases_on ‘x’ >> simp[honestL1EPModelTheory.edo_def, AllCaseEqs()] >> rw[] >>
  TRY (PairCases_on ‘z’ >> gvs[] >> every_case_tac >> gvs[] >> NO_TAC) >>
  TRY (every_case_tac >> gvs[] >> NO_TAC) >>
  qpat_x_assum ‘sys_connect _ _ = _’ mp_tac >>
  simp[honestL1EPModelTheory.sys_connect_def, honestL1ModelTheory.l0_do_def,
       honestL0WorldTheory.l0_ffi_fn_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >>
  simp[honestL0WorldTheory.l0_call_def, honestL0WorldTheory.l0_hdr_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> irule connect_out_nosock >>
  simp[honestL0Theory.enc_res_def, honestL0WorldTheory.enc_err_val_def, MarshallingTheory.LENGTH_n2w8]
QED

Theorem eacts_nosock:
  ∀acts w es rs evs ws'.
    eacts lfd pol (w, es) acts = SOME (rs, evs, ws') ∧ (∀h. LENGTH (w.ch.errno_of h) = 4) ⇒
    hl_nosock (ZIP (acts, rs)) ≤ LENGTH (FILTER proxyL0Stmts$l0_nosock evs)
Proof
  Induct >> simp[honestL1EPModelTheory.eacts_def, hl_nosock_def] >> rpt gen_tac >>
  simp[AllCaseEqs()] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  PairCases_on ‘ws1’ >>
  ‘ws10.ch = w.ch’ by (drule edo_ch >> simp[]) >>
  first_x_assum (qspecl_then [‘ws10’, ‘ws11’, ‘rs'’, ‘evs'’, ‘ws'’] mp_tac) >>
  impl_tac >- simp[] >> simp[hl_nosock_def, FILTER_APPEND] >>
  Cases_on ‘r = EConnected NONE’ >> simp[] >>
  qpat_x_assum ‘r = _’ SUBST_ALL_TAC >>
  drule_all edo_nosock >> strip_tac >> simp[]
QED

Theorem erounds_nosock:
  (∀n h ws evs logs. erounds lfd pol ifds m ws0 n = SOME (h, ws, evs, logs) ⇒
                     ∀hh. LENGTH ((FST ws).ch.errno_of hh) = 4) ⇒
  ∀n h ws evs logs.
    erounds lfd pol ifds m ws0 n = SOME (h, ws, evs, logs) ⇒
    hl_nosock (hl_pairs m h) ≤ LENGTH (FILTER proxyL0Stmts$l0_nosock evs)
Proof
  strip_tac >> Induct
  >- simp[honestL1EPModelTheory.erounds_def, hl_pairs_def, hl_nosock_def] >>
  rpt gen_tac >> strip_tac >> drule erounds_SUC_SOME >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rename1 ‘erounds _ _ _ _ _ n = SOME (h0, ws1, evs0, logs0)’ >>
  first_x_assum (qspecl_then [‘h0’, ‘ws1’, ‘evs0’, ‘logs0’] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  ‘∀hh. LENGTH ((FST ws1).ch.errno_of hh) = 4’
    by (first_x_assum (qspecl_then [‘n’, ‘h0’, ‘ws1’, ‘evs0’, ‘logs0’] mp_tac) >> simp[]) >>
  qpat_x_assum ‘eround _ _ _ _ _ = _’ mp_tac >>
  simp[honestL1EPModelTheory.eround_def, AllCaseEqs()] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >> PairCases_on ‘ws1’ >>
  drule eacts_nosock >> impl_tac >- fs[] >> strip_tac >>
  qpat_x_assum ‘(h, ws, evs, logs) = _’
    (strip_assume_tac o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  simp[moonshotClientTheory.hl_pairs_SNOC, asyncM3WorldTheory.ssnap_def, FILTER_APPEND] >>
  fs[hl_nosock_def, FILTER_APPEND]
QED

(* On the handle layer's history: E1's history is L1's (l1ep_refines_ehl) *)
Theorem ehl_nosock_l0:
  l0_rely w0 ∧ honestL0WorldProps$fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (ecm lfd pol ifds m w0 n) + 1 < dimword (:64)) ∧
  erounds lfd pol ifds m (w0, einit) n = SOME (h, ws, evs, logs) ⇒
  hl_nosock (hl_pairs m (ehhist lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) n)) ≤
  LENGTH (FILTER proxyL0Stmts$l0_nosock evs)
Proof
  strip_tac >>
  mp_tac (Q.INST [‘a’ |-> ‘a’, ‘calls’ |-> ‘calls’] honestL1EPRefineTheory.l1ep_refines_ehl) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  first_assum (qspecl_then [‘n’, ‘h’, ‘ws’, ‘evs’, ‘logs’] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qpat_x_assum ‘ehhist _ _ _ _ _ _ = _’ SUBST1_TAC >>
  mp_tac (Q.INST [‘ws0’ |-> ‘(w0, einit)’] erounds_nosock) >>
  impl_tac
  >- (rpt strip_tac >>
      first_x_assum (qspecl_then [‘n'’, ‘h'’, ‘ws'’, ‘evs'’, ‘logs'’] mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
      qpat_x_assum ‘l0_rely (FST ws')’ mp_tac >> simp[honestL0RelyTheory.l0_rely_def]) >>
  disch_then irule >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The run's trace: round n's events are the first n rounds' chunks
   ------------------------------------------------------------------------ *)

Theorem erounds_evs_genlist:
  (∀i. erounds lfd pol ifds m ws0 i ≠ NONE) ⇒
  ∀n h ws evs logs. erounds lfd pol ifds m ws0 n = SOME (h, ws, evs, logs) ⇒
    evs = FLAT (GENLIST (eround_evs lfd pol ifds m ws0) n)
Proof
  strip_tac >> Induct
  >- simp[honestL1EPModelTheory.erounds_def] >>
  rpt gen_tac >> strip_tac >>
  ‘erounds lfd pol ifds m ws0 (SUC n) ≠ NONE’ by simp[] >>
  drule erun_SUC >> strip_tac >>
  ‘erun lfd pol ifds m ws0 (SUC n) = (h, ws, evs, logs)’
    by (REWRITE_TAC[e1DriverLoopTheory.erun_def] >>
        qpat_x_assum ‘erounds _ _ _ _ _ (SUC n) = _’ SUBST1_TAC >> simp[]) >>
  Cases_on ‘erounds lfd pol ifds m ws0 n’
  >- (qpat_x_assum ‘∀i. _ ≠ NONE’ (qspec_then ‘n’ mp_tac) >> simp[]) >>
  rename1 ‘erounds _ _ _ _ _ n = SOME r0’ >> PairCases_on ‘r0’ >>
  first_x_assum (qspecl_then [‘r00’, ‘(r01, r02)’, ‘r03’, ‘r04’] mp_tac) >> simp[] >> strip_tac >>
  ‘erun lfd pol ifds m ws0 n = (r00, (r01, r02), r03, r04)’
    by (REWRITE_TAC[e1DriverLoopTheory.erun_def] >>
        qpat_x_assum ‘erounds _ _ _ _ _ n = _’ SUBST1_TAC >> simp[]) >>
  gvs[GENLIST, SNOC_APPEND, FLAT_APPEND]
QED

(* ------------------------------------------------------------------------
   Episode numbers: position i's episode is the number of episodes before it
   ------------------------------------------------------------------------ *)

Theorem ep_fds_conn_LENGTH:
  ∀evs. LENGTH (ep_fds evs) = LENGTH (ep_conn evs)
Proof
  Induct >> simp[l0sysInvTheory.ep_fds_def, ep_conn_def] >> gen_tac >>
  fs[l0sysInvTheory.ep_fds_def] >>
  Cases_on ‘ev_new h’ >> simp[] >> PairCases_on ‘x’ >> simp[]
QED

Theorem TAKE_EL_DROP:
  i < LENGTH l ⇒ TAKE i l ++ EL i l :: DROP (SUC i) l = l
Proof
  strip_tac >> ‘DROP i l = EL i l :: DROP (SUC i) l’ by simp[DROP_EL_CONS, ADD1] >>
  pop_assum (SUBST1_TAC o SYM) >> simp[TAKE_DROP]
QED

Theorem ep_conn_mid:
  ev_new e = SOME (f, x) ⇒
  LENGTH (ep_conn l1) < LENGTH (ep_conn (l1 ++ e :: l2)) ∧
  EL (LENGTH (ep_conn l1)) (ep_conn (l1 ++ e :: l2)) = ISL x
Proof
  strip_tac >> simp[ep_conn_def] >>
  REWRITE_TAC [GSYM APPEND_ASSOC, APPEND] >> simp[EL_APPEND2]
QED

Theorem ep_conn_at:
  i < LENGTH evs ∧ ev_new (EL i evs) = SOME (f, x) ⇒
  LENGTH (ep_conn (TAKE i evs)) < LENGTH (ep_conn evs) ∧
  EL (LENGTH (ep_conn (TAKE i evs))) (ep_conn evs) = ISL x
Proof
  strip_tac >>
  qspecl_then [‘EL i evs’, ‘f’, ‘x’, ‘TAKE i evs’, ‘DROP (SUC i) evs’] mp_tac
    (Q.GENL [‘e’, ‘f’, ‘x’, ‘l1’, ‘l2’] ep_conn_mid) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  drule TAKE_EL_DROP >> disch_then (fn th => REWRITE_TAC [th])
QED

Theorem ep_conn_from:
  ∀evs j. j < LENGTH (ep_conn evs) ⇒
          ∃i. i < LENGTH evs ∧ ev_new (EL i evs) ≠ NONE ∧ LENGTH (ep_conn (TAKE i evs)) = j
Proof
  Induct >> simp[ep_conn_def] >> rpt gen_tac >>
  Cases_on ‘ev_new h’ >> simp[]
  >- (strip_tac >> first_x_assum drule >> strip_tac >>
      qexists_tac ‘SUC i’ >> simp[ep_conn_def]) >>
  PairCases_on ‘x’ >> simp[] >> strip_tac >>
  Cases_on ‘j’
  >- (qexists_tac ‘0’ >> simp[ep_conn_def]) >>
  first_x_assum (qspec_then ‘n’ mp_tac) >> impl_tac >- fs[] >> strip_tac >>
  qexists_tac ‘SUC i’ >> simp[ep_conn_def]
QED

Theorem ep_conn_TAKE_lt:
  i1 < i2 ∧ i2 ≤ LENGTH evs ∧ ev_new (EL i1 evs) ≠ NONE ⇒
  LENGTH (ep_conn (TAKE i1 evs)) < LENGTH (ep_conn (TAKE i2 evs))
Proof
  strip_tac >> Cases_on ‘ev_new (EL i1 evs)’ >> fs[] >> PairCases_on ‘x’ >>
  qspecl_then [‘i1’, ‘TAKE i2 evs’, ‘x0’, ‘x1’] mp_tac (Q.GENL [‘i’, ‘evs’, ‘f’, ‘x’] ep_conn_at) >>
  simp[EL_TAKE, TAKE_TAKE]
QED

(* ------------------------------------------------------------------------
   Positions of the whole trace, through its finite prefixes
   ------------------------------------------------------------------------ *)

Theorem LTAKE_SOME_LAPPEND:
  ∀n ll l. LTAKE n ll = SOME l ⇒ ∃ll'. ll = LAPPEND (fromList l) ll'
Proof
  Induct >- (rw[] >> qexists_tac ‘ll’ >> simp[]) >>
  rpt gen_tac >> qspec_then ‘ll’ STRUCT_CASES_TAC llist_CASES >> simp[] >>
  strip_tac >> first_x_assum drule >> strip_tac >> simp[] >> metis_tac[]
QED

Theorem LNTH_prefix:
  LNTH q ll = SOME e ⇒ ∃l. LPREFIX (fromList l) ll ∧ q < LENGTH l ∧ EL q l = e
Proof
  strip_tac >>
  ‘LTAKE q ll ≠ NONE’ by (strip_tac >> drule LTAKE_EQ_NONE_LNTH >> simp[]) >>
  Cases_on ‘LTAKE q ll’ >> fs[] >>
  qexists_tac ‘x ++ [e]’ >>
  ‘LTAKE (SUC q) ll = SOME (x ++ [e])’ by simp[LTAKE_SNOC_LNTH] >>
  drule LTAKE_LENGTH >> drule LTAKE_SOME_LAPPEND >> rpt strip_tac >>
  ‘q = LENGTH x’ by fs[] >> simp[LPREFIX_APPEND, EL_APPEND2] >> metis_tac[]
QED

Theorem LPREFIX_io:
  LPREFIX (fromList l) ll ⇒
  (∀p. p < LENGTH l ⇒ LNTH p ll = SOME (EL p l)) ∧
  (∀p. p ≤ LENGTH l ⇒ LTAKE p ll = SOME (TAKE p l))
Proof
  simp[LPREFIX_APPEND] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >> conj_tac >> rpt strip_tac
  >- simp[LNTH_LAPPEND, LNTH_fromList] >>
  irule LTAKE_TAKE_LESS >> qexists_tac ‘LENGTH l’ >> simp[] >>
  qspecl_then [‘ll'’, ‘l’, ‘0’] mp_tac LTAKE_LAPPEND_fromList >> simp[]
QED

(* The start's events are no episodes *)
Theorem proxy_start_pre:
  proxy_start a w0 pre w4 k ⇒ EVERY (λe. ev_new e = NONE) pre
Proof
  simp[proxy_start_def, honestL1ModelTheory.l0_do_def, AllCaseEqs()] >> rw[] >>
  simp[ev_new_def]
QED

Theorem ep_conn_nonew:
  ∀pre. EVERY (λe. ev_new e = NONE) pre ⇒ ep_conn (pre ++ l) = ep_conn l
Proof
  Induct >> simp[ep_conn_def]
QED

(* ------------------------------------------------------------------------
   A front's episode: an accept at position p of the run's trace is raw
   episode j of some round prefix, without a peer address
   ------------------------------------------------------------------------ *)

Theorem front_episode:
  io = LAPPEND (fromList pre)
         (LFLATTEN (LGENLIST (λi. fromList (eround_evs lfd pol ifds m ws0 i)) NONE)) ∧
  EVERY (λe. ev_new e = NONE) pre ∧ (∀i. erounds lfd pol ifds m ws0 i ≠ NONE) ∧
  LPREFIX (fromList evs) io ∧ p < LENGTH evs ∧ ev_new (EL p evs) = SOME (f, INR l) ⇒
  ∃n h ws EV logs.
    erounds lfd pol ifds m ws0 n = SOME (h, ws, EV, logs) ∧
    LPREFIX (fromList (pre ++ EV)) io ∧ p < LENGTH (pre ++ EV) ∧
    io_ep_at io p ∧ io_ep_idx io p < LENGTH (ep_conn EV) ∧ ¬EL (io_ep_idx io p) (ep_conn EV)
Proof
  strip_tac >>
  qpat_assum ‘LPREFIX (fromList evs) io’ mp_tac >>
  qpat_assum ‘io = _’ (fn th => REWRITE_TAC [th]) >> strip_tac >>
  drule e1_lprefix_rounds >> strip_tac >>
  Cases_on ‘erounds lfd pol ifds m ws0 n’
  >- (qpat_x_assum ‘∀i. _ ≠ NONE’ (qspec_then ‘n’ mp_tac) >> simp[]) >>
  rename1 ‘_ = SOME r0’ >> PairCases_on ‘r0’ >>
  qexistsl_tac [‘n’, ‘r00’, ‘(r01, r02)’, ‘r03’, ‘r04’] >>
  ‘r03 = FLAT (GENLIST (eround_evs lfd pol ifds m ws0) n)’
    by (mp_tac erounds_evs_genlist >> impl_tac >- first_assum ACCEPT_TAC >>
        disch_then (qspecl_then [‘n’, ‘r00’, ‘(r01, r02)’, ‘r03’, ‘r04’] mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  ‘LPREFIX (fromList (pre ++ r03)) io’
    by (qspecl_then [‘eround_evs lfd pol ifds m ws0’, ‘n’] mp_tac
          (Q.GENL [‘f’, ‘n’] rounds_LPREFIX) >>
        qpat_x_assum ‘r03 = _’ (SUBST1_TAC o SYM) >>
        simp[LPREFIX_APPEND] >> strip_tac >>
        qpat_x_assum ‘io = _’ SUBST1_TAC >> qpat_x_assum ‘LFLATTEN _ = _’ SUBST1_TAC >>
        qexists_tac ‘ll’ >> simp[GSYM LAPPEND_fromList, LAPPEND_ASSOC]) >>
  qpat_x_assum ‘r03 = _’ (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum ‘isPREFIX _ _’ (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
  rename1 ‘pre ++ r03 = evs ++ rest’ >>
  ‘p < LENGTH (pre ++ r03) ∧ EL p (pre ++ r03) = EL p evs’
    by (qpat_x_assum ‘pre ++ r03 = _’ SUBST1_TAC >> simp[EL_APPEND1]) >>
  ‘LENGTH pre ≤ p’
    by (CCONTR_TAC >>
        ‘EL p (pre ++ r03) = EL p pre’ by (irule EL_APPEND1 >> fs[]) >>
        qpat_x_assum ‘EVERY _ pre’ (mp_tac o REWRITE_RULE [EVERY_EL]) >>
        disch_then (qspec_then ‘p’ mp_tac) >> fs[]) >>
  ‘p - LENGTH pre < LENGTH r03 ∧ EL (p - LENGTH pre) r03 = EL p evs’
    by (fs[] >> qpat_x_assum ‘EL p (pre ++ r03) = _’ (SUBST1_TAC o SYM) >>
        simp[EL_APPEND2]) >>
  qpat_assum ‘LPREFIX (fromList (pre ++ _)) io’ (strip_assume_tac o MATCH_MP LPREFIX_io) >>
  ‘io_ep_idx io p = LENGTH (ep_conn (TAKE (p - LENGTH pre) r03))’
    by (REWRITE_TAC [io_ep_idx_def] >>
        qpat_x_assum ‘∀p. p ≤ _ ⇒ LTAKE p io = _’ (qspec_then ‘p’ mp_tac) >>
        impl_tac >- (irule LESS_IMP_LESS_OR_EQ >> first_assum ACCEPT_TAC) >>
        disch_then SUBST1_TAC >> simp_tac (srw_ss()) [ep_fds_conn_LENGTH] >>
        REWRITE_TAC [TAKE_APPEND] >>
        ‘TAKE p pre = pre’ by (irule TAKE_LENGTH_TOO_LONG >> first_assum ACCEPT_TAC) >>
        pop_assum SUBST1_TAC >>
        qpat_x_assum ‘EVERY _ pre’ (fn th => REWRITE_TAC [MATCH_MP ep_conn_nonew th])) >>
  qspecl_then [‘p - LENGTH pre’, ‘r03’, ‘f’, ‘INR l’] mp_tac
    (Q.GENL [‘i’, ‘evs’, ‘f’, ‘x’] ep_conn_at) >>
  impl_tac >- simp[] >> strip_tac >>
  qpat_x_assum ‘io = _’ (fn th => REWRITE_TAC [SYM th]) >> qpat_x_assum ‘pre ++ r03 = _’ kall_tac >>
  qpat_x_assum ‘LPREFIX (fromList evs) (_ ++ₗ _)’ kall_tac >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[io_ep_at_def]
QED

(* The proxy performs every round's actions *)
Theorem proxy_ehacts:
  proxy_world lfd a W0 ⇒
  ehacts lfd lv n 0 (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n)
    (new_actions (log_of (pprog lfd b hw)) (ehhist lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n))
    ≠ NONE
Proof
  strip_tac >> drule PS_round >> disch_then (qspecl_then [‘n’, ‘lv’, ‘hw’, ‘b’] strip_assume_tac) >>
  rewrite_tac [pprog_new_actions] >> asm_rewrite_tac [] >> simp[]
QED

(* A front's channel gets bound: the program accepts it, or the accept cap
   is closed, so more than 2^62 fronts were accepted *)
Theorem front_bound:
  l0_rely w0 ∧ honestL0WorldProps$fds_lt w0 ∧ MEM lfd (l0_used w0) ∧ MEM 0w (l0_used w0) ∧
  (∀n. erounds lfd pol_never (pifds lfd b hw) (pprog lfd b hw) (w0, einit) n ≠ NONE) ∧
  erounds lfd pol_never (pifds lfd b hw) (pprog lfd b hw) (w0, einit) n = SOME (h, ws, evs, logs) ∧
  j < LENGTH (ep_conn evs) ∧ ¬EL j (ep_conn evs) ∧
  LENGTH (FILTER $¬ (ep_conn evs)) ≤ 2 ** 62 ⇒
  ∃n'. MEM j (MAP FST (ehbinds lfd (elv lfd pol_never (pifds lfd b hw) (pprog lfd b hw) w0)
                         (pifds lfd b hw) (pprog lfd b hw)
                         (pew lfd a pol_never (pifds lfd b hw) (pprog lfd b hw) w0 calls) n'))
Proof
  strip_tac >>
  ‘∀n. SND (ecm lfd pol_never (pifds lfd b hw) (pprog lfd b hw) w0 n) + 1 < dimword (:64)’
    by (irule proxy_ecm_bound >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  ‘proxy_world lfd a (pew lfd a pol_never (pifds lfd b hw) (pprog lfd b hw) w0 calls)’
    by REWRITE_TAC [pew_proxy_world] >>
  ‘∀n. ehacts lfd (elv lfd pol_never (pifds lfd b hw) (pprog lfd b hw) w0) n 0
         (ehst lfd (elv lfd pol_never (pifds lfd b hw) (pprog lfd b hw) w0) (pifds lfd b hw)
            (pprog lfd b hw) (pew lfd a pol_never (pifds lfd b hw) (pprog lfd b hw) w0 calls) n)
         (new_actions (log_of (pprog lfd b hw))
            (ehhist lfd (elv lfd pol_never (pifds lfd b hw) (pprog lfd b hw) w0) (pifds lfd b hw)
               (pprog lfd b hw) (pew lfd a pol_never (pifds lfd b hw) (pprog lfd b hw) w0 calls) n))
       ≠ NONE’
    by (gen_tac >> irule proxy_ehacts >> qexists_tac ‘a’ >> first_assum ACCEPT_TAC) >>
  drule_all e1_acc_queued >> strip_tac
  >- (qexists_tac ‘n’ >> first_assum ACCEPT_TAC) >>
  qabbrev_tac ‘lv = elv lfd pol_never (pifds lfd b hw) (pprog lfd b hw) w0’ >>
  qabbrev_tac ‘EW = pew lfd a pol_never (pifds lfd b hw) (pprog lfd b hw) w0 calls’ >>
  Cases_on ‘2 * LENGTH (PS lfd b hw lv EW n).pc + 2 ≤ cbound’
  >- (qexists_tac ‘SUC n’ >> irule proxy_queued_bound >> rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- (qexistsl_tac [‘a’, ‘[]’] >> first_assum ACCEPT_TAC) >>
      qexists_tac ‘a’ >> first_assum ACCEPT_TAC) >>
  (* the cap is closed: the pairs' fronts and the queued one are accepted *)
  ‘MAP cpa (FST (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) EW n)).chans = ep_conn evs’
    by (qunabbrev_tac ‘lv’ >> qunabbrev_tac ‘EW’ >> drule_all e1_roles >>
        disch_then (qspecl_then [‘calls’, ‘a’] ACCEPT_TAC)) >>
  drule PS_prel_n >> disch_then (qspecl_then [‘n’, ‘lv’, ‘hw’, ‘b’] assume_tac) >>
  qpat_assum ‘proxy_world _ _ _’ (strip_assume_tac o REWRITE_RULE [proxy_world_def]) >>
  ‘gchinv lfd (ehbinds lfd lv (pifds lfd b hw) (pprog lfd b hw) EW n)
     (hl_pairs (pprog lfd b hw) (ehhist lfd lv (pifds lfd b hw) (pprog lfd b hw) EW n))
     (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) EW n)’
    by (irule ehrounds_gchinv >> asm_rewrite_tac [] >> simp[]) >>
  ‘kinv (ehbinds lfd lv (pifds lfd b hw) (pprog lfd b hw) EW n)
     (hl_pairs (pprog lfd b hw) (ehhist lfd lv (pifds lfd b hw) (pprog lfd b hw) EW n))
     (FST (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) EW n))’
    by (irule ehrounds_kinv >> asm_rewrite_tac [] >> simp[]) >>
  qabbrev_tac ‘X = ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) EW n’ >> PairCases_on ‘X’ >>
  RULE_ASSUM_TAC (REWRITE_RULE [pairTheory.FST, pairTheory.SND]) >>
  qpat_assum ‘prel _ _ _ _ _ _’ (fn p => qpat_assum ‘gchinv _ _ _ _’ (fn g =>
    qpat_assum ‘kinv _ _ _’ (fn k => qpat_assum ‘X0.listening = _’ (fn l =>
      assume_tac (MATCH_MP cap_count (LIST_CONJ [p, g, k, l])))))) >>
  ‘LENGTH (FILTER (λc. ¬cpa c) X0.chans) = LENGTH (FILTER $¬ (ep_conn evs))’
    by (qpat_x_assum ‘MAP cpa _ = _’ (SUBST1_TAC o SYM) >>
        simp_tac (srw_ss()) [FILTER_MAP, combinTheory.o_DEF]) >>
  ‘F’ suffices_by REWRITE_TAC [] >>
  qpat_x_assum ‘LENGTH (FILTER (λc. _) _) = _’ (fn eq =>
    qpat_x_assum ‘LENGTH _.pc + 1 ≤ _’ (mp_tac o REWRITE_RULE [eq])) >>
  qpat_x_assum ‘LENGTH (FILTER $¬ _) ≤ _’ mp_tac >>
  qpat_x_assum ‘¬(2 * _ + 2 ≤ cbound)’ mp_tac >>
  REWRITE_TAC [cbound_def] >> simp_tac (srw_ss() ++ ARITH_ss) []
QED

(* ------------------------------------------------------------------------
   Rounds and positions of the run's trace
   ------------------------------------------------------------------------ *)

Theorem round_prefix:
  io = LAPPEND (fromList pre)
         (LFLATTEN (LGENLIST (λi. fromList (eround_evs lfd pol ifds m ws0 i)) NONE)) ∧
  (∀i. erounds lfd pol ifds m ws0 i ≠ NONE) ∧
  erounds lfd pol ifds m ws0 n = SOME (h, ws, EV, logs) ⇒
  LPREFIX (fromList (pre ++ EV)) io
Proof
  strip_tac >>
  ‘EV = FLAT (GENLIST (eround_evs lfd pol ifds m ws0) n)’
    by (mp_tac erounds_evs_genlist >> impl_tac >- first_assum ACCEPT_TAC >>
        disch_then (qspecl_then [‘n’, ‘h’, ‘ws’, ‘EV’, ‘logs’] mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  qspecl_then [‘eround_evs lfd pol ifds m ws0’, ‘n’] mp_tac
    (Q.GENL [‘f’, ‘n’] rounds_LPREFIX) >>
  qpat_x_assum ‘EV = _’ (SUBST1_TAC o SYM) >>
  simp[LPREFIX_APPEND] >> strip_tac >>
  qpat_x_assum ‘io = _’ SUBST1_TAC >> qpat_x_assum ‘LFLATTEN _ = _’ SUBST1_TAC >>
  qexists_tac ‘ll’ >> simp[GSYM LAPPEND_fromList, LAPPEND_ASSOC]
QED

Theorem round_evs_mono:
  (∀i. erounds lfd pol ifds m ws0 i ≠ NONE) ∧
  erounds lfd pol ifds m ws0 n1 = SOME (h1, ws1, E1, logs1) ∧
  erounds lfd pol ifds m ws0 n2 = SOME (h2, ws2, E2, logs2) ∧ n1 ≤ n2 ⇒
  ∃l. E2 = E1 ++ l
Proof
  strip_tac >>
  drule erounds_evs_genlist >> strip_tac >>
  first_assum (qspecl_then [‘n1’, ‘h1’, ‘ws1’, ‘E1’, ‘logs1’] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> disch_then SUBST1_TAC >>
  first_assum (qspecl_then [‘n2’, ‘h2’, ‘ws2’, ‘E2’, ‘logs2’] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> disch_then SUBST1_TAC >>
  qspecl_then [‘n1’, ‘n2’, ‘[]’, ‘eround_evs lfd pol ifds m ws0’] mp_tac
    (Q.GENL [‘i’, ‘n’, ‘pre’, ‘f’] e1TraceRoundTheory.rounds_prefix_mono) >>
  simp[IS_PREFIX_APPEND]
QED

(* Episode i of a round prefix is at position LENGTH pre + i of the trace *)
Theorem round_ep_pos:
  LPREFIX (fromList (pre ++ EV)) io ∧ EVERY (λe. ev_new e = NONE) pre ∧
  i < LENGTH EV ∧ ev_new (EL i EV) ≠ NONE ⇒
  io_ep_at io (LENGTH pre + i) ∧ LENGTH pre + i < LENGTH (pre ++ EV) ∧
  io_ep_idx io (LENGTH pre + i) = LENGTH (ep_conn (TAKE i EV))
Proof
  strip_tac >> drule LPREFIX_io >> strip_tac >> rpt conj_tac
  >- (REWRITE_TAC [io_ep_at_def] >> qexists_tac ‘EL i EV’ >> asm_rewrite_tac [] >>
      qpat_x_assum ‘∀p. p < _ ⇒ LNTH _ _ = _’ (qspec_then ‘LENGTH pre + i’ mp_tac) >>
      simp[EL_APPEND2])
  >- simp[] >>
  REWRITE_TAC [io_ep_idx_def] >>
  qpat_x_assum ‘∀p. p ≤ _ ⇒ LTAKE _ _ = _’ (qspec_then ‘LENGTH pre + i’ mp_tac) >>
  impl_tac >- simp[] >> disch_then SUBST1_TAC >>
  ‘TAKE (LENGTH pre + i) (pre ++ EV) = pre ++ TAKE i EV’
    by simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG] >>
  pop_assum SUBST1_TAC >>
  REWRITE_TAC [optionTheory.option_case_def, ep_fds_conn_LENGTH] >> BETA_TAC >>
  qpat_x_assum ‘EVERY _ pre’ (fn th => REWRITE_TAC [MATCH_MP ep_conn_nonew th])
QED

(* Distinct episode positions have distinct episode numbers *)
Theorem io_ep_idx_lt:
  q1 < q2 ∧ io_ep_at io q1 ∧ io_ep_at io q2 ⇒ io_ep_idx io q1 < io_ep_idx io q2
Proof
  REWRITE_TAC [io_ep_at_def] >> strip_tac >>
  qpat_x_assum ‘LNTH q2 io = _’ (strip_assume_tac o MATCH_MP LNTH_prefix) >>
  drule LPREFIX_io >> strip_tac >>
  ‘LNTH q1 io = SOME (EL q1 l)’ by (first_x_assum irule >> decide_tac) >>
  ‘ev_new (EL q1 l) ≠ NONE’ by fs[] >>
  REWRITE_TAC [io_ep_idx_def] >>
  ‘LTAKE q1 io = SOME (TAKE q1 l) ∧ LTAKE q2 io = SOME (TAKE q2 l)’
    by (conj_tac >> first_x_assum irule >> decide_tac) >>
  asm_rewrite_tac [] >> simp_tac (srw_ss()) [ep_fds_conn_LENGTH] >>
  irule ep_conn_TAKE_lt >> simp[]
QED

Theorem io_ep_idx_inj:
  io_ep_at io q1 ∧ io_ep_at io q2 ∧ io_ep_idx io q1 = io_ep_idx io q2 ⇒ q1 = q2
Proof
  strip_tac >> CCONTR_TAC >>
  ‘q1 < q2 ∨ q2 < q1’ by decide_tac
  >- (‘io_ep_idx io q1 < io_ep_idx io q2’ by (irule io_ep_idx_lt >> simp[]) >> fs[]) >>
  ‘io_ep_idx io q2 < io_ep_idx io q1’ by (irule io_ep_idx_lt >> simp[]) >> fs[]
QED

(* ------------------------------------------------------------------------
   Channels' handles: bound once, to distinct channels
   ------------------------------------------------------------------------ *)

Theorem proxy_gchinv:
  proxy_world lfd a W0 ⇒
  gchinv lfd (ehbinds lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n)
    (hl_pairs (pprog lfd b hw) (ehhist lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n))
    (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n)
Proof
  strip_tac >> qpat_assum ‘proxy_world _ _ _’ (strip_assume_tac o REWRITE_RULE [proxy_world_def]) >>
  irule ehrounds_gchinv >> asm_rewrite_tac [] >> simp[] >>
  gen_tac >> irule proxy_ehacts >> qexists_tac ‘a’ >> first_assum ACCEPT_TAC
QED

Theorem proxy_kinv:
  proxy_world lfd a W0 ⇒
  kinv (ehbinds lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n)
    (hl_pairs (pprog lfd b hw) (ehhist lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n))
    (FST (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n))
Proof
  strip_tac >> qpat_assum ‘proxy_world _ _ _’ (strip_assume_tac o REWRITE_RULE [proxy_world_def]) >>
  irule ehrounds_kinv >> asm_rewrite_tac [] >> simp[] >>
  gen_tac >> irule proxy_ehacts >> qexists_tac ‘a’ >> first_assum ACCEPT_TAC
QED

Theorem bind_hdl_unique:
  ALOOKUP (ehbinds lfd lv ifds m W0 n1) j = SOME h1 ∧
  ALOOKUP (ehbinds lfd lv ifds m W0 n2) j = SOME h2 ⇒ h1 = h2
Proof
  strip_tac >>
  ‘ALOOKUP (ehbinds lfd lv ifds m W0 (n1 + n2)) j = SOME h1 ∧
   ALOOKUP (ehbinds lfd lv ifds m W0 (n1 + n2)) j = SOME h2’
    by (conj_tac >> irule ehbinds_lookup_mono >> simp[] >| [qexists_tac ‘n1’, qexists_tac ‘n2’] >>
        simp[]) >>
  fs[]
QED

Theorem bind_chan_unique:
  proxy_world lfd a W0 ∧
  ALOOKUP (ehbinds lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n1) j1 = SOME c ∧
  ALOOKUP (ehbinds lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n2) j2 = SOME c ⇒ j1 = j2
Proof
  strip_tac >>
  ‘ALOOKUP (ehbinds lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 (n1 + n2)) j1 = SOME c ∧
   ALOOKUP (ehbinds lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 (n1 + n2)) j2 = SOME c’
    by (conj_tac >> irule ehbinds_lookup_mono >> simp[] >| [qexists_tac ‘n1’, qexists_tac ‘n2’] >>
        simp[]) >>
  drule proxy_gchinv >>
  disch_then (qspecl_then [‘n1 + n2’, ‘lv’, ‘hw’, ‘b’] mp_tac) >>
  Cases_on ‘ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 (n1 + n2)’ >>
  REWRITE_TAC [gchinv_def] >> strip_tac >>
  ‘MEM (j1, c) (ehbinds lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 (n1 + n2)) ∧
   MEM (j2, c) (ehbinds lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 (n1 + n2))’
    by (conj_tac >> irule alistTheory.ALOOKUP_MEM >> first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘ALL_DISTINCT (MAP SND _)’ mp_tac >> qpat_x_assum ‘MEM (j1, c) _’ mp_tac >>
  qpat_x_assum ‘MEM (j2, c) _’ mp_tac >> rpt (pop_assum kall_tac) >> metis_tac[bind_inj]
QED

Theorem proxy_chan_hdl_intro:
  ALOOKUP (ehbinds (plfd k) (proxy_lv b hw k w4) (pifds_k b hw k) (pprog_k b hw k)
                   (proxy_pew a b hw k w4) n) j = SOME hd ⇒
  proxy_chan_hdl a b hw k w4 j = SOME hd
Proof
  strip_tac >> REWRITE_TAC [proxy_chan_hdl_def] >> DEEP_INTRO_TAC some_intro >> conj_tac
  >- (rpt strip_tac >> AP_TERM_TAC >> irule (INST_TYPE [alpha |-> “:unit option”] bind_hdl_unique) >>
      qexistsl_tac [‘proxy_pew a b hw k w4’, ‘pifds_k b hw k’, ‘j’, ‘plfd k’, ‘proxy_lv b hw k w4’,
                    ‘pprog_k b hw k’, ‘n'’, ‘n’] >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qspec_then ‘hd’ mp_tac) >> simp[] >> qexists_tac ‘n’ >> first_assum ACCEPT_TAC
QED

Theorem proxy_chan_hdl_elim:
  proxy_chan_hdl a b hw k w4 j = SOME hd ⇒
  ∃n. ALOOKUP (ehbinds (plfd k) (proxy_lv b hw k w4) (pifds_k b hw k) (pprog_k b hw k)
                       (proxy_pew a b hw k w4) n) j = SOME hd
Proof
  REWRITE_TAC [proxy_chan_hdl_def] >> DEEP_INTRO_TAC some_intro >> simp[]
QED

(* The pairing by position, from the handles *)
Theorem proxy_pr_SOME:
  io_ep_at io p ∧ proxy_chan_hdl a b hw k w4 (io_ep_idx io p) = SOME hd ∧
  ppair (plfd k) b hw (proxy_lv b hw k w4) (proxy_pew a b hw k w4) hd = SOME c ∧
  io_ep_at io q ∧ proxy_chan_hdl a b hw k w4 (io_ep_idx io q) = SOME c ⇒
  proxy_pr a b hw k w4 io p = SOME q
Proof
  strip_tac >> asm_rewrite_tac [proxy_pr_def] >> simp_tac (srw_ss()) [] >> asm_rewrite_tac [] >>
  simp_tac (srw_ss()) [] >>
  DEEP_INTRO_TAC some_intro >> conj_tac
  >- (rpt strip_tac >> AP_TERM_TAC >> irule io_ep_idx_inj >> qexists_tac ‘io’ >>
      asm_rewrite_tac [] >>
      ‘proxy_world (plfd k) a (proxy_pew a b hw k w4)’
        by REWRITE_TAC [proxy_pew_def, pew_proxy_world] >>
      qpat_x_assum ‘proxy_chan_hdl _ _ _ _ _ (io_ep_idx io q) = _’
        (strip_assume_tac o MATCH_MP proxy_chan_hdl_elim) >>
      qpat_x_assum ‘proxy_chan_hdl _ _ _ _ _ (io_ep_idx io x) = _’
        (strip_assume_tac o MATCH_MP proxy_chan_hdl_elim) >>
      irule bind_chan_unique >> metis_tac[]) >>
  disch_then (qspec_then ‘q’ mp_tac) >> asm_rewrite_tac []
QED

Theorem proxy_round_prefix:
  (∀n. erounds (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4, einit) n ≠ NONE) ∧
  erounds (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4, einit) n = SOME (h, ws, EV, logs) ⇒
  ∀pre. LPREFIX (fromList (pre ++ EV)) (proxy_run_io b hw k w4 pre)
Proof
  rpt strip_tac >> irule (INST_TYPE [alpha |-> “:unit option”] round_prefix) >>
  qexistsl_tac [‘h’, ‘pifds_k b hw k’, ‘plfd k’, ‘logs’, ‘pprog_k b hw k’, ‘n’, ‘pol_never’, ‘ws’,
                ‘(w4, einit)’] >>
  REWRITE_TAC [proxy_run_io_def] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem proxy_roles:
  l0_rely w4 ∧ honestL0WorldProps$fds_lt w4 ∧ MEM (plfd k) (l0_used w4) ∧ MEM 0w (l0_used w4) ∧
  (∀n. erounds (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4, einit) n ≠ NONE) ∧
  erounds (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4, einit) n = SOME (h, ws, EV, logs) ⇒
  MAP cpa (FST (ehst (plfd k) (proxy_lv b hw k w4) (pifds_k b hw k) (pprog_k b hw k)
                     (proxy_pew a b hw k w4) n)).chans = ep_conn EV
Proof
  strip_tac >> REWRITE_TAC [proxy_lv_def, proxy_pew_def] >>
  ‘∀n. SND (ecm (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) w4 n) + 1 < dimword (:64)’
    by (irule proxy_ecm_bound >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all e1_roles >> disch_then (qspecl_then [‘[]’, ‘a’] ACCEPT_TAC)
QED

(* A connect handle of the history is the handle of an episode of the run *)
Theorem proxy_backend_pos:
  l0_rely w4 ∧ honestL0WorldProps$fds_lt w4 ∧ MEM (plfd k) (l0_used w4) ∧ MEM 0w (l0_used w4) ∧
  EVERY (λe. ev_new e = NONE) pre ∧
  (∀n. erounds (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4, einit) n ≠ NONE) ∧
  MEM c (hl_conn_handles (hl_pairs (pprog_k b hw k)
           (ehhist (plfd k) (proxy_lv b hw k w4) (pifds_k b hw k) (pprog_k b hw k)
                   (proxy_pew a b hw k w4) n))) ⇒
  ∃evs' q. LPREFIX (fromList evs') (proxy_run_io b hw k w4 pre) ∧ q < LENGTH evs' ∧
           io_ep_at (proxy_run_io b hw k w4 pre) q ∧
           proxy_chan_hdl a b hw k w4 (io_ep_idx (proxy_run_io b hw k w4 pre) q) = SOME c
Proof
  strip_tac >>
  ‘proxy_world (plfd k) a (proxy_pew a b hw k w4)’ by REWRITE_TAC [proxy_pew_def, pew_proxy_world] >>
  drule proxy_kinv >> disch_then (qspecl_then [‘n’, ‘proxy_lv b hw k w4’, ‘hw’, ‘b’] mp_tac) >>
  REWRITE_TAC [kinv_def] >> strip_tac >>
  ‘MEM c (MAP SND (ehbinds (plfd k) (proxy_lv b hw k w4) (pifds_k b hw k) (pprog_k b hw k)
                           (proxy_pew a b hw k w4) n))’
    by (qpat_x_assum ‘∀hd. _ ∨ _ ⇒ _’ irule >> disj1_tac >> first_assum ACCEPT_TAC) >>
  pop_assum (strip_assume_tac o REWRITE_RULE [MEM_MAP]) >> PairCases_on ‘y’ >>
  qpat_x_assum ‘c = SND _’ (SUBST_ALL_TAC o REWRITE_RULE [pairTheory.SND]) >>
  rename1 ‘MEM (j', c) _’ >>
  Cases_on ‘erounds (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4, einit) n’
  >- (qpat_x_assum ‘∀n. erounds _ _ _ _ _ n ≠ NONE’ (qspec_then ‘n’ mp_tac) >> asm_rewrite_tac []) >>
  rename1 ‘_ = SOME r0’ >> PairCases_on ‘r0’ >>
  ‘MAP cpa (FST (ehst (plfd k) (proxy_lv b hw k w4) (pifds_k b hw k) (pprog_k b hw k)
                     (proxy_pew a b hw k w4) n)).chans = ep_conn r03’
    by (irule proxy_roles >> asm_rewrite_tac [] >>
        qexistsl_tac [‘r00’, ‘r04’, ‘(r01, r02)’] >> REWRITE_TAC []) >>
  drule proxy_gchinv >> disch_then (qspecl_then [‘n’, ‘proxy_lv b hw k w4’, ‘hw’, ‘b’] mp_tac) >>
  Cases_on ‘ehst (plfd k) (proxy_lv b hw k w4) (pifds_k b hw k) (pprog_k b hw k)
                 (proxy_pew a b hw k w4) n’ >>
  REWRITE_TAC [gchinv_def] >> strip_tac >>
  ‘j' < LENGTH (ep_conn r03)’
    by (qpat_x_assum ‘MAP cpa _ = ep_conn r03’ (SUBST1_TAC o SYM) >>
        REWRITE_TAC [LENGTH_MAP, pairTheory.FST] >>
        qpat_x_assum ‘∀j hd. MEM (j, hd) _ ⇒ j < _ ∧ _’ (drule_then strip_assume_tac) >>
        first_assum ACCEPT_TAC) >>
  ‘ALOOKUP (ehbinds (plfd k) (proxy_lv b hw k w4) (pifds_k b hw k) (pprog_k b hw k)
                    (proxy_pew a b hw k w4) n) j' = SOME c’
    by (irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM >> conj_tac >> first_assum ACCEPT_TAC) >>
  drule ep_conn_from >> strip_tac >>
  qpat_assum ‘erounds _ _ _ _ _ n = _’ (fn th => qpat_assum ‘∀n. erounds _ _ _ _ _ n ≠ NONE’
    (fn tt => assume_tac (Q.SPEC ‘pre’ (MATCH_MP proxy_round_prefix (CONJ tt th))))) >>
  qspecl_then [‘pre’, ‘r03’, ‘proxy_run_io b hw k w4 pre’, ‘i’] mp_tac
    (Q.GENL [‘pre’, ‘EV’, ‘io’, ‘i’] round_ep_pos) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qexistsl_tac [‘pre ++ r03’, ‘LENGTH pre + i’] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  asm_rewrite_tac [] >> irule proxy_chan_hdl_intro >> qexists_tac ‘n’ >> asm_rewrite_tac []
QED

(* Socketless connects without bound in the history are without bound in
   the run's trace *)
Theorem proxy_nosock_lift:
  l0_rely w4 ∧ honestL0WorldProps$fds_lt w4 ∧ MEM (plfd k) (l0_used w4) ∧
  (∀n. erounds (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4, einit) n ≠ NONE) ∧
  (∀k'. ∃n'. k' ≤ hl_nosock (hl_pairs (pprog_k b hw k)
                (ehhist (plfd k) (proxy_lv b hw k w4) (pifds_k b hw k) (pprog_k b hw k)
                        (proxy_pew a b hw k w4) n'))) ⇒
  ∀k'. ∃evs'. LPREFIX (fromList evs') (proxy_run_io b hw k w4 pre) ∧
              k' ≤ LENGTH (FILTER l0_nosock evs')
Proof
  strip_tac >> gen_tac >>
  qpat_x_assum ‘∀k'. ∃n'. _’ (qspec_then ‘k'’ strip_assume_tac) >>
  ‘∀n. SND (ecm (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) w4 n) + 1 < dimword (:64)’
    by (irule proxy_ecm_bound >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  Cases_on ‘erounds (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4, einit) n'’
  >- (qpat_x_assum ‘∀n. erounds _ _ _ _ _ n ≠ NONE’ (qspec_then ‘n'’ mp_tac) >> asm_rewrite_tac []) >>
  rename1 ‘_ = SOME r0’ >> PairCases_on ‘r0’ >>
  qpat_x_assum ‘k' ≤ _’ mp_tac >> REWRITE_TAC [proxy_lv_def, proxy_pew_def] >> strip_tac >>
  drule_all ehl_nosock_l0 >> strip_tac >>
  qpat_assum ‘erounds _ _ _ _ _ n' = _’ (fn th => qpat_assum ‘∀n. erounds _ _ _ _ _ n ≠ NONE’
    (fn tt => assume_tac (Q.SPEC ‘pre’ (MATCH_MP proxy_round_prefix (CONJ tt th))))) >>
  qexists_tac ‘pre ++ r03’ >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum ‘∀calls a. _’ (qspecl_then [‘[]’, ‘a’] mp_tac) >>
  qpat_x_assum ‘k' ≤ _’ mp_tac >> REWRITE_TAC [FILTER_APPEND, LENGTH_APPEND] >>
  decide_tac
QED

(* A front's channel gets a handle, which the history accepted *)
Theorem proxy_front_hdl:
  l0_rely w4 ∧ honestL0WorldProps$fds_lt w4 ∧ MEM (plfd k) (l0_used w4) ∧ MEM 0w (l0_used w4) ∧
  EVERY (λe. ev_new e = NONE) pre ∧
  (∀n. erounds (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4, einit) n ≠ NONE) ∧
  (∀evs. LPREFIX (fromList evs) (proxy_run_io b hw k w4 pre) ⇒
         LENGTH (honestEchoL0Spec$l0_accepted evs) < 2 ** 62 + 1) ∧
  LPREFIX (fromList evs) (proxy_run_io b hw k w4 pre) ∧ p < LENGTH evs ∧
  ev_new (EL p evs) = SOME (f, INR l) ⇒
  ∃hd N. io_ep_at (proxy_run_io b hw k w4 pre) p ∧
         proxy_chan_hdl a b hw k w4 (io_ep_idx (proxy_run_io b hw k w4 pre) p) = SOME hd ∧
         MEM hd (hl_acc_handles (hl_pairs (pprog_k b hw k)
                   (ehhist (plfd k) (proxy_lv b hw k w4) (pifds_k b hw k) (pprog_k b hw k)
                           (proxy_pew a b hw k w4) N)))
Proof
  strip_tac >>
  ‘proxy_run_io b hw k w4 pre =
   LAPPEND (fromList pre) (LFLATTEN (LGENLIST (λi. fromList
     (eround_evs (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4, einit) i)) NONE))’
    by REWRITE_TAC [proxy_run_io_def] >>
  drule_all front_episode >> strip_tac >>
  qpat_x_assum ‘proxy_run_io _ _ _ _ _ = _’ kall_tac >>
  qabbrev_tac ‘j = io_ep_idx (proxy_run_io b hw k w4 pre) p’ >>
  ‘LENGTH (FILTER $¬ (ep_conn EV)) ≤ 2 ** 62’
    by (qpat_x_assum ‘∀evs. _ ⇒ LENGTH _ < _’ (qspec_then ‘pre ++ EV’ mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >>
        REWRITE_TAC [GSYM ep_conn_accepted] >>
        qpat_assum ‘EVERY _ pre’ (fn th => REWRITE_TAC [MATCH_MP ep_conn_nonew th]) >>
        decide_tac) >>
  drule_all front_bound >>
  disch_then (qspecl_then [‘[]’, ‘a’] (strip_assume_tac o
    REWRITE_RULE [GSYM proxy_lv_def, GSYM proxy_pew_def])) >>
  Cases_on ‘ALOOKUP (ehbinds (plfd k) (proxy_lv b hw k w4) (pifds_k b hw k) (pprog_k b hw k)
                             (proxy_pew a b hw k w4) n') j’
  >- (qpat_x_assum ‘ALOOKUP _ _ = NONE’ (mp_tac o REWRITE_RULE [alistTheory.ALOOKUP_NONE]) >>
      qpat_x_assum ‘MEM j _’ (fn th => REWRITE_TAC [th])) >>
  rename1 ‘_ = SOME hd’ >>
  qexistsl_tac [‘hd’, ‘n + n'’] >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (irule proxy_chan_hdl_intro >> qexists_tac ‘n'’ >> first_assum ACCEPT_TAC) >>
  ‘ALOOKUP (ehbinds (plfd k) (proxy_lv b hw k w4) (pifds_k b hw k) (pprog_k b hw k)
                    (proxy_pew a b hw k w4) (n + n')) j = SOME hd’
    by (irule ehbinds_lookup_mono >> qexists_tac ‘n'’ >> asm_rewrite_tac [] >> decide_tac) >>
  Cases_on ‘erounds (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4, einit) (n + n')’
  >- (qpat_x_assum ‘∀n. erounds _ _ _ _ _ n ≠ NONE’ (qspec_then ‘n + n'’ mp_tac) >>
      asm_rewrite_tac []) >>
  rename1 ‘_ = SOME r0’ >> PairCases_on ‘r0’ >>
  ‘∃l. r03 = EV ++ l’
    by (irule (INST_TYPE [alpha |-> “:unit option”] round_evs_mono) >>
        qexistsl_tac [‘h’, ‘r00’, ‘pifds_k b hw k’, ‘plfd k’, ‘logs’, ‘r04’, ‘pprog_k b hw k’,
                      ‘n’, ‘n + n'’, ‘pol_never’, ‘(w4, einit)’, ‘ws’, ‘(r01, r02)’] >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  ‘MAP cpa (FST (ehst (plfd k) (proxy_lv b hw k w4) (pifds_k b hw k) (pprog_k b hw k)
                     (proxy_pew a b hw k w4) (n + n'))).chans = ep_conn r03’
    by (irule proxy_roles >> asm_rewrite_tac [] >>
        qexistsl_tac [‘r00’, ‘r04’, ‘(r01, r02)’] >> REWRITE_TAC []) >>
  ‘proxy_world (plfd k) a (proxy_pew a b hw k w4)’ by REWRITE_TAC [proxy_pew_def, pew_proxy_world] >>
  drule proxy_kinv >> disch_then (qspecl_then [‘n + n'’, ‘proxy_lv b hw k w4’, ‘hw’, ‘b’] mp_tac) >>
  REWRITE_TAC [kinv_def] >> disch_then (qspecl_then [‘j’, ‘hd’] mp_tac o CONJUNCT1) >>
  impl_tac >- (irule alistTheory.ALOOKUP_MEM >> first_assum ACCEPT_TAC) >>
  disch_then (fn th => REWRITE_TAC [hl_acc_handles_acc_hdls, CONJUNCT2 th]) >>
  qabbrev_tac ‘cs = (FST (ehst (plfd k) (proxy_lv b hw k w4) (pifds_k b hw k) (pprog_k b hw k)
                              (proxy_pew a b hw k w4) (n + n'))).chans’ >>
  ‘j < LENGTH cs’
    by (‘LENGTH (MAP cpa cs) = LENGTH (ep_conn r03)’ by asm_rewrite_tac [] >>
        pop_assum mp_tac >> asm_rewrite_tac [ep_conn_APPEND, LENGTH_MAP, LENGTH_APPEND] >>
        decide_tac) >>
  ‘¬cpa (EL j cs)’
    by (‘cpa (EL j cs) = EL j (MAP cpa cs)’ by (irule (GSYM EL_MAP) >> first_assum ACCEPT_TAC) >>
        pop_assum SUBST1_TAC >> asm_rewrite_tac [ep_conn_APPEND] >>
        ‘EL j (ep_conn EV ++ ep_conn l') = EL j (ep_conn EV)’
          by (irule EL_APPEND1 >> first_assum ACCEPT_TAC) >>
        asm_rewrite_tac []) >>
  asm_rewrite_tac []
QED

(* The run and the live block's hypotheses *)
Definition proxy_live_hyps_def:
  proxy_live_hyps a b hw w0 pre w4 k ⇔
    a < 65536 ∧ b < 65536 ∧ proxy_start a w0 pre w4 k ∧
    (∀n. erounds (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4, einit) n ≠ NONE) ∧
    F1_io (proxy_run_io b hw k w4 pre) ∧ F2 w0 ∧ accepts_below (proxy_run_io b hw k w4 pre)
End

Definition proxy_live_run_def:
  proxy_live_run ⇔
    ∀a b hw w0 pre w4 k.
      proxy_live_hyps a b hw w0 pre w4 k ⇒
      proxy_live_l0 pf_sendwait (proxy_pr a b hw k w4 (proxy_run_io b hw k w4 pre)) w0
                    (proxy_run_io b hw k w4 pre)
End

Definition proxy_pairs_run_def:
  proxy_pairs_run ⇔
    ∀a b hw w0 pre w4 k.
      proxy_live_hyps a b hw w0 pre w4 k ∧ accepts_lt (2 ** 62 + 1) (proxy_run_io b hw k w4 pre) ⇒
      proxy_pairs_l0 pf_sendwait (proxy_pr a b hw k w4 (proxy_run_io b hw k w4 pre))
                     (proxy_run_io b hw k w4 pre)
End

Theorem proxy_pairs_run_thm:
  proxy_pairs_run
Proof
  REWRITE_TAC [proxy_pairs_run_def, proxy_live_hyps_def, proxy_pairs_l0_def, accepts_lt_def,
               is_front_def] >> rpt strip_tac >>
  drule proxy_start_facts >> strip_tac >> drule proxy_start_pre >> strip_tac >>
  ‘∃f l. ev_new (EL p evs) = SOME (f, INR l)’
    by (REWRITE_TAC [GSYM accepted_new_local] >> first_assum ACCEPT_TAC) >>
  drule_all proxy_front_hdl >> disch_then (qspec_then ‘a’ strip_assume_tac) >>
  ‘proxy_world (plfd k) a (proxy_pew a b hw k w4)’ by REWRITE_TAC [proxy_pew_def, pew_proxy_world] >>
  drule_all proxy_pairs_hl >> strip_tac
  >- (disj2_tac >> disj1_tac >> drule_all proxy_backend_pos >> strip_tac >>
      qexistsl_tac [‘evs'’, ‘q’] >> asm_rewrite_tac [] >>
      irule proxy_pr_SOME >> asm_rewrite_tac [] >> qexistsl_tac [‘c’, ‘hd’] >> asm_rewrite_tac []) >>
  disj2_tac >> disj2_tac >> irule proxy_nosock_lift >>
  rpt conj_tac >> TRY (qexists_tac ‘a’) >> first_assum ACCEPT_TAC
QED

(* ------------------------------------------------------------------------
   G3 (moonshot-live's backend cap): the run's connect episodes are at most
   2^62, one per pair at most (a pair's backend is set once), and the pairs
   are below cbound / 2
   ------------------------------------------------------------------------ *)

Theorem roles_conn_count:
  ∀evs lst. LENGTH (FILTER (λr. ∃p. r = Connected p) (ep_roles lst evs)) =
            LENGTH (FILTER I (ep_conn evs))
Proof
  Induct >> simp[ep_roles_def, ep_conn_def] >> rpt gen_tac >>
  Cases_on ‘ev_new h’ >> simp[] >> PairCases_on ‘x’ >> Cases_on ‘x1’ >> simp[]
QED

Theorem ep_conn_count_prefix:
  evs ≼ l ⇒ LENGTH (FILTER I (ep_conn evs)) ≤ LENGTH (FILTER I (ep_conn l))
Proof
  rw[IS_PREFIX_APPEND] >> simp[FILTER_APPEND]
QED

Theorem FILTER_I_MAP:
  ∀l. LENGTH (FILTER I (MAP f l)) = LENGTH (FILTER f l)
Proof
  Induct >> rw[]
QED

Theorem distinct_below:
  ALL_DISTINCT l ∧ EVERY (λx. x < N) l ⇒ LENGTH l ≤ N
Proof
  strip_tac >> ‘set l ⊆ count N’ by fs[SUBSET_DEF, EVERY_MEM] >>
  ‘CARD (set l) ≤ CARD (count N)’ by (irule CARD_SUBSET >> simp[]) >>
  ‘CARD (set l) = LENGTH l’ by simp[ALL_DISTINCT_CARD_LIST_TO_SET] >> fs[CARD_COUNT]
QED

(* The connect-born channels are bound to distinct pairs' backends *)
Theorem conn_cap_count:
  prel lfd st rdy ps (FST X) (SND X) ∧ gchinv lfd B ps X ∧ kinv B ps (FST X) ⇒
  LENGTH (FILTER cpa (FST X).chans) ≤ LENGTH st.pc
Proof
  PairCases_on ‘X’ >> REWRITE_TAC [FST, SND] >> strip_tac >>
  ‘∀j. j < LENGTH X0.chans ∧ cpa (EL j X0.chans) ⇒ MEM j (MAP FST B)’
    by (qpat_x_assum ‘kinv _ _ _’ mp_tac >> REWRITE_TAC [kinv_def] >> strip_tac >>
        first_assum ACCEPT_TAC) >>
  ‘∀j hd. MEM (j, hd) B ∧ cpa (EL j X0.chans) ⇒ MEM hd (hl_conn_handles ps)’
    by (qpat_x_assum ‘kinv _ _ _’ mp_tac >> REWRITE_TAC [kinv_def] >> strip_tac >>
        rpt strip_tac >>
        qpat_x_assum ‘∀j hd. MEM (j, hd) B ⇒ _’ (qspecl_then [‘j’, ‘hd’] mp_tac) >>
        asm_rewrite_tac [] >> strip_tac) >>
  ‘∀c. MEM c (hl_conn_handles ps) ⇒ ∃q. q < LENGTH st.pc ∧ (EL q st.pc).bh = SOME c’
    by (qpat_x_assum ‘prel _ _ _ _ _ _’ mp_tac >> REWRITE_TAC [prel_def] >> strip_tac >>
        gen_tac >> qpat_x_assum ‘∀c. MEM c (hl_conn_handles ps) ⇔ _’ (fn th => REWRITE_TAC [th]) >>
        strip_tac >> qpat_x_assum ‘MEM p st.pc’ (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
        qexists_tac ‘n’ >> rpt BasicProvers.VAR_EQ_TAC >> asm_rewrite_tac []) >>
  ‘ALL_DISTINCT (MAP SND B)’
    by (qpat_x_assum ‘gchinv _ _ _ _’ mp_tac >> REWRITE_TAC [gchinv_def] >> strip_tac >>
        first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘prel _ _ _ _ _ _’ kall_tac >> qpat_x_assum ‘gchinv _ _ _ _’ kall_tac >>
  qpat_x_assum ‘kinv _ _ _’ kall_tac >>
  qabbrev_tac ‘idx = FILTER (λi. cpa (EL i X0.chans)) (COUNT_LIST (LENGTH X0.chans))’ >>
  ‘LENGTH idx = LENGTH (FILTER cpa X0.chans)’ by simp[Abbr ‘idx’, FILTER_COUNT_LIST_LENGTH] >>
  pop_assum (SUBST1_TAC o SYM) >>
  ‘ALL_DISTINCT idx’ by simp[Abbr ‘idx’, FILTER_ALL_DISTINCT, all_distinct_count_list] >>
  ‘∀i. MEM i idx ⇔ i < LENGTH X0.chans ∧ cpa (EL i X0.chans)’
    by simp[Abbr ‘idx’, MEM_FILTER, MEM_COUNT_LIST, CONJ_COMM] >>
  ‘∀i. MEM i idx ⇒ ∃q. q < LENGTH st.pc ∧ ∃hd. MEM (i, hd) B ∧ (EL q st.pc).bh = SOME hd’
    by (gen_tac >> qpat_assum ‘∀i. MEM i idx ⇔ _’ (fn th => REWRITE_TAC [th]) >> strip_tac >>
        ‘MEM i (MAP FST B)’ by (first_x_assum irule >> asm_rewrite_tac []) >>
        pop_assum (strip_assume_tac o REWRITE_RULE [MEM_MAP]) >>
        PairCases_on ‘y’ >> fs[] >> rpt BasicProvers.VAR_EQ_TAC >>
        ‘MEM y1 (hl_conn_handles ps)’
          by (qpat_x_assum ‘∀j hd. MEM (j, hd) B ∧ _ ⇒ _’ (qspecl_then [‘i’, ‘y1’] mp_tac) >>
              asm_rewrite_tac []) >>
        qpat_x_assum ‘∀c. MEM c (hl_conn_handles ps) ⇒ _’ drule >> strip_tac >>
        qexists_tac ‘q’ >> asm_rewrite_tac [] >> qexists_tac ‘y1’ >> asm_rewrite_tac []) >>
  qabbrev_tac ‘g = λi. @q. q < LENGTH st.pc ∧ ∃hd. MEM (i, hd) B ∧ (EL q st.pc).bh = SOME hd’ >>
  ‘∀i. MEM i idx ⇒ g i < LENGTH st.pc ∧ ∃hd. MEM (i, hd) B ∧ (EL (g i) st.pc).bh = SOME hd’
    by (gen_tac >> strip_tac >> qunabbrev_tac ‘g’ >> BETA_TAC >> SELECT_ELIM_TAC >>
        conj_tac >- (first_x_assum irule >> first_assum ACCEPT_TAC) >>
        gen_tac >> strip_tac >> asm_rewrite_tac [] >> qexists_tac ‘hd’ >> asm_rewrite_tac []) >>
  ‘LENGTH idx = LENGTH (MAP g idx)’ by REWRITE_TAC [LENGTH_MAP] >> pop_assum SUBST1_TAC >>
  ‘EVERY (λx. x < LENGTH st.pc) (MAP g idx)’
    by (REWRITE_TAC [EVERY_MAP, EVERY_MEM] >> BETA_TAC >> rpt strip_tac >>
        qpat_assum ‘∀i. MEM i idx ⇒ g i < _ ∧ _’ drule >> strip_tac) >>
  ‘ALL_DISTINCT (MAP g idx)’ suffices_by
    (strip_tac >> irule distinct_below >> conj_tac >> first_assum ACCEPT_TAC) >>
  irule ALL_DISTINCT_MAP_INJ >> conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  rpt strip_tac >>
  qpat_assum ‘∀i. MEM i idx ⇒ g i < _ ∧ _’ (qspec_then ‘x’ mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qpat_assum ‘∀i. MEM i idx ⇒ g i < _ ∧ _’ (qspec_then ‘y’ mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  ‘hd = hd'’ by (qpat_x_assum ‘(EL (g x) st.pc).bh = SOME hd’ mp_tac >>
                 qpat_x_assum ‘g x = g y’ (fn th => REWRITE_TAC [th]) >>
                 qpat_x_assum ‘(EL (g y) st.pc).bh = SOME hd'’ (fn th => REWRITE_TAC [th]) >>
                 simp[]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  qspecl_then [‘B’, ‘y’, ‘hd’, ‘x’] mp_tac (Q.GENL [‘B’, ‘j’, ‘h’, ‘j'’] bind_inj) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]
QED

Definition proxy_conn_cap_run_def:
  proxy_conn_cap_run ⇔
    ∀a b hw w0 pre w4 k.
      a < 65536 ∧ b < 65536 ∧ proxy_start a w0 pre w4 k ∧
      (∀n. erounds (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4, einit) n ≠ NONE) ⇒
      ∀evs. LPREFIX (fromList evs) (proxy_run_io b hw k w4 pre) ⇒
            LENGTH (FILTER (λr. ∃p. r = Connected p) (ep_roles [] evs)) ≤ 2 ** 62
End

Theorem proxy_conn_cap_run_thm:
  proxy_conn_cap_run
Proof
  REWRITE_TAC [proxy_conn_cap_run_def] >> rpt strip_tac >>
  drule proxy_start_facts >> strip_tac >> drule proxy_start_pre >> strip_tac >>
  REWRITE_TAC [roles_conn_count] >>
  qpat_x_assum ‘LPREFIX _ _’ (mp_tac o REWRITE_RULE [proxy_run_io_def]) >>
  disch_then (strip_assume_tac o MATCH_MP e1_lprefix_rounds) >>
  Cases_on ‘erounds (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4, einit) n’
  >- (qpat_x_assum ‘∀n. _ ≠ NONE’ (qspec_then ‘n’ mp_tac) >> asm_rewrite_tac []) >>
  rename1 ‘_ = SOME r0’ >> PairCases_on ‘r0’ >>
  ‘r03 = FLAT (GENLIST (eround_evs (plfd k) pol_never (pifds_k b hw k) (pprog_k b hw k) (w4, einit)) n)’
    by (qpat_assum ‘∀n. _ ≠ NONE’
          (mp_tac o MATCH_MP (INST_TYPE [alpha |-> “:unit option”] erounds_evs_genlist)) >>
        disch_then (qspecl_then [‘n’, ‘r00’, ‘(r01, r02)’, ‘r03’, ‘r04’] mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  qpat_x_assum ‘r03 = _’ (SUBST_ALL_TAC o SYM) >>
  drule ep_conn_count_prefix >>
  qpat_x_assum ‘EVERY _ pre’ (fn th => REWRITE_TAC [MATCH_MP ep_conn_nonew th]) >>
  strip_tac >> irule LESS_EQ_TRANS >> first_assum (irule_at Any) >>
  ‘MAP cpa (FST (ehst (plfd k) (proxy_lv b hw k w4) (pifds_k b hw k) (pprog_k b hw k)
                     (proxy_pew a b hw k w4) n)).chans = ep_conn r03’
    by (irule proxy_roles >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        qexistsl_tac [‘r00’, ‘r04’, ‘(r01, r02)’] >> first_assum ACCEPT_TAC) >>
  pop_assum (SUBST1_TAC o SYM) >> REWRITE_TAC [FILTER_I_MAP] >>
  ‘proxy_world (plfd k) a (proxy_pew a b hw k w4)’ by REWRITE_TAC [proxy_pew_def, pew_proxy_world] >>
  drule PS_prel_n >> disch_then (qspecl_then [‘n’, ‘proxy_lv b hw k w4’, ‘hw’, ‘b’] assume_tac) >>
  drule proxy_gchinv >> disch_then (qspecl_then [‘n’, ‘proxy_lv b hw k w4’, ‘hw’, ‘b’] assume_tac) >>
  drule proxy_kinv >> disch_then (qspecl_then [‘n’, ‘proxy_lv b hw k w4’, ‘hw’, ‘b’] assume_tac) >>
  drule_all conn_cap_count >> strip_tac >>
  irule LESS_EQ_TRANS >> first_assum (irule_at Any) >>
  qpat_x_assum ‘prel _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [prel_def]) >>
  fs[cbound_def]
QED

Definition conn_live_run_def:
  conn_live_run ⇔
    ∀a b hw w0 pre w4 k.
      proxy_live_hyps a b hw w0 pre w4 k ∧ accepts_lt (2 ** 62 + 1) (proxy_run_io b hw k w4 pre) ⇒
      conn_live_l0 w0 (proxy_run_io b hw k w4 pre)
End
