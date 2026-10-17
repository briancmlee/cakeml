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
  proxyL0Run proxyL0Stmts honestL1BStmts honestL1PFModel e1DriverLoop
  moonshotProxyLive moonshotProxySafe moonshotProxyRel proxyHLStmts e1TraceAccBind e1TraceKind
  e1TraceRole e1TraceChan moonshotProxy moonshotClientSpec endpointHLModel endpointWorld
  honestEchoL0Spec l0sysEpisodes
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

Definition conn_live_run_def:
  conn_live_run ⇔
    ∀a b hw w0 pre w4 k.
      proxy_live_hyps a b hw w0 pre w4 k ∧ accepts_lt (2 ** 62 + 1) (proxy_run_io b hw k w4 pre) ⇒
      conn_live_l0 w0 (proxy_run_io b hw k w4 pre)
End
