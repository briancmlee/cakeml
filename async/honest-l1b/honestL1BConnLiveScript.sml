(*
  L3-09 (S3): raw liveness for connections transfers from the PF trace to
  the blocking trace.  A connection queued at a blocking prefix is queued
  at its PF image, so the PF trace accepts it, sees it broken, or sees
  accepts fail infinitely often; each of these shows on some blocking
  prefix (non-poll events and channels agree), except a break seen only
  while the blocking run sleeps.  But the run cannot sleep with a
  connection queued: the listener is polled for input in every idle round
  (S1, pf_idle), and its PF image's empty polls would then be followed by
  an accept (honestL1PFConnRun.run_lfd).  So the connection left the queue
  before the sleep, at an event that resolves it (qexit_trace).

  MAIN: conn_live_transfer.
*)
Theory honestL1BConnLive
Ancestors
  honestL1BConn honestL1BFaith honestL1BLive honestL1BDrains honestL1BTransfer
  honestL1BChan honestL1BCorr honestL1BObs honestL1BRuns honestL1BSim honestL1BRefine
  honestL1BPoll honestL1BModel honestL1BStmts honestL0Reindex
  honestL1PFConnRun honestL1PFConn honestL1PFLive honestL1PFRefine honestL1PFRound
  honestL1PFModel honestL1Inv honestL1Model honestEchoL0Spec honestL0WorldInv honestL0Part
  honestL0World honestL0 llist
Libs
  preamble

(* ------------------------------------------------------------------------
   Blocking prefixes are faithful
   ------------------------------------------------------------------------ *)

Theorem bpre_faithful:
  l0_rely w0 ∧ bpre lfd hw ifds bz m (w0, ps0) bp ⇒ faithful w0 bp
Proof
  strip_tac >> drule bpre_BRun >> strip_tac >> PairCases_on ‘ws’ >>
  drule fplays_brounds >> rw[fplays_def] >>
  fs[IS_PREFIX_APPEND] >> metis_tac[faithful_prefix]
QED

Theorem faithful_world_inv:
  (∀n conf b out u u'. P u ∧ l0_ffi_fn n conf b u = SOME (FFIreturn out u') ∧
                       MEM n l1_names ⇒ P u') ∧
  faithful w0 (a ++ b) ∧ P w0 ∧ world_at w0 a = SOME w ⇒ P w
Proof
  rw[world_at_def, l0_replay_def] >> drule faithful_inv >>
  disch_then irule >> metis_tac[faithful_prefix]
QED

Theorem lone_qof:
  lone l0 w ∧ MEM (l, p, q) w.listeners ⇒ l = l0 ∧ qof w l = q
Proof
  rw[lone_def, qof_def] >> Cases_on ‘w.listeners’ >> gvs[] >>
  PairCases_on ‘h’ >> gvs[]
QED

(* ------------------------------------------------------------------------
   What the PF trace shows, a blocking prefix shows
   ------------------------------------------------------------------------ *)

Definition acc_fail_def:
  acc_fail ev ⇔ ∃conf bs e x. ev = IO_event (ExtCall «sys_accept») conf bs ∧
                              l0_ev_res bs = SOME (Fail e x)
End

Theorem accepts_fail_ioinf:
  accepts_fail_io io ⇔ ioinf acc_fail io
Proof
  rw[accepts_fail_io_def, ioinf_def, acc_fail_def] >> metis_tac[]
QED

Theorem cnt_nopoll:
  (∀ev. Q ev ⇒ ¬is_poll ev) ⇒ cnt Q (nopoll l) = cnt Q l
Proof
  strip_tac >> Induct_on ‘l’ >> rw[cnt_def, nopoll_def] >>
  gvs[cnt_def, nopoll_def] >> metis_tac[]
QED

Theorem accepts_fail_transfer:
  bquiet m ifds bz ∧ l0_rely w0 ∧ (∀n. brounds lfd hw ifds bz m (w0, ps0) n ≠ NONE) ∧
  btrace lfd hw ifds bz m w0 ps0 io_b ∧ ptrace lfd hw ifds bz m w0 ps0 io_p ∧
  accepts_fail_io io_p ⇒ accepts_fail_io io_b
Proof
  rw[accepts_fail_ioinf, ioinf_cnt] >> first_x_assum (qspec_then ‘n’ strip_assume_tac) >>
  ‘ppre lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0, ps0) l’
    by metis_tac[ptrace_def] >>
  drule_all p2b_nopoll >> strip_tac >> qexists_tac ‘bp’ >>
  ‘∀ev. acc_fail ev ⇒ ¬is_poll ev’ by (rw[acc_fail_def] >> simp[is_poll_def]) >>
  ‘cnt acc_fail bp = cnt acc_fail l’ by metis_tac[cnt_nopoll] >>
  simp[] >> metis_tac[btrace_def]
QED

Theorem open_fds_deliver[local]:
  (l0_deliver w a).open_fds = w.open_fds
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >> simp[upd_lchan_def]
QED

Theorem open_fds_ticks:
  ∀k w. (l0_ticks nm k w).open_fds = w.open_fds
Proof
  ‘∀as w. (FOLDL l0_deliver w as).open_fds = w.open_fds’
    by (Induct >> simp[open_fds_deliver]) >>
  Induct >> simp[l0_ticks_def, l0_tick_def]
QED

Theorem accepted_transfer:
  bquiet m ifds bz ∧ l0_rely w0 ∧ (∀n. brounds lfd hw ifds bz m (w0, ps0) n ≠ NONE) ∧
  btrace lfd hw ifds bz m w0 ps0 io_b ∧ ptrace lfd hw ifds bz m w0 ps0 io_p ∧
  LPREFIX (fromList pp) io_p ∧
  world_at (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) pp = SOME w' ∧
  ALOOKUP w'.open_fds f = SOME j0 ∧ MEM f (l0_accepted pp) ⇒
  ∃bp wb. LPREFIX (fromList bp) io_b ∧ world_at w0 bp = SOME wb ∧
          ALOOKUP wb.open_fds f = SOME j0 ∧ MEM f (l0_accepted bp)
Proof
  strip_tac >>
  ‘ppre lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0, ps0) pp’
    by metis_tac[ptrace_def] >>
  drule_all p2b >> strip_tac
  >- (qpat_x_assum ‘palign _ _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE[palign_def]) >>
      ‘w' = lift (btr lfd hw ifds bz m (w0, ps0)) hp wb’ by metis_tac[optionTheory.SOME_11] >>
      qexistsl_tac [‘bp’, ‘wb’] >> rpt conj_tac
      >- metis_tac[btrace_def]
      >- first_assum ACCEPT_TAC
      >- (qpat_x_assum ‘ALOOKUP _ _ = SOME j0’ mp_tac >> asm_rewrite_tac[lift_fields])
      >> metis_tac[nopoll_accepted])
  >> qpat_x_assum ‘pmid _ _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE[pmid_def]) >>
  ‘w' = lift (btr lfd hw ifds bz m (w0, ps0)) hp (l0_ticks «sys_poll» i wb)’
    by metis_tac[optionTheory.SOME_11] >>
  ‘bpre lfd hw ifds bz m (w0, ps0) bp’ by (irule bpre_round >> metis_tac[IS_PREFIX_REFL]) >>
  ‘l0_accepted bp = l0_accepted pp’ by metis_tac[nopoll_accepted] >>
  qexistsl_tac [‘bp’, ‘wb’] >>
  (conj_tac
   >- (qpat_assum ‘btrace _ _ _ _ _ _ _ _’ (fn th => REWRITE_TAC[REWRITE_RULE[btrace_def] th]) >>
       first_assum ACCEPT_TAC) >>
   conj_tac >- first_assum ACCEPT_TAC >>
   conj_tac
   >- (qpat_x_assum ‘ALOOKUP _ _ = SOME j0’ mp_tac >>
       asm_rewrite_tac[lift_fields, open_fds_ticks]) >>
   qpat_assum ‘l0_accepted bp = _’ SUBST1_TAC >> first_assum ACCEPT_TAC)
QED

(* A break the PF trace sees shows on the blocking trace, unless the
   blocking run fell asleep *)
Theorem broke_transfer:
  bquiet m ifds bz ∧ l0_rely w0 ∧ (∀n. brounds lfd hw ifds bz m (w0, ps0) n ≠ NONE) ∧
  btrace lfd hw ifds bz m w0 ps0 io_b ∧ ptrace lfd hw ifds bz m w0 ps0 io_p ∧
  broke (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) io_p j0 ⇒
  broke w0 io_b j0 ∨
  ∃n h wb ps bp logs cb.
    brounds lfd hw ifds bz m (w0, ps0) n = SOME (BRun h (wb, ps) bp logs) ∧
    brounds lfd hw ifds bz m (w0, ps0) (SUC n) = SOME (BSlept h bp cb)
Proof
  rw[broke_def] >>
  ‘ppre lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0, ps0) evs’
    by metis_tac[ptrace_def] >>
  drule_all p2b >> rw[palign_def, pmid_def] >> gvs[]
  >- (disj1_tac >> qexistsl_tac [‘bp’, ‘wb’] >> simp[] >> metis_tac[btrace_def])
  >- (disj2_tac >> drule_at (Pos (el 4)) idle_asleep >> simp[] >> strip_tac >>
      metis_tac[])
  >> disj1_tac >>
  drule_at (Pos (el 2)) idle_wake_pre >> simp[] >> strip_tac >>
  qexistsl_tac [‘bp ++ [ev]’, ‘v’] >> simp[] >> conj_tac >- metis_tac[btrace_def] >>
  ‘l0_ticks «sys_poll» (SUC k) wb = l0_ticks «sys_poll» (SUC k − i) (l0_ticks «sys_poll» i wb)’
    by (REWRITE_TAC[GSYM ticks_add] >> AP_THM_TAC >> AP_TERM_TAC >> decide_tac) >>
  qspecl_then [‘SUC k − i’, ‘l0_ticks «sys_poll» i wb’] mp_tac
    (Q.INST [‘nm’ |-> ‘«sys_poll»’] wmono_ticks) >>
  rw[wmono_def] >> gvs[] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Nothing is queued when the blocking run falls asleep
   ------------------------------------------------------------------------ *)

Theorem acq_idle[local]:
  pf_ready lfd ps hs = [] ∧ MEM lfd hs ∧ ALOOKUP ps.b.tbl lfd = NONE ⇒ ps.acq = []
Proof
  rw[pf_ready_def, FILTER_EQ_NIL, EVERY_MEM] >> first_x_assum drule >> simp[]
QED

Theorem epoll_not_accept[local]:
  epoll fes e ⇒ ¬ev_on «sys_accept» f e
Proof
  rw[epoll_def] >> simp[ev_on_def]
QED

(* MAIN: the listener is polled for input in every idle round, and its
   PF image would then accept; so its queue is empty when the run sleeps *)
Theorem asleep_queue_empty:
  bquiet m ifds bz ∧ ps0 = pinit ∧
  run_ok lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) ∧
  winv (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) ∧
  linv lfd (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) ∧
  MEM lfd (l0_used (reindex (btr lfd hw ifds bz m (w0, ps0)) w0)) ∧
  (∀n. SND (pcm lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) n) + 1 <
       dimword (:64)) ∧
  S1 lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) ∧
  brounds lfd hw ifds bz m (w0, ps0) n0 = SOME (BRun kept (w, ps) evs0 logs) ∧
  bround lfd hw (¬bz kept) (ifds kept) (w, ps) (new_actions (log_of m) kept) =
    SOME (BAsleep rvs cb) ⇒
  qof w lfd = []
Proof
  strip_tac >>
  qabbrev_tac ‘pw = reindex (btr lfd hw ifds bz m (w0, ps0)) w0’ >>
  ‘binv lfd hw ifds bz m w0 ps0 kept w ps evs0’
    by (qpat_assum ‘brounds _ _ _ _ _ _ n0 = _’ mp_tac >>
        qpat_assum ‘bquiet _ _ _’ (fn th => REWRITE_TAC[MATCH_MP l1b_refines_pf th])) >>
  pop_assum (strip_assume_tac o REWRITE_RULE[binv_def]) >>
  drule_all asleep_at >> strip_tac >>
  ‘sfor m ifds bz full kept’ by fs[binv_at_def] >>
  ‘ifds full = ifds kept’ by (fs[sfor_def] >> first_x_assum (qspec_then ‘[]’ mp_tac) >> simp[]) >>
  first_assum (qspec_then ‘0’ strip_assume_tac) >>
  first_x_assum (qspec_then ‘1’ strip_assume_tac) >>
  rename1 ‘prounds _ _ _ _ _ (N + 1) = SOME (_, _, pevs ++ es1, _)’ >>
  ‘es = []’ by fs[] >> gvs[] >>
  ‘∃e. es1 = [e]’ by (Cases_on ‘es1’ >> gvs[]) >> gvs[] >>
  ‘prun lfd hw ifds m pw N = (full, (lift (btr lfd hw ifds bz m (w0, pinit)) (w0.hist ++ xs) w, ps),
                             pevs, plogs)’
    by (simp[prun_def] >> qpat_assum ‘prounds _ _ _ _ _ N = _’ (fn th => REWRITE_TAC[th]) >>
        simp[l0_ticks_def]) >>
  qpat_x_assum ‘prounds _ _ _ _ _ (N + 1) = _’ (assume_tac o REWRITE_RULE[GSYM ADD1]) >>
  ‘prun lfd hw ifds m pw (SUC N) =
     (full ++ [esnap],
      (lift (btr lfd hw ifds bz m (w0, pinit))
            (w0.hist ++ xs ++ [pcall (pf_poll_set lfd hw ps (ifds kept))])
            (l0_ticks «sys_poll» 1 w), ps), pevs ++ [e], plogs ++ [[]])’
    by (simp[prun_def] >> qpat_assum ‘prounds _ _ _ _ _ (SUC N) = _’ (fn th => REWRITE_TAC[th]) >>
        REWRITE_TAC[ONE, REPLICATE] >> simp[]) >>
  ‘rrev lfd hw ifds m pw N = [e]’
    by (REWRITE_TAC[rrev_def, revs_def, rstate_def, rhist_def, rworld_def] >>
        qpat_assum ‘prun _ _ _ _ _ N = _’ (fn th => REWRITE_TAC[th]) >>
        qpat_assum ‘prun _ _ _ _ _ (SUC N) = _’ (fn th => REWRITE_TAC[th]) >>
        simp[qof_def, DROP_LENGTH_APPEND]) >>
  ‘rstate lfd hw ifds m pw N = ps ∧ rhist lfd hw ifds m pw N = full ∧
   qof (rworld lfd hw ifds m pw N) lfd = qof w lfd’
    by (REWRITE_TAC[rrev_def, revs_def, rstate_def, rhist_def, rworld_def] >>
        qpat_assum ‘prun _ _ _ _ _ N = _’ (fn th => REWRITE_TAC[th]) >>
        qpat_assum ‘prun _ _ _ _ _ (SUC N) = _’ (fn th => REWRITE_TAC[th]) >>
        simp[qof_def, DROP_LENGTH_APPEND]) >>
  ‘MEM lfd (ifds full)’
    by (qpat_assum ‘S1 _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE[S1_def]) >>
        first_x_assum (qspec_then ‘N’ mp_tac) >> asm_rewrite_tac[]) >>
  ‘pf_idle lfd hw ps (ifds kept)’ by fs[bidle_def] >>
  ‘∀n. SND (pcm lfd hw ifds m pw n) + 1 < dimword (:64)’ by fs[] >>
  ‘ALOOKUP ps.b.tbl lfd = NONE’
    by (drule_all round_facts >> disch_then (qspec_then ‘N’ strip_assume_tac) >>
        irule tbl_lfd >> gvs[]) >>
  ‘ps.acq = [] ∧ ps.pause = 0’ by (fs[pf_idle_def] >> metis_tac[acq_idle]) >>
  CCONTR_TAC >>
  drule_all run_lfd >> disch_then (qspec_then ‘N’ mp_tac) >> asm_rewrite_tac[] >>
  simp[] >>
  ‘¬retried e ∧ ¬ev_on «sys_accept» lfd e’ by metis_tac[epoll_not_retried, epoll_not_accept] >>
  ‘MEM lfd (ifds kept)’ by metis_tac[] >>
  Cases_on ‘ev_on «sys_poll» lfd e’ >> simp[]
QED

(* ------------------------------------------------------------------------
   The transfer
   ------------------------------------------------------------------------ *)

Theorem accepted_last[local]:
  l0_event_accepted ev = SOME k ⇒ MEM k (l0_accepted (a ++ [ev]))
Proof
  simp[l0_accepted_def]
QED

(* A connection queued at a blocking prefix of a run that falls asleep is
   resolved before the sleep *)
Theorem asleep_resolved:
  bquiet m ifds bz ∧ l0_rely w0 ∧ l0wf w0 ∧ lone lfd w0 ∧ ps0 = pinit ∧
  btrace lfd hw ifds bz m w0 ps0 io_b ∧
  run_ok lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) ∧
  winv (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) ∧
  linv lfd (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) ∧
  MEM lfd (l0_used (reindex (btr lfd hw ifds bz m (w0, ps0)) w0)) ∧
  (∀n. SND (pcm lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) n) + 1 <
       dimword (:64)) ∧
  S1 lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) ∧
  brounds lfd hw ifds bz m (w0, ps0) n1 = SOME (BSlept h bp cb) ∧
  bpre lfd hw ifds bz m (w0, ps0) evs ∧ world_at w0 evs = SOME w ∧
  MEM (l, p, q) w.listeners ∧ MEM j0 q ⇒
  (∃evs' w' f. LPREFIX (fromList evs') io_b ∧ world_at w0 evs' = SOME w' ∧
               ALOOKUP w'.open_fds f = SOME j0 ∧ MEM f (l0_accepted evs')) ∨
  broke w0 io_b j0
Proof
  strip_tac >> drule brounds_BSlept >> strip_tac >>
  drule bround_asleep >> strip_tac >>
  qpat_x_assum ‘_ = []’ SUBST_ALL_TAC >>
  qpat_x_assum ‘bp = _’ (SUBST_ALL_TAC o REWRITE_RULE[APPEND_NIL]) >>
  qpat_x_assum ‘ps0 = _’ SUBST_ALL_TAC >>
  ‘qof w' lfd = []’
    by (mp_tac (GEN_ALL (REWRITE_RULE[] (Q.INST [‘ps0’ |-> ‘pinit’] asleep_queue_empty))) >>
        disch_then drule_all >> simp[]) >>
  ‘brounds lfd hw ifds bz m (w0, pinit) (SUC n0) = SOME (BSlept h evs0 cb)’
    by (simp[brounds_def] >>
        qpat_assum ‘brounds _ _ _ _ _ _ n0 = _’ (fn th => REWRITE_TAC[th]) >> simp[] >>
        qpat_assum ‘bround _ _ _ _ _ _ = _’ (fn th => REWRITE_TAC[th]) >> simp[]) >>
  ‘evs ≼ evs0’ by (irule asleep_prefixes >> metis_tac[]) >>
  ‘bpre lfd hw ifds bz m (w0, pinit) evs0’ by metis_tac[bpre_round, IS_PREFIX_REFL] >>
  ‘faithful w0 evs0’ by metis_tac[bpre_faithful] >>
  ‘∃s. evs0 = evs ++ s’ by metis_tac[IS_PREFIX_APPEND] >>
  ‘lone lfd w ∧ l0wf w’
    by (conj_tac >>
        (irule faithful_world_inv >> conj_tac >- metis_tac[lone_ffi, l0wf_ffi_fn] >>
         qexistsl_tac [‘evs’, ‘s’, ‘w0’] >> rpt conj_tac >>
         TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
         qpat_x_assum ‘evs0 = _’ (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC)) >>
  drule_all lone_qof >> strip_tac >>
  qpat_x_assum ‘l = lfd’ SUBST_ALL_TAC >> qpat_x_assum ‘qof _ _ = q’ (SUBST_ALL_TAC o SYM) >>
  ‘world_at w0 (evs ++ s) = SOME w'’ by metis_tac[bworld] >>
  ‘FOLDL l0_step (SOME w) (MAP ev_lcall s) = SOME w'’
    by (qpat_x_assum ‘world_at w0 (evs ++ s) = _’ mp_tac >>
        REWRITE_TAC[world_at_append] >> asm_rewrite_tac[optionTheory.OPTION_BIND_def] >>
        BETA_TAC >> REWRITE_TAC[]) >>
  ‘faithful w s’
    by (irule faithful_drop >> qexistsl_tac [‘evs’, ‘w0’] >> gvs[world_at_def, l0_replay_def]) >>
  ‘¬MEM j0 (qof w' lfd)’ by (strip_tac >> gvs[]) >>
  drule_all qexit_trace >> strip_tac >>
  qpat_x_assum ‘s = _’ SUBST_ALL_TAC >>
  ‘world_at w0 (evs ++ a ++ [ev]) = SOME x’
    by (REWRITE_TAC[GSYM APPEND_ASSOC] >> ONCE_REWRITE_TAC[world_at_append] >>
        qpat_assum ‘world_at w0 evs = _’ (fn th => REWRITE_TAC[th]) >>
        REWRITE_TAC[optionTheory.OPTION_BIND_def] >> BETA_TAC >> first_assum ACCEPT_TAC) >>
  ‘LPREFIX (fromList (evs ++ a ++ [ev])) io_b’
    by (qpat_assum ‘btrace _ _ _ _ _ _ _ _’ (fn th => REWRITE_TAC[REWRITE_RULE[btrace_def] th]) >>
        irule bpre_prefix >> qexists_tac ‘evs0’ >> rpt conj_tac >>
        TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
        qpat_x_assum ‘evs0 = _’ SUBST1_TAC >>
        REWRITE_TAC[IS_PREFIX_APPEND] >> qexists_tac ‘b’ >> REWRITE_TAC[APPEND_ASSOC])
  >- (disj1_tac >> qexistsl_tac [‘evs ++ a ++ [ev]’, ‘x’, ‘k’] >> rpt conj_tac >>
      TRY (first_assum ACCEPT_TAC >> NO_TAC) >> irule accepted_last >> first_assum ACCEPT_TAC)
  >> disj2_tac >> REWRITE_TAC[broke_def] >> qexistsl_tac [‘evs ++ a ++ [ev]’, ‘x’] >>
  asm_rewrite_tac[]
QED

(* MAIN: raw liveness for connections (PF ⇒ blocking) *)
Theorem conn_live_transfer:
  bquiet m ifds bz ∧ l0_rely w0 ∧ l0wf w0 ∧ lone lfd w0 ∧ ps0 = pinit ∧
  (∀n. brounds lfd hw ifds bz m (w0, ps0) n ≠ NONE) ∧
  btrace lfd hw ifds bz m w0 ps0 io_b ∧ ptrace lfd hw ifds bz m w0 ps0 io_p ∧
  run_ok lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) ∧
  winv (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) ∧
  linv lfd (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) ∧
  MEM lfd (l0_used (reindex (btr lfd hw ifds bz m (w0, ps0)) w0)) ∧
  (∀n. SND (pcm lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) n) + 1 <
       dimword (:64)) ∧
  S1 lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) ∧
  conn_live_l0 (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) io_p ⇒
  conn_live_l0 w0 io_b
Proof
  rw[conn_live_l0_def, conn_live_unless_def] >>
  ‘bpre lfd hw ifds bz m (w0, pinit) evs’ by metis_tac[btrace_def] >>
  drule_all b2p >> strip_tac >>
  ‘wb = w’ by metis_tac[optionTheory.SOME_11] >> pop_assum SUBST_ALL_TAC >>
  first_x_assum (qspecl_then [‘pp’, ‘lift (btr lfd hw ifds bz m (w0, pinit)) hp w’,
                              ‘l’, ‘p’, ‘q’, ‘j0’] mp_tac) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      TRY (qpat_assum ‘ptrace _ _ _ _ _ _ _ _’
             (fn th => REWRITE_TAC[REWRITE_RULE[ptrace_def] th]) >>
           first_assum ACCEPT_TAC >> NO_TAC) >>
      asm_simp_tac (srw_ss()) []) >>
  strip_tac
  >- (drule_all accepts_fail_transfer >> simp[])
  >- (drule_all accepted_transfer >> strip_tac >> disj2_tac >> disj1_tac >>
      qexistsl_tac [‘bp’, ‘wb’, ‘f’] >> asm_rewrite_tac[])
  >> drule_all broke_transfer >> strip_tac
  >- (disj2_tac >> disj2_tac >> first_assum ACCEPT_TAC)
  >> ‘∀n. SND (pcm lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) n) + 1 <
         dimword (:64)’ by fs[] >>
  mp_tac (GEN_ALL (REWRITE_RULE[] (Q.INST [‘ps0’ |-> ‘pinit’] asleep_resolved))) >>
  disch_then drule_all >> strip_tac
  >- (disj2_tac >> disj1_tac >> metis_tac[])
  >> disj2_tac >> disj2_tac >> first_assum ACCEPT_TAC
QED
