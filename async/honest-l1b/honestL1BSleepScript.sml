(*
  L3-09 (S4′), l1b_sleeps: with finitely many arrivals the blocking run
  sleeps, unless [F1] fails or accepts fail infinitely often (on its
  trace).  If it never slept, the PF run of the reindexed world would
  settle (l1pf_stable: [F1] and the accepts excuse go blocking ⇒ PF); a
  blocking round at or past a settled PF round is idle, so it polls
  blocking; its poll cannot return with a report (the round would then
  call: honestL1BWake, and the settled PF round makes only its poll), so
  it returns failed.  Every such poll lists the listener, so [F1] fails
  on the blocking trace.

  MAIN: l1b_sleeps.
*)
Theory honestL1BSleep
Ancestors
  honestL1BStable honestL1BWake honestL1BSettleState honestL1BCallsStop honestL1BGone
  honestL1BConnLive honestL1BGuar honestL1BTransfer honestL1BCorr honestL1BSim
  honestL1BRefine honestL1BPoll honestL1BModel honestL1BStmts honestL0Reindex
  honestL1BDrains honestL1BFaith honestEchoL0Spec honestL1PFFlush
  honestL1PFOutLive honestL1PFConnRun honestL1PFConn honestL1PFLive honestL1PFRound honestL1PFModel
  honestL1PFInv honestL1Inv honestL1Model honestL0WorldProps honestL0Rely honestL0World honestL0 llist
Libs
  preamble

(* ------------------------------------------------------------------------
   The PF trace is the PF run's events
   ------------------------------------------------------------------------ *)

Theorem ptrace_revs:
  ptrace lfd hw ifds bz m w0 pinit io ∧
  run_ok lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ⇒
  (∀n i. i < LENGTH (revs lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) n) ⇒
         LNTH i io = SOME (EL i (revs lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) n))) ∧
  (∀i ev. LNTH i io = SOME ev ⇒
          ∃n. i < LENGTH (revs lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) n) ∧
              EL i (revs lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) n) = ev)
Proof
  strip_tac >> qabbrev_tac ‘W' = reindex (btr lfd hw ifds bz m (w0, pinit)) w0’ >>
  drule prun_some >> strip_tac >> conj_tac
  >- (rpt strip_tac >>
      ‘LPREFIX (fromList (revs lfd hw ifds m W' n)) io’
        by (fs[ptrace_def] >> simp[ppre_def] >>
            qexistsl_tac [‘n’, ‘FST (prun lfd hw ifds m W' n)’,
                          ‘FST (SND (prun lfd hw ifds m W' n))’,
                          ‘revs lfd hw ifds m W' n’,
                          ‘SND (SND (SND (prun lfd hw ifds m W' n)))’] >>
            simp[revs_def] >> first_x_assum (qspec_then ‘n’ mp_tac) >>
            Cases_on ‘prun lfd hw ifds m W' n’ >> rename1 ‘(a, r)’ >> PairCases_on ‘r’ >> simp[]) >>
      fs[LPREFIX_fromList_LNTH])
  >> rpt strip_tac >> drule LNTH_prefix_exists >> strip_tac >>
  ‘ppre lfd hw ifds m (W', pinit) l’ by metis_tac[ptrace_def] >>
  fs[ppre_def] >>
  ‘prun lfd hw ifds m W' N = (h, ws, evs, logs)’
    by (first_x_assum (qspec_then ‘N’ mp_tac) >> simp[]) >>
  qexists_tac ‘N’ >> simp[revs_def] >>
  fs[IS_PREFIX_APPEND] >> gvs[EL_APPEND1]
QED

(* [F1], trace ⇒ run *)
Theorem F1_run:
  ptrace lfd hw ifds bz m w0 pinit io ∧
  run_ok lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ∧ F1_io io ⇒
  F1 lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0)
Proof
  strip_tac >> drule_all ptrace_revs >> strip_tac >>
  simp[F1_def, call_at_def, call_ok_at_def] >> rpt strip_tac >>
  qpat_x_assum ‘F1_io _’ (mp_tac o REWRITE_RULE[F1_io_def]) >>
  disch_then (qspecl_then [‘nm’, ‘f’] mp_tac) >> impl_tac
  >- (gen_tac >> first_x_assum (qspec_then ‘i’ strip_assume_tac) >>
      qexistsl_tac [‘i'’, ‘EL i' (revs lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) n)’] >>
      simp[]) >>
  disch_then (qspec_then ‘i’ strip_assume_tac) >>
  qpat_x_assum ‘∀i ev. LNTH i io = SOME ev ⇒ _’ drule >> strip_tac >>
  qexists_tac ‘i'’ >> gvs[] >> metis_tac[]
QED

(* An accept's result decodes *)
Theorem accept_dec[local]:
  l0_ffi_fn «sys_accept» conf bytes u = SOME (FFIreturn out v) ∧
  (∀h. LENGTH (u.ch.errno_of h) = 4) ⇒
  ∃r. dec_res out = SOME r ∧ l0_res_of out = r
Proof
  rw[l0_ffi_fn_def, AllCaseEqs()] >> gvs[l0_call_def, AllCaseEqs()] >>
  pairarg_tac >> gvs[] >>
  ‘l0_res_ok r’
    by (qpat_x_assum ‘l0_accept _ _ = _’ mp_tac >>
        rw[l0_accept_def, AllCaseEqs(), fail_def] >> simp[l0_res_ok_def] >>
        TRY (qspec_then ‘f’ mp_tac (INST_TYPE [alpha |-> “:64”] w2n_lt) >> simp[]) >>
        fs[l0_tick_def]) >>
  drule dec_enc_res >> disch_then (qspec_then ‘[]’ mp_tac) >> simp[l0_res_of_def]
QED

Theorem ffi_fn_ch[local]:
  l0_ffi_fn n conf b w = SOME (FFIreturn out w') ⇒ w'.ch = w.ch
Proof
  rw[l0_ffi_fn_def, AllCaseEqs()] >> drule l0_call_ch >> simp[]
QED

Theorem faithful_last[local]:
  ∀a w. faithful w (a ++ [ev]) ⇒
        ∃n conf bs u v. ev = IO_event (ExtCall n) conf bs ∧ u.ch = w.ch ∧
                        l0_ffi_fn n conf (MAP FST bs) u = SOME (FFIreturn (MAP SND bs) v)
Proof
  Induct >> simp[faithful_def] >> rpt strip_tac
  >- metis_tac[]
  >> first_x_assum drule >> strip_tac >> imp_res_tac ffi_fn_ch >> metis_tac[]
QED

(* The accepts excuse, run ⇒ trace *)
Theorem accepts_run:
  ptrace lfd hw ifds bz m w0 pinit io ∧ l0_rely w0 ∧
  run_ok lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ∧
  accepts_fail lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ⇒
  accepts_fail_io io
Proof
  strip_tac >> drule_all ptrace_revs >> strip_tac >>
  qabbrev_tac ‘W' = reindex (btr lfd hw ifds bz m (w0, pinit)) w0’ >>
  rw[accepts_fail_io_def] >> fs[accepts_fail_def] >>
  qpat_x_assum ‘∀i. ∃i' n. _’ (qspec_then ‘i’ strip_assume_tac) >>
  qabbrev_tac ‘ev = EL i' (revs lfd hw ifds m W' n)’ >>
  ‘LNTH i' io = SOME ev’ by (simp[Abbr ‘ev’] >> first_x_assum irule >> simp[]) >>
  ‘LPREFIX (fromList (TAKE i' (revs lfd hw ifds m W' n) ++ [ev])) io’
    by (simp[LPREFIX_fromList_LNTH] >> rw[] >>
        Cases_on ‘i'' < i'’ >> simp[EL_APPEND1, EL_APPEND2, EL_TAKE]
        >> TRY (first_x_assum irule >> simp[] >> NO_TAC)
        >> ‘i'' = i'’ by decide_tac >> simp[]) >>
  drule_all pf_faithful >> simp[Abbr ‘W'’] >> strip_tac >>
  drule faithful_last >> strip_tac >> gvs[ev_on_def, failed_def] >>
  ‘l0_rely (reindex (btr lfd hw ifds bz m (w0, pinit)) w0)’ by fs[run_ok_def] >>
  ‘∀h. LENGTH (u.ch.errno_of h) = 4’ by fs[l0_rely_def] >>
  drule_all accept_dec >> strip_tac >>
  qexistsl_tac [‘i'’, ‘conf’, ‘bs’, ‘e’, ‘x’] >> gvs[l0_ev_res_def]
QED

(* ------------------------------------------------------------------------
   Blocking rounds run at least as far as PF rounds
   ------------------------------------------------------------------------ *)

Theorem brounds_binv_ge:
  bquiet m ifds bz ⇒
  ∀n kept w ps evs logs.
    brounds lfd hw ifds bz m (w0, ps0) n = SOME (BRun kept (w, ps) evs logs) ⇒
    ∃N full xs pevs plogs. n ≤ N ∧
      binv_at lfd hw ifds bz m w0 ps0 N full xs pevs plogs kept w ps evs
Proof
  strip_tac >> Induct
  >- (rw[brounds_def] >> qexistsl_tac [‘0’, ‘[]’, ‘[]’, ‘[]’, ‘[]’] >>
      simp[binv_at_def, prounds_def, lift_reindex, trs_rules, evrel_rules])
  >> rpt strip_tac >> drule brounds_SUC_BRun >> strip_tac >>
  PairCases_on ‘ws’ >> first_x_assum drule >> strip_tac >>
  drule bround_cases >> strip_tac >> gvs[] >>
  RULE_ASSUM_TAC (REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND]
  >- (drule_all binv_plain >> strip_tac >> goal_assum (drule_at Any) >> simp[])
  >> drule_all binv_idle >> strip_tac >> goal_assum (drule_at Any) >> simp[]
QED

(* ------------------------------------------------------------------------
   A blocking poll that returns
   ------------------------------------------------------------------------ *)

Theorem pollb_out:
  sys_pollb fes w = SOME (INL (out, w2, ev)) ⇒
  ev = IO_event (ExtCall «sys_poll») pollb_conf (ZIP (poll_buf fes, out)) ∧
  ((∃e. (l0_tick «sys_poll» w).ch.transient (l0_tick «sys_poll» w).hist = SOME e ∧
        out = poll_failed (l0_tick «sys_poll» w) e (poll_buf fes)) ∨
   ∃k. out = poll_out (l0_ticks «sys_poll» k (l0_tick «sys_poll» w)) (poll_buf fes) ∧
       any_revents (l0_ticks «sys_poll» k (l0_tick «sys_poll» w)) (pfes fes))
Proof
  simp[sys_pollb_def, l0_ffi_fn_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >>
  simp[l0_call_def, pollb_conf_def, poll_buf_ok] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  qexists_tac ‘k’ >> simp[] >>
  qpat_x_assum ‘l0_wait _ _ = _’ mp_tac >> simp[l0_wait_def] >> rw[] >>
  simp[pfes_eq] >> numLib.LEAST_ELIM_TAC >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   A blocking round past a settled PF round
   ------------------------------------------------------------------------ *)

Theorem chan_ticks[local]:
  l0_chan_of w f = SOME j ⇒ l0_chan_of (l0_ticks nm k w) f = SOME j
Proof
  rw[l0_chan_of_def, open_fds_ticks, AllCaseEqs()] >>
  qspecl_then [‘k’, ‘w’] mp_tac (Q.INST [‘c’ |-> ‘j’] cflow_ticks) >> simp[]
QED

Theorem polls_after[local]:
  run_ok lfd pol ifds m w0 ∧
  (∀k. N ≤ k ⇒ EVERY (λev. ev_name ev = ExtCall «sys_poll») (rrev lfd pol ifds m w0 k)) ⇒
  ∀d. EVERY (λev. ev_name ev = ExtCall «sys_poll»)
            (DROP (LENGTH (revs lfd pol ifds m w0 N)) (revs lfd pol ifds m w0 (N + d)))
Proof
  strip_tac >> Induct >> simp[DROP_LENGTH_NIL] >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘N + d’] strip_assume_tac) >>
  simp[ADD_CLAUSES] >>
  ‘LENGTH (revs lfd pol ifds m w0 N) ≤ LENGTH (revs lfd pol ifds m w0 (N + d))’
    by (irule revs_len_mono >> simp[]) >>
  simp[DROP_APPEND1] >> first_x_assum (qspec_then ‘N + d’ mp_tac) >> simp[]
QED

Theorem binv_run[local]:
  binv_at lfd hw ifds bz m w0 pinit N full xs pevs plogs kept w ps evs ∧
  run_ok lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ⇒
  revs lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) N = pevs ∧
  rstate lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) N = ps ∧
  rhist lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) N = full ∧
  rworld lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) N =
    lift (btr lfd hw ifds bz m (w0, pinit)) (w0.hist ++ xs) w
Proof
  rw[binv_at_def] >> drule prun_some >> disch_then (qspec_then ‘N’ mp_tac) >>
  qpat_x_assum ‘prounds _ _ _ _ _ _ = _’ (fn th => REWRITE_TAC[th]) >>
  simp[revs_def, rstate_def, rhist_def, rworld_def] >> strip_tac >>
  pop_assum (SUBST1_TAC o SYM) >> simp[]
QED

Theorem pf_after_polls_nil[local]:
  pf_after lfd hw hs ps fes (rv, w1, []) = SOME (rdy, ws, log, tevs) ∧
  EVERY (λev. ev_name ev = ExtCall «sys_poll») tevs ⇒ tevs = []
Proof
  simp[pf_after_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  ‘fevs = []’ by (irule names_nil >> simp[] >> qexists_tac ‘«sys_send»’ >> simp[] >>
                  drule flush_names >> simp[]) >>
  ‘gevs = []’ by (drule pf_fetch_names >> rw[] >> Cases_on ‘gevs’ >> gvs[] >>
                  Cases_on ‘h’ >> gvs[ev_name_def]) >>
  ‘cevs = []’ by (irule names_nil >> simp[] >> qexists_tac ‘«sys_close»’ >> simp[] >>
                  drule reap_names >> simp[]) >>
  gvs[]
QED

Theorem stable_bround:
  bquiet m ifds bz ∧ l0_rely w0 ∧
  binv_at lfd hw ifds bz m w0 pinit N full xs pevs plogs kept w ps evs ∧
  brounds lfd hw ifds bz m (w0, pinit) n = SOME (BRun kept (w, ps) evs logs) ∧
  brounds lfd hw ifds bz m (w0, pinit) (SUC n) = SOME (BRun kept' ws' evs' logs') ∧
  run_ok lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ∧
  (∀k. N ≤ k ⇒
       new_actions (log_of m) (rhist lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) k) = [] ∧
       ¬bz (rhist lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) k) ∧
       pf_idle lfd hw (rstate lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) k)
         (ifds (rhist lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) k)) ∧
       EVERY (λev. ev_name ev = ExtCall «sys_poll»)
         (rrev lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) k)) ∧
  (∀f. MEM f (MAP SND ps.b.tbl) ∨ outbox_of ps.b f ≠ [] ⇒
       ∃j. l0_chan_of (rworld lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) N) f = SOME j) ∧
  linv lfd (rworld lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) N) ∧
  obwf ps.b ∧ gone_clear ps.b ∧ psmall lfd ps ∧
  MEM lfd (ifds kept) ∧ ALOOKUP ps.b.tbl lfd = NONE ⇒
  ∃ev. evs' = evs ++ [ev] ∧ ev_on «sys_poll» lfd ev ∧ retried ev
Proof
  strip_tac >> qabbrev_tac ‘W' = reindex (btr lfd hw ifds bz m (w0, pinit)) w0’ >>
  drule prun_some >> strip_tac >>
  ‘prun lfd hw ifds m W' N =
     (full, (lift (btr lfd hw ifds bz m (w0, pinit)) (w0.hist ++ xs) w, ps), pevs, plogs)’
    by (fs[binv_at_def] >> first_x_assum (qspec_then ‘N’ mp_tac) >> simp[]) >>
  ‘rstate lfd hw ifds m W' N = ps ∧ rhist lfd hw ifds m W' N = full ∧
   rworld lfd hw ifds m W' N = lift (btr lfd hw ifds bz m (w0, pinit)) (w0.hist ++ xs) w ∧
   revs lfd hw ifds m W' N = pevs’ by simp[rstate_def, rhist_def, rworld_def, revs_def] >>
  qpat_assum ‘∀k. N ≤ k ⇒ _’ (qspec_then ‘N’ mp_tac) >> impl_tac >- simp[] >>
  asm_rewrite_tac[] >> strip_tac >>
  ‘sfor m ifds bz full kept’ by fs[binv_at_def] >>
  ‘bidle lfd hw ifds bz m kept ps’
    by (drule sfor_now >> strip_tac >> fs[bidle_def]) >>
  drule brounds_SUC_BRun >> strip_tac >> gvs[] >>
  drule bround_cases >> strip_tac >> gvs[] >>
  PairCases_on ‘ws'’ >>
  drule_all binv_idle >> strip_tac >>
  qabbrev_tac ‘fes = pf_poll_set lfd hw (rstate lfd hw ifds m W' N) (ifds h)’ >>
  (* the PF rounds N .. N + k made only polls, so the round's tail called nothing *)
  ‘revs lfd hw ifds m W' (N + SUC k) =
     revs lfd hw ifds m W' N ++ es ++
     IO_event (ExtCall «sys_poll») [0w] (ZIP (poll_buf fes, out)) :: tevs’
    by (qpat_assum ‘binv_at _ _ _ _ _ _ _ (SUC _) _ _ _ _ _ _ _ _’
          (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] binv_run)) >>
        impl_tac >- (qpat_x_assum ‘run_ok _ _ _ _ _’ mp_tac >> simp[Abbr ‘W'’]) >>
        simp[Abbr ‘W'’, ADD_CLAUSES]) >>
  ‘EVERY (λev. ev_name ev = ExtCall «sys_poll») tevs’
    by (drule polls_after >>
        disch_then (qspecl_then [‘N’] mp_tac) >> impl_tac >- simp[] >>
        disch_then (qspec_then ‘SUC k’ mp_tac) >>
        qpat_x_assum ‘revs _ _ _ _ _ (N + SUC k) = _’ SUBST1_TAC >>
        REWRITE_TAC[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  ‘tevs = []’ by (drule_all pf_after_polls_nil >> simp[]) >>
  gvs[] >>
  (* so the poll reported nothing *)
  ‘∀f e r. MEM (f, e) fes ∧ MEM (f, r) (poll_revents fes out) ⇒
           ¬((ODD e ∧ (r.rin ∨ r.rhup ∨ r.rerr)) ∨ (2 ≤ e ∧ (r.rout ∨ r.rhup ∨ r.rerr)))’
    by (rpt gen_tac >> strip_tac >> strip_tac >>
        qpat_x_assum ‘pf_after _ _ _ _ _ _ = _’ mp_tac >> simp[Abbr ‘fes’] >> strip_tac >>
        drule pf_after_wakes >> simp[] >> qexistsl_tac [‘r’, ‘f’, ‘e’] >> simp[]) >>
  qabbrev_tac ‘ps = rstate lfd hw ifds m W' N’ >>
  ‘pf_idle lfd hw ps (ifds h)’ by fs[bidle_def] >>
  ‘l0_rely w’ by metis_tac[bworld] >>
  (* the listener is polled *)
  ‘ps.acq = [] ∧ ps.pause = 0’
    by (fs[pf_idle_def, pf_ready_def, FILTER_EQ_NIL, EVERY_MEM] >>
        first_x_assum drule >> simp[]) >>
  ‘MEM (lfd, 1) fes’
    by (simp[Abbr ‘fes’, pf_poll_set_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
        disj1_tac >> qexists_tac ‘lfd’ >> simp[wants_input_def]) >>
  ‘small lfd ∧ EVERY (λ(f, e). small f ∧ e < 4) fes’
    by (fs[psmall_def, small_fds_def] >> simp[Abbr ‘fes’] >>
        irule pf_poll_set_small >> fs[psmall_def, small_fds_def]) >>
  ‘LENGTH out = LENGTH (poll_buf fes)’
    by (qpat_x_assum ‘sys_pollb _ _ = _’ mp_tac >> simp[sys_pollb_def, AllCaseEqs()] >>
        strip_tac >> drule_all l0_ffi_fn_length >> simp[]) >>
  drule pollb_out >> strip_tac >> gvs[]
  >- (conj_tac
      >- (simp[ev_on_def, call_fds_def, MAP_ZIP, poll_buf_ok, MEM_MAP] >>
          qexists_tac ‘pfd_bytes (lfd, 1)’ >> simp[] >>
          drule_at Any pe_pfd_bytes >> disch_then (qspec_then ‘1’ mp_tac) >> simp[pe_fe_def] >>
          strip_tac >> simp[pollfd_entries_buf, MEM_MAP] >> qexists_tac ‘(lfd, 1)’ >> simp[])
      >> simp[retried_def, MAP_ZIP] >>
      ‘LENGTH ((l0_tick «sys_poll» w).ch.errno_of (l0_tick «sys_poll» w).hist) = 4’
        by fs[l0_rely_def] >>
      drule res_of_poll_failed >> simp[])
  >> spose_not_then kall_tac >>
  qabbrev_tac ‘x = l0_ticks «sys_poll» k (l0_tick «sys_poll» w)’ >>
  ‘l0_tick «sys_poll» w = l0_ticks «sys_poll» 1 w’ by REWRITE_TAC[ONE, l0_ticks_def] >>
  ‘linv lfd x’
    by (‘linv lfd w’ by fs[linv_def] >>
        simp[Abbr ‘x’] >> rpt (irule linv_ticks) >> simp[]) >>
  ‘∀f e. MEM (f, e) fes ⇒
         (e = 1 ∨ e = 2 ∨ e = 3) ∧
         ((∃j. l0_chan_of x f = SOME j) ∨
          (l0_chan_of x f = NONE ∧ MEM f (MAP FST x.listeners)))’
    by (rpt gen_tac >> strip_tac >>
        ‘MEM (f, e) (pf_poll_set lfd hw ps (ifds h))’ by fs[Abbr ‘fes’] >>
        drule_all poll_set_entry >> strip_tac >> simp[] >>
        TRY (disj2_tac >> qpat_x_assum ‘linv lfd x’ mp_tac >>
             simp[linv_def, l0_chan_of_def] >> NO_TAC) >>
        disj1_tac >>
        ‘∃j. l0_chan_of w f = SOME j’
          by (qpat_x_assum ‘∀f. (outbox_of _ f = [] ⇒ _) ⇒ _’ irule >> fs[]) >>
        qexists_tac ‘j’ >> simp[Abbr ‘x’] >> irule chan_ticks >>
        qpat_x_assum ‘l0_tick _ _ = _’ SUBST1_TAC >> irule chan_ticks >> simp[]) >>
  qspecl_then [‘fes’, ‘x’] mp_tac (Q.GENL [‘fes’, ‘x’] poll_out_wakes) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum ‘∀f e r. MEM (f, e) fes ∧ _ ⇒ _’ drule_all >> simp[]
QED
