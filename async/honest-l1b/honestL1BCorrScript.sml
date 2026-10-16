(*
  L3-09 (S3): the prefix correspondence between the blocking run's trace
  and the PF run's (in the reindexed world).

  bpre / ppre: the finite prefixes of the two traces.
  b2p: every prefix of the blocking trace has a prefix of the PF trace with
  the same non-poll events (nopoll), whose world (world_at, the replay) is
  the blocking prefix's world, lifted.

  MAIN: b2p.
*)
Theory honestL1BCorr
Ancestors
  honestL1BObs honestL1BRuns honestL1BReplay honestL1BSim honestL1BRefine
  honestL1BLift honestL1BHist honestL1BPoll honestL1BModel honestL1BStmts honestL0Reindex
  honestL0Part honestL1PFModel honestL0WorldProps honestL0World honestL0 rich_list
Libs
  preamble

Definition bpre_def:
  bpre lfd hw ifds bz m ws0 (bp : io_event list) ⇔
    (∃n h ws evs logs. brounds lfd hw ifds bz m ws0 n = SOME (BRun h ws evs logs) ∧ bp ≼ evs) ∨
    (∃n h evs cb. brounds lfd hw ifds bz m ws0 n = SOME (BSlept h evs cb) ∧ bp ≼ evs)
End

Definition ppre_def:
  ppre lfd hw ifds m ws0 (pp : io_event list) ⇔
    ∃N h ws evs logs. prounds lfd hw ifds m ws0 N = SOME (h, ws, evs, logs) ∧ pp ≼ evs
End

Theorem prefix_append_cases:
  ∀a b p. p ≼ a ++ b ⇒ p ≼ a ∨ ∃t. p = a ++ t ∧ t ≼ b ∧ t ≠ []
Proof
  Induct >> simp[] >- (rw[] >> Cases_on ‘p’ >> fs[]) >>
  rw[] >> Cases_on ‘p’ >> fs[] >> first_x_assum drule >> rw[] >> simp[]
QED

Theorem FOLDL_step_prefix:
  ∀a b w w'. FOLDL l0_step (SOME w) (a ++ b) = SOME w' ⇒
             ∃w1. FOLDL l0_step (SOME w) a = SOME w1 ∧ FOLDL l0_step (SOME w1) b = SOME w'
Proof
  rw[FOLDL_APPEND] >> Cases_on ‘FOLDL l0_step (SOME w) a’ >> fs[]
QED

Theorem world_at_append:
  world_at w0 (a ++ b) = OPTION_BIND (world_at w0 a) (λw. FOLDL l0_step (SOME w) (MAP ev_lcall b))
Proof
  simp[world_at_def, l0_replay_def, FOLDL_APPEND] >>
  Cases_on ‘FOLDL l0_step (SOME w0) (MAP ev_lcall a)’ >> simp[]
QED

Theorem epoll_lcall:
  epoll fes ev ⇒ ev_lcall ev = pcall fes
Proof
  rw[epoll_def] >> simp[ev_lcall_def, MAP_ZIP, LENGTH_poll_out]
QED

Theorem epolls_lcall:
  ∀es. EVERY (epoll fes) es ⇒ MAP ev_lcall es = REPLICATE (LENGTH es) (pcall fes)
Proof
  Induct >> rw[] >> imp_res_tac epoll_lcall >> simp[]
QED

(* The translation around an idle round's blocking poll *)
Theorem idle_tr:
  binv_at lfd hw ifds bz m w0 ps0 N full xs pevs plogs h w ps evs ∧
  brounds lfd hw ifds bz m (w0, ps0) n = SOME (BRun h (w, ps) evs logs) ∧
  brounds lfd hw ifds bz m (w0, ps0) (SUC n) = SOME (BRun h' (w', ps') evs' logs') ∧
  bidle lfd hw ifds bz m h ps ∧
  fes = pf_poll_set lfd hw ps (ifds h) ∧
  sys_pollb fes w = SOME (INL (out, v, ev)) ∧ pollb_wait fes w = SOME k ∧
  LENGTH w.hist + 1 + L ≤ LENGTH w'.hist ⇒
  (∀j. j ≤ k ⇒ btr lfd hw ifds bz m (w0, ps0) (w0.hist ++ xs ++ REPLICATE j (pcall fes)) = w.hist) ∧
  v.hist = w.hist ++ [unblk (pcall fes)] ∧
  tr_from (btr lfd hw ifds bz m (w0, ps0))
          (w0.hist ++ xs ++ REPLICATE (SUC k) (pcall fes)) v.hist L ∧
  ∀cs. LENGTH cs ≤ L ⇒
       trs (bwait lfd hw ifds bz m (w0, ps0)) v.hist cs (v.hist ++ cs)
Proof
  strip_tac >>
  qpat_x_assum ‘binv_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[binv_at_def]) >>
  qabbrev_tac ‘tr = btr lfd hw ifds bz m (w0, ps0)’ >>
  ‘bwait lfd hw ifds bz m (w0, ps0) w.hist = SOME (SOME k)’
    by (qpat_assum ‘brounds _ _ _ _ _ _ n = _’ (mp_tac o MATCH_MP bwait_at) >>
        asm_rewrite_tac[] >> qpat_x_assum ‘fes = _’ (fn th => REWRITE_TAC[GSYM th]) >>
        asm_rewrite_tac[]) >>
  ‘∀zs. tr (w0.hist ++ xs ++ zs) = trw (bwait lfd hw ifds bz m (w0, ps0)) w.hist zs’
    by (simp[Abbr ‘tr’] >> drule btr_walk >> simp[]) >>
  drule (Q.INST [‘c’ |-> ‘pcall fes’] trw_reps) >> disch_then (strip_assume_tac o Q.SPEC ‘fes’) >>
  ‘v.hist = w.hist ++ [unblk (pcall fes)]’
    by (qpat_assum ‘sys_pollb _ _ = _’ (assume_tac o MATCH_MP sys_pollb_hist) >>
        pop_assum SUBST1_TAC >> REWRITE_TAC[unblk_pcall]) >>
  ‘∀j. j ≤ k ⇒ tr (w0.hist ++ xs ++ REPLICATE j (pcall fes)) = w.hist’
    by (rpt strip_tac >> qpat_assum ‘∀zs. tr _ = _’ (fn th => REWRITE_TAC[th]) >>
        qpat_assum ‘∀j. j ≤ k ⇒ _’ irule >> simp[]) >>
  ‘∀zs. tr (w0.hist ++ xs ++ REPLICATE (SUC k) (pcall fes) ++ zs) =
        trw (bwait lfd hw ifds bz m (w0, ps0)) (w.hist ++ [unblk (pcall fes)]) zs’
    by (gen_tac >>
        qpat_assum ‘∀zs. tr _ = _’ (qspec_then ‘REPLICATE (SUC k) (pcall fes) ++ zs’ mp_tac) >>
        REWRITE_TAC[APPEND_ASSOC] >> disch_then SUBST1_TAC >>
        qpat_assum ‘∀zs. trw _ _ (_ ++ zs) = _’ (fn th => REWRITE_TAC[th])) >>
  ‘[unblk (pcall fes)] ≠ []’ by simp[] >>
  ‘LENGTH w.hist + LENGTH [unblk (pcall fes)] + L ≤ LENGTH w'.hist’
    by (REWRITE_TAC[LENGTH] >> qpat_x_assum ‘_ ≤ LENGTH w'.hist’ mp_tac >> simp[]) >>
  drule_all tr_from_after >> strip_tac >>
  qpat_assum ‘v.hist = _’ (fn th => REWRITE_TAC[th]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >> qpat_assum ‘∀j. j ≤ k ⇒ tr _ = _’ irule >> first_assum ACCEPT_TAC
QED

Theorem bworld:
  l0_rely w0 ∧ brounds lfd hw ifds bz m (w0, ps0) n = SOME (BRun h (w, ps) evs logs) ⇒
  world_at w0 evs = SOME w ∧ l0_rely w
Proof
  strip_tac >> drule rplays_brounds >> rw[rplays_def, world_at_def, l0_replay_def]
QED

Theorem pworld:
  l0_rely w0 ∧ prounds lfd hw ifds m (reindex tr w0, ps0) N = SOME (full, (x, ps), pevs, plogs) ⇒
  world_at (reindex tr w0) pevs = SOME x ∧ l0_rely x
Proof
  strip_tac >> drule rplays_prounds >> imp_res_tac l0_rely_reindex >>
  rw[rplays_def, world_at_def, l0_replay_def] >> metis_tac[]
QED

(* A prefix ending inside a round that is not idle *)
Theorem b2p_plain:
  l0_rely w0 ∧
  binv_at lfd hw ifds bz m w0 ps0 N full xs pevs plogs h w ps evs ∧
  brounds lfd hw ifds bz m (w0, ps0) n = SOME (BRun h (w, ps) evs logs) ∧
  brounds lfd hw ifds bz m (w0, ps0) (SUC n) = SOME (BRun h' (w', ps') (evs ++ rvs) logs') ∧
  bround lfd hw (¬bz h) (ifds h) (w, ps) (new_actions (log_of m) h) =
    SOME (BRound snap (w', ps') log rvs) ∧
  ¬bidle lfd hw ifds bz m h ps ∧ t ≼ rvs ⇒
  ∃wb hp. world_at w0 (evs ++ t) = SOME wb ∧
          world_at (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) (pevs ++ t) =
            SOME (lift (btr lfd hw ifds bz m (w0, ps0)) hp wb)
Proof
  strip_tac >>
  qpat_assum ‘binv_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[binv_at_def]) >>
  qabbrev_tac ‘tr = btr lfd hw ifds bz m (w0, ps0)’ >>
  ‘world_at w0 evs = SOME w ∧ l0_rely w’ by metis_tac[bworld] >>
  drule_all pworld >> strip_tac >>
  drule rplays_bround >> REWRITE_TAC[rplays_def] >> disch_then drule >> strip_tac >>
  ‘∃rest. rvs = t ++ rest’ by metis_tac[IS_PREFIX_APPEND] >>
  qpat_x_assum ‘FOLDL _ _ (MAP _ rvs) = _’ mp_tac >>
  qpat_assum ‘rvs = _’ SUBST1_TAC >> REWRITE_TAC[MAP_APPEND] >> strip_tac >>
  drule FOLDL_step_prefix >> strip_tac >>
  qexistsl_tac [‘w1’, ‘w0.hist ++ xs ++ MAP ev_lcall t’] >>
  REWRITE_TAC[world_at_append] >> asm_rewrite_tac[optionTheory.OPTION_BIND_def] >>
  BETA_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  imp_res_tac bround_hgrows >>
  ‘∀zs. tr (w0.hist ++ xs ++ zs) = trw (bwait lfd hw ifds bz m (w0, ps0)) (w.hist ++ []) zs’
    by (simp[Abbr ‘tr’] >> drule btr_walk >> simp[]) >>
  ‘LENGTH w.hist + LENGTH ([] : lcall list) + LENGTH (MAP ev_lcall t) ≤ LENGTH w'.hist’
    by (qpat_assum ‘hgrows _ _ _’ (strip_assume_tac o REWRITE_RULE[hgrows_def]) >>
        qpat_x_assum ‘w'.hist = _’ SUBST1_TAC >>
        qpat_assum ‘rvs = _’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE[th])) >> fs[]) >>
  mp_tac (Q.INST [‘pre’ |-> ‘[] : lcall list’,
                  ‘L’ |-> ‘LENGTH (MAP ev_lcall (t : io_event list))’,
                  ‘hp’ |-> ‘w0.hist ++ xs’,
                  ‘evs'’ |-> ‘(evs : io_event list) ++ rvs’] tr_from_round) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
                disj2_tac >> first_assum ACCEPT_TAC)) >>
  REWRITE_TAC[APPEND_NIL] >> strip_tac >>
  drule lift_replay >> disch_then (fn th => REWRITE_TAC[th]) >>
  asm_rewrite_tac[optionTheory.OPTION_MAP_DEF]
QED

Theorem REPLICATE_SNOC_APP[local]:
  ∀k. REPLICATE k x ++ [x] = REPLICATE (SUC k) x
Proof
  Induct >> simp[]
QED

Theorem sys_pollb_length:
  l0_rely w ∧ sys_pollb fes w = SOME (INL (out, w', ev)) ⇒ LENGTH out = LENGTH fes + 13
Proof
  rw[sys_pollb_def, AllCaseEqs()] >> drule_all l0_ffi_fn_length >> simp[]
QED

(* A prefix ending inside an idle round, after its blocking poll *)
Theorem b2p_idle:
  l0_rely w0 ∧
  binv_at lfd hw ifds bz m w0 ps0 N full xs pevs plogs h w ps evs ∧
  brounds lfd hw ifds bz m (w0, ps0) n = SOME (BRun h (w, ps) evs logs) ∧
  brounds lfd hw ifds bz m (w0, ps0) (SUC n) = SOME (BRun h' (w', ps') evs' logs') ∧
  bidle lfd hw ifds bz m h ps ∧ fes = pf_poll_set lfd hw ps (ifds h) ∧
  sys_pollb fes w = SOME (INL (out, w2, ev)) ∧
  pf_after lfd hw (ifds h) ps fes (poll_revents fes out, w2, []) = SOME (rdy, (w', ps'), log, tevs) ∧
  pollb_wait fes w = SOME k ∧ EVERY (epoll fes) es ∧ LENGTH es = k ∧ t ≼ tevs ⇒
  ∃wb hp. world_at w0 (evs ++ ev :: t) = SOME wb ∧
          world_at (reindex (btr lfd hw ifds bz m (w0, ps0)) w0)
            (pevs ++ es ++ IO_event (ExtCall «sys_poll») (poll_conf fes)
                             (ZIP (REPLICATE (LENGTH fes + 13) 0w, out)) :: t) =
            SOME (lift (btr lfd hw ifds bz m (w0, ps0)) hp wb)
Proof
  strip_tac >>
  qpat_assum ‘binv_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[binv_at_def]) >>
  qabbrev_tac ‘tr = btr lfd hw ifds bz m (w0, ps0)’ >>
  ‘world_at w0 evs = SOME w ∧ l0_rely w’ by metis_tac[bworld] >>
  ‘world_at (reindex tr w0) pevs = SOME (lift tr (w0.hist ++ xs) w)’ by metis_tac[pworld] >>
  (* the blocking side *)
  ‘l0_step (SOME w) (ev_lcall ev) = SOME w2 ∧ l0_rely w2’
    by (qpat_assum ‘sys_pollb _ _ = _’ (mp_tac o MATCH_MP rplays_pollb) >>
        REWRITE_TAC[rplays_def, MAP, FOLDL] >> disch_then drule >> REWRITE_TAC[]) >>
  ‘FOLDL l0_step (SOME w2) (MAP ev_lcall tevs) = SOME w'’
    by (qpat_assum ‘pf_after _ _ _ _ _ _ = _’ (mp_tac o MATCH_MP rplays_after) >>
        REWRITE_TAC[rplays_def] >> disch_then drule >> strip_tac) >>
  ‘∃rest. tevs = t ++ rest’ by metis_tac[IS_PREFIX_APPEND] >>
  qpat_x_assum ‘FOLDL _ _ (MAP _ tevs) = _’ mp_tac >>
  qpat_assum ‘tevs = _’ SUBST1_TAC >> REWRITE_TAC[MAP_APPEND] >> strip_tac >>
  drule FOLDL_step_prefix >> strip_tac >>
  (* the PF side *)
  ‘poll_ok fes’
    by (irule sys_pollb_ok >> rpt conj_tac >>
        TRY (qexists_tac ‘w’ >>
             qpat_assum ‘sys_pollb _ _ = _’ (fn th => REWRITE_TAC[th, optionTheory.NOT_SOME_NONE]) >>
             NO_TAC) >>
        TRY (qpat_assum ‘fes = _’ SUBST1_TAC >> REWRITE_TAC[pf_poll_set_small] >> NO_TAC) >>
        qpat_assum ‘bidle _ _ _ _ _ _ _’ mp_tac >> qpat_assum ‘fes = _’ SUBST1_TAC >>
        REWRITE_TAC[bidle_def, pf_idle_def] >> rpt strip_tac) >>
  ‘LENGTH out = LENGTH fes + 13’
    by metis_tac[sys_pollb_length] >>
  ‘ev_lcall (IO_event (ExtCall «sys_poll») (poll_conf fes)
               (ZIP (REPLICATE (LENGTH fes + 13) 0w, out))) = pcall fes’
    by simp[ev_lcall_def, MAP_ZIP] >>
  imp_res_tac epolls_lcall >>
  drule hgrows_after >> strip_tac >>
  ‘LENGTH w.hist + 1 + LENGTH (MAP ev_lcall t) ≤ LENGTH w'.hist’
    by (qpat_assum ‘sys_pollb _ _ = _’ (assume_tac o MATCH_MP sys_pollb_hist) >>
        qpat_assum ‘hgrows _ _ _’ (strip_assume_tac o REWRITE_RULE[hgrows_def]) >>
        qpat_x_assum ‘w'.hist = _’ SUBST1_TAC >> qpat_x_assum ‘w2.hist = _’ SUBST1_TAC >>
        qpat_assum ‘tevs = _’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE[th])) >> fs[]) >>
  drule_all idle_tr >> strip_tac >> qpat_x_assum ‘fes = _’ kall_tac >>
  qexistsl_tac [‘w1’, ‘w0.hist ++ xs ++ REPLICATE (SUC k) (pcall fes) ++ MAP ev_lcall t’] >>
  conj_tac
  >- (REWRITE_TAC[world_at_append] >> asm_rewrite_tac[optionTheory.OPTION_BIND_def] >>
      BETA_TAC >> REWRITE_TAC[MAP, FOLDL] >> asm_rewrite_tac[]) >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >> REWRITE_TAC[world_at_append] >>
  asm_rewrite_tac[optionTheory.OPTION_BIND_def] >> BETA_TAC >>
  REWRITE_TAC[MAP_APPEND, MAP] >>
  qpat_assum ‘MAP ev_lcall es = _’ (fn th => REWRITE_TAC[th]) >>
  qpat_assum ‘ev_lcall _ = pcall fes’ (fn th => REWRITE_TAC[th]) >>
  qpat_assum ‘LENGTH es = k’ (fn th => REWRITE_TAC[th]) >>
  ‘REPLICATE k (pcall fes) ++ pcall fes :: MAP ev_lcall t =
     REPLICATE (SUC k) (pcall fes) ++ MAP ev_lcall t’
    by (REWRITE_TAC[GSYM REPLICATE_SNOC_APP, GSYM APPEND_ASSOC, APPEND]) >>
  pop_assum (fn th => REWRITE_TAC[th]) >> REWRITE_TAC[FOLDL_APPEND] >>
  ‘FOLDL l0_step (SOME (lift tr (w0.hist ++ xs) w)) (REPLICATE (SUC k) (pcall fes)) =
     SOME (lift tr (w0.hist ++ xs ++ REPLICATE (SUC k) (pcall fes)) w2)’
    by (qunabbrev_tac ‘tr’ >> irule replay_wake >> rpt conj_tac >>
        TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  pop_assum (fn th => REWRITE_TAC[th]) >>
  ‘tr_from tr (w0.hist ++ xs ++ REPLICATE (SUC k) (pcall fes)) w2.hist (LENGTH (MAP ev_lcall t))’
    by (qunabbrev_tac ‘tr’ >> first_assum ACCEPT_TAC) >>
  drule lift_replay >> disch_then (fn th => REWRITE_TAC[th]) >>
  qpat_assum ‘FOLDL _ (SOME w2) (MAP ev_lcall t) = _’ (fn th => REWRITE_TAC[th]) >>
  REWRITE_TAC[optionTheory.OPTION_MAP_DEF, APPEND_ASSOC]
QED

Theorem bpre_BRun:
  bpre lfd hw ifds bz m ws0 bp ⇒
  ∃n h ws evs logs. brounds lfd hw ifds bz m ws0 n = SOME (BRun h ws evs logs) ∧ bp ≼ evs
Proof
  rw[bpre_def] >- metis_tac[] >>
  drule brounds_BSlept >> strip_tac >>
  drule bround_asleep >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem prefix_app[local]:
  ∀l. t ≼ u ⇒ l ++ t ≼ l ++ u
Proof
  Induct >> simp[]
QED

Theorem ppre_intro:
  prounds lfd hw ifds m ws0 N = SOME (a, b, evs, c) ⇒ ∀pp. pp ≼ evs ⇒ ppre lfd hw ifds m ws0 pp
Proof
  rw[ppre_def] >> metis_tac[]
QED

Theorem poll_nopoll[local]:
  nopoll [IO_event (ExtCall «sys_poll») conf bs] = []
Proof
  simp[nopoll_def, is_poll_def]
QED

(* MAIN: every prefix of the blocking trace has a prefix of the PF trace
   with the same non-poll events, in the lifted world *)
Theorem b2p:
  bquiet m ifds bz ∧ l0_rely w0 ∧ bpre lfd hw ifds bz m (w0, ps0) bp ⇒
  ∃pp wb hp.
    ppre lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0, ps0) pp ∧
    nopoll pp = nopoll bp ∧ world_at w0 bp = SOME wb ∧
    world_at (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) pp =
      SOME (lift (btr lfd hw ifds bz m (w0, ps0)) hp wb)
Proof
  strip_tac >> drule bpre_BRun >> strip_tac >>
  pop_assum mp_tac >> pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [‘bp’, ‘evs’, ‘logs’, ‘ws’, ‘h’, ‘n’] >>
  Induct
  >- (rw[brounds_def] >> qexistsl_tac [‘[]’, ‘w0’, ‘w0.hist’] >>
      simp[ppre_def, world_at_def, l0_replay_def, lift_reindex] >>
      qexists_tac ‘0’ >> simp[prounds_def]) >>
  rpt gen_tac >> strip_tac >> drule brounds_SUC_BRun >> strip_tac >>
  rename1 ‘brounds _ _ _ _ _ _ n = SOME (BRun h0 wsa evs0 logs0)’ >>
  rename1 ‘bround _ _ _ _ _ _ = SOME (BRound snap wsb log rvs)’ >>
  strip_tac >> gvs[] >>
  drule prefix_append_cases >> strip_tac
  >- (first_x_assum drule_all >> simp[]) >>
  gvs[] >> PairCases_on ‘wsa’ >> PairCases_on ‘wsb’ >>
  ‘binv lfd hw ifds bz m w0 ps0 h0 wsa0 wsa1 evs0’
    by (qpat_assum ‘brounds _ _ _ _ _ _ n = _’ mp_tac >>
        qpat_assum ‘bquiet _ _ _’ (fn th => REWRITE_TAC[MATCH_MP l1b_refines_pf th])) >>
  pop_assum (strip_assume_tac o REWRITE_RULE[binv_def]) >>
  drule bround_cases >> strip_tac >> gvs[]
  >- (RULE_ASSUM_TAC (REWRITE_RULE [GSYM APPEND_ASSOC]) >>
      drule_all b2p_plain >> strip_tac >>
      drule_all binv_plain >> strip_tac >>
      qexistsl_tac [‘pevs ++ t’, ‘wb’, ‘hp’] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (fs[binv_at_def, ppre_def] >> qexists_tac ‘SUC N’ >>
          qpat_assum ‘prounds _ _ _ _ _ (SUC N) = _’ (fn th => REWRITE_TAC[th]) >> simp[] >>
          REWRITE_TAC[GSYM APPEND_ASSOC] >> irule prefix_app >> first_assum ACCEPT_TAC)
      >> fs[binv_at_def] >> imp_res_tac evrel_nopoll >> simp[]) >>
  rename1 ‘sys_pollb _ _ = SOME (INL (out, w2, ev))’ >>
  qpat_x_assum ‘t ≼ _’ mp_tac >> qpat_x_assum ‘t ≠ []’ mp_tac >>
  Cases_on ‘t’ >> REWRITE_TAC[isPREFIX_THM, NOT_CONS_NIL] >> rpt strip_tac >>
  qpat_x_assum ‘h = ev’ SUBST_ALL_TAC >>
  rename1 ‘t ≼ tevs’ >>
  drule_all binv_idle >> strip_tac >>
  qabbrev_tac ‘fes = pf_poll_set lfd hw wsa1 (ifds h0)’ >>
  ‘fes = pf_poll_set lfd hw wsa1 (ifds h0)’ by simp[Abbr ‘fes’] >>
  drule_all b2p_idle >> strip_tac >>
  qexistsl_tac [‘pevs ++ es ++ IO_event (ExtCall «sys_poll») (poll_conf fes)
                                 (ZIP (REPLICATE (LENGTH fes + 13) 0w, out)) :: t’, ‘wb’, ‘hp’] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qpat_assum ‘binv_at _ _ _ _ _ _ _ (SUC (N + k)) _ _ _ _ _ _ _ _’
        (strip_assume_tac o REWRITE_RULE[binv_at_def]) >>
      qpat_assum ‘prounds _ _ _ _ _ (SUC (N + k)) = _’ (fn th => irule (MATCH_MP ppre_intro th)) >>
      irule prefix_app >> REWRITE_TAC[isPREFIX_THM] >> first_assum ACCEPT_TAC)
  >> qpat_assum ‘binv_at _ _ _ _ _ _ _ N _ _ _ _ _ _ _ _’
       (strip_assume_tac o REWRITE_RULE[binv_at_def]) >>
  qpat_assum ‘evrel pevs _’ (assume_tac o MATCH_MP evrel_nopoll) >>
  qpat_assum ‘EVERY (epoll _) es’ (assume_tac o MATCH_MP nopoll_epolls) >>
  qpat_assum ‘ev = _’ SUBST1_TAC >>
  ‘∀conf bs l. nopoll (IO_event (ExtCall «sys_poll») conf bs :: l) = nopoll l’
    by simp[nopoll_def, is_poll_def] >>
  pop_assum (fn th => REWRITE_TAC[th, nopoll_append]) >>
  qpat_assum ‘nopoll pevs = _’ (fn th => REWRITE_TAC[th]) >>
  qpat_assum ‘nopoll es = _’ (fn th => REWRITE_TAC[th, APPEND_NIL])
QED

(* ------------------------------------------------------------------------
   From the PF trace back to the blocking trace
   ------------------------------------------------------------------------ *)

(* pp is aligned with a prefix of the blocking trace *)
Definition palign_def:
  palign lfd hw ifds bz m w0 ps0 pp ⇔
    ∃bp wb hp. bpre lfd hw ifds bz m (w0, ps0) bp ∧ nopoll pp = nopoll bp ∧
               world_at w0 bp = SOME wb ∧
               world_at (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) pp =
                 SOME (lift (btr lfd hw ifds bz m (w0, ps0)) hp wb)
End

(* pp ends inside an idle segment: i empty polls after the blocking round
   n's start, which polls blocking for at least i steps *)
Definition pmid_def:
  pmid lfd hw ifds bz m w0 ps0 pp ⇔
    ∃n h wb ps bp logs hp i.
      brounds lfd hw ifds bz m (w0, ps0) n = SOME (BRun h (wb, ps) bp logs) ∧
      bidle lfd hw ifds bz m h ps ∧ nopoll pp = nopoll bp ∧
      world_at w0 bp = SOME wb ∧
      world_at (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) pp =
        SOME (lift (btr lfd hw ifds bz m (w0, ps0)) hp (l0_ticks «sys_poll» i wb)) ∧
      (pollb_wait (pf_poll_set lfd hw ps (ifds h)) wb = NONE ∨
       ∃k. pollb_wait (pf_poll_set lfd hw ps (ifds h)) wb = SOME k ∧ i ≤ k)
End

Theorem prounds_mono:
  ∀M N h ws evs logs h' ws' evs' logs'.
    prounds lfd hw ifds m ws0 N = SOME (h, ws, evs, logs) ∧
    prounds lfd hw ifds m ws0 M = SOME (h', ws', evs', logs') ∧ N ≤ M ⇒ evs ≼ evs'
Proof
  Induct >> rw[] >- gvs[] >>
  Cases_on ‘N = SUC M’ >> gvs[] >>
  qpat_x_assum ‘prounds _ _ _ _ _ (SUC M) = _’ mp_tac >>
  simp[prounds_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  ‘evs ≼ evs''’ by (first_x_assum (qspecl_then [‘N’, ‘h’, ‘ws’, ‘evs’, ‘logs’] mp_tac) >> simp[]) >>
  fs[IS_PREFIX_APPEND] >> qexists_tac ‘l ++ revs'’ >> simp[]
QED

Theorem prefix_epolls[local]:
  ∀t es. t ≼ es ∧ EVERY (epoll fes) es ⇒ EVERY (epoll fes) t
Proof
  Induct >> rw[] >> Cases_on ‘es’ >> fs[] >> metis_tac[]
QED

(* The empty polls of an idle segment, replayed *)
Theorem mid_world:
  l0_rely w0 ∧
  binv_at lfd hw ifds bz m w0 ps0 N full xs pevs plogs h w ps evs ∧
  brounds lfd hw ifds bz m (w0, ps0) n = SOME (BRun h (w, ps) evs logs) ∧
  brounds lfd hw ifds bz m (w0, ps0) (SUC n) = SOME (BRun h' (w', ps') evs' logs') ∧
  bidle lfd hw ifds bz m h ps ∧ fes = pf_poll_set lfd hw ps (ifds h) ∧
  sys_pollb fes w = SOME (INL (out, v, ev)) ∧ pollb_wait fes w = SOME k ∧
  LENGTH w.hist + 1 ≤ LENGTH w'.hist ∧
  EVERY (epoll fes) t ∧ LENGTH t ≤ k ⇒
  world_at (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) (pevs ++ t) =
    SOME (lift (btr lfd hw ifds bz m (w0, ps0))
               (w0.hist ++ xs ++ REPLICATE (LENGTH t) (pcall fes))
               (l0_ticks «sys_poll» (LENGTH t) w))
Proof
  strip_tac >>
  mp_tac (Q.INST [‘L’ |-> ‘0’] idle_tr) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[])) >> strip_tac >>
  qpat_assum ‘binv_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE[binv_at_def]) >>
  ‘world_at (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) pevs =
     SOME (lift (btr lfd hw ifds bz m (w0, ps0)) (w0.hist ++ xs) w)’ by metis_tac[pworld] >>
  REWRITE_TAC[world_at_append] >>
  qpat_assum ‘world_at _ pevs = _’ (fn th => REWRITE_TAC[th]) >>
  REWRITE_TAC[optionTheory.OPTION_BIND_def] >> BETA_TAC >>
  qpat_assum ‘EVERY _ t’ (fn th => REWRITE_TAC[MATCH_MP epolls_lcall th]) >>
  ‘poll_ok fes’
    by (irule sys_pollb_ok >> rpt conj_tac >>
        TRY (qexists_tac ‘w’ >>
             qpat_assum ‘sys_pollb _ _ = _’ (fn th => REWRITE_TAC[th, optionTheory.NOT_SOME_NONE]) >>
             NO_TAC) >>
        TRY (qpat_assum ‘fes = _’ SUBST1_TAC >> REWRITE_TAC[pf_poll_set_small] >> NO_TAC) >>
        qpat_assum ‘bidle _ _ _ _ _ _ _’ mp_tac >> qpat_assum ‘fes = _’ SUBST1_TAC >>
        REWRITE_TAC[bidle_def, pf_idle_def] >> rpt strip_tac) >>
  irule replay_idle >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (disj2_tac >> qexists_tac ‘k’ >>
       qpat_assum ‘pollb_wait _ _ = _’ (fn th => REWRITE_TAC[th]) >> first_assum ACCEPT_TAC >> NO_TAC) >>
  rpt strip_tac >> qpat_assum ‘∀j. j ≤ k ⇒ _’ irule >> decide_tac
QED

Theorem binv_at_start:
  binv_at lfd hw ifds bz m w0 ps0 0 [] [] [] [] [] w0 ps0 []
Proof
  simp[binv_at_def, prounds_def, lift_reindex, trs_rules, evrel_rules]
QED

Theorem bpre_round:
  brounds lfd hw ifds bz m ws0 n = SOME (BRun h ws evs logs) ∧ bp ≼ evs ⇒
  bpre lfd hw ifds bz m ws0 bp
Proof
  rw[bpre_def] >> metis_tac[]
QED

(* The induction behind p2b: at each round of the blocking run, the PF
   run's prefixes so far are aligned or inside an idle segment *)
Theorem corr_inv:
  bquiet m ifds bz ∧ l0_rely w0 ⇒
  ∀n h w ps evs logs.
    brounds lfd hw ifds bz m (w0, ps0) n = SOME (BRun h (w, ps) evs logs) ⇒
    ∃N full xs pevs plogs.
      n ≤ N ∧ binv_at lfd hw ifds bz m w0 ps0 N full xs pevs plogs h w ps evs ∧
      ∀pp. pp ≼ pevs ⇒ palign lfd hw ifds bz m w0 ps0 pp ∨ pmid lfd hw ifds bz m w0 ps0 pp
Proof
  strip_tac >> Induct
  >- (rw[brounds_def] >> qexistsl_tac [‘0’, ‘[]’, ‘[]’, ‘[]’, ‘[]’] >>
      simp[binv_at_start] >> rw[] >> disj1_tac >> simp[palign_def] >>
      qexistsl_tac [‘[]’, ‘w’, ‘w.hist’] >>
      simp[world_at_def, l0_replay_def, lift_reindex] >>
      simp[bpre_def] >> disj1_tac >> qexists_tac ‘0’ >> simp[brounds_def]) >>
  rpt strip_tac >> drule brounds_SUC_BRun >> strip_tac >>
  rename1 ‘brounds _ _ _ _ _ _ n = SOME (BRun h0 wsa evs0 logs0)’ >>
  rename1 ‘bround _ _ _ _ _ _ = SOME (BRound snap _ log rvs)’ >>
  PairCases_on ‘wsa’ >>
  first_x_assum (qspecl_then [‘h0’, ‘wsa0’, ‘wsa1’, ‘evs0’, ‘logs0’] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  drule bround_cases >> strip_tac >> gvs[] >>
  RULE_ASSUM_TAC (REWRITE_RULE [GSYM APPEND_ASSOC]) >> REWRITE_TAC[GSYM APPEND_ASSOC]
  >- (drule_all binv_plain >> strip_tac >>
      qexistsl_tac [‘SUC N’, ‘full ++ [ssnap rdy rs]’, ‘xs ++ DROP (LENGTH wsa0.hist) w.hist’,
                    ‘pevs ++ (evs1 ++ tevs)’, ‘plogs ++ [log]’] >>
      conj_tac >- decide_tac >> conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >> drule prefix_append_cases >> strip_tac
      >- (first_x_assum drule >> REWRITE_TAC[]) >>
      disj1_tac >> REWRITE_TAC[palign_def] >>
      qpat_x_assum ‘pp = _’ SUBST_ALL_TAC >>
      drule_all b2p_plain >> strip_tac >>
      qexistsl_tac [‘evs0 ++ t’, ‘wb’, ‘hp’] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (‘evs0 ++ t ≼ evs0 ++ (evs1 ++ tevs)’ by (irule prefix_app >> first_assum ACCEPT_TAC) >>
          metis_tac[bpre_round])
      >> qpat_assum ‘binv_at _ _ _ _ _ _ _ N _ _ _ _ _ _ _ _’
           (strip_assume_tac o REWRITE_RULE[binv_at_def]) >>
      qpat_assum ‘evrel pevs _’ (assume_tac o MATCH_MP evrel_nopoll) >>
      asm_rewrite_tac[nopoll_append]) >>
  drule_all binv_idle >> strip_tac >>
  qabbrev_tac ‘fes = pf_poll_set lfd hw wsa1 (ifds h0)’ >>
  ‘fes = pf_poll_set lfd hw wsa1 (ifds h0)’ by simp[Abbr ‘fes’] >>
  qpat_x_assum ‘binv_at _ _ _ _ _ _ _ (SUC (N + k)) _ _ _ _ _ _ _ _’
    (fn th => assume_tac th >> mp_tac th) >>
  qmatch_goalsub_abbrev_tac ‘binv_at _ _ _ _ _ _ _ _ FULL XS PEVS PLOGS _ _ _ _ ⇒ _’ >>
  strip_tac >>
  qexistsl_tac [‘SUC (N + k)’, ‘FULL’, ‘XS’, ‘PEVS’, ‘PLOGS’] >>
  conj_tac >- decide_tac >> conj_tac >- first_assum ACCEPT_TAC >>
  qunabbrev_tac ‘PEVS’ >> rpt strip_tac >>
  qpat_x_assum ‘pp ≼ _’ (mp_tac o REWRITE_RULE[GSYM APPEND_ASSOC]) >> strip_tac >>
  drule prefix_append_cases >> strip_tac
  >- (first_x_assum drule >> REWRITE_TAC[]) >>
  qpat_x_assum ‘pp = _’ SUBST_ALL_TAC >>
  ‘LENGTH wsa0.hist + 1 ≤ LENGTH w.hist’
    by (qpat_assum ‘bround _ _ _ _ _ _ = _’ (mp_tac o MATCH_MP bround_hgrows) >>
        rw[hgrows_def] >> simp[]) >>
  ‘world_at w0 evs0 = SOME wsa0’ by metis_tac[bworld] >>
  qpat_x_assum ‘t ≼ _’ mp_tac >> REWRITE_TAC[GSYM APPEND_ASSOC] >> strip_tac >>
  drule prefix_append_cases >> strip_tac
  >- (disj2_tac >> REWRITE_TAC[pmid_def] >>
      ‘EVERY (epoll fes) t’
        by (irule prefix_epolls >> qexists_tac ‘es’ >> conj_tac >> first_assum ACCEPT_TAC) >>
      ‘LENGTH t ≤ k’
        by (qpat_assum ‘t ≼ es’ (mp_tac o MATCH_MP IS_PREFIX_LENGTH) >>
            qpat_assum ‘LENGTH es = k’ (fn th => REWRITE_TAC[th])) >>
      mp_tac (Q.INST [‘h’ |-> ‘h0’, ‘w’ |-> ‘wsa0’, ‘ps’ |-> ‘wsa1’, ‘evs’ |-> ‘evs0’,
                      ‘logs’ |-> ‘logs0’, ‘h'’ |-> ‘h0 ++ [ssnap rdy []]’, ‘w'’ |-> ‘w’,
                      ‘ps'’ |-> ‘ps’, ‘evs'’ |-> ‘evs0 ++ ev :: tevs’,
                      ‘logs'’ |-> ‘logs0 ++ [log]’, ‘v’ |-> ‘w2’] mid_world) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
      qexistsl_tac [‘n’, ‘h0’, ‘wsa0’, ‘wsa1’, ‘evs0’, ‘logs0’,
                    ‘w0.hist ++ xs ++ REPLICATE (LENGTH t) (pcall fes)’, ‘LENGTH t’] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (qpat_assum ‘binv_at _ _ _ _ _ _ _ N _ _ _ _ _ _ _ _’
            (strip_assume_tac o REWRITE_RULE[binv_at_def]) >>
          qpat_assum ‘evrel pevs _’ (assume_tac o MATCH_MP evrel_nopoll) >>
          qpat_assum ‘EVERY (epoll _) t’ (assume_tac o MATCH_MP nopoll_epolls) >>
          REWRITE_TAC[nopoll_append] >>
          qpat_assum ‘nopoll pevs = _’ (fn th => REWRITE_TAC[th]) >>
          qpat_assum ‘nopoll t = _’ (fn th => REWRITE_TAC[th, APPEND_NIL]))
      >> disj2_tac >> qexists_tac ‘k’ >>
      qpat_assum ‘fes = _’ (fn th => REWRITE_TAC[GSYM th]) >>
      qpat_assum ‘pollb_wait _ _ = _’ (fn th => REWRITE_TAC[th]) >> first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘t = _’ SUBST_ALL_TAC >>
  qpat_x_assum ‘t' ≼ _’ mp_tac >> qpat_x_assum ‘t' ≠ []’ mp_tac >>
  Cases_on ‘t'’ >> REWRITE_TAC[isPREFIX_THM, NOT_CONS_NIL] >> rpt strip_tac >>
  qpat_x_assum ‘h = _’ SUBST_ALL_TAC >> rename1 ‘tt ≼ tevs’ >>
  disj1_tac >> REWRITE_TAC[palign_def] >>
  drule_all b2p_idle >> strip_tac >>
  qexistsl_tac [‘evs0 ++ ev :: tt’, ‘wb’, ‘hp’] >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (‘evs0 ++ ev :: tt ≼ evs0 ++ ev :: tevs’
        by (irule prefix_app >> REWRITE_TAC[isPREFIX_THM] >> first_assum ACCEPT_TAC) >>
      metis_tac[bpre_round])
  >- (qpat_assum ‘binv_at _ _ _ _ _ _ _ N _ _ _ _ _ _ _ _’
        (strip_assume_tac o REWRITE_RULE[binv_at_def]) >>
      qpat_assum ‘evrel pevs _’ (assume_tac o MATCH_MP evrel_nopoll) >>
      qpat_assum ‘EVERY (epoll _) es’ (assume_tac o MATCH_MP nopoll_epolls) >>
      qpat_assum ‘ev = _’ SUBST1_TAC >>
      ‘∀conf bs l. nopoll (IO_event (ExtCall «sys_poll») conf bs :: l) = nopoll l’
        by simp[nopoll_def, is_poll_def] >>
      pop_assum (fn th => REWRITE_TAC[th, nopoll_append]) >>
      qpat_assum ‘nopoll pevs = _’ (fn th => REWRITE_TAC[th]) >>
      qpat_assum ‘nopoll es = _’ (fn th => REWRITE_TAC[th, APPEND_NIL]))
  >> qpat_x_assum ‘world_at _ (pevs ++ es ++ _) = _’ mp_tac >>
  REWRITE_TAC[GSYM APPEND_ASSOC]
QED
