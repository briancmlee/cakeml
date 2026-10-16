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
