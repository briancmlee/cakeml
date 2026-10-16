(*
  L3-09 (S3): replaying calls (honestL0Part's l0_replay, which the raw-trace
  statements read through world_at) in the lifted world.

  - lift_replay: where tr extends by identity along the calls, replaying
    them in the lifted world is the lifted replay.
  - replay_idle, replay_wake: the PF run's empty polls, replayed in the
    lifted world, are the blocking poll's steps of time; the last one is
    the blocking poll.

  MAIN: lift_replay, replay_idle, replay_wake.
*)
Theory honestL1BReplay
Ancestors
  honestL1BSim honestL1BModel honestL1BLift honestL1BPoll honestL1BHist honestL0Reindex honestL0Part
  honestL1PFRound honestL1Model honestL0World honestL0
Libs
  preamble

Theorem FOLDL_step_NONE[simp]:
  ∀cs. FOLDL l0_step NONE cs = NONE
Proof
  Induct >> simp[l0_step_def]
QED

Theorem lift_step:
  tr hp = w.hist ⇒
  l0_step (SOME (lift tr hp w)) c =
    OPTION_MAP (lift tr (hp ++ [c])) (l0_step (SOME w) c)
Proof
  PairCases_on ‘c’ >> strip_tac >>
  simp[l0_step_def] >> drule_then (fn th => simp[th]) lift_ffi_fn_call >>
  simp[l0_ffi_fn_def] >>
  Cases_on ‘l0_call c0 c1 c2 (l0_tick c0 w)’ >> simp[lift_res_def] >>
  rename1 ‘SOME r’ >> Cases_on ‘r’ >> simp[lift_res_def]
QED

(* MAIN *)
Theorem lift_replay:
  ∀cs hp w. tr_from tr hp w.hist (LENGTH cs) ⇒
    FOLDL l0_step (SOME (lift tr hp w)) cs =
    OPTION_MAP (lift tr (hp ++ cs)) (FOLDL l0_step (SOME w) cs)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  ‘tr hp = w.hist’ by (irule tr_from_hist >> metis_tac[]) >>
  drule lift_step >> disch_then (qspec_then ‘h’ SUBST1_TAC) >>
  Cases_on ‘l0_step (SOME w) h’ >> simp[] >>
  rename1 ‘l0_step _ _ = SOME w1’ >>
  ‘w1.hist = w.hist ++ [h]’
    by (PairCases_on ‘h’ >> gvs[l0_step_def, l0_ffi_fn_def, AllCaseEqs()]) >>
  first_x_assum (qspecl_then [‘hp ++ [h]’, ‘w1’] mp_tac) >>
  impl_tac
  >- (gvs[tr_from_def] >> rpt strip_tac >>
      first_x_assum (qspec_then ‘h :: cs'’ mp_tac) >> simp[] >>
      REWRITE_TAC[GSYM APPEND_ASSOC, APPEND]) >>
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

Theorem sys_poll_step:
  sys_poll fes w = SOME (out, w', ev) ⇒ l0_step (SOME w) (pcall fes) = SOME w'
Proof
  rw[sys_poll_def] >> drule l0_do_cases >> rw[] >>
  fs[l0_step_def, l0_ffi_fn_def]
QED

(* MAIN: the empty polls, replayed in the lifted world *)
Theorem replay_idle:
  ∀i. poll_ok fes ∧
      (pollb_wait fes u = NONE ∨ ∃k. pollb_wait fes u = SOME k ∧ i ≤ k) ∧
      (∀j. j ≤ i ⇒ tr (hp ++ REPLICATE j (pcall fes)) = u.hist) ⇒
      FOLDL l0_step (SOME (lift tr hp u)) (REPLICATE i (pcall fes)) =
        SOME (lift tr (hp ++ REPLICATE i (pcall fes)) (l0_ticks «sys_poll» i u))
Proof
  Induct >- simp[l0_ticks_def] >>
  rpt gen_tac >> strip_tac >>
  ‘FOLDL l0_step (SOME (lift tr hp u)) (REPLICATE i (pcall fes)) =
     SOME (lift tr (hp ++ REPLICATE i (pcall fes)) (l0_ticks «sys_poll» i u))’
    by (first_x_assum irule >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        TRY (rpt strip_tac >> qpat_assum ‘∀j. j ≤ SUC i ⇒ _’ irule >> decide_tac >> NO_TAC) >>
        TRY (disj1_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
        disj2_tac >> qexists_tac ‘k’ >> asm_rewrite_tac[] >> decide_tac) >>
  drule sys_poll_idle >> disch_then (qspecl_then [‘u’, ‘i’] mp_tac) >>
  (impl_tac >- (TRY (disj1_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
                disj2_tac >> qexists_tac ‘k’ >> asm_rewrite_tac[] >> decide_tac)) >>
  strip_tac >>
  REWRITE_TAC[GSYM SNOC_REPLICATE, FOLDL_SNOC] >>
  qpat_x_assum ‘FOLDL _ _ (REPLICATE i _) = _’ SUBST1_TAC >>
  ‘tr (hp ++ REPLICATE i (pcall fes)) = (l0_ticks «sys_poll» i u).hist’
    by (REWRITE_TAC[ticks_hist_ch] >> qpat_assum ‘∀j. j ≤ SUC i ⇒ _’ irule >> decide_tac) >>
  drule lift_step >> disch_then (qspec_then ‘pcall fes’ SUBST1_TAC) >>
  drule sys_poll_step >> disch_then SUBST1_TAC >>
  REWRITE_TAC[optionTheory.OPTION_MAP_DEF, lift_hist, SNOC_APPEND, APPEND_ASSOC]
QED

(* The blocking poll, replayed in the real world *)
Theorem sys_pollb_step:
  sys_pollb fes u = SOME (INL (out, v, ev)) ⇒
  l0_step (SOME u) (unblk (pcall fes)) = SOME v
Proof
  rw[sys_pollb_def, AllCaseEqs(), unblk_pcall] >> fs[l0_step_def]
QED

(* MAIN: the k empty polls and the one that finds what the blocking poll
   found, replayed in the lifted world, end in the blocking poll's world *)
Theorem replay_wake:
  poll_ok fes ∧ pollb_wait fes u = SOME k ∧ sys_pollb fes u = SOME (INL (out, v, ev)) ∧
  (∀j. j ≤ k ⇒ tr (hp ++ REPLICATE j (pcall fes)) = u.hist) ⇒
  FOLDL l0_step (SOME (lift tr hp u)) (REPLICATE (SUC k) (pcall fes)) =
    SOME (lift tr (hp ++ REPLICATE (SUC k) (pcall fes)) v)
Proof
  strip_tac >>
  ‘FOLDL l0_step (SOME (lift tr hp u)) (REPLICATE k (pcall fes)) =
     SOME (lift tr (hp ++ REPLICATE k (pcall fes)) (l0_ticks «sys_poll» k u))’
    by (irule replay_idle >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        disj2_tac >> qexists_tac ‘k’ >> asm_rewrite_tac[LESS_EQ_REFL]) >>
  drule (cj 2 sys_pollb_wait) >> disch_then drule >> strip_tac >>
  qpat_x_assum ‘sys_pollb _ _ = SOME (INL (out', _, _))’ mp_tac >>
  qpat_assum ‘sys_pollb _ _ = SOME (INL (out, _, _))’ (fn th => REWRITE_TAC[th]) >>
  REWRITE_TAC[optionTheory.SOME_11, sumTheory.INR_INL_11, PAIR_EQ] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  REWRITE_TAC[GSYM SNOC_REPLICATE, FOLDL_SNOC] >>
  qpat_x_assum ‘FOLDL _ _ (REPLICATE k _) = _’ SUBST1_TAC >>
  ‘tr (hp ++ REPLICATE k (pcall fes)) = (l0_ticks «sys_poll» k u).hist’
    by (REWRITE_TAC[ticks_hist_ch] >> qpat_assum ‘∀j. j ≤ k ⇒ _’ irule >> REWRITE_TAC[LESS_EQ_REFL]) >>
  drule lift_step >> disch_then (qspec_then ‘pcall fes’ SUBST1_TAC) >>
  qpat_assum ‘sys_poll _ _ = _’ (fn th => REWRITE_TAC[MATCH_MP sys_poll_step th]) >>
  REWRITE_TAC[optionTheory.OPTION_MAP_DEF, lift_hist, SNOC_APPEND, APPEND_ASSOC]
QED
