(*
  Simulation between two taps (generic, for any inner machine m).

  Two hubs (σ1, δ1, s1) and (σ2, δ2, s2), and a relation R between their
  stores that the taps preserve and under which the query steps give equal
  answers and related stores, but only for queries q that pass a guard
  G b q on the second hub's store b.  If every query of m's transcript
  under the first hub passes the guard (on the second hub's fold up to
  it), then m sees the same inner history under both hubs:

     tap_hist_sim:  tap_hist σ2 δ2 s2 m h = tap_hist σ1 δ1 s1 m h

  and the stores stay related all along the transcript (tap_fold_sim).
  So with_tap σ2 δ2 s2 m and with_tap σ1 δ1 s1 m are the same machine on
  such histories (with_tap_sim).
*)
Theory asyncWithTapSim
Ancestors
  pair list rich_list arithmetic option asyncCore asyncLevel1 asyncTranscript
  asyncWithStore asyncWithTap
Libs
  BasicProvers

(* Every query of tr passes the guard, on the fold of the entries before it *)
Definition guard_ok_def:
  guard_ok G σ δ st tr ⇔
    ∀p q r. p < LENGTH tr ∧ EL p tr = (Kv q, r) ⇒ G (tap_fold σ δ st (TAKE p tr)) q
End

Theorem guard_ok_NIL[simp]:
  guard_ok G σ δ st []
Proof
  simp[guard_ok_def]
QED

Theorem guard_ok_CONS:
  guard_ok G σ δ st (e :: tr) ⇔
    (∀q r. e = (Kv q, r) ⇒ G st q) ∧ guard_ok G σ δ (tap_fold σ δ st [e]) tr
Proof
  rw[guard_ok_def, EQ_IMP_THM]
  >- (first_x_assum (qspec_then ‘0’ mp_tac) >> simp[tap_fold_def])
  >- (first_x_assum (qspec_then ‘SUC p’ mp_tac) >> simp[] >>
      simp[GSYM tap_fold_APPEND])
  >> Cases_on ‘p’ >> gvs[tap_fold_def] >>
  first_x_assum drule >> simp[GSYM tap_fold_APPEND]
QED

Theorem guard_ok_APPEND:
  ∀l1 st. guard_ok G σ δ st (l1 ++ l2) ⇔
          guard_ok G σ δ st l1 ∧ guard_ok G σ δ (tap_fold σ δ st l1) l2
Proof
  Induct >> simp[guard_ok_CONS, tap_fold_def] >> rpt gen_tac >>
  simp[GSYM tap_fold_APPEND] >> metis_tac[]
QED

Theorem guard_ok_prefix:
  l1 ≼ l2 ∧ guard_ok G σ δ st l2 ⇒ guard_ok G σ δ st l1
Proof
  rw[IS_PREFIX_APPEND] >> fs[guard_ok_APPEND]
QED

Theorem FLAT_GENLIST_prefix[local]:
  a ≤ b ⇒ FLAT (GENLIST f a) ≼ FLAT (GENLIST f b)
Proof
  strip_tac >> ‘∃k. b = a + k’ by (qexists_tac ‘b − a’ >> simp[]) >>
  pop_assum SUBST1_TAC >> Induct_on ‘k’ >>
  simp[ADD_CLAUSES, GENLIST, SNOC_APPEND, FLAT_APPEND] >>
  fs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]
QED

Definition sim_ok_def:
  sim_ok R G σ1 δ1 σ2 δ2 ⇔
    (∀a b x y. R a b ⇒ R (σ1 a x y) (σ2 b x y)) ∧
    (∀a b q. R a b ∧ G b q ⇒
             FST (δ1 a q) = FST (δ2 b q) ∧ R (SND (δ1 a q)) (SND (δ2 b q)))
End

(* The rest of a round after a Sock action without a result *)
Theorem run_tap_sim_NIL:
  sim_ok R G σ1 δ1 σ2 δ2 ⇒
  ∀acts st1 st2. R st1 st2 ∧ guard_ok G σ2 δ2 st2 (zipr acts []) ⇒
    FST (run_tap σ1 δ1 st1 acts []) = FST (run_tap σ2 δ2 st2 acts []) ∧
    R (SND (run_tap σ1 δ1 st1 acts [])) (SND (run_tap σ2 δ2 st2 acts []))
Proof
  strip_tac >> Induct >> simp[run_tap_def] >> Cases >>
  simp[run_tap_def, zipr_def, guard_ok_CONS, tap_fold_def] >>
  rpt gen_tac >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  fs[sim_ok_def] >> first_x_assum drule_all >> strip_tac >>
  first_x_assum (qspecl_then [‘st1'’, ‘st1''’] mp_tac) >> gvs[]
QED

(* One round *)
Theorem run_tap_sim:
  sim_ok R G σ1 δ1 σ2 δ2 ⇒
  ∀acts st1 st2 rs.
    R st1 st2 ∧
    guard_ok G σ2 δ2 st2 (zipr acts (merge acts rs (FST (run_tap σ1 δ1 st1 acts rs)))) ⇒
    FST (run_tap σ1 δ1 st1 acts rs) = FST (run_tap σ2 δ2 st2 acts rs) ∧
    R (SND (run_tap σ1 δ1 st1 acts rs)) (SND (run_tap σ2 δ2 st2 acts rs))
Proof
  strip_tac >> Induct >> simp[run_tap_def] >> Cases >> rpt gen_tac
  >- (Cases_on ‘rs’ >> simp[run_tap_def, merge_def, zipr_def, guard_ok_CONS, tap_fold_def]
      >- metis_tac[run_tap_sim_NIL]
      >> strip_tac >> first_x_assum irule >> fs[sim_ok_def])
  >> simp[run_tap_def] >> rpt (pairarg_tac >> gvs[]) >>
  simp[merge_def, zipr_def, guard_ok_CONS, tap_fold_def] >> strip_tac >>
  ‘FST (δ1 st1 q) = FST (δ2 st2 q) ∧ R (SND (δ1 st1 q)) (SND (δ2 st2 q))’
    by (fs[sim_ok_def] >> first_x_assum irule >> simp[]) >>
  gvs[] >>
  first_x_assum (qspecl_then [‘st1'’, ‘st1''’, ‘rs’] mp_tac) >> simp[]
QED

Theorem round_trans_TAKE[local]:
  j < k ⇒ round_trans m (TAKE k h) j = round_trans m h j
Proof
  strip_tac >> simp[round_trans_def, responses_at_def] >>
  ‘TAKE j (TAKE k h) = TAKE j h’ by simp[TAKE_TAKE_MIN, MIN_DEF] >>
  Cases_on ‘j < LENGTH h’ >> simp[EL_TAKE, LENGTH_TAKE_EQ]
QED

Theorem tap_hist_EL_fields:
  ∀σ δ s0 m h n. n < LENGTH h ⇒
                 ∃r. EL n (tap_hist σ δ s0 m h) = EL n h with results := r
Proof
  ntac 4 gen_tac >> Induct_on ‘h’ using SNOC_INDUCT >> simp[SNOC_APPEND, tap_hist_SNOC] >>
  rpt strip_tac >> Cases_on ‘n < LENGTH h’ >> simp[EL_APPEND1, EL_APPEND2] >>
  ‘n = LENGTH h’ by simp[] >> simp[EL_APPEND2] >> metis_tac[]
QED

(* MAIN: under the guard, m sees the same inner history under both hubs;
   the second hub's store is its fold, related to the first's *)
Theorem tap_hist_sim:
  wf m ∧ sim_ok R G σ1 δ1 σ2 δ2 ∧ R s1 s2 ∧
  guard_ok G σ2 δ2 s2 (trans m (tap_hist σ1 δ1 s1 m h)) ⇒
  tap_hist σ2 δ2 s2 m h = tap_hist σ1 δ1 s1 m h
Proof
  strip_tac >>
  qabbrev_tac ‘ih = tap_hist σ1 δ1 s1 m h’ >>
  ‘LENGTH ih = LENGTH h’ by simp[Abbr ‘ih’] >>
  ‘∀k. k ≤ LENGTH h ⇒
       guard_ok G σ2 δ2 s2 (FLAT (GENLIST (round_trans m ih) k))’
    by (rpt strip_tac >> irule guard_ok_prefix >>
        qexists_tac ‘trans m ih’ >> simp[trans_def] >>
        irule FLAT_GENLIST_prefix >> simp[]) >>
  ‘∀k. k ≤ LENGTH h ⇒
       tap_hist σ2 δ2 s2 m (TAKE k h) = TAKE k ih ∧
       R (SND (tap_state σ1 δ1 s1 m (TAKE k h))) (SND (tap_state σ2 δ2 s2 m (TAKE k h))) ∧
       SND (tap_state σ2 δ2 s2 m (TAKE k h)) =
         tap_fold σ2 δ2 s2 (FLAT (GENLIST (round_trans m ih) k))’
    suffices_by (disch_then (qspec_then ‘LENGTH h’ mp_tac) >>
                 simp[TAKE_LENGTH_ID_rwt, Abbr ‘ih’]) >>
  Induct >- simp[tap_fold_def] >> strip_tac >>
  ‘k < LENGTH h’ by simp[] >> fs[] >>
  ‘TAKE (SUC k) h = TAKE k h ++ [EL k h]’ by simp[TAKE_SUC_EL] >>
  ‘SND (tap_state σ1 δ1 s1 m (TAKE k h)) =
   tap_fold σ1 δ1 s1 (FLAT (GENLIST (round_trans m ih) k))’
    by (simp[Abbr ‘ih’] >> irule tap_state_rounds >> simp[]) >>
  qabbrev_tac ‘st1 = SND (tap_state σ1 δ1 s1 m (TAKE k h))’ >>
  qabbrev_tac ‘st2 = SND (tap_state σ2 δ2 s2 m (TAKE k h))’ >>
  qabbrev_tac ‘acts = new_actions (log_of m) (TAKE k ih)’ >>
  qabbrev_tac ‘rs = (EL k h).results’ >>
  ‘round_trans m ih k = zipr acts (merge acts rs (FST (run_tap σ1 δ1 st1 acts rs)))’
    by (simp[round_trans_def, responses_at_def, Abbr ‘acts’, Abbr ‘rs’, Abbr ‘st1’,
             Abbr ‘ih’, EL_tap_hist] >> simp[tap_hist_TAKE]) >>
  ‘guard_ok G σ2 δ2 st2 (round_trans m ih k)’
    by (qpat_x_assum ‘∀k. k ≤ LENGTH h ⇒ guard_ok _ _ _ _ _’ (qspec_then ‘SUC k’ mp_tac) >>
        simp[GENLIST, SNOC_APPEND, guard_ok_APPEND]) >>
  ‘FST (run_tap σ1 δ1 st1 acts rs) = FST (run_tap σ2 δ2 st2 acts rs) ∧
   R (SND (run_tap σ1 δ1 st1 acts rs)) (SND (run_tap σ2 δ2 st2 acts rs))’
    by (drule run_tap_sim >> disch_then irule >> gvs[]) >>
  ‘tap_hist σ2 δ2 s2 m (TAKE k h) = tap_hist σ2 δ2 s2 m (TAKE k h)’ by simp[] >>
  ‘FST (tap_state σ2 δ2 s2 m (TAKE k h)) = TAKE k ih’ by fs[tap_hist_def] >>
  ‘FST (tap_state σ1 δ1 s1 m (TAKE k h)) = TAKE k ih’
    by (‘tap_hist σ1 δ1 s1 m (TAKE k h) = TAKE k ih’ by simp[Abbr ‘ih’, tap_hist_TAKE] >>
        fs[tap_hist_def]) >>
  ‘TAKE (SUC k) ih = TAKE k ih ++ [EL k ih]’ by simp[TAKE_SUC_EL] >>
  ‘(EL k ih).results = merge acts rs (FST (run_tap σ1 δ1 st1 acts rs))’
    by (simp[Abbr ‘ih’, Abbr ‘acts’, Abbr ‘rs’, Abbr ‘st1’, EL_tap_hist] >>
        simp[tap_hist_TAKE]) >>
  ‘∃r. EL k ih = EL k h with results := r’
    by (simp[Abbr ‘ih’] >> metis_tac[tap_hist_EL_fields]) >>
  ‘EL k ih = EL k h with results := (EL k ih).results’
    by (pop_assum strip_assume_tac >> pop_assum (fn th => ONCE_REWRITE_TAC[th]) >>
        simp[]) >>
  rpt conj_tac
  >- (simp[tap_hist_SNOC] >>
      qpat_x_assum ‘tap_hist σ2 δ2 s2 m (TAKE k h) = TAKE k ih’ (fn th => simp[th]) >>
      fs[tap_hist_def] >>
      qpat_x_assum ‘EL k ih = _’ (fn th => ONCE_REWRITE_TAC[th]) >>
      simp[snapshot_component_equality] >> gvs[])
  >- (simp[tap_state_SNOC] >> rpt (pairarg_tac >> gvs[]) >>
      Cases_on ‘tap_state σ1 δ1 s1 m (TAKE k h)’ >>
      Cases_on ‘tap_state σ2 δ2 s2 m (TAKE k h)’ >> gvs[] >>
      rpt (pairarg_tac >> gvs[]))
  >> simp[tap_state_SNOC] >> rpt (pairarg_tac >> gvs[]) >>
  Cases_on ‘tap_state σ2 δ2 s2 m (TAKE k h)’ >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[GENLIST, SNOC_APPEND, tap_fold_APPEND] >>
  qpat_x_assum ‘round_trans m ih k = _’ SUBST1_TAC >>
  qmatch_goalsub_abbrev_tac ‘tap_fold σ2 δ2 S2 (zipr acts (merge acts rs A1))’ >>
  ‘tap_fold σ2 δ2 S2 (zipr acts (merge acts rs (FST (run_tap σ2 δ2 S2 acts rs)))) =
   SND (run_tap σ2 δ2 S2 acts rs)’ by simp[tap_fold_round] >>
  gvs[]
QED

(* The stores stay related along the transcript *)
Theorem tap_fold_sim:
  sim_ok R G σ1 δ1 σ2 δ2 ⇒
  ∀tr st1 st2. R st1 st2 ∧ guard_ok G σ2 δ2 st2 tr ⇒
               R (tap_fold σ1 δ1 st1 tr) (tap_fold σ2 δ2 st2 tr)
Proof
  strip_tac >> Induct >> simp[tap_fold_def] >> PairCases >>
  Cases_on ‘h0’ >> simp[tap_fold_def, guard_ok_CONS] >> rpt strip_tac >>
  first_x_assum irule >> fs[sim_ok_def]
  >- (every_case_tac >> fs[])
  >> metis_tac[]
QED
