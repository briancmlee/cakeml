(*
  with_tap, one poll at a time: what the CakeML implementation does.

  with_tap σ δ s0 m, polled with a snapshot w, is with_tap again, of m
  polled with w' (w with the hub's answers to m's first-round queries
  merged in), on the store after the first round (its socket results
  tapped, its queries run):

     with_tap_suspended:
       suspended (with_tap σ δ s0 m) [w] = with_tap σ δ s1 (suspended m [w'])

  So an implementation can keep the store in a closure argument and pass
  it on, round by round.  Also: a finished m gives a finished with_tap,
  and relabelling commutes with with_tap (the tap seeing relabelled
  actions and responses through σ').
*)
Theory asyncWithTapStep
Ancestors
  pair list rich_list arithmetic option asyncCore asyncLevel1 asyncChoose
  asyncTranscript asyncCfActModel asyncM4Relabel asyncM4RelabelDist asyncWithStore
  asyncWithTap
Libs
  BasicProvers

(* (As in KV's asyncWithStoreStep, which is still WIP: own copies.) *)
Definition merged_def:
  merged acts (bs : 'b list) (w : ('e, 'r) snapshot) =
    ((w with results := merge acts w.results bs) : ('e, ('b, 'r) kres) snapshot)
End

Definition kfa_def:
  kfa fa (Sock a) = Sock (fa a) ∧ kfa fa (Kv q) = Kv q
End

Definition kfr_def:
  kfr fr (SockR r) = SockR (fr r) ∧ kfr fr (KvR b) = KvR b
End

(* The first round: the answers, the store after it *)
Definition first_tap_def:
  first_tap σ δ s0 (m : ('e, ('b, 'r) kres) snapshot list -> (('a, 'q) kact, 'x) outcome) w =
    run_tap σ δ s0 (m []).actions w.results
End

Theorem wf_new_actions_CONS[local]:
  wf m ⇒
  new_actions (log_of m) (w :: ih) =
  new_actions (log_of (suspended m [w])) ih
Proof
  strip_tac >>
  ‘∀p. (m []).actions ≼ (m (w :: p)).actions’
    by (rpt strip_tac >> irule wf_actions_grow >> simp[]) >>
  Cases_on ‘ih’ using SNOC_CASES
  >- simp[new_actions_def, log_of_def, suspended_one] >>
  REWRITE_TAC[SNOC_APPEND] >>
  ‘w :: (l ++ [x]) = (w :: l) ++ [x]’ by simp[] >>
  pop_assum SUBST1_TAC >>
  ‘LENGTH (m []).actions ≤ LENGTH (m (w :: l)).actions’
    by metis_tac[IS_PREFIX_LENGTH] >>
  REWRITE_TAC[new_actions_SNOC] >>
  simp[log_of_def, suspended_one, DROP_DROP_T]
QED

(* MAIN: the inner state, one snapshot at a time from the front *)
Theorem tap_state_CONS:
  wf m ⇒
  ∀h. tap_state σ δ s0 m (w :: h) =
        let (bs, s1) = first_tap σ δ s0 m w;
            w' = merged (m []).actions bs w;
            (ih, st) = tap_state σ δ s1 (suspended m [w']) h
        in (w' :: ih, st)
Proof
  strip_tac >> Induct_on ‘h’ using SNOC_INDUCT
  >- (simp[Once tap_state_def, new_actions_NIL, log_of_def, first_tap_def] >>
      rpt (pairarg_tac >> gvs[]) >> simp[merged_def]) >>
  rpt strip_tac >> simp[SNOC_APPEND] >>
  ‘w :: (h ++ [x]) = (w :: h) ++ [x]’ by simp[] >> pop_assum SUBST1_TAC >>
  REWRITE_TAC[tap_state_SNOC] >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[tap_state_SNOC] >> rpt (pairarg_tac >> gvs[]) >>
  drule wf_new_actions_CONS >> strip_tac >> gvs[]
QED

Theorem tap_hist_CONS:
  wf m ⇒
  tap_hist σ δ s0 m (w :: h) =
    merged (m []).actions (FST (first_tap σ δ s0 m w)) w ::
    tap_hist σ δ (SND (first_tap σ δ s0 m w))
      (suspended m [merged (m []).actions (FST (first_tap σ δ s0 m w)) w]) h
Proof
  strip_tac >> simp[tap_hist_def, tap_state_CONS] >>
  rpt (pairarg_tac >> gvs[])
QED

(* MAIN: with_tap, polled once *)
Theorem with_tap_suspended:
  wf m ⇒
  suspended (with_tap σ δ s0 m) [w] =
    with_tap σ δ (SND (first_tap σ δ s0 m w))
      (suspended m [merged (m []).actions (FST (first_tap σ δ s0 m w)) w])
Proof
  strip_tac >> simp[FUN_EQ_THM, suspended_one] >> gen_tac >>
  simp[with_tap_def, tap_hist_CONS] >>
  qmatch_goalsub_abbrev_tac ‘m (w' :: ih)’ >>
  ‘(m []).actions ≼ (m (w' :: ih)).actions’
    by (irule wf_actions_grow >> simp[]) >>
  gvs[IS_PREFIX_APPEND] >>
  simp[suspended_one, DROP_LENGTH_APPEND]
QED

(* MAIN: a finished computation, tapped *)
Theorem with_tap_finished:
  with_tap σ δ s0 (finished A x) = finished (socks A) x
Proof
  simp[FUN_EQ_THM, with_tap_def, finished_def]
QED

Theorem with_tap_first:
  (with_tap σ δ s0 m []).actions = socks (m []).actions ∧
  (with_tap σ δ s0 m []).result = (m []).result
Proof
  simp[with_tap_def]
QED

(* ------------------------------------------------------------------------
   Relabelling commutes with with_tap
   ------------------------------------------------------------------------ *)

Theorem socks_kfa[local]:
  ∀acts. socks (MAP (kfa fa) acts) = MAP fa (socks acts)
Proof
  Induct >> simp[] >> Cases >> simp[kfa_def]
QED

Theorem merge_kfa[local]:
  ∀acts rs ans.
    MAP (kfr fr) (merge (MAP (kfa fa) acts) rs ans) = merge acts (MAP fr rs) ans
Proof
  Induct >> simp[merge_def] >> Cases >> rpt gen_tac >>
  simp[kfa_def, merge_def] >> every_case_tac >> gvs[kfr_def]
QED

Theorem run_tap_kfa[local]:
  (∀st a r. σ' st (fa a) r = σ st a (fr r)) ⇒
  ∀acts st rs. run_tap σ' δ st (MAP (kfa fa) acts) rs = run_tap σ δ st acts (MAP fr rs)
Proof
  strip_tac >> Induct >> simp[run_tap_def] >> Cases >>
  simp[kfa_def, run_tap_def] >> rpt gen_tac >>
  Cases_on ‘rs’ >> simp[]
QED

Theorem tap_state_relabel[local]:
  ∀σ σ' fa fr δ s0 m fe.
  (∀st a r. σ' st (fa a) r = σ st a (fr r)) ⇒
  ∀h. (MAP (snap_map fe (kfr fr))
         (FST (tap_state σ' δ s0 (relabel (kfa fa) (snap_map fe (kfr fr)) m) h)),
       SND (tap_state σ' δ s0 (relabel (kfa fa) (snap_map fe (kfr fr)) m) h)) =
      tap_state σ δ s0 m (MAP (snap_map fe fr) h)
Proof
  rpt gen_tac >> strip_tac >> Induct_on ‘h’ using SNOC_INDUCT >> simp[SNOC_APPEND, tap_state_SNOC] >>
  rpt gen_tac >>
  Cases_on ‘tap_state σ' δ s0 (relabel (kfa fa) (snap_map fe (kfr fr)) m) h’ >>
  gvs[] >> pop_assum (SUBST1_TAC o SYM) >> simp[] >>
  ‘∀acts st rs. run_tap σ' δ st (MAP (kfa fa) acts) rs = run_tap σ δ st acts (MAP fr rs)’
    by (irule run_tap_kfa >> first_assum ACCEPT_TAC) >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[new_actions_relabel] >> fs[asyncM4RelabelDistTheory.snap_map_def] >>
  gvs[merge_kfa, asyncM4RelabelDistTheory.snap_map_def] >>
  REWRITE_TAC[merge_kfa] >> rw[asyncCoreTheory.snapshot_component_equality]
QED

(* MAIN: relabelling commutes with with_tap, the tap σ' seeing what σ
   sees through the relabelling *)
Theorem relabel_with_tap:
  (∀st a r. σ' st (fa a) r = σ st a (fr r)) ⇒
  relabel fa (snap_map fe fr) (with_tap σ δ s0 m) =
  with_tap σ' δ s0 (relabel (kfa fa) (snap_map fe (kfr fr)) m)
Proof
  strip_tac >>
  ‘∀h. (MAP (snap_map fe (kfr fr))
          (FST (tap_state σ' δ s0 (relabel (kfa fa) (snap_map fe (kfr fr)) m) h)),
        SND (tap_state σ' δ s0 (relabel (kfa fa) (snap_map fe (kfr fr)) m) h)) =
       tap_state σ δ s0 m (MAP (snap_map fe fr) h)’
    by (irule tap_state_relabel >> first_assum ACCEPT_TAC) >>
  simp[FUN_EQ_THM, relabel_def, with_tap_def, tap_hist_def] >> gen_tac >>
  first_x_assum (qspec_then ‘x’ mp_tac) >>
  Cases_on ‘tap_state σ δ s0 m (MAP (snap_map fe fr) x)’ >> simp[] >>
  strip_tac >> simp[socks_kfa]
QED
