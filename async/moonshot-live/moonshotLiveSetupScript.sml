(*
  Moonshot liveness, the setup chain: connect_pairs_claim PROVED (the
  kernel's part).  A connect end to a port of `isolated` is eventually lost
  or paired, and its partner is at a process that listened on the port
  (the only one, by topology_ob).

   - step_target / irun_target: an end's target is fixed once it exists
     (only a connect sets one, on its new end);
   - irun_pair_listens: a paired end's partner is at a process that had a
     listener on the end's target port, at some earlier instant
     (Handshake: sys_room; a connect paired at once: likewise, with the
     caller's listeners unchanged by the connect);
   - connect_settles: by kernel fairness (C) the end stops connecting
     unless it is closed; then, unless broken, isolated's last clause pairs
     it.
*)
Theory moonshotLiveSetup
Ancestors
  moonshotLiveObs moonshotLiveStmts moonshotLiveDeliver moonshotLiveDrains moonshotLiveChain moonshotLiveProjInf
  l0sysFair l0sys l0sysCausal l0sysMono l0sysRun l0sysProj honestL0World
Libs
  preamble

(* ------------------------------------------------------------------------
   Targets and ends persist
   ------------------------------------------------------------------------ *)

Theorem step_target:
  sys_step s r s' ∧ is_end s e ⇒ s'.target e = s.target e
Proof
  Cases_on ‘e’ >> Cases_on ‘r’ >> TRY (rename1 ‘Kern kk’ >> Cases_on ‘kk’) >>
  TRY (rename1 ‘Env ee’ >> Cases_on ‘ee’) >>
  simp[sys_step_def, LET_THM] >> rpt strip_tac >>
  gvs[sys_deliver_def, sys_pair_def, LET_THM] >>
  every_case_tac >> gvs[combinTheory.APPLY_UPDATE_THM, is_end_def] >> rw[] >> fs[]
QED

Theorem sys_ext_end:
  sys_ext s s' ∧ is_end s e ⇒ is_end s' e
Proof
  Cases_on ‘e’ >> rw[sys_ext_def, is_end_def] >> res_tac >> fs[wext_def]
QED

Theorem irun_target:
  l0sys_irun ps ss rs ∧ is_end (ss n) e ⇒
  ∀n'. n ≤ n' ⇒ is_end (ss n') e ∧ (ss n').target e = (ss n).target e
Proof
  strip_tac >>
  ‘∀d. is_end (ss (n + d)) e ∧ (ss (n + d)).target e = (ss n).target e’
    suffices_by (rpt strip_tac >> first_x_assum (qspec_then ‘n' − n’ mp_tac) >> simp[]) >>
  Induct >> simp[] >>
  ‘sys_step (ss (n + d)) (rs (n + d)) (ss (SUC (n + d)))’ by fs[l0sys_irun_def] >>
  ‘sys_ext (ss (n + d)) (ss (SUC (n + d)))’ by metis_tac[irun_ext] >>
  ‘n + SUC d = SUC (n + d)’ by simp[] >> pop_assum SUBST1_TAC >>
  metis_tac[sys_ext_end, step_target]
QED

(* ------------------------------------------------------------------------
   Who a connect end is paired with
   ------------------------------------------------------------------------ *)

Theorem room_listens:
  sys_room s k p ⇒ listens_on s k p
Proof
  rw[sys_room_def, listens_on_def] >>
  Cases_on ‘FILTER (λ(l, p', q). p' = p) (EL k s.procs).listeners’ >> fs[] >>
  rename1 ‘FILTER _ _ = h :: t’ >> PairCases_on ‘h’ >>
  ‘MEM (h0, h1, h2) (FILTER (λ(l, p', q). p' = p) (EL k s.procs).listeners)’ by simp[] >>
  fs[MEM_FILTER] >> metis_tac[]
QED

Theorem connect_listeners:
  l0_call «sys_connect» conf bs w = SOME (FFIreturn out w1) ⇒ w1.listeners = w.listeners
Proof
  rw[l0_call_def, l0_connect_def] >> every_case_tac >> gvs[LET_THM, upd_lchan_def]
QED

Theorem listens_on_procs:
  (s'.procs = s.procs ⇒ (listens_on s' k p ⇔ listens_on s k p)) ∧
  ((EL k s'.procs).listeners = (EL k s.procs).listeners ⇒ (listens_on s' k p ⇔ listens_on s k p))
Proof
  simp[listens_on_def]
QED

(* A pair sys_pair makes: on the connect end e0 (the one with the target);
   the reverse end has none, by kinv *)
Theorem pair_new_peer:
  kinv (sys_pair e0 k' p0 s0) ∧ (sys_pair e0 k' p0 s0).peer x = SOME y ∧ s0.peer x ≠ SOME y ∧
  s0.target e0 = SOME p0 ∧ (sys_pair e0 k' p0 s0).target x = SOME p ⇒ FST y = k' ∧ p = p0
Proof
  strip_tac >>
  ‘(sys_pair e0 k' p0 s0).target = s0.target’ by simp[sys_pair_def, sys_deliver_def] >>
  qabbrev_tac ‘e' = (k', LENGTH (EL k' s0.procs).chans)’ >>
  ‘(sys_pair e0 k' p0 s0).peer = (e0 =+ SOME e') ((e' =+ SOME e0) s0.peer)’
    by simp[sys_pair_def, sys_deliver_def, Abbr‘e'’] >>
  Cases_on ‘x = e0’ >- gvs[combinTheory.APPLY_UPDATE_THM, Abbr‘e'’] >>
  ‘x = e' ∧ y = e0’ by (Cases_on ‘x = e'’ >> gvs[combinTheory.APPLY_UPDATE_THM]) >>
  qpat_x_assum ‘kinv _’ mp_tac >> rewrite_tac[kinv_def] >> strip_tac >>
  qpat_x_assum ‘∀e e'. _.peer e = SOME e' ⇒ _’ (qspecl_then [‘x’, ‘y’] mp_tac) >>
  gvs[]
QED

(* A pair the step makes: the partner of a connect end with a target is at
   a process listening on it before the step *)
Theorem step_pair_listens:
  sys_step s r s' ∧ kinv s' ∧ s'.peer e = SOME e' ∧ s.peer e ≠ SOME e' ∧
  s'.target e = SOME p ⇒ listens_on s (FST e') p
Proof
  Cases_on ‘r’ >> TRY (rename1 ‘Kern kk’ >> Cases_on ‘kk’) >>
  TRY (rename1 ‘Env ee’ >> Cases_on ‘ee’) >>
  simp[sys_step_def, LET_THM] >> rpt strip_tac >> gvs[sys_deliver_def]
  (* Call: only a connect paired at once *)
  >~ [‘poll_may_return _ _ _ _’]
  >- (every_case_tac >> gvs[] >>
      rename1 ‘sys_room _ k' _’ >>
      ‘w1.listeners = (EL n s.procs).listeners’ by metis_tac[connect_listeners] >>
      drule pair_new_peer >> disch_then (qspecl_then [‘e'’, ‘e’, ‘p’] mp_tac) >>
      impl_tac
      >- (rpt conj_tac >>
          FIRST [first_assum ACCEPT_TAC, simp[combinTheory.APPLY_UPDATE_THM] >> NO_TAC,
                 simp[] >> first_assum ACCEPT_TAC]) >>
      strip_tac >>
      qpat_x_assum ‘sys_room _ _ _’ (assume_tac o MATCH_MP room_listens) >>
      qpat_x_assum ‘listens_on _ _ _’ mp_tac >>
      qpat_x_assum ‘FST _ = _’ SUBST1_TAC >> qpat_x_assum ‘p = _’ SUBST1_TAC >>
      simp[listens_on_def, EL_LUPDATE] >> IF_CASES_TAC >> simp[] >>
      pop_assum SUBST_ALL_TAC >> asm_rewrite_tac[])
  (* Handshake *)
  >> drule pair_new_peer >> disch_then (qspecl_then [‘e'’, ‘e’, ‘p’] mp_tac) >>
  impl_tac
  >- (rpt conj_tac >>
      FIRST [first_assum ACCEPT_TAC, simp[] >> first_assum ACCEPT_TAC]) >>
  strip_tac >>
  qpat_x_assum ‘sys_room _ _ _’ (assume_tac o MATCH_MP room_listens) >>
  qpat_x_assum ‘FST _ = _’ SUBST1_TAC >> qpat_x_assum ‘p = _’ SUBST1_TAC >>
  first_assum ACCEPT_TAC
QED

Theorem irun_pair_listens:
  l0sys_irun ps ss rs ⇒
  ∀n e e' p. (ss n).peer e = SOME e' ∧ (ss n).target e = SOME p ⇒
             ∃n'. n' ≤ n ∧ listens_on (ss n') (FST e') p
Proof
  strip_tac >> Induct
  >- fs[l0sys_irun_def, sys_init_def] >>
  rpt strip_tac >>
  ‘sys_step (ss n) (rs n) (ss (SUC n))’ by fs[l0sys_irun_def] >>
  ‘kinv (ss n) ∧ kinv (ss (SUC n))’ by metis_tac[irun_kinv] >>
  Cases_on ‘(ss n).peer e = SOME e'’
  >- (‘is_end (ss n) e’ by metis_tac[kinv_peer_end] >>
      ‘(ss (SUC n)).target e = (ss n).target e’ by metis_tac[step_target] >>
      first_x_assum (qspecl_then [‘e’, ‘e'’, ‘p’] mp_tac) >> impl_tac >- fs[] >>
      strip_tac >> qexists_tac ‘n'’ >> simp[]) >>
  qexists_tac ‘n’ >> simp[] >> metis_tac[step_pair_listens]
QED

(* ------------------------------------------------------------------------
   Settlement
   ------------------------------------------------------------------------ *)

Theorem connect_settles:
  l0sys_irun ps ss rs ∧ kernel_fair_obs ss rs ∧ isolated ports ss rs ∧
  is_end (ss n) e ∧ (ss n).target e = SOME p ∧ MEM p ports ⇒
  (∃n'. ended ss e n') ∨ ∃n' e'. (ss n').peer e = SOME e'
Proof
  CCONTR_TAC >> fs[] >>
  ‘∀n'. n ≤ n' ⇒ is_end (ss n') e ∧ (ss n').target e = SOME p’ by metis_tac[irun_target] >>
  ‘∀n'. n ≤ n' ⇒ ¬(sys_chan (ss n') e).closed ∧ ¬(sys_chan (ss n') e).broken’ by
    (rpt strip_tac >> fs[ended_def, frozen_def] >> metis_tac[]) >>
  (* (C): the end stops connecting *)
  ‘∃n1. n ≤ n1 ∧ ¬(sys_chan (ss n1) e).connecting’ by
    (qpat_x_assum ‘kernel_fair_obs _ _’ mp_tac >> rewrite_tac[kernel_fair_obs_def] >>
     strip_tac >> qpat_x_assum ‘∀e n0. ¬∀n. _ ⇒ _ ∧ (sys_chan _ _).connecting ∧ _’
       (qspecl_then [‘e’, ‘n’] mp_tac) >>
     simp[] >> strip_tac >> qexists_tac ‘n'’ >> simp[] >>
     qpat_x_assum ‘∀n'. n ≤ n' ⇒ is_end _ _ ∧ _’ (qspec_then ‘n'’ mp_tac) >>
     qpat_x_assum ‘∀n'. n ≤ n' ⇒ ¬_.closed ∧ _’ (qspec_then ‘n'’ mp_tac) >>
     simp[]) >>
  ‘n1 ≠ 0’ by
    (strip_tac >> gvs[] >> ‘(ss 0).target = K NONE’ by fs[l0sys_irun_def, sys_init_def] >>
     qpat_x_assum ‘∀n'. is_end _ _ ∧ _’ (qspec_then ‘0’ mp_tac) >> simp[]) >>
  Cases_on ‘n1’ >> fs[] >> rename1 ‘ss (SUC n2)’ >>
  Cases_on ‘e’ >>
  qpat_x_assum ‘isolated _ _ _’ mp_tac >> rewrite_tac[isolated_def] >>
  disch_then (qspec_then ‘n2’ (strip_assume_tac o CONJUNCT2 o CONJUNCT2)) >>
  pop_assum (qspecl_then [‘q’, ‘r’, ‘p’] mp_tac) >> simp[] >>
  Cases_on ‘(ss (SUC n2)).peer (q, r)’ >> fs[] >> metis_tac[]
QED

Theorem connect_pairs:
  connect_pairs_claim
Proof
  rw[connect_pairs_claim_def] >> rename1 ‘l0sys_irun ps _ _’ >>
  drule_all connect_settles >> strip_tac >- (disj1_tac >> metis_tac[]) >>
  disj2_tac >>
  (* at N = MAX n n': still paired, still the target p *)
  qabbrev_tac ‘N = MAX n n'’ >>
  ‘n ≤ N ∧ n' ≤ N’ by simp[Abbr‘N’] >>
  ‘(ss N).peer e = SOME e'’ by metis_tac[irun_mono] >>
  ‘(ss N).target e = SOME p’ by metis_tac[irun_target] >>
  drule irun_pair_listens >> disch_then drule_all >> strip_tac >>
  ‘is_end (ss N) e'’ by metis_tac[kinv_peer_end, irun_kinv] >>
  ‘LENGTH (ss N).procs = LENGTH ps’ by metis_tac[irun_procs_length] >>
  Cases_on ‘e'’ >> ‘q < LENGTH ps’ by fs[is_end_def] >>
  ‘q = k0’ by metis_tac[FST] >> metis_tac[]
QED
