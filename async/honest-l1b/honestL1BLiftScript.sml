(*
  L3-09 (S2): the PF L1's steps in a lifted world (honestL0Reindex).
  Where the translation tr is the identity extension for the step's calls
  (tr_from tr hp H L: tr (hp ++ cs) = H ++ cs for up to L calls cs), every
  L1 step (the actions, the polls, the flush, the fetch, the reap, the
  tail) in the lifted world lift tr hp w is the step in w, lifted: the same
  results and events, and the lifted world records the same calls.

  MAIN: lift_pacts, lift_tail, lift_after.
*)
Theory honestL1BLift
Ancestors
  honestL1BHist honestL1BPoll honestL1BModel honestL0Reindex honestL1PFRound
  honestL1PFModel honestL1Model honestL0World honestL0
Libs
  preamble

Definition tr_from_def:
  tr_from tr hp H L ⇔ ∀cs. LENGTH cs ≤ L ⇒ tr (hp ++ cs) = H ++ cs
End

Theorem tr_from_hist:
  tr_from tr hp H L ⇒ tr hp = H
Proof
  rw[tr_from_def] >> first_x_assum (qspec_then ‘[]’ mp_tac) >> simp[]
QED

Theorem tr_from_mono:
  tr_from tr hp H L ∧ L' ≤ L ⇒ tr_from tr hp H L'
Proof
  rw[tr_from_def]
QED

Theorem tr_from_step:
  ∀w w1 a tr hp b.
  hgrows w w1 a ∧ tr_from tr hp w.hist (a + b) ⇒
  tr_from tr (hp ++ DROP (LENGTH w.hist) w1.hist) w1.hist b
Proof
  rpt gen_tac >> rw[hgrows_def, tr_from_def] >> simp[DROP_LENGTH_APPEND] >>
  first_x_assum (qspec_then ‘cs ++ cs'’ mp_tac) >> simp[]
QED

Theorem drop_step:
  ∀w w1 w2 a b hp.
  hgrows w w1 a ∧ hgrows w1 w2 b ⇒
  hp ++ DROP (LENGTH w.hist) w1.hist ++ DROP (LENGTH w1.hist) w2.hist =
  hp ++ DROP (LENGTH w.hist) w2.hist
Proof
  rpt gen_tac >> rw[hgrows_def] >> REWRITE_TAC[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND] >>
  ‘LENGTH cs + LENGTH w.hist = LENGTH (w.hist ++ cs)’ by simp[] >>
  pop_assum SUBST1_TAC >> REWRITE_TAC[APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  REWRITE_TAC[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND]
QED

(* Two steps in sequence: what the second step needs, and how the
   histories compose *)
Theorem lift_seq:
  ∀w w1 w2 a b tr hp.
  hgrows w w1 a ∧ hgrows w1 w2 b ∧ tr_from tr hp w.hist (a + b) ⇒
  tr_from tr (hp ++ DROP (LENGTH w.hist) w1.hist) w1.hist b ∧
  hp ++ DROP (LENGTH w.hist) w2.hist =
  hp ++ DROP (LENGTH w.hist) w1.hist ++ DROP (LENGTH w1.hist) w2.hist
Proof
  rpt strip_tac >- metis_tac[tr_from_step] >> metis_tac[drop_step]
QED

Theorem drop_refl[simp]:
  hp ++ DROP (LENGTH (w : l0world).hist) w.hist = hp
Proof
  simp[DROP_LENGTH_NIL]
QED

(* ------------------------------------------------------------------------
   One call
   ------------------------------------------------------------------------ *)

Theorem lift_do_from:
  l0_do n conf alen w = SOME (out, w', ev) ∧ tr_from tr hp w.hist L ⇒
  l0_do n conf alen (lift tr hp w) =
    SOME (out, lift tr (hp ++ DROP (LENGTH w.hist) w'.hist) w', ev)
Proof
  strip_tac >> imp_res_tac tr_from_hist >> drule lift_do >> simp[] >> strip_tac >>
  drule l0_do_cases >> strip_tac >> gvs[DROP_LENGTH_APPEND]
QED

Theorem lift_sys:
  (tr_from tr hp w.hist L ∧ sys_accept l w = SOME (out, w', ev) ⇒
     sys_accept l (lift tr hp w) = SOME (out, lift tr (hp ++ DROP (LENGTH w.hist) w'.hist) w', ev)) ∧
  (tr_from tr hp w.hist L ∧ sys_recv f k w = SOME (out, w', ev) ⇒
     sys_recv f k (lift tr hp w) = SOME (out, lift tr (hp ++ DROP (LENGTH w.hist) w'.hist) w', ev)) ∧
  (tr_from tr hp w.hist L ∧ sys_send f bs w = SOME (out, w', ev) ⇒
     sys_send f bs (lift tr hp w) = SOME (out, lift tr (hp ++ DROP (LENGTH w.hist) w'.hist) w', ev)) ∧
  (tr_from tr hp w.hist L ∧ sys_close f w = SOME (out, w', ev) ⇒
     sys_close f (lift tr hp w) = SOME (out, lift tr (hp ++ DROP (LENGTH w.hist) w'.hist) w', ev)) ∧
  (tr_from tr hp w.hist L ∧ sys_poll fes w = SOME (out, w', ev) ⇒
     sys_poll fes (lift tr hp w) = SOME (out, lift tr (hp ++ DROP (LENGTH w.hist) w'.hist) w', ev))
Proof
  rw[sys_accept_def, sys_recv_def, sys_send_def, sys_close_def, sys_poll_def] >>
  drule_all lift_do_from >> simp[]
QED

(* ------------------------------------------------------------------------
   The steps
   ------------------------------------------------------------------------ *)

Theorem lift_close:
  l1_close f (w, st) = SOME ((w', st'), evs) ∧ tr_from tr hp w.hist (LENGTH evs) ⇒
  l1_close f (lift tr hp w, st) =
    SOME ((lift tr (hp ++ DROP (LENGTH w.hist) w'.hist) w', st'), evs)
Proof
  rw[l1_close_def, AllCaseEqs()] >> TRY (PairCases_on ‘v’) >> gvs[] >>
  drule_all (cj 4 lift_sys) >> simp[]
QED

Theorem lift_flush:
  ∀fs w st w' st' evs hp.
    l1_flush fs (w, st) = SOME ((w', st'), evs) ∧ tr_from tr hp w.hist (LENGTH evs) ⇒
    l1_flush fs (lift tr hp w, st) =
      SOME ((lift tr (hp ++ DROP (LENGTH w.hist) w'.hist) w', st'), evs)
Proof
  Induct >> rw[l1_flush_def, AllCaseEqs()] >> gvs[] >>
  imp_res_tac hgrows_sys >> imp_res_tac hgrows_flush >>
  drule_all (cj 3 lift_sys) >> strip_tac >> simp[] >>
  qspecl_then [‘w’, ‘w''’, ‘w'’, ‘1’, ‘LENGTH evs'’, ‘tr’, ‘hp’] mp_tac lift_seq >>
  (impl_tac >- fs[ADD1]) >> strip_tac >> simp[]
QED

Theorem lift_reap:
  ∀fs w st w' st' evs hp.
    l1_reap fs (w, st) = SOME ((w', st'), evs) ∧ tr_from tr hp w.hist (LENGTH evs) ⇒
    l1_reap fs (lift tr hp w, st) =
      SOME ((lift tr (hp ++ DROP (LENGTH w.hist) w'.hist) w', st'), evs)
Proof
  Induct >> rw[l1_reap_def, AllCaseEqs()] >> gvs[] >>
  rename1 ‘l1_close _ _ = SOME (ws1, evs1)’ >> PairCases_on ‘ws1’ >>
  rename1 ‘l1_reap _ _ = SOME ((w2, st2), evs2)’ >>
  imp_res_tac hgrows_close >> imp_res_tac hgrows_reap >>
  qspecl_then [‘w’, ‘ws10’, ‘w2’, ‘LENGTH evs1’, ‘LENGTH evs2’, ‘tr’, ‘hp’] mp_tac lift_seq >>
  (impl_tac >- fs[]) >> strip_tac >>
  ‘tr_from tr hp w.hist (LENGTH evs1)’ by (irule tr_from_mono >> qexists_tac ‘LENGTH evs1 + LENGTH evs2’ >> fs[]) >>
  drule_all lift_close >> strip_tac >> simp[]
QED

Theorem lift_polls:
  ∀chs w rv w' evs hp.
    l1_polls chs w = SOME (rv, w', evs) ∧ tr_from tr hp w.hist (LENGTH evs) ⇒
    l1_polls chs (lift tr hp w) = SOME (rv, lift tr (hp ++ DROP (LENGTH w.hist) w'.hist) w', evs)
Proof
  Induct >> rw[l1_polls_def, AllCaseEqs()] >> gvs[] >>
  rename1 ‘l1_polls _ w1 = SOME (rv2, w2, evs2)’ >>
  imp_res_tac hgrows_sys >> imp_res_tac hgrows_polls >>
  qspecl_then [‘w’, ‘w1’, ‘w2’, ‘1’, ‘LENGTH evs2’, ‘tr’, ‘hp’] mp_tac lift_seq >>
  (impl_tac >- fs[ADD1]) >> strip_tac >>
  drule_all (cj 5 lift_sys) >> strip_tac >> simp[]
QED

Theorem lift_fetch:
  ∀fs w ps w' ps' log evs hp.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ∧ tr_from tr hp w.hist (LENGTH evs) ⇒
    pf_fetch lfd hw fs (lift tr hp w, ps) =
      SOME ((lift tr (hp ++ DROP (LENGTH w.hist) w'.hist) w', ps'), log, evs)
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[] >> TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> pairarg_tac >> gvs[] >>
  qpat_x_assum ‘_ = (ps1, fl)’ (fn th => fs[th] >> assume_tac th) >> gvs[AllCaseEqs()] >>
  imp_res_tac hgrows_sys >> imp_res_tac hgrows_fetch >>
  rename1 ‘pf_fetch _ _ _ (w1, _) = SOME ((w', ps'), log', evs')’ >>
  qspecl_then [‘w’, ‘w1’, ‘w'’, ‘1’, ‘LENGTH evs'’, ‘tr’, ‘hp’] mp_tac lift_seq >>
  (impl_tac >- (simp[] >> qpat_x_assum ‘tr_from _ _ _ (SUC _)’ mp_tac >> simp[ADD1])) >>
  strip_tac >>
  TRY (drule_all (cj 1 lift_sys) >> strip_tac) >>
  TRY (drule_all (cj 2 lift_sys) >> strip_tac) >> simp[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem lift_l1do:
  l1do lfd (w, st) a = SOME (r, (w', st'), evs) ∧ tr_from tr hp w.hist (LENGTH evs) ⇒
  l1do lfd (lift tr hp w, st) a =
    SOME (r, (lift tr (hp ++ DROP (LENGTH w.hist) w'.hist) w', st'), evs)
Proof
  Cases_on ‘a’ >> rw[l1do_def, AllCaseEqs()] >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac hgrows_sys >> imp_res_tac hgrows_close >> gvs[] >>
  TRY (drule_all (cj 1 lift_sys) >> strip_tac >> simp[] >> NO_TAC) >>
  TRY (drule_all (cj 3 lift_sys) >> strip_tac >> simp[] >> NO_TAC) >>
  TRY (drule_all lift_close >> strip_tac >> simp[] >> NO_TAC) >>
  TRY (drule_all (cj 2 lift_sys) >> strip_tac >> simp[] >> NO_TAC) >>
  drule_all (cj 2 lift_sys) >> strip_tac >> simp[] >>
  qspecl_then [‘w’, ‘w''’, ‘w'’, ‘1’, ‘LENGTH evs'’, ‘tr’, ‘hp’] mp_tac lift_seq >>
  (impl_tac >- fs[ADD1]) >> strip_tac >>
  drule_all lift_close >> strip_tac >> simp[]
QED

Theorem lift_pdo:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ tr_from tr hp w.hist (LENGTH evs) ⇒
  pdo lfd (lift tr hp w, ps) a =
    SOME (r, (lift tr (hp ++ DROP (LENGTH w.hist) w'.hist) w', ps'), evs)
Proof
  Cases_on ‘a’ >> rw[pdo_def, AllCaseEqs()] >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  TRY (drule_all lift_close >> strip_tac >> simp[] >> NO_TAC) >>
  drule_all lift_l1do >> simp[]
QED

(* MAIN: the actions *)
Theorem lift_pacts:
  ∀acts w ps rs evs w' ps' hp.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ tr_from tr hp w.hist (LENGTH evs) ⇒
    pacts lfd (lift tr hp w, ps) acts =
      SOME (rs, evs, (lift tr (hp ++ DROP (LENGTH w.hist) w'.hist) w', ps'))
Proof
  Induct >> rw[pacts_def, AllCaseEqs()] >> gvs[] >>
  rename1 ‘pdo _ _ _ = SOME (r1, ws1, evs1)’ >> PairCases_on ‘ws1’ >>
  rename1 ‘pacts _ _ _ = SOME (rs2, evs2, w2, ps2)’ >>
  imp_res_tac hgrows_pdo >> imp_res_tac hgrows_pacts >>
  qspecl_then [‘w’, ‘ws10’, ‘w2’, ‘LENGTH evs1’, ‘LENGTH evs2’, ‘tr’, ‘hp’] mp_tac lift_seq >>
  (impl_tac >- fs[]) >> strip_tac >>
  ‘tr_from tr hp w.hist (LENGTH evs1)’ by (irule tr_from_mono >> qexists_tac ‘LENGTH evs1 + LENGTH evs2’ >> fs[]) >>
  drule_all lift_pdo >> strip_tac >> simp[]
QED

(* MAIN: the tail after the poll *)
Theorem lift_after:
  pf_after lfd hw hs ps fes (rv, w1, pevs) = SOME (rdy, (w', ps'), log, evs) ∧
  tr_from tr hp w1.hist (LENGTH evs − LENGTH pevs) ⇒
  pf_after lfd hw hs ps fes (rv, lift tr hp w1, pevs) =
    SOME (rdy, (lift tr (hp ++ DROP (LENGTH w1.hist) w'.hist) w', ps'), log, evs)
Proof
  rw[pf_after_def, AllCaseEqs()] >> gvs[] >>
  imp_res_tac hgrows_flush >> imp_res_tac hgrows_fetch >> imp_res_tac hgrows_reap >>
  ‘hgrows w2 w' (LENGTH gevs + LENGTH cevs)’ by metis_tac[hgrows_trans] >>
  qspecl_then [‘w1’, ‘w2’, ‘w'’, ‘LENGTH fevs’, ‘LENGTH gevs + LENGTH cevs’, ‘tr’, ‘hp’]
    mp_tac lift_seq >> (impl_tac >- fs[]) >> strip_tac >>
  qspecl_then [‘w2’, ‘w3’, ‘w'’, ‘LENGTH gevs’, ‘LENGTH cevs’, ‘tr’,
               ‘hp ++ DROP (LENGTH w1.hist) w2.hist’] mp_tac lift_seq >>
  (impl_tac >- fs[]) >> strip_tac >>
  ‘tr_from tr hp w1.hist (LENGTH fevs)’ by (irule tr_from_mono >> goal_assum (drule_at Any) >> fs[]) >>
  drule_all lift_flush >> strip_tac >>
  ‘tr_from tr (hp ++ DROP (LENGTH w1.hist) w2.hist) w2.hist (LENGTH gevs)’
    by (irule tr_from_mono >> goal_assum (drule_at Any) >> fs[]) >>
  drule_all lift_fetch >> strip_tac >>
  drule_all lift_reap >> strip_tac >> gvs[]
QED

(* MAIN: the round's tail *)
Theorem lift_tail:
  pf_tail lfd hw hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ∧
  tr_from tr hp w.hist (LENGTH evs) ⇒
  pf_tail lfd hw hs (lift tr hp w, ps) =
    SOME (rdy, (lift tr (hp ++ DROP (LENGTH w.hist) w'.hist) w', ps'), log, evs)
Proof
  simp[pf_tail_after, AllCaseEqs()] >> strip_tac >>
  rename1 ‘l1_polls _ w = SOME vv’ >> PairCases_on ‘vv’ >> gvs[] >>
  rename1 ‘l1_polls _ w = SOME (rv, w1, pevs)’ >>
  imp_res_tac hgrows_polls >> drule hgrows_after >> strip_tac >>
  qspecl_then [‘w’, ‘w1’, ‘w'’, ‘LENGTH pevs’, ‘k’, ‘tr’, ‘hp’] mp_tac lift_seq >>
  (impl_tac >- fs[]) >> strip_tac >>
  ‘tr_from tr hp w.hist (LENGTH pevs)’ by (irule tr_from_mono >> goal_assum (drule_at Any) >> fs[]) >>
  drule_all lift_polls >> strip_tac >> simp[] >>
  ‘tr_from tr (hp ++ DROP (LENGTH w.hist) w1.hist) w1.hist (LENGTH evs − LENGTH pevs)’ by simp[] >>
  drule_all lift_after >> simp[]
QED
