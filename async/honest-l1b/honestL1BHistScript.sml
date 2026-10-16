(*
  L3-09: the world's history grows by one call per event.  Every L1 step
  (the actions, the polls, the flush, the fetch, the reap) and every
  blocking round extends the world's history by as many calls as it has
  events, and a round has at least one (its poll).  So the history after
  a round determines the round: the refinement (S2) uses this to read the
  blocking run's waits off the history.

  MAIN: bround_hgrows.
*)
Theory honestL1BHist
Ancestors
  honestL1BModel honestL1BPoll honestL1PFRound honestL1PFModel honestL1Model
  honestL0World honestL0
Libs
  preamble

Definition hgrows_def:
  hgrows (w : l0world) (w' : l0world) k ⇔ ∃cs. w'.hist = w.hist ++ cs ∧ LENGTH cs = k
End

Theorem hgrows_refl[simp]:
  hgrows w w 0
Proof
  simp[hgrows_def]
QED

Theorem hgrows_trans:
  hgrows w1 w2 a ∧ hgrows w2 w3 b ⇒ hgrows w1 w3 (a + b)
Proof
  rw[hgrows_def] >> simp[]
QED

Theorem hgrows_do:
  l0_do n conf alen w = SOME (out, w', ev) ⇒ hgrows w w' 1
Proof
  strip_tac >> drule l0_do_cases >> rw[hgrows_def] >> simp[]
QED

Theorem hgrows_sys:
  (sys_accept l w = SOME (out, w', ev) ⇒ hgrows w w' 1) ∧
  (sys_recv f k w = SOME (out, w', ev) ⇒ hgrows w w' 1) ∧
  (sys_send f bs w = SOME (out, w', ev) ⇒ hgrows w w' 1) ∧
  (sys_close f w = SOME (out, w', ev) ⇒ hgrows w w' 1) ∧
  (sys_poll fes w = SOME (out, w', ev) ⇒ hgrows w w' 1)
Proof
  rw[sys_accept_def, sys_recv_def, sys_send_def, sys_close_def, sys_poll_def] >>
  metis_tac[hgrows_do]
QED

Theorem hgrows_close:
  l1_close f (w, st) = SOME ((w', st'), evs) ⇒ hgrows w w' (LENGTH evs)
Proof
  rw[l1_close_def, AllCaseEqs()] >> TRY (PairCases_on ‘v’) >> gvs[] >>
  metis_tac[hgrows_sys]
QED

Theorem hgrows_l1do:
  l1do lfd (w, st) a = SOME (r, (w', st'), evs) ⇒ hgrows w w' (LENGTH evs)
Proof
  Cases_on ‘a’ >> rw[l1do_def, AllCaseEqs()] >> gvs[] >>
  TRY (PairCases_on ‘v’) >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac hgrows_sys >> imp_res_tac hgrows_close >> gvs[] >>
  TRY (drule_all hgrows_trans >> simp[ADD1] >> NO_TAC) >>
  metis_tac[hgrows_trans, ADD1, ADD_COMM]
QED

Theorem hgrows_pdo:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ⇒ hgrows w w' (LENGTH evs)
Proof
  Cases_on ‘a’ >> rw[pdo_def, AllCaseEqs()] >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac hgrows_close >> imp_res_tac hgrows_l1do >> gvs[]
QED

Theorem hgrows_pacts:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ⇒ hgrows w w' (LENGTH evs)
Proof
  Induct >> rw[pacts_def, AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  res_tac >> imp_res_tac hgrows_pdo >>
  drule_all hgrows_trans >> simp[]
QED

Theorem hgrows_polls:
  ∀chs w rv w' evs. l1_polls chs w = SOME (rv, w', evs) ⇒ hgrows w w' (LENGTH evs)
Proof
  Induct >> rw[l1_polls_def, AllCaseEqs()] >>
  res_tac >> imp_res_tac hgrows_sys >>
  drule_all hgrows_trans >> simp[ADD1]
QED

Theorem hgrows_flush:
  ∀fs w st w' st' evs. l1_flush fs (w, st) = SOME ((w', st'), evs) ⇒ hgrows w w' (LENGTH evs)
Proof
  Induct >> rw[l1_flush_def, AllCaseEqs()] >> res_tac >> imp_res_tac hgrows_sys >>
  TRY (drule_all hgrows_trans >> simp[ADD1]) >> metis_tac[]
QED

Theorem hgrows_fetch:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ⇒ hgrows w w' (LENGTH evs)
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[] >- metis_tac[] >>
  gvs[AllCaseEqs()] >> pairarg_tac >> gvs[] >>
  qpat_x_assum ‘_ = (ps1, fl)’ (fn th => fs[th]) >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> imp_res_tac hgrows_sys >> strip_tac >>
  drule_all hgrows_trans >> simp[ADD1]
QED

Theorem hgrows_reap:
  ∀fs w st w' st' evs. l1_reap fs (w, st) = SOME ((w', st'), evs) ⇒ hgrows w w' (LENGTH evs)
Proof
  Induct >> rw[l1_reap_def, AllCaseEqs()] >> TRY (PairCases_on ‘ws’) >>
  res_tac >> imp_res_tac hgrows_close >> gvs[] >>
  metis_tac[hgrows_trans, ADD_COMM]
QED

Theorem hgrows_after:
  pf_after lfd hw hs ps fes (rv, w1, pevs) = SOME (rdy, (w', ps'), log, evs) ⇒
  ∃k. hgrows w1 w' k ∧ LENGTH evs = LENGTH pevs + k
Proof
  rw[pf_after_def, AllCaseEqs()] >> gvs[] >>
  imp_res_tac hgrows_flush >> imp_res_tac hgrows_fetch >> imp_res_tac hgrows_reap >>
  qexists_tac ‘(LENGTH fevs + LENGTH gevs) + LENGTH cevs’ >> reverse conj_tac >- decide_tac >>
  irule hgrows_trans >> qexists_tac ‘w3’ >> reverse conj_tac >- simp[] >>
  irule hgrows_trans >> qexists_tac ‘w2’ >> simp[]
QED

Theorem hgrows_tail:
  pf_tail lfd hw hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ⇒
  hgrows w w' (LENGTH evs) ∧ 0 < LENGTH evs
Proof
  simp[pf_tail_after, AllCaseEqs()] >> strip_tac >> PairCases_on ‘v’ >> gvs[] >>
  drule hgrows_after >> strip_tac >> imp_res_tac hgrows_polls >>
  drule_all hgrows_trans >> simp[] >> strip_tac >>
  ‘poll_chunks (pf_poll_set lfd hw ps hs) ≠ []’
    by (simp[Once poll_chunks_def] >> rw[]) >>
  Cases_on ‘poll_chunks (pf_poll_set lfd hw ps hs)’ >> gvs[l1_polls_def, AllCaseEqs()]
QED

Theorem hgrows_pollb:
  sys_pollb fes w = SOME (INL (out, w', ev)) ⇒ hgrows w w' 1
Proof
  rw[sys_pollb_def, AllCaseEqs(), l0_ffi_fn_def, hgrows_def] >> simp[]
QED

(* MAIN: a round extends the history by one call per event, and has one *)
Theorem bround_hgrows:
  bround lfd hw idle hs (w, ps) acts = SOME (BRound snap (w', ps') log evs) ⇒
  hgrows w w' (LENGTH evs) ∧ 0 < LENGTH evs
Proof
  rw[bround_def, AllCaseEqs()] >> gvs[] >>
  imp_res_tac hgrows_pacts >> imp_res_tac hgrows_tail >> imp_res_tac hgrows_after >>
  imp_res_tac hgrows_pollb >> gvs[]
  >> TRY (irule hgrows_trans >> qexists_tac ‘w1’ >> simp[] >> NO_TAC)
  >> ‘k + (LENGTH evs' + 1) = (LENGTH evs' + 1) + k’ by decide_tac >> pop_assum SUBST1_TAC >>
  irule hgrows_trans >> qexists_tac ‘w2’ >> reverse conj_tac >- simp[] >>
  irule hgrows_trans >> qexists_tac ‘w1’ >> simp[]
QED
