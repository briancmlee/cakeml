(*
  A round's actions, seen from f's output (close-v2, shared E1 progress
  layer, post-R3): for an fd f with bytes queued and not gone (olive), and
  not a connect's fd, no E1 action sends on f, closes it, or changes f's
  channel's flow; f stays so (eflive).  EClose of f's handle moves f to
  closing (it still has output); EShut only queues; a connect's socket is
  a fresh fd (so (A)'s close and a new connect handle are never f).

  MAIN: eacts_flive.
*)
Theory e1RoundActs
Ancestors
  e1RoundTail e1RoundConn e1RoundCflow e1RoundInv honestL1EPRefine honestL1EPModel
  honestL1PFClose honestL1PFFlush honestL1PFOut honestL1PFRound honestL1PFRefine
  honestL1PFModel honestL1Props honestL1Model honestL0WorldInv honestL0WorldProps honestL0Rely
  honestL0World
Libs
  preamble

(* f stays an outbox fd of the prefetching part, not of the connects *)
Definition eflive_def:
  eflive lfd f es ⇔ olive lfd f es.p ∧ ¬MEM f (MAP SND es.ctbl)
End

(* ------------------------------------------------------------------------
   The prefetching part's actions (honest-l1's pdo_live on ewinv)
   ------------------------------------------------------------------------ *)

Theorem pdo_ewinv:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ ewinv w ⇒ ewinv w' ∧ (nc c w ⇒ nc c w')
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> rw[AllCaseEqs()] >> gvs[] >>
  PairCases_on ‘z’ >> gvs[] >>
  TRY (drule_all l1_close_ewinv >> simp[] >> NO_TAC) >>
  gvs[l1do_def, AllCaseEqs()] >> metis_tac[sys_ewinv, sys_nc]
QED

Theorem pdo_elive:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ ewinv w ∧ olive lfd f ps ∧
  l0_chan_of w f = SOME c ⇒
  olive lfd f ps' ∧ l0_chan_of w' f = SOME c ∧ cflow w w' c ∧
  csent w' c = csent w c ∧ ¬EXISTS (ev_on «sys_send» f) evs
Proof
  strip_tac >>
  qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >>
  Cases_on ‘a’ >> simp[pdo_def] >> strip_tac
  >- ((* Accept *)
      gvs[AllCaseEqs()] >> gvs[olive_def, outbox_of_def] >> metis_tac[])
  >- ((* Read *)
      Cases_on ‘ALOOKUP ps.b.tbl c'’ >> gvs[] >> rename1 ‘ALOOKUP _ c' = SOME g’ >>
      gvs[AllCaseEqs()] >>
      TRY (gvs[olive_def, set_inb_def, outbox_of_def] >> NO_TAC) >>
      PairCases_on ‘z’ >> gvs[] >>
      ‘g ≠ f’ by (strip_tac >> gvs[olive_def]) >>
      gvs[l1_close_def, AllCaseEqs()] >>
      drule_all (cj 5 sys_ecflow) >> strip_tac >>
      gvs[sys_close_def] >> drule l0_do_cases >> strip_tac >> gvs[ev_on_def] >>
      gvs[olive_def, forget_def, outbox_of_set_outbox, MEM_FILTER, MEM_MAP, EXISTS_PROD,
          ALOOKUP_ADELKEY] >> gvs[outbox_of_def])
  >> (* Write *)
  PairCases_on ‘z’ >> gvs[l1do_def, AllCaseEqs()] >>
  TRY (‘ps with b := ps.b = ps’ by simp[l1p_component_equality] >> gvs[] >> NO_TAC) >>
  rename1 ‘ALOOKUP _ c' = SOME g’ >>
  TRY (Cases_on ‘g = f’ >> gvs[olive_def, outbox_of_set_outbox] >> NO_TAC) >>
  ‘g ≠ f’ by (strip_tac >> gvs[olive_def]) >>
  drule_all (cj 4 sys_ecflow) >> strip_tac >>
  drule ev_on_send >> disch_then (qspec_then ‘f’ assume_tac) >> gvs[] >>
  simp[outbox_of_after_send_other, outbox_of_set_outbox] >>
  gvs[olive_def, after_send_def, set_outbox_def] >> every_case_tac >>
  gvs[MEM_FILTER, outbox_of_def, ALOOKUP_ADELKEY]
QED

(* ------------------------------------------------------------------------
   E1's own steps
   ------------------------------------------------------------------------ *)

Theorem not_send_close:
  sys_close g w = SOME (out, w', ev) ⇒ ¬ev_on «sys_send» f ev
Proof
  rw[sys_close_def] >> drule l0_do_cases >> strip_tac >> gvs[ev_on_def]
QED

Theorem not_send_connect:
  sys_connect p w = SOME (out, w', ev) ⇒ ¬ev_on «sys_send» f ev
Proof
  rw[sys_connect_def] >> drule l0_do_cases >> strip_tac >> gvs[ev_on_def]
QED

Theorem used_chan:
  l0_chan_of w f = SOME c ⇒ MEM f (l0_used w)
Proof
  rw[l0_chan_of_def, AllCaseEqs(), l0_used_def] >> imp_res_tac ALOOKUP_MEM >>
  simp[MEM_MAP] >> metis_tac[FST]
QED

(* A connect handle's socket closed (refused, or EClose): not f *)
Theorem ctbl_close_flive:
  l1_close g (w, b) = SOME ((w', b'), evs) ∧ ewinv w ∧ nc c w ∧
  l0_chan_of w f = SOME c ∧ g ≠ f ⇒
  ewinv w' ∧ nc c w' ∧ l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c ∧
  b' = forget g b ∧ ¬EXISTS (ev_on «sys_send» f) evs
Proof
  strip_tac >> drule_all l1_close_ewinv >> disch_then (qspec_then ‘c’ strip_assume_tac) >>
  drule_all l1_close_ecflow >> strip_tac >> gvs[l1_close_def, AllCaseEqs()] >>
  metis_tac[not_send_close]
QED

Theorem olive_forget:
  olive lfd f ps ∧ g ≠ f ⇒ olive lfd f (ps with b := forget g ps.b)
Proof
  rw[olive_def, forget_def, outbox_of_set_outbox, MEM_FILTER] >> gvs[outbox_of_def, ALOOKUP_ADELKEY]
QED

Theorem edo_flive:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ ewinv w ∧ nc c w ∧
  eflive lfd f es ∧ l0_chan_of w f = SOME c ⇒
  ewinv w' ∧ nc c w' ∧ eflive lfd f es' ∧ l0_chan_of w' f = SOME c ∧ cflow w w' c ∧
  csent w' c = csent w c ∧ ¬EXISTS (ev_on «sys_send» f) evs
Proof
  strip_tac >> ‘MEM f (l0_used w)’ by metis_tac[used_chan] >>
  qpat_x_assum ‘edo _ _ _ _ = _’ mp_tac >>
  Cases_on ‘a’
  >~ [‘edo _ _ _ (EAccept _)’]
  >- (simp[edo_def] >> strip_tac >> PairCases_on ‘z’ >> gvs[] >>
      ‘olive lfd f es.p’ by fs[eflive_def] >>
      drule_all pdo_ewinv >> disch_then (qspec_then ‘c’ strip_assume_tac) >>
      drule_all pdo_elive >> strip_tac >> fs[eflive_def] >> gvs[EVERY_MEM, EXISTS_MEM])
  >~ [‘edo _ _ _ (EConnect _)’]
  >- (simp[edo_def] >> strip_tac >> gvs[AllCaseEqs()] >>
      rename1 ‘sys_connect _ _ = SOME (out, w1, ev)’ >>
      ‘ewinv w1’ by (drule_all (cj 8 sys_ewinv) >> simp[]) >>
      ‘nc c w1’ by (drule_all (cj 8 sys_nc) >> simp[]) >>
      drule_all (cj 8 sys_ecflow) >> strip_tac >>
      ‘¬ev_on «sys_send» f ev’ by (drule not_send_connect >> simp[]) >>
      ‘res_val out ≠ 0 ⇒ n2w (res_val out) ≠ f’
        by (strip_tac >> gvs[ewinv_def] >> drule_all sys_connect_l0 >> strip_tac >>
            strip_tac >> gvs[])
      >~ [‘sys_close _ _ = SOME z’]
      >- ((* (A): the fresh socket closed at once *)
          PairCases_on ‘z’ >> gvs[] >> rename1 ‘sys_close _ _ = SOME (out', w2, ev')’ >>
          ‘ewinv w2’ by (drule_all (cj 1 sys_ewinv) >> simp[]) >>
          ‘nc c w2’ by (drule_all (cj 1 sys_nc) >> simp[]) >>
          drule_all (cj 5 sys_ecflow) >> strip_tac >>
          ‘¬ev_on «sys_send» f ev'’ by (drule not_send_close >> simp[]) >>
          simp[] >> irule cflow_trans >> qexists_tac ‘w1’ >> simp[]) >>
      (* no socket, or a new connect handle: its fd is fresh *)
      gvs[eflive_def, olive_def, outbox_of_def])
  >~ [‘edo _ _ _ (ERead _ _)’]
  >- (simp[edo_def] >> Cases_on ‘ALOOKUP es.ctbl c'’ >> simp[] >> strip_tac >>
      gvs[AllCaseEqs()]
      >~ [‘l1_close _ _ = SOME z’]
      >- ((* refused connect handle: its socket closed *)
          PairCases_on ‘z’ >> gvs[] >> rename1 ‘ALOOKUP es.ctbl _ = SOME g’ >>
          ‘g ≠ f’ by (strip_tac >> gvs[eflive_def, MEM_MAP] >> imp_res_tac ALOOKUP_MEM >>
                      metis_tac[SND]) >>
          drule_all ctbl_close_flive >> strip_tac >> gvs[] >>
          gvs[eflive_def, ec_del_def] >>
          conj_tac >- (irule olive_forget >> simp[]) >>
          gvs[MEM_MAP, ALOOKUP_ADELKEY] >> rw[] >> rename1 ‘MEM y _’ >>
          Cases_on ‘y’ >> gvs[MEM_ADELKEY] >> metis_tac[SND])
      >>~- ([‘pdo _ _ _ = SOME z’],
            PairCases_on ‘z’ >> gvs[] >>
            ‘olive lfd f es.p’ by fs[eflive_def] >>
            drule_all pdo_ewinv >> disch_then (qspec_then ‘c’ strip_assume_tac) >>
            drule_all pdo_elive >> strip_tac >> fs[eflive_def] >> gvs[EVERY_MEM, EXISTS_MEM]) >>
      gvs[eflive_def])
  >~ [‘edo _ _ _ (EWrite _ _)’]
  >- (simp[edo_def] >> rw[AllCaseEqs()] >> gvs[] >>
      PairCases_on ‘z’ >> gvs[] >>
      ‘olive lfd f es.p’ by fs[eflive_def] >>
      drule_all pdo_ewinv >> disch_then (qspec_then ‘c’ strip_assume_tac) >>
      drule_all pdo_elive >> strip_tac >> fs[eflive_def] >> gvs[EVERY_MEM, EXISTS_MEM])
  >~ [‘edo _ _ _ (ELevel _)’]
  >- (simp[edo_def] >> rw[] >> simp[])
  >~ [‘edo _ _ _ (EClose _)’]
  >- (simp[edo_def] >> strip_tac >> gvs[AllCaseEqs()]
      >~ [‘l1_close _ _ = SOME z’]
      >- ((* a connect handle *)
          PairCases_on ‘z’ >> gvs[] >> rename1 ‘ALOOKUP es.ctbl _ = SOME g’ >>
          ‘g ≠ f’ by (strip_tac >> gvs[eflive_def, MEM_MAP] >> imp_res_tac ALOOKUP_MEM >>
                      metis_tac[SND]) >>
          drule_all ctbl_close_flive >> strip_tac >> gvs[] >>
          gvs[eflive_def, ec_del_def] >>
          conj_tac >- (irule olive_forget >> simp[]) >>
          gvs[MEM_MAP, ALOOKUP_ADELKEY] >> rw[] >> rename1 ‘MEM y _’ >>
          Cases_on ‘y’ >> gvs[MEM_ADELKEY] >> metis_tac[SND])
      >~ [‘pf_close _ _ = SOME z’]
      >- ((* a prefetching handle: f's (to closing, it has output) or another's *)
          PairCases_on ‘z’ >> gvs[] >> rename1 ‘ALOOKUP es.p.b.tbl h = SOME g’ >>
          qpat_x_assum ‘pf_close _ _ = _’ mp_tac >> simp[pf_close_def] >>
          Cases_on ‘g = f’
          >- (gvs[eflive_def, olive_def, pf_release_def, set_inb_def, outbox_of_def] >>
              rw[] >> gvs[]) >>
          IF_CASES_TAC >> strip_tac
          >- (gvs[] >> PairCases_on ‘z’ >> gvs[] >>
              drule_all ctbl_close_flive >> strip_tac >> gvs[] >>
              gvs[eflive_def, olive_def, pf_release_def, set_inb_def, forget_def, outbox_of_set_outbox, MEM_FILTER] >>
              gvs[outbox_of_def, ALOOKUP_ADELKEY]) >>
          gvs[eflive_def, olive_def, pf_release_def, set_inb_def, outbox_of_def]) >>
      gvs[eflive_def])
  >> simp[edo_def] >> rw[AllCaseEqs()] >> gvs[eflive_def]
QED

(* MAIN *)
Theorem eacts_flive:
  ∀acts w es rs evs w' es'.
    eacts lfd pol (w, es) acts = SOME (rs, evs, (w', es')) ∧ ewinv w ∧ nc c w ∧
    eflive lfd f es ∧ l0_chan_of w f = SOME c ⇒
    ewinv w' ∧ nc c w' ∧ eflive lfd f es' ∧ l0_chan_of w' f = SOME c ∧ cflow w w' c ∧
    csent w' c = csent w c ∧ ¬EXISTS (ev_on «sys_send» f) evs
Proof
  Induct >> simp[eacts_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  drule_all edo_flive >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  conj_tac >- (irule cflow_trans >> qexists_tac ‘ws10’ >> simp[]) >>
  gvs[EVERY_MEM, EXISTS_MEM] >> metis_tac[]
QED
