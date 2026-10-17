(*
  E1's per-round flush lemma (close-v2, shared E1 progress layer,
  post-R3): honest-l1's pround_live on an E1 round (eround: eacts, etail,
  eshuts), the per-round hypothesis e1FlushLift's flush_lift takes.

  For an fd f with bytes queued and not gone (olive), not a connect's fd
  (eflive), whose channel c is not connecting (nc): in one round, a send
  on f goes through, or f's outbox empties (a drop), or f stays so, its
  channel's flow is kept, nothing is sent on it, a poll on f is
  attempted, and a poll that goes through while the channel is up and
  empty is followed by a send on f.  The world invariant (ewinv), c not
  connecting, and E1's fds being small (esmall) are kept.

  MAIN: eround_flush.
*)
Theory e1RoundFlush
Ancestors
  e1RoundActs e1RoundTail e1RoundConn e1RoundCflow e1RoundInv honestL1EPTotal
  honestL1EPOut honestL1EPRefine honestL1EPModel honestL1PFClose honestL1PFFlush
  honestL1PFOut honestL1PFConnRun honestL1PFConn honestL1PFRound honestL1PFRefine
  honestL1PFInv honestL1PFModel honestL1Inv honestL1Props honestL1Model
  honestL0WorldInv honestL0WorldProps honestL0Rely honestL0World
Libs
  preamble

(* ------------------------------------------------------------------------
   E1's fds stay small along the actions
   ------------------------------------------------------------------------ *)

Theorem esmall_ctbl_close:
  l1_close g (w, es.p.b) = SOME ((w', b'), evs) ∧ esmall lfd es ∧
  ALOOKUP es.ctbl h = SOME g ⇒
  esmall lfd (ec_del h g (es with p := es.p with b := b')) ∧
  esmall lfd (ec_del h g (es with <| p := es.p with b := b'; early := ADELKEY g es.early |>))
Proof
  strip_tac >>
  ‘small g’ by (gvs[esmall_def] >> metis_tac[small_ctbl_lookup]) >>
  ‘small_fds lfd es.p.b’ by gvs[esmall_def, psmall_def] >>
  ‘b' = forget g es.p.b’ by gvs[l1_close_def, AllCaseEqs()] >>
  ‘small_fds lfd b'’ by metis_tac[small_fds_forget] >>
  gvs[esmall_def, ec_del_def, psmall_def, EVERY_MEM] >> metis_tac[MEM_SND_ADELKEY_sub]
QED

Theorem edo_esmall:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ l0_rely w ∧ esmall lfd es ⇒
  esmall lfd es'
Proof
  strip_tac >> qpat_x_assum ‘edo _ _ _ _ = _’ mp_tac >>
  Cases_on ‘a’
  >~ [‘edo _ _ _ (EAccept _)’]
  >- (simp[edo_def] >> strip_tac >> PairCases_on ‘z’ >> gvs[] >>
      ‘psmall lfd es.p’ by gvs[esmall_def] >>
      drule_all pdo_psmall >> gvs[esmall_def])
  >~ [‘edo _ _ _ (EConnect _)’]
  >- (simp[edo_def] >> strip_tac >> gvs[AllCaseEqs()] >>
      rename1 ‘sys_connect p w = SOME (out, w1, ev)’ >>
      drule sys_connect_ok >> disch_then (qspec_then ‘p’ strip_assume_tac) >> gvs[] >>
      TRY (PairCases_on ‘z’ >> gvs[] >> NO_TAC) >>
      ‘small (n2w (res_val out) : word64)’ by simp[small_def] >>
      gvs[esmall_def, psmall_def, small_fds_def])
  >~ [‘edo _ _ _ (ERead _ _)’]
  >- (simp[edo_def] >> Cases_on ‘ALOOKUP es.ctbl c’ >> simp[] >> strip_tac >>
      gvs[AllCaseEqs()]
      >~ [‘l1_close _ _ = SOME z’]
      >- (PairCases_on ‘z’ >> gvs[] >> drule_all esmall_ctbl_close >> simp[])
      >~ [‘pdo _ _ _ = SOME z’]
      >- (PairCases_on ‘z’ >> gvs[] >>
          ‘psmall lfd es.p’ by gvs[esmall_def] >>
          drule_all pdo_psmall >> gvs[esmall_def]))
  >~ [‘edo _ _ _ (EWrite _ _)’]
  >- (simp[edo_def] >> strip_tac >> gvs[AllCaseEqs()] >>
      PairCases_on ‘z’ >> gvs[] >>
      ‘psmall lfd es.p’ by gvs[esmall_def] >>
      drule_all pdo_psmall >> gvs[esmall_def])
  >~ [‘edo _ _ _ (ELevel _)’]
  >- (simp[edo_def] >> strip_tac >> gvs[])
  >~ [‘edo _ _ _ (EClose _)’]
  >- (simp[edo_def] >> strip_tac >> gvs[AllCaseEqs()]
      >~ [‘l1_close _ _ = SOME z’]
      >- (PairCases_on ‘z’ >> gvs[] >> drule_all esmall_ctbl_close >> simp[])
      >~ [‘pf_close _ _ = SOME z’]
      >- (PairCases_on ‘z’ >> gvs[] >> rename1 ‘ALOOKUP es.p.b.tbl h = SOME g’ >>
          ‘psmall lfd es.p’ by gvs[esmall_def] >>
          ‘small g’ by (gvs[psmall_def] >> metis_tac[small_tbl_lookup]) >>
          ‘psmall lfd (pf_release h g (set_inb g [] es.p))’
            by metis_tac[psmall_release, psmall_set_inb] >>
          qabbrev_tac ‘ps = pf_release h g (set_inb g [] es.p)’ >>
          qpat_x_assum ‘pf_close _ _ = _’ mp_tac >> simp[pf_close_def] >>
          IF_CASES_TAC >> strip_tac
          >- (gvs[] >> PairCases_on ‘z’ >> gvs[] >>
              rename1 ‘l1_close g (w, ps.b) = SOME ((_, b1), _)’ >>
              ‘b1 = forget g ps.b’ by gvs[l1_close_def, AllCaseEqs()] >>
              ‘small_fds lfd b1’ by (gvs[] >> irule small_fds_forget >> gvs[psmall_def]) >>
              qpat_x_assum ‘b1 = _’ kall_tac >>
              ‘psmall lfd (ps with b := b1)’ by gvs[psmall_def] >>
              gvs[esmall_def]) >>
          gvs[esmall_def, psmall_def, small_fds_def]))
  >> simp[edo_def] >> rw[AllCaseEqs()] >> gvs[esmall_def]
QED

Theorem eacts_esmall:
  ∀acts w es rs evs w' es'.
    eacts lfd pol (w, es) acts = SOME (rs, evs, (w', es')) ∧ ewinv w ∧ nc c w ∧
    eflive lfd f es ∧ l0_chan_of w f = SOME c ∧ esmall lfd es ⇒
    esmall lfd es'
Proof
  Induct >> simp[eacts_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  ‘l0_rely w’ by gvs[ewinv_def] >>
  drule_all edo_esmall >> strip_tac >>
  drule_all edo_flive >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

(* The actions make no poll *)
Theorem sys_close_nopoll:
  sys_close f w = SOME (out, w', ev) ⇒ ev_name ev ≠ ExtCall «sys_poll»
Proof
  rw[sys_close_def] >> drule l0_do_cases >> rw[] >> simp[ev_name_def]
QED

Theorem sys_connect_nopoll:
  sys_connect p w = SOME (out, w', ev) ⇒ ev_name ev ≠ ExtCall «sys_poll»
Proof
  rw[sys_connect_def] >> drule l0_do_cases >> rw[] >> simp[ev_name_def]
QED

Theorem l1_close_nopoll:
  l1_close f (w, b) = SOME ((w', b'), evs) ⇒
  EVERY (λev. ev_name ev ≠ ExtCall «sys_poll») evs
Proof
  rw[l1_close_def, AllCaseEqs()] >> gvs[] >> drule sys_close_nopoll >> simp[]
QED

Theorem edo_nopoll:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ⇒
  EVERY (λev. ev_name ev ≠ ExtCall «sys_poll») evs
Proof
  Cases_on ‘a’ >> simp[edo_def, AllCaseEqs()] >> rw[] >> TRY (PairCases_on ‘z’) >> gvs[] >>
  TRY (drule pdo_names >> simp[EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[] >> NO_TAC) >>
  TRY (drule l1_close_nopoll >> simp[] >> NO_TAC) >>
  TRY (qpat_x_assum ‘pf_close _ _ = _’ mp_tac >> simp[pf_close_def] >> rw[] >>
       PairCases_on ‘z’ >> gvs[] >> drule l1_close_nopoll >> simp[] >> NO_TAC) >>
  imp_res_tac sys_connect_nopoll >> imp_res_tac sys_close_nopoll >> simp[]
QED

Theorem eacts_nopoll:
  ∀acts w es rs evs w' es'.
    eacts lfd pol (w, es) acts = SOME (rs, evs, (w', es')) ⇒
    EVERY (λev. ev_name ev ≠ ExtCall «sys_poll») evs
Proof
  Induct >> simp[eacts_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  drule edo_nopoll >> strip_tac >> first_x_assum drule >> simp[]
QED

(* ------------------------------------------------------------------------
   The round's tail
   ------------------------------------------------------------------------ *)

Theorem settle_fds_flive:
  ∀fs w es w' es' evs.
    settle_fds fs (w, es) = SOME ((w', es'), evs) ∧ ewinv w ∧ nc c w ⇒
    ewinv w' ∧ nc c w' ∧ es'.p = es.p ∧ es'.ctbl = es.ctbl ∧
    EVERY (λev. ev_name ev = ExtCall «sys_connerr») evs ∧
    (l0_chan_of w f = SOME c ⇒
     l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c)
Proof
  Induct >> simp[settle_fds_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘sys_connerr _ _ = SOME (out, w1, ev)’ >>
  ‘ewinv w1’ by (drule_all (cj 6 sys_ewinv) >> simp[]) >>
  ‘nc c w1’ by (drule_all (cj 6 sys_nc) >> simp[]) >>
  ‘ev_name ev = ExtCall «sys_connerr»’
    by (gvs[sys_connerr_def] >> drule l0_do_cases >> rw[] >> simp[ev_name_def]) >>
  qmatch_asmsub_abbrev_tac ‘settle_fds fs (w1, es1)’ >>
  ‘es1.p = es.p ∧ es1.ctbl = es.ctbl’ by (simp[Abbr ‘es1’] >> every_case_tac >> simp[]) >>
  first_x_assum drule >> impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  simp[] >> strip_tac >>
  drule_all (cj 6 sys_ecflow) >> strip_tac >> gvs[] >>
  irule cflow_trans >> qexists_tac ‘w1’ >> simp[]
QED

Theorem every_mem:
  EVERY P l ∧ MEM x l ⇒ P x
Proof
  rw[EVERY_MEM]
QED

Theorem promote_outbox:
  es.p.b = b ⇒ outbox_of (promote es).p.b g = outbox_of b g
Proof
  rw[promote_def, outbox_of_def]
QED

Theorem promote_eflive:
  ∀es b ctbl lfd f.
    es.p.b = b ∧ es.ctbl = ctbl ∧ f ≠ lfd ∧ outbox_of b f ≠ [] ∧ ¬MEM f b.gone ∧
    ¬MEM f (MAP SND ctbl) ⇒
    ∀sl. eflive lfd f (promote es with settling := sl)
Proof
  rw[eflive_def, olive_def, promote_def, outbox_of_def, MEM_MAP, MEM_FILTER] >>
  gvs[outbox_of_def, MEM_MAP] >> metis_tac[]
QED

Theorem etail_flush:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, tevs) ∧
  ewinv w ∧ nc c w ∧ esmall lfd es ∧ eflive lfd f es ∧ l0_chan_of w f = SOME c ⇒
  ewinv w' ∧ nc c w' ∧ esmall lfd es' ∧
  ((∃ev. MEM ev tevs ∧ ev_on «sys_send» f ev ∧ ¬retried ev) ∨ outbox_of es'.p.b f = [] ∨
   (eflive lfd f es' ∧ l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c ∧
    EXISTS (ev_on «sys_poll» f) tevs ∧
    ∀ev. MEM ev tevs ∧ ev_on «sys_poll» f ev ∧ ¬retried ev ∧
         ¬(EL c w'.chans).broken ∧ ¬(EL c w.chans).shut ∧ (EL c w.chans).inflight = 0 ∧
         (∀hh. 0 < w.ch.takes c hh 0 1) ⇒
         EXISTS (ev_on «sys_send» f) tevs))
Proof
  strip_tac >>
  ‘esmall lfd es'’
    by (‘l0_rely w’ by gvs[ewinv_def] >>
        drule_all etail_ok >> disch_then (qspecl_then [‘pol’, ‘hs’] strip_assume_tac) >>
        gvs[]) >>
  qpat_x_assum ‘etail _ _ _ _ = _’ mp_tac >>
  simp[etail_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘FILTER _ hs = rdy’ kall_tac >>
  qpat_x_assum ‘_ = tevs’ (SUBST_ALL_TAC o SYM) >>
  ‘olive lfd f es.p ∧ ¬MEM f (MAP SND es.ctbl)’ by fs[eflive_def] >>
  qabbrev_tac ‘fes = pf_poll_set lfd pol es.p hs ++ MAP (λf. (f, 2n)) (pend_fds es)’ >>
  ‘EVERY (λ(g, e). small g ∧ e < 4) fes’
    by (simp[Abbr ‘fes’] >> conj_tac
        >- (irule pf_poll_set_small >> gvs[esmall_def]) >>
        qpat_x_assum ‘esmall lfd es’ (mp_tac o MATCH_MP pend_fds_small) >>
        simp[EVERY_MAP, EVERY_MEM]) >>
  (* the poll *)
  qpat_x_assum ‘l1_polls [fes] _ = _’ mp_tac >> simp[l1_polls_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> rename1 ‘sys_poll fes w = SOME (out, w1, pev)’ >>
  ‘ewinv w1’ by (drule_all (cj 5 sys_ewinv) >> simp[]) >>
  ‘nc c w1’ by (drule_all (cj 5 sys_nc) >> simp[]) >>
  drule_all (cj 3 sys_ecflow) >> strip_tac >>
  drule_all sys_poll_eon >> strip_tac >>
  ‘∃e. MEM (f, e) fes ∧ 2 ≤ e ∧ e < 4’
    by (‘∃e. MEM (f, e) (pf_poll_set lfd pol es.p hs) ∧ 2 ≤ e ∧ e < 4’
          by (irule pf_poll_set_out >> gvs[olive_def]) >>
        qexists_tac ‘e’ >> simp[Abbr ‘fes’]) >>
  (* the flush, fetch, reap and settling keep ewinv and nc *)
  rename1 ‘l1_flush _ (w1, es.p.b) = SOME ((w2, b2), fevs)’ >>
  drule_all l1_flush_ewinv >> disch_then (qspec_then ‘c’ strip_assume_tac) >>
  ‘nc c w2’ by (qpat_x_assum ‘nc c w1 ⇒ _’ irule >> first_assum ACCEPT_TAC) >>
  rename1 ‘pf_fetch _ _ _ (w2, es.p with b := b2) = SOME ((w3, ps3'), log, gevs)’ >>
  drule_all pf_fetch_ewinv >> disch_then (qspec_then ‘c’ strip_assume_tac) >>
  ‘nc c w3’ by (qpat_x_assum ‘nc c w2 ⇒ _’ irule >> first_assum ACCEPT_TAC) >>
  qabbrev_tac ‘ps3 = stall_step (pf_held ps3') (outbox_of es.p.b) log ps3'’ >>
  rename1 ‘l1_reap _ (w3, ps3.b) = SOME ((w4, b4), cevs)’ >>
  drule_all l1_reap_ewinv >> disch_then (qspec_then ‘c’ strip_assume_tac) >>
  ‘nc c w4’ by (qpat_x_assum ‘nc c w3 ⇒ _’ irule >> first_assum ACCEPT_TAC) >>
  rename1 ‘settle_fds _ _ = SOME ((w5, es5), sevs)’ >>
  drule_all settle_fds_flive >> disch_then (qspec_then ‘f’ strip_assume_tac) >>
  (* a send on f in the flush *)
  Cases_on ‘∃ev. MEM ev fevs ∧ ev_on «sys_send» f ev ∧ ¬retried ev’
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> disj1_tac >>
      first_x_assum (qx_choose_then ‘ev’ strip_assume_tac) >> qexists_tac ‘ev’ >> simp[]) >>
  (* else f's flow along the flush *)
  qpat_assum ‘l1_flush _ _ = _’ (strip_assume_tac o MATCH_MP l1_flush_names) >>
  drule_all l1_flush_ecflow >> strip_tac >>
  drule_all l1_flush_elive >> strip_tac >>
  qpat_x_assum ‘¬_ ⇒ _’ mp_tac >> impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  (* the fetch *)
  drule_all pf_fetch_ecflow >> strip_tac >>
  drule (cj 1 honestL1PFConnRunTheory.pf_fetch_b) >> strip_tac >>
  drule pf_fetch_names >> strip_tac >>
  (* the hang-up policy: a drop empties f's outbox *)
  ‘¬MEM f ps3'.b.gone ∧ outbox_of ps3'.b f = outbox_of es.p.b f’ by gvs[olive_def] >>
  (* the reap, settling, promotion: f's outbox and gone are those of b4 *)
  drule l1_reap_names >> strip_tac >>
  ‘es5.p.b = b4’
    by (qpat_x_assum ‘es5.p = _’ (fn th => REWRITE_TAC[th]) >> simp[apply_early_def]) >>
  ‘es5.ctbl = es.ctbl’
    by (qpat_x_assum ‘es5.ctbl = _’ (fn th => REWRITE_TAC[th]) >> simp[apply_early_def]) >>
  ‘outbox_of (promote es5).p.b f = outbox_of b4 f’
    by (irule promote_outbox >> first_assum ACCEPT_TAC) >>
  ‘f ≠ lfd ∧ outbox_of es.p.b f ≠ [] ∧ ¬MEM f es.p.b.gone’
    by (qpat_x_assum ‘olive lfd f es.p’ mp_tac >> simp[olive_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum ‘outbox_of (promote es5).p.b f = _’ (fn th => REWRITE_TAC[th]) >>
  Cases_on ‘MEM f ps3.b.gone’
  >- ((* dropped (D19): f's outbox is empty, and stays so *)
      disj2_tac >> disj1_tac >>
      ‘outbox_of ps3.b f = []’
        by (qspecl_then [‘pf_held ps3'’, ‘outbox_of es.p.b’, ‘log’, ‘ps3'’, ‘ps3’, ‘f’] mp_tac
              (Q.GENL [‘hfs’, ‘ob’, ‘log’, ‘ps’, ‘ps'’, ‘f’] (SPEC_ALL stall_f)) >>
            impl_tac >- simp[Abbr ‘ps3’] >>
            disch_then (fn th => irule (last (CONJUNCTS th))) >>
            rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
            qpat_x_assum ‘¬MEM f ps3'.b.gone’ (fn th => REWRITE_TAC[th])) >>
      drule_all l1_reap_empty >> simp[]) >>
  ‘outbox_of ps3.b f = outbox_of ps3'.b f’
    by (qspecl_then [‘ps3’, ‘pf_held ps3'’, ‘outbox_of es.p.b’, ‘log’, ‘ps3'’, ‘f’] mp_tac
          (Q.GENL [‘ps'’, ‘hfs’, ‘ob’, ‘log’, ‘ps’, ‘f’] (SPEC_ALL stall_kept)) >>
        impl_tac >- (conj_tac >- simp[Abbr ‘ps3’] >> first_assum ACCEPT_TAC) >>
        disch_then (ACCEPT_TAC o CONJUNCT2)) >>
  ‘outbox_of ps3.b f ≠ []’
    by (qpat_assum ‘outbox_of ps3.b f = _’ SUBST1_TAC >>
        qpat_assum ‘outbox_of ps3'.b f = _’ SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  drule_all l1_reap_elive >> strip_tac >>
  qpat_x_assum ‘l0_chan_of w4 f = SOME c ⇒ _’ mp_tac >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  ‘cflow w1 w5 c’
    by (irule cflow_trans >> qexists_tac ‘w4’ >> conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        irule cflow_trans >> qexists_tac ‘w3’ >> conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        irule cflow_trans >> qexists_tac ‘w2’ >> conj_tac >> first_assum ACCEPT_TAC) >>
  ‘cflow w w5 c’
    by (irule cflow_trans >> qexists_tac ‘w1’ >> conj_tac >> first_assum ACCEPT_TAC) >>
  ‘csent w5 c = csent w c’
    by (qpat_x_assum ‘csent w5 c = _’ SUBST1_TAC >> qpat_x_assum ‘csent w4 c = _’ SUBST1_TAC >>
        qpat_x_assum ‘csent w3 c = _’ SUBST1_TAC >> qpat_x_assum ‘csent w2 c = _’ SUBST1_TAC >>
        qpat_x_assum ‘csent w1 c = _’ ACCEPT_TAC) >>
  ‘outbox_of b4 f ≠ []’
    by (qpat_assum ‘outbox_of b4 f = _’ SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  disj2_tac >> disj2_tac >>
  conj_tac
  >- (qspecl_then [‘es5’, ‘b4’, ‘es.ctbl’, ‘lfd’, ‘f’] mp_tac promote_eflive >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (‘MEM f (MAP FST fes)’
        by (simp[MEM_MAP, EXISTS_PROD] >> qexists_tac ‘e’ >> first_assum ACCEPT_TAC) >>
      qpat_assum ‘∀nm g. ev_on nm g pev ⇔ _’ (fn th => REWRITE_TAC[th]) >>
      qpat_x_assum ‘MEM f (MAP FST fes)’ (fn th => REWRITE_TAC[th])) >>
  (* the round's poll went through with f's channel up and empty: f writable *)
  gen_tac >> disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  qpat_assum ‘ev_on «sys_poll» f ev'’ (assume_tac o MATCH_MP ev_on_name) >>
  ‘ev' = pev’
    by (qpat_x_assum ‘_ ∨ MEM ev' sevs’ strip_assume_tac >>
        TRY (first_assum ACCEPT_TAC ORELSE REFL_TAC) >>
        qpat_x_assum ‘MEM ev' _’
          (fn m => first_x_assum (fn e => mp_tac (MATCH_MP every_mem (CONJ e m)))) >>
        qpat_x_assum ‘ev_name ev' = _’ (fn th => simp[th])) >>
  qpat_x_assum ‘ev' = pev’ SUBST_ALL_TAC >>
  ‘¬(EL c w1.chans).broken’
    by (strip_tac >> qpat_x_assum ‘cflow w1 w5 c’ (mp_tac o REWRITE_RULE [cflow_def]) >>
        qpat_x_assum ‘(EL c w1.chans).broken’ mp_tac >>
        qpat_x_assum ‘¬(EL c w5.chans).broken’ mp_tac >> simp[]) >>
  ‘¬(EL c w1.chans).shut ∧ (EL c w1.chans).inflight = 0’
    by (qpat_x_assum ‘cflow w w1 c’ (mp_tac o REWRITE_RULE [cflow_def]) >>
        qpat_x_assum ‘csent w1 c = csent w c’ (fn th => REWRITE_TAC[th]) >>
        qpat_x_assum ‘¬(EL c w.chans).shut’ mp_tac >>
        qpat_x_assum ‘(EL c w.chans).inflight = 0’ mp_tac >> simp[]) >>
  ‘MEM f (writable_fds (poll_revents fes out))’
    by (qspecl_then [‘fes’, ‘w’, ‘out’, ‘w1’, ‘pev’, ‘f’, ‘c’, ‘e’] mp_tac
          (Q.GENL [‘fes’, ‘w’, ‘out’, ‘w'’, ‘ev’, ‘f’, ‘c’, ‘e’] (SPEC_ALL sys_poll_eout)) >>
        impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
  ‘EXISTS (ev_on «sys_send» f) fevs’
    by (qpat_x_assum ‘MEM f (writable_fds _) ∧ _ ⇒ _’ irule >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘EXISTS (ev_on «sys_send» f) fevs’ (fn th => REWRITE_TAC[th])
QED

(* ------------------------------------------------------------------------
   The queued shutdowns: f, with output, is not shut; another fd's
   shutdown keeps f's channel
   ------------------------------------------------------------------------ *)

Theorem pf_shuts_flive:
  ∀qs w ps w' ps' kp sh evs.
    pf_shuts qs (w, ps) = SOME ((w', ps'), kp, sh, evs) ∧ ewinv w ⇒
    ewinv w' ∧ (nc c w ⇒ nc c w') ∧ (∀g. outbox_of ps'.b g = outbox_of ps.b g) ∧
    EVERY (λev. ev_name ev = ExtCall «sys_shutdown») evs ∧
    (outbox_of ps.b f ≠ [] ∧ l0_chan_of w f = SOME c ⇒
     l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c ∧
     (MEM f ps'.b.gone ⇔ MEM f ps.b.gone))
Proof
  Induct >- simp[pf_shuts_def] >>
  rpt gen_tac >> rename1 ‘kf :: qs’ >> PairCases_on ‘kf’ >> rename1 ‘(k, g) :: qs’ >>
  simp[Once pf_shuts_def] >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  IF_CASES_TAC
  >- (strip_tac >> gvs[] >> PairCases_on ‘z’ >> gvs[] >> first_x_assum drule_all >> simp[]) >>
  strip_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘sys_shutdown g w = SOME (out, w1, ev)’ >>
  ‘ewinv w1’ by (drule_all (cj 7 sys_ewinv) >> simp[]) >>
  ‘nc c w ⇒ nc c w1’ by (strip_tac >> drule_all (cj 7 sys_nc) >> simp[]) >>
  ‘ev_name ev = ExtCall «sys_shutdown»’
    by (gvs[sys_shutdown_def] >> drule l0_do_cases >> rw[] >> simp[ev_name_def]) >>
  pairarg_tac >> gvs[] >> PairCases_on ‘z’ >> gvs[] >>
  ‘∀h. outbox_of ps1.b h = outbox_of ps.b h’
    by (Cases_on ‘l0_res_of out’ >> gvs[] >>
        qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> rw[] >>
        simp[drop_out_def, outbox_of_set_outbox] >> rw[] >> simp[outbox_of_def]) >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  strip_tac >>
  ‘g ≠ f’ by (strip_tac >> gvs[]) >>
  ‘(MEM f ps1.b.gone ⇔ MEM f ps.b.gone)’
    by (Cases_on ‘l0_res_of out’ >> gvs[] >>
        qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> rw[] >>
        simp[drop_out_def, set_outbox_def, MEM_FILTER]) >>
  drule_all (cj 7 sys_ecflow) >> strip_tac >>
  qpat_x_assum ‘_ ∧ l0_chan_of w1 f = SOME c ⇒ _’ mp_tac >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  simp[] >> irule cflow_trans >> qexists_tac ‘w1’ >> simp[]
QED

Theorem eshuts_flive:
  eshuts (w, es) = SOME ((w', es'), evs) ∧ ewinv w ∧ esmall lfd es ⇒
  ewinv w' ∧ (nc c w ⇒ nc c w') ∧ esmall lfd es' ∧ (∀g. outbox_of es'.p.b g = outbox_of es.p.b g) ∧
  es'.ctbl = es.ctbl ∧ EVERY (λev. ev_name ev = ExtCall «sys_shutdown») evs ∧
  (outbox_of es.p.b f ≠ [] ∧ l0_chan_of w f = SOME c ⇒
   l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c ∧
   (MEM f es'.p.b.gone ⇔ MEM f es.p.b.gone))
Proof
  simp[eshuts_def] >> strip_tac >> PairCases_on ‘z’ >> gvs[] >>
  drule_all pf_shuts_flive >> disch_then (qspecl_then [‘f’, ‘c’] strip_assume_tac) >> simp[] >>
  ‘l0_rely w ∧ psmall lfd es.p’ by gvs[ewinv_def, esmall_def] >>
  qmatch_asmsub_abbrev_tac ‘pf_shuts qs (w, es.p)’ >>
  qspecl_then [‘qs’, ‘w’, ‘es.p’] mp_tac pf_shuts_ok >> simp[] >> strip_tac >>
  gvs[esmall_def]
QED

(* ------------------------------------------------------------------------
   One E1 round
   ------------------------------------------------------------------------ *)

(* MAIN *)
Theorem eround_flush:
  eround lfd pol hs (w, es) acts = SOME (snap, (w', es'), log, evs) ∧
  ewinv w ∧ nc c w ∧ esmall lfd es ∧ eflive lfd f es ∧ l0_chan_of w f = SOME c ⇒
  ewinv w' ∧ nc c w' ∧ esmall lfd es' ∧
  ((∃ev. MEM ev evs ∧ ev_on «sys_send» f ev ∧ ¬retried ev) ∨ outbox_of es'.p.b f = [] ∨
   (eflive lfd f es' ∧ l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c ∧
    EXISTS (ev_on «sys_poll» f) evs ∧
    ∀ev. MEM ev evs ∧ ev_on «sys_poll» f ev ∧ ¬retried ev ∧
         ¬(EL c w'.chans).broken ∧ ¬(EL c w.chans).shut ∧ (EL c w.chans).inflight = 0 ∧
         (∀hh. 0 < w.ch.takes c hh 0 1) ⇒
         EXISTS (ev_on «sys_send» f) evs))
Proof
  simp[eround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >> PairCases_on ‘ws2’ >>
  gvs[] >>
  rename1 ‘eacts _ _ _ _ = SOME (rs, aevs, (wa, ea))’ >>
  rename1 ‘etail _ _ _ _ = SOME (rdy, (wt, et), log, tevs)’ >>
  drule_all eacts_esmall >> strip_tac >>
  drule_all eacts_flive >> strip_tac >>
  drule_all etail_flush >> disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  drule eacts_nopoll >> strip_tac >>
  rename1 ‘eshuts _ = SOME (_, shevs)’ >>
  drule_all eshuts_flive >> disch_then (qspecl_then [‘f’, ‘c’] strip_assume_tac) >>
  ‘nc c w'’ by (qpat_x_assum ‘nc c wt ⇒ _’ irule >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘_ ∨ outbox_of et.p.b f = [] ∨ _’ strip_assume_tac
  >- (disj1_tac >> qexists_tac ‘ev’ >> simp[])
  >- (disj2_tac >> disj1_tac >>
      qpat_x_assum ‘∀g. outbox_of es'.p.b g = _’ (fn th => REWRITE_TAC[th]) >>
      first_assum ACCEPT_TAC) >>
  ‘outbox_of et.p.b f ≠ []’ by fs[eflive_def, olive_def] >>
  qpat_x_assum ‘_ ∧ l0_chan_of wt f = SOME c ⇒ _’ mp_tac >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  disj2_tac >> disj2_tac >>
  rpt conj_tac
  >- (qpat_x_assum ‘eflive lfd f et’ mp_tac >>
      qpat_x_assum ‘∀g. outbox_of es'.p.b g = _’ (fn th => REWRITE_TAC[eflive_def, olive_def, th]) >>
      qpat_x_assum ‘es'.ctbl = et.ctbl’ SUBST1_TAC >>
      qpat_x_assum ‘MEM f es'.p.b.gone ⇔ _’ SUBST1_TAC >> simp[])
  >- first_assum ACCEPT_TAC
  >- (irule cflow_trans >> qexists_tac ‘wt’ >> conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      irule cflow_trans >> qexists_tac ‘wa’ >> conj_tac >> first_assum ACCEPT_TAC)
  >- simp[]
  >- simp[EXISTS_APPEND]
  >> rpt gen_tac >> strip_tac >> imp_res_tac ev_on_name >>
  ‘MEM ev tevs’
    by (FIRST [first_assum ACCEPT_TAC,
               qpat_x_assum ‘EVERY _ aevs’ mp_tac >> simp[EVERY_MEM] >>
               disch_then (qspec_then ‘ev’ mp_tac) >>
               qpat_x_assum ‘MEM ev aevs’ (fn th => simp[th]) >>
               qpat_x_assum ‘ev_name ev = _’ (fn th => simp[th]) >> NO_TAC,
               qpat_x_assum ‘EVERY _ shevs’ mp_tac >> simp[EVERY_MEM] >>
               disch_then (qspec_then ‘ev’ mp_tac) >>
               qpat_x_assum ‘MEM ev shevs’ (fn th => simp[th]) >>
               qpat_x_assum ‘ev_name ev = _’ (fn th => simp[th]) >> NO_TAC]) >>
  ‘¬(EL c wt.chans).broken’ by (gvs[cflow_def] >> metis_tac[]) >>
  ‘¬(EL c wa.chans).shut ∧ (EL c wa.chans).inflight = 0 ∧ wa.ch = w.ch’
    by gvs[cflow_def] >>
  qpat_x_assum ‘∀ev. MEM ev tevs ∧ _ ⇒ _’ (qspec_then ‘ev’ mp_tac) >> simp[EXISTS_APPEND]
QED
