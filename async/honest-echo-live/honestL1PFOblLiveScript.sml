(*
  D26 (design/48): S1 for servers polled through the LIVE interest list
  (asyncM4LiveInterest.live fds0: the handles handed out, less those whose
  Read returned end-of-file), and its converse live_held: a live handle
  other than the listener is in L1's table.

  The servers' side condition, reads_handed: a server reads only handles it
  was handed (interest fds0), never the listener.  (Without it a server
  could Read a predictable handle before its Accept, get end-of-file, and
  drop it from live while the Accept puts it in the table.)

  As S1_interest: proved on the handle layer, where L1's table is exactly
  the live list less the listener, and moved to the PF run by R1-safe.

  MAIN: S1_live, live_held.
*)
Theory honestL1PFOblLive
Ancestors
  honestL1PFObl asyncM4LiveInterest honestL1PFLive honestL1PFRefine honestL1PFModel
  honestL1Model asyncHLModel asyncM4Loop asyncM3World asyncCore asyncLevel1 alist
Libs
  preamble

Definition reads_handed_def:
  reads_handed lfd fds0 m ⇔
    (∀h. MEM h fds0 ⇒ h = lfd) ∧
    ∀hh h k. MEM (Read h k) (new_actions (log_of m) hh) ⇒ MEM h (interest fds0 hh) ∧ h ≠ lfd
End

Theorem MEM_add_accepted:
  ∀rs fds. MEM x (add_accepted fds rs) ⇔ MEM x fds ∨ MEM (Accepted (SOME x)) rs
Proof
  Induct >> rw[add_accepted_def] >> every_case_tac >> simp[] >> metis_tac[]
QED

(* The handles: the listener's number skipped; valid ones are distinct *)
Definition hvalid_def:
  hvalid (lfd : word64) j ⇔ hdln (w2n lfd) j < dimword (:64)
End

Theorem hdl_not_lfd:
  hvalid lfd j ⇒ hdl lfd j ≠ lfd
Proof
  rw[hvalid_def, hdl_def, hdln_def] >> strip_tac >>
  ‘w2n (n2w (if j < w2n lfd then j else j + 1) : word64) = w2n lfd’ by simp[] >>
  pop_assum mp_tac >> simp[] >> rw[] >> fs[]
QED

Theorem hdl_inj:
  hvalid lfd j ∧ hvalid lfd j' ∧ hdl lfd j = hdl lfd j' ⇒ j = j'
Proof
  rw[hvalid_def, hdl_def] >>
  ‘hdln (w2n lfd) j = hdln (w2n lfd) j'’ by gvs[LESS_MOD] >>
  fs[hdln_def] >> rw[] >> fs[] >> every_case_tac >> fs[]
QED

Theorem MAP_FST_ADELKEY_MEM:
  MEM x (MAP FST (ADELKEY h l)) ⇔ MEM x (MAP FST l) ∧ x ≠ h
Proof
  simp[ADELKEY_def, MEM_MAP, MEM_FILTER, EXISTS_PROD] >> metis_tac[]
QED

Theorem hdo_live:
  hdo lfd (s, hs) a = SOME (r, (s1, hs1), evs) ∧
  (∀h. MEM h (MAP FST hs.tbl) ⇒ h ≠ lfd ∧ ∃j. j < hs.nxt ∧ hvalid lfd j ∧ h = hdl lfd j) ⇒
  hs.nxt ≤ hs1.nxt ∧
  (∀h. MEM h (MAP FST hs1.tbl) ⇒ h ≠ lfd ∧ ∃j. j < hs1.nxt ∧ hvalid lfd j ∧ h = hdl lfd j) ∧
  (∀h. r = Accepted (SOME h) ⇒ ∃j. hs.nxt ≤ j ∧ j < hs1.nxt ∧ hvalid lfd j ∧ h = hdl lfd j) ∧
  (∀h. MEM h (MAP FST hs1.tbl) ⇔
         (MEM h (MAP FST hs.tbl) ∨ r = Accepted (SOME h)) ∧ ¬∃k. a = Read h k ∧ r = Got (SOME []))
Proof
  strip_tac >> Cases_on ‘a’ >> gvs[hdo_def, AllCaseEqs()] >>
  TRY (‘hvalid lfd hs.nxt’ by simp[hvalid_def]) >>
  rpt conj_tac >> rpt strip_tac >> gvs[hdl_not_lfd, MAP_FST_ADELKEY_MEM] >>
  TRY (qexists_tac ‘hs.nxt’ >> simp[] >> NO_TAC) >>
  TRY (res_tac >> qexists_tac ‘j’ >> simp[] >> NO_TAC) >>
  TRY (res_tac >> fs[] >> NO_TAC) >>
  TRY (fs[ALOOKUP_NONE] >> metis_tac[] >> NO_TAC) >> metis_tac[]
QED

(* One round's actions on the handle layer: the table after them is the
   table before, plus the handles accepted, less those read to EOF; the
   accepted handles are fresh *)
Theorem hacts_live:
  ∀acts s hs rs evs s' hs'.
    hacts lfd (s, hs) acts = SOME (rs, evs, (s', hs')) ∧
    (∀h. MEM h (MAP FST hs.tbl) ⇒ h ≠ lfd ∧ ∃j. j < hs.nxt ∧ hvalid lfd j ∧ h = hdl lfd j) ∧
    (∀h k. MEM (Read h k) acts ⇒ h ≠ lfd ∧ ∀j. hs.nxt ≤ j ∧ hvalid lfd j ⇒ h ≠ hdl lfd j) ⇒
    LENGTH rs = LENGTH acts ∧ hs.nxt ≤ hs'.nxt ∧
    (∀h. MEM (Accepted (SOME h)) rs ⇒ ∃j. hs.nxt ≤ j ∧ j < hs'.nxt ∧ hvalid lfd j ∧ h = hdl lfd j) ∧
    (∀h. MEM h (MAP FST hs'.tbl) ⇔
           (MEM h (MAP FST hs.tbl) ∨ MEM (Accepted (SOME h)) rs) ∧
           ¬∃k. MEM (Read h k, Got (SOME [])) (ZIP (acts, rs)))
Proof
  Induct >- simp[hacts_def] >> rpt gen_tac >> simp[Once hacts_def, AllCaseEqs()] >>
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >> fs[] >>
  rpt BasicProvers.VAR_EQ_TAC >> PairCases_on ‘st1’ >>
  rename1 ‘hdo lfd (s, hs) a = SOME (r1, (s1, hs1), evs1)’ >>
  drule hdo_live >> impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  first_x_assum (drule_then mp_tac) >>
  impl_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >> rpt gen_tac >> strip_tac >>
      qpat_x_assum ‘∀h' k. Read h' k = a ∨ _ ⇒ _’ (qspecl_then [‘h’, ‘k’] mp_tac) >>
      simp[] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  strip_tac >> rpt conj_tac
  >- simp[]
  >- simp[]
  >- (rw[] >> res_tac >> qexists_tac ‘j’ >> simp[])
  >> qx_gen_tac ‘x’ >> asm_rewrite_tac [] >>
  ‘MEM (Accepted (SOME x)) rs' ⇒ ∀k. a ≠ Read x k’
    by (rpt strip_tac >> res_tac >> gvs[] >>
        qpat_x_assum ‘∀h' k'. _’ (qspecl_then [‘hdl lfd j’, ‘k’] mp_tac) >>
        impl_tac >- simp[] >> strip_tac >>
        pop_assum (qspec_then ‘j’ mp_tac) >> fs[]) >>
  simp[] >> metis_tac[]
QED

Theorem live_round_nil:
  live_round fds acts [] = fds
Proof
  Cases_on ‘acts’ >> simp[live_round_def, eof_reads_def, add_accepted_def, FILTER_T]
QED

Theorem MEM_ZIP_FST'[local]:
  ∀l1 l2. MEM (x, r) (ZIP (l1, l2)) ∧ LENGTH l1 = LENGTH l2 ⇒ MEM x l1
Proof
  Induct >> Cases_on ‘l2’ >> simp[] >> metis_tac[]
QED

(* The handle layer, polled through the live list: L1's table is the live
   list less the listener; the listener stays live; every handle handed out
   so far is the listener or a valid issued handle *)
Theorem hl_live_inv:
  reads_handed lfd fds0 m ∧ MEM lfd fds0 ⇒
  ∀n. (∀h. MEM h (MAP FST (SND (hst lfd (live fds0 (log_of m)) m s0 n)).tbl) ⇔
           MEM h (live fds0 (log_of m) (hhist lfd (live fds0 (log_of m)) m s0 n)) ∧ h ≠ lfd) ∧
      MEM lfd (live fds0 (log_of m) (hhist lfd (live fds0 (log_of m)) m s0 n)) ∧
      (∀h. MEM h (live fds0 (log_of m) (hhist lfd (live fds0 (log_of m)) m s0 n)) ⇒
           MEM h (interest fds0 (hhist lfd (live fds0 (log_of m)) m s0 n))) ∧
      (∀h. MEM h (interest fds0 (hhist lfd (live fds0 (log_of m)) m s0 n)) ⇒
           h = lfd ∨
           ∃j. j < (SND (hst lfd (live fds0 (log_of m)) m s0 n)).nxt ∧ hvalid lfd j ∧
               h = hdl lfd j)
Proof
  strip_tac >> Induct
  >- (simp[hst_def, hhist_def, hrounds_def, hinit_def] >> fs[reads_handed_def] >> metis_tac[]) >>
  qabbrev_tac ‘ifds = live fds0 (log_of m)’ >>
  Cases_on ‘hacts_tot lfd (hst lfd ifds m s0 n) (hacts_of lfd ifds m s0 n)’ >>
  rename1 ‘_ = (rs, x)’ >> PairCases_on ‘x’ >> rename1 ‘_ = (rs, evs, s1, hs1)’ >>
  drule hround_step >> strip_tac >> asm_rewrite_tac [] >>
  simp[Abbr ‘ifds’, live_SNOC, interest_SNOC, ssnap_def] >>
  qabbrev_tac ‘H = hhist lfd (live fds0 (log_of m)) m s0 n’ >>
  qabbrev_tac ‘L = live fds0 (log_of m) H’ >>
  qabbrev_tac ‘I0 = interest fds0 H’ >>
  qabbrev_tac ‘acts = new_actions (log_of m) H’ >>
  Cases_on ‘hst lfd (live fds0 (log_of m)) m s0 n’ >> rename1 ‘_ = (s, hs)’ >> fs[] >>
  ‘hacts_of lfd (live fds0 (log_of m)) m s0 n = acts’ by simp[hacts_of_def, Abbr ‘acts’] >>
  fs[hacts_tot_def] >>
  Cases_on ‘hacts lfd (s, hs) acts’ >> fs[]
  >- (gvs[live_round_nil, add_accepted_def] >> metis_tac[]) >>
  qpat_x_assum ‘x = _’ SUBST_ALL_TAC >>
  ‘∀h k. MEM (Read h k) acts ⇒ MEM h I0 ∧ h ≠ lfd’
    by (qpat_x_assum ‘reads_handed _ _ _’ mp_tac >> simp[reads_handed_def, Abbr ‘acts’, Abbr ‘I0’] >>
        metis_tac[]) >>
  drule hacts_live >> impl_tac
  >- (conj_tac
      >- (rpt gen_tac >> strip_tac >>
          ‘MEM h L ∧ h ≠ lfd’ by (qpat_assum ‘∀h. MEM h (MAP FST hs.tbl) ⇔ _’
                                    (fn th => mp_tac (Q.SPEC ‘h’ th)) >> asm_rewrite_tac []) >>
          ‘MEM h I0’ by (qpat_assum ‘∀h. MEM h L ⇒ _’ irule >> first_assum ACCEPT_TAC) >>
          qpat_assum ‘∀h. MEM h I0 ⇒ _’ (qspec_then ‘h’ mp_tac) >>
          impl_tac >- first_assum ACCEPT_TAC >> strip_tac >> TRY (fs[] >> NO_TAC) >>
          conj_tac >- first_assum ACCEPT_TAC >> qexists_tac ‘j’ >> asm_rewrite_tac [])
      >> rpt gen_tac >> strip_tac >>
      qpat_assum ‘∀h k. MEM (Read h k) acts ⇒ _’ (drule_then strip_assume_tac) >>
      qpat_assum ‘∀h. MEM h I0 ⇒ _’ (drule_then strip_assume_tac) >>
      TRY (fs[] >> NO_TAC) >> conj_tac >- first_assum ACCEPT_TAC >> rpt strip_tac >>
      ‘j = j'’ by (irule hdl_inj >> qexists_tac ‘lfd’ >> fs[]) >> fs[]) >>
  strip_tac >>
  ‘LENGTH acts = LENGTH rs’ by simp[] >>
  qpat_assum ‘LENGTH acts = LENGTH rs’ (fn th => REWRITE_TAC [MATCH_MP MEM_live_round th]) >>
  REWRITE_TAC [MEM_add_accepted] >> rpt conj_tac
  >- (qx_gen_tac ‘x’ >>
      qpat_x_assum ‘∀h. MEM h (MAP FST hs1.tbl) ⇔ _’ (fn th => REWRITE_TAC [th]) >>
      qpat_x_assum ‘∀h. MEM h (MAP FST hs.tbl) ⇔ _’ (fn th => REWRITE_TAC [th]) >>
      Cases_on ‘MEM (Accepted (SOME x)) rs’ >> pop_assum (fn th => REWRITE_TAC [th] >> assume_tac th)
      >- (‘x ≠ lfd’
            by (qpat_x_assum ‘∀h. MEM (Accepted (SOME h)) rs ⇒ _’ drule >> strip_tac >>
                pop_assum SUBST1_TAC >> irule hdl_not_lfd >> first_assum ACCEPT_TAC) >>
          pop_assum (fn th => REWRITE_TAC [th]) >> REWRITE_TAC [] >> rpt (pop_assum kall_tac) >> metis_tac[])
      >> rpt (pop_assum kall_tac) >> metis_tac[])
  >- (disj1_tac >> first_assum ACCEPT_TAC)
  >- (rpt strip_tac >> drule MEM_ZIP_FST' >> impl_tac >- first_assum ACCEPT_TAC >>
      strip_tac >> qpat_x_assum ‘∀h k. MEM (Read h k) acts ⇒ _’ drule >>
      REWRITE_TAC [])
  >- (rpt strip_tac
      >- (disj1_tac >> qpat_x_assum ‘∀h. MEM h L ⇒ _’ irule >> first_assum ACCEPT_TAC)
      >> disj2_tac >> first_assum ACCEPT_TAC)
  >> rpt strip_tac
  >- (qpat_x_assum ‘∀h. MEM h I0 ⇒ _’ drule >> strip_tac
      >- (disj1_tac >> first_assum ACCEPT_TAC)
      >> disj2_tac >> qexists_tac ‘j’ >> asm_rewrite_tac [] >>
      irule LESS_LESS_EQ_TRANS >> qexists_tac ‘hs.nxt’ >> asm_rewrite_tac [])
  >> qpat_x_assum ‘∀h. MEM (Accepted (SOME h)) rs ⇒ _’ drule >> strip_tac >>
  disj2_tac >> qexists_tac ‘j’ >> asm_rewrite_tac []
QED

(* On the PF run, by R1-safe: L1's table is the live list less the
   listener, and the listener is live *)
Theorem pf_tbl_live:
  run_ok lfd pol (live fds0 (log_of m)) m w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol (live fds0 (log_of m)) m w0 n) + 1 < dimword (:64)) ∧
  MEM lfd fds0 ∧ reads_handed lfd fds0 m ⇒
  ∀n. (∀h. MEM h (MAP FST (rstate lfd pol (live fds0 (log_of m)) m w0 n).b.tbl) ⇔
           MEM h (live fds0 (log_of m) (rhist lfd pol (live fds0 (log_of m)) m w0 n)) ∧ h ≠ lfd) ∧
      MEM lfd (live fds0 (log_of m) (rhist lfd pol (live fds0 (log_of m)) m w0 n))
Proof
  strip_tac >> gen_tac >>
  ‘l0_rely w0’ by fs[run_ok_def] >>
  drule_then (qspec_then ‘n’ assume_tac) prun_some >>
  Cases_on ‘prun lfd pol (live fds0 (log_of m)) m w0 n’ >> rename1 ‘_ = (hh, x)’ >>
  PairCases_on ‘x’ >>
  mp_tac (Q.INST [‘ifds’ |-> ‘live fds0 (log_of m)’] l1pf_refines_hl) >>
  impl_tac >- simp[] >> disch_then drule >> strip_tac >>
  mp_tac (Q.INST [‘s0’ |-> ‘psk lfd pol (live fds0 (log_of m)) m w0’] hl_live_inv) >>
  impl_tac >- simp[] >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  gvs[rstate_def, rhist_def, hs_of_def]
QED

(* MAIN (D26): S1 for the live interest list *)
Theorem S1_live:
  run_ok lfd pol (live fds0 (log_of m)) m w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol (live fds0 (log_of m)) m w0 n) + 1 < dimword (:64)) ∧
  MEM lfd fds0 ∧ reads_handed lfd fds0 m ⇒
  S1 lfd pol (live fds0 (log_of m)) m w0
Proof
  strip_tac >> drule_all pf_tbl_live >> strip_tac >> simp[S1_def] >>
  TRY (conj_tac >- (gen_tac >> first_x_assum (qspec_then ‘n’ strip_assume_tac))) >>
  (rpt strip_tac >> first_x_assum (qspec_then ‘n’ strip_assume_tac) >>
      imp_res_tac ALOOKUP_MEM >>
      ‘MEM h (MAP FST (rstate lfd pol (live fds0 (log_of m)) m w0 n).b.tbl)’
        by (REWRITE_TAC [MEM_MAP] >> qexists_tac ‘(h, f)’ >> REWRITE_TAC [FST] >>
            first_assum ACCEPT_TAC) >>
      metis_tac[])
QED

(* MAIN (D26): a live handle other than the listener is held by L1 *)
Theorem live_held:
  run_ok lfd pol (live fds0 (log_of m)) m w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol (live fds0 (log_of m)) m w0 n) + 1 < dimword (:64)) ∧
  MEM lfd fds0 ∧ reads_handed lfd fds0 m ⇒
  ∀n h. MEM h (live fds0 (log_of m) (rhist lfd pol (live fds0 (log_of m)) m w0 n)) ∧ h ≠ lfd ⇒
        ∃f. ALOOKUP (rstate lfd pol (live fds0 (log_of m)) m w0 n).b.tbl h = SOME f
Proof
  strip_tac >> drule_all pf_tbl_live >> rpt strip_tac >>
  first_x_assum (qspec_then ‘n’ strip_assume_tac) >>
  ‘MEM h (MAP FST (rstate lfd pol (live fds0 (log_of m)) m w0 n).b.tbl)’ by metis_tac[] >>
  Cases_on ‘ALOOKUP (rstate lfd pol (live fds0 (log_of m)) m w0 n).b.tbl h’ >> fs[ALOOKUP_NONE]
QED
