(*
  After L1 closes an fd f (with channel c), what the kernel took on c no
  longer changes: c is unused (the close went through) or still f's (an
  interrupted close kept it, POSIX close EINTR), and L1 never sends on an
  fd it no longer holds.  With this, the round lemma of honestL1PFOut is
  sharpened (tkx): an fd L1 closes in a round with nothing left to send
  had everything it was given taken by the kernel, unless L1 dropped its
  output (a send on it failed hard, or the write timeout dropped it, D23).
*)
Theory honestL1PFDead
Ancestors
  honestL1PFFlushLive honestL1PFFlush honestL1PFOut honestL0WorldProps honestL1PFRound
  honestL1PFRefine honestL1PFInv honestL1PFModel honestL1Steps honestL1Inv honestL1Props
  honestL1Model honestL0WorldInv honestL0Rely honestL0World honestL0 socketV2FFI
  asyncHLModel asyncCore Marshalling
Libs
  preamble

(* ------------------------------------------------------------------------
   A closed fd's channel
   ------------------------------------------------------------------------ *)

(* f's channel c, with sent sb: unused, or still f's *)
Definition dinv_def:
  dinv f c sb w ⇔ uchan c sb w ∨ (l0_chan_of w f = SOME c ∧ csent w c = sb)
End

Theorem close_fd_uchan:
  l0wf w ∧ l0_chan_of w f = SOME c ⇒ uchan c (csent w c) (close_fd f w)
Proof
  rw[close_fd_def, uchan_def] >> gvs[l0_chan_of_def, AllCaseEqs()] >>
  ‘MEM (f, c) w.open_fds’ by metis_tac[ALOOKUP_MEM] >>
  ‘ALL_DISTINCT (MAP SND w.open_fds) ∧
   ∀x. MEM x (MAP SND w.open_fds) ⇒ ¬MEM x (FLAT (MAP (SND o SND) w.listeners))’
    by gvs[l0wf_def, used_chans_def, ALL_DISTINCT_APPEND] >>
  simp[upd_lchan_def, used_chans_def, csent_def, EL_LUPDATE, MEM_MAP, MEM_FLAT,
       FORALL_PROD] >>
  rw[]
  >- (CCONTR_TAC >> gvs[] >> metis_tac[distinct_snd])
  >> CCONTR_TAC >> gvs[MEM_MAP, MEM_FLAT] >>
  first_x_assum (qspec_then ‘c’ mp_tac) >> simp[MEM_MAP, MEM_FLAT] >>
  conj_tac >- (qexists_tac ‘(f, c)’ >> simp[]) >>
  qexists_tac ‘l’ >> simp[] >> qexists_tac ‘(p_1, p_1', l)’ >> simp[]
QED

Theorem sys_close_dinv:
  winv w ∧ l0_chan_of w f = SOME c ∧ sys_close f w = SOME (out, w', ev) ⇒
  dinv f c (csent w c) w'
Proof
  rw[sys_close_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  ‘l0_chan_of (l0_tick «sys_close» w) f = SOME c ∧
   csent (l0_tick «sys_close» w) c = csent w c ∧ l0wf (l0_tick «sys_close» w)’
    by (‘c < LENGTH w.chans’ by metis_tac[chan_lt] >>
        ‘c < LENGTH (l0_tick «sys_close» w).chans ∧
         csent (l0_tick «sys_close» w) c = csent w c’ by metis_tac[csent_tick] >>
        gvs[l0_chan_of_def, winv_def, l0wf_tick, AllCaseEqs()]) >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >>
  simp[l0_call_def, fd_bytes_lfd] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  gvs[l0_close_def, AllCaseEqs(), fail_def, dinv_def] >>
  TRY (disj1_tac >> drule_all close_fd_uchan >>
       simp[uchan_def, used_chans_def, csent_def] >> NO_TAC) >>
  disj2_tac >> gvs[l0_chan_of_def, csent_def]
QED

Theorem sys_dinv:
  winv w ∧ dinv f c sb w ⇒
  (sys_recv g k w = SOME (out, w', ev) ⇒ dinv f c sb w') ∧
  (sys_accept g w = SOME (out, w', ev) ⇒ dinv f c sb w') ∧
  (sys_poll fes w = SOME (out, w', ev) ⇒ dinv f c sb w') ∧
  (sys_send g bs w = SOME (out, w', ev) ∧ g ≠ f ∧ small_send ev ⇒ dinv f c sb w') ∧
  (sys_close g w = SOME (out, w', ev) ⇒ dinv f c sb w')
Proof
  strip_tac >> qpat_x_assum ‘dinv _ _ _ _’ mp_tac >> simp[dinv_def] >> strip_tac
  >- (‘wpres (uchan c sb)’ by simp[wpres_uchan] >>
      drule_all sys_wpres >> strip_tac >> rpt conj_tac >> rpt strip_tac >>
      disj1_tac >> metis_tac[]) >>
  rpt conj_tac >> rpt strip_tac
  >- (disj2_tac >> drule_all (cj 2 sys_csents) >> simp[])
  >- (disj2_tac >> drule_all (cj 3 sys_csents) >> simp[])
  >- (disj2_tac >> drule_all (cj 1 sys_csents) >> simp[])
  >- (disj2_tac >> drule_all sys_send_csent >> simp[])
  >> Cases_on ‘g = f’ >> gvs[]
  >- (drule_all sys_close_dinv >> simp[dinv_def])
  >> disj2_tac >> drule_all (cj 4 sys_csents) >> simp[]
QED

Theorem l1_close_dinv:
  l1_close g (w, st) = SOME ((w', st'), evs) ∧ winv w ∧ dinv f c sb w ⇒ dinv f c sb w'
Proof
  rw[l1_close_def, AllCaseEqs()] >> metis_tac[sys_dinv]
QED

Theorem l1_polls_dinv:
  ∀chs w rv w' evs. l1_polls chs w = SOME (rv, w', evs) ∧ winv w ∧ dinv f c sb w ⇒
    dinv f c sb w'
Proof
  Induct >> simp[l1_polls_def] >> rw[AllCaseEqs()] >> metis_tac[sys_dinv, sys_winv]
QED

(* The flush leaves an fd with nothing to send (or gone) alone *)
Theorem l1_flush_dinv:
  ∀fs w b w' b' evs.
    l1_flush fs (w, b) = SOME ((w', b'), evs) ∧ winv w ∧ EVERY small_send evs ∧
    dinv f c sb w ∧ (outbox_of b f = [] ∨ MEM f b.gone) ⇒
    dinv f c sb w' ∧ evs_sent f evs = []
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac >>
  TRY (first_x_assum (qspecl_then [‘w’, ‘b’] mp_tac) >> simp[] >> metis_tac[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >>
  ‘h ≠ f’ by (strip_tac >> gvs[]) >>
  ‘dinv f c sb w''’ by metis_tac[sys_dinv] >>
  ‘winv w''’ by metis_tac[sys_winv] >>
  drule_all sys_send_other >> strip_tac >>
  first_x_assum (qspecl_then [‘w''’, ‘after_send h (l0_res_of out) b’] mp_tac) >>
  simp[outbox_of_after_send_other] >> disch_then irule >>
  gvs[after_send_def] >> every_case_tac >> gvs[MEM_FILTER]
QED

Theorem pf_fetch_dinv:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ winv w ∧ dinv f c sb w ⇒
    dinv f c sb w'
Proof
  Induct >> simp[pf_fetch_def] >> rw[AllCaseEqs()] >>
  TRY (pairarg_tac >> gvs[AllCaseEqs()]) >> metis_tac[sys_dinv, sys_winv]
QED

Theorem l1_reap_dinv:
  ∀fs w st w' st' evs.
    l1_reap fs (w, st) = SOME ((w', st'), evs) ∧ winv w ∧ dinv f c sb w ⇒ dinv f c sb w'
Proof
  Induct >> simp[l1_reap_def] >> rw[AllCaseEqs()] >>
  TRY (Cases_on ‘ws’) >> metis_tac[l1_close_dinv, l1_close_winv]
QED

(* An action on others leaves f's channel alone *)
Theorem pdo_dinv:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ winv w ∧ EVERY small_send evs ∧
  dinv f c sb w ∧ ¬MEM f (MAP SND ps.b.tbl) ⇒
  dinv f c sb w'
Proof
  strip_tac >> qpat_x_assum ‘dinv _ _ _ _’ mp_tac >> simp[dinv_def] >> strip_tac
  >- (disj1_tac >> irule pdo_wpres >> simp[wpres_uchan] >> metis_tac[])
  >> disj2_tac >> drule_all pdo_chan >> simp[]
QED
