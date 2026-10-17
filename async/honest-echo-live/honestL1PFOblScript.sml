(*
  The server obligations of R1-live (honestL1PFLive's S1, honestL1PFConnRun's
  S2, S3), for servers whose poll interest is m4's `interest fds0`: the
  initial fds plus every handle the server was handed.

  S1 holds for every server: L1's handle table only ever holds handles
  that some Accept returned, and `interest` keeps every such handle.  It is
  proved on the handle layer (asyncHLModel), where a round is hacts then a
  poll, and moved to the PF run by R1-safe (l1pf_refines_hl: the same
  history, and the PF state's handle table is the handle layer's).
*)
Theory honestL1PFObl
Ancestors
  honestL1PFLive honestL1PFRefine honestL1PFModel asyncHLModel asyncM4Loop
  asyncM3World asyncCore asyncLevel1 alist
Libs
  preamble

(* ------------------------------------------------------------------------
   interest
   ------------------------------------------------------------------------ *)

Theorem add_accepted_mono:
  ∀rs fds x. MEM x fds ⇒ MEM x (add_accepted fds rs)
Proof
  Induct >> rw[add_accepted_def] >> first_x_assum irule >> CASE_TAC >> simp[] >>
  CASE_TAC >> simp[]
QED

Theorem add_accepted_new:
  ∀rs fds c. MEM (Accepted (SOME c)) rs ⇒ MEM c (add_accepted fds rs)
Proof
  Induct >> rw[add_accepted_def] >> simp[add_accepted_mono]
QED

(* ------------------------------------------------------------------------
   The handle layer: handles in the table were returned by an Accept
   ------------------------------------------------------------------------ *)

Theorem hdo_tbl:
  hdo lfd (s, hs) a = SOME (r, (s', hs'), evs) ∧ MEM h (MAP FST hs'.tbl) ⇒
  MEM h (MAP FST hs.tbl) ∨ r = Accepted (SOME h)
Proof
  Cases_on ‘a’ >> rw[hdo_def, AllCaseEqs()] >> gvs[] >>
  rpt (pairarg_tac >> gvs[AllCaseEqs()]) >>
  gvs[ADELKEY_def, MEM_MAP, MEM_FILTER, EXISTS_PROD] >> metis_tac[]
QED

Theorem hacts_tbl:
  ∀acts s hs rs evs s' hs' h.
    hacts lfd (s, hs) acts = SOME (rs, evs, (s', hs')) ∧ MEM h (MAP FST hs'.tbl) ⇒
    MEM h (MAP FST hs.tbl) ∨ MEM (Accepted (SOME h)) rs
Proof
  Induct >> rw[hacts_def, AllCaseEqs()] >> gvs[] >>
  rename1 ‘hdo _ _ _ = SOME (r1, st1, evs1)’ >> PairCases_on ‘st1’ >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  drule_all hdo_tbl >> strip_tac >> simp[]
QED

Theorem hl_tbl_interest:
  ∀n h. MEM h (MAP FST (SND (hst lfd (interest fds0) m s0 n)).tbl) ⇒
        MEM h (interest fds0 (hhist lfd (interest fds0) m s0 n))
Proof
  Induct >- simp[hst_def, hrounds_def, hinit_def] >>
  rpt strip_tac >>
  Cases_on ‘hacts_tot lfd (hst lfd (interest fds0) m s0 n)
              (hacts_of lfd (interest fds0) m s0 n)’ >>
  rename1 ‘_ = (rs, x)’ >> PairCases_on ‘x’ >>
  drule hround_step >> strip_tac >> gvs[interest_SNOC, ssnap_def] >>
  Cases_on ‘hst lfd (interest fds0) m s0 n’ >> rename1 ‘_ = (s, hs)’ >> gvs[] >>
  gvs[hacts_tot_def, AllCaseEqs()] >>
  TRY (irule add_accepted_mono >> first_x_assum irule >> simp[] >> NO_TAC) >>
  drule_all hacts_tbl >> strip_tac
  >- (irule add_accepted_mono >> first_x_assum irule >> simp[])
  >> irule add_accepted_new >> simp[]
QED

(* ------------------------------------------------------------------------
   S1 on the PF run
   ------------------------------------------------------------------------ *)

(* MAIN: every server polled through `interest fds0`, with the listener
   among fds0, meets S1 *)
Theorem S1_interest:
  run_ok lfd pol (interest fds0) m w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol (interest fds0) m w0 n) + 1 < dimword (:64)) ∧
  MEM lfd fds0 ⇒
  S1 lfd pol (interest fds0) m w0
Proof
  strip_tac >> simp[S1_def] >> conj_tac
  >- (rpt strip_tac >>
      ‘l0_rely w0’ by fs[run_ok_def] >>
      drule_then (qspec_then ‘n’ assume_tac) prun_some >>
      Cases_on ‘prun lfd pol (interest fds0) m w0 n’ >> rename1 ‘_ = (hh, x)’ >>
      PairCases_on ‘x’ >>
      mp_tac (Q.INST [‘ifds’ |-> ‘interest fds0’] l1pf_refines_hl) >>
      impl_tac >- simp[] >> disch_then drule >> strip_tac >>
      gvs[rstate_def, rhist_def] >>
      irule hl_tbl_interest >>
      simp[hs_of_def, MEM_MAP, EXISTS_PROD] >>
      imp_res_tac ALOOKUP_MEM >> metis_tac[])
  >> gen_tac >> qspec_tac (‘rhist lfd pol (interest fds0) m w0 n’, ‘hh’) >>
  ho_match_mp_tac SNOC_INDUCT >> simp[SNOC_APPEND, interest_SNOC] >>
  rpt strip_tac >> irule add_accepted_mono >> simp[]
QED
