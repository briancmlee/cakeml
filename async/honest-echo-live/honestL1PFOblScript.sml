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
  honestL1PFLive honestL1PFRound honestL1PFRefine honestL1PFModel honestL1Model asyncHLModel asyncM4Loop
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

(* ------------------------------------------------------------------------
   An fd's inbox within a round: L1 only drops a prefix of it, unless it
   fetches on the fd
   ------------------------------------------------------------------------ *)

(* One action drops a prefix of f's inbox; a Read on f's handle while the
   inbox is not empty drops at least one byte; f's handle stays bound to f
   while the inbox is not empty (an Accept binds a fresh handle) *)
Theorem pdo_inb:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ⇒
  ps.b.nxt ≤ ps'.b.nxt ∧
  ∀f. ∃d. inb_of ps' f = DROP d (inb_of ps f) ∧
      ∀h. (ALOOKUP ps.b.tbl h = SOME f ∧ inb_of ps f ≠ [] ⇒
       (∀k. a = Read h k ⇒ 0 < d) ∧
       ((a = Accept lfd ∧ l1hdln (w2n lfd) ps.b.nxt < dimword (:64) ⇒
         h ≠ l1hdl lfd ps.b.nxt) ⇒ ALOOKUP ps'.b.tbl h = SOME f))
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> rw[AllCaseEqs()] >> gvs[] >> rpt gen_tac >>
  TRY (PairCases_on ‘z’ >> gvs[]) >>
  TRY (drule l1_close_b >> strip_tac >> gvs[]) >>
  TRY (drule l1do_write_tbl >> strip_tac >> gvs[] >> qexists_tac ‘0’ >> simp[] >> NO_TAC) >>
  TRY (gvs[] >> NO_TAC) >>
  TRY (qexists_tac ‘0’ >> simp[] >> NO_TAC) >>
  TRY (IF_CASES_TAC >- (qexists_tac ‘n’ >> fs[]) >> qexists_tac ‘0’ >> fs[] >> NO_TAC) >>
  qexists_tac ‘0’ >> simp[] >>
  TRY (strip_tac >> fs[] >> NO_TAC) >>
  gen_tac >> strip_tac >> Cases_on ‘c = h’ >> fs[ALOOKUP_ADELKEY] >> rfs[]
QED

(* The actions of a round drop a prefix of f's inbox *)
Theorem pacts_inb_drop:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ⇒
    ∃d. inb_of ps' f = DROP d (inb_of ps f)
Proof
  Induct >> simp[pacts_def] >- (rpt strip_tac >> qexists_tac ‘0’ >> simp[]) >>
  rpt gen_tac >> simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 ‘pdo _ _ _ = SOME (r1, ws1, evs1)’ >> PairCases_on ‘ws1’ >>
  drule pdo_inb >> strip_tac >> pop_assum (qspec_then ‘f’ strip_assume_tac) >>
  first_x_assum drule >> strip_tac >> metis_tac[DROP_DROP_T]
QED

(* ... and a Read on f's handle while the inbox is not empty shortens it;
   the handle stays bound to f, as an Accept binds a fresh handle *)
Theorem pacts_inb_read:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧
    ALOOKUP ps.b.tbl h = SOME f ∧ inb_of ps f ≠ [] ∧
    (∀i. ps.b.nxt ≤ i ∧ l1hdln (w2n lfd) i < dimword (:64) ⇒ h ≠ l1hdl lfd i) ⇒
    MEM (Read h k) acts ⇒ LENGTH (inb_of ps' f) < LENGTH (inb_of ps f)
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘pacts _ _ _ = _’ (strip_assume_tac o SIMP_RULE (srw_ss()) [pacts_def, AllCaseEqs()]) >>
  rpt BasicProvers.VAR_EQ_TAC >> PairCases_on ‘ws1’ >>
  rename1 ‘pacts lfd (w1, ps1) acts = SOME _’ >>
  qpat_assum ‘pdo _ _ _ = _’ (strip_assume_tac o MATCH_MP pdo_inb) >>
  pop_assum (qspec_then ‘f’ strip_assume_tac) >>
  pop_assum (qspec_then ‘h’ assume_tac) >>
  ‘∃d2. inb_of ps' f = DROP d2 (inb_of ps1 f)’ by metis_tac[pacts_inb_drop] >>
  ‘LENGTH (inb_of ps1 f) ≤ LENGTH (inb_of ps f) ∧
   LENGTH (inb_of ps' f) ≤ LENGTH (inb_of ps1 f)’ by simp[LENGTH_DROP] >>
  Cases_on ‘inb_of ps1 f = []’
  >- (strip_tac >> ‘inb_of ps' f = []’ by fs[] >> simp[] >> Cases_on ‘inb_of ps f’ >> fs[]) >>
  ‘ALOOKUP ps1.b.tbl h = SOME f’
    by (qpat_x_assum ‘ALOOKUP ps.b.tbl h = SOME f ∧ _ ⇒ _’ mp_tac >> simp[] >>
        strip_tac >> first_x_assum irule >> strip_tac >> first_x_assum irule >> simp[]) >>
  simp[] >> strip_tac
  >- ((* the Read is this action *)
      rpt BasicProvers.VAR_EQ_TAC >>
      ‘0 < d’ by (qpat_x_assum ‘ALOOKUP ps.b.tbl h = SOME f ∧ _ ⇒ _’ mp_tac >> simp[]) >>
      ‘LENGTH (inb_of ps1 f) < LENGTH (inb_of ps f)’
        by (simp[LENGTH_DROP] >> Cases_on ‘inb_of ps f’ >> fs[]) >>
      simp[]) >>
  (* the Read is later *)
  ‘LENGTH (inb_of ps' f) < LENGTH (inb_of ps1 f)’ suffices_by
    (strip_tac >> conj_tac
     >- (Cases_on ‘d2’ >> simp[] >>
         qpat_x_assum ‘LENGTH _ < LENGTH _’ mp_tac >>
         qpat_x_assum ‘inb_of ps' f = _’ SUBST1_TAC >> simp[])
     >> Cases_on ‘inb_of ps f’ >> fs[]) >>
  first_x_assum (qspecl_then [‘w1’, ‘ps1’, ‘rs'’, ‘evs'’, ‘w'’, ‘ps'’] mp_tac) >>
  impl_tac >- (simp[] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  disch_then irule >> first_assum ACCEPT_TAC
QED

(* The fetch changes f's inbox only by fetching on f *)
Theorem pf_fetch_inb:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ ¬fetched f log ⇒
    inb_of ps' f = inb_of ps f
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[] >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs(), fetched_def] >>
  first_x_assum drule >> simp[fetched_def] >> rw[] >> gvs[]
QED

(* The round's tail (poll, flush, fetch, hang-ups, reap) leaves f's inbox
   alone unless it fetches on f *)
Theorem pf_tail_inb:
  pf_tail lfd pol hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ∧ ¬fetched f log ⇒
  inb_of ps' f = inb_of ps f
Proof
  rw[pf_tail_def, AllCaseEqs()] >> gvs[] >>
  drule_all pf_fetch_inb >> simp[hup_step_def, inb_of_def]
QED

(* A round: f's inbox loses a prefix, a strictly shorter one if the server
   read f's handle, unless L1 fetched on f *)
Theorem pround_inb:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧ ¬fetched f log ⇒
  (∃d. inb_of ps' f = DROP d (inb_of ps f)) ∧
  (ALOOKUP ps.b.tbl h = SOME f ∧ inb_of ps f ≠ [] ∧ MEM (Read h k) acts ∧
   (∀i. ps.b.nxt ≤ i ∧ l1hdln (w2n lfd) i < dimword (:64) ⇒ h ≠ l1hdl lfd i) ⇒
   LENGTH (inb_of ps' f) < LENGTH (inb_of ps f))
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> gvs[] >> PairCases_on ‘ws1’ >>
  rename1 ‘pf_tail _ _ _ (w1, ps1) = _’ >>
  ‘inb_of ps' f = inb_of ps1 f’ by metis_tac[pf_tail_inb] >> simp[] >> conj_tac
  >- (drule pacts_inb_drop >> simp[])
  >> strip_tac >> drule pacts_inb_read >> simp[] >>
  disch_then irule >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   f's handle stays bound to f while its inbox is not empty
   ------------------------------------------------------------------------ *)

Theorem l1_flush_tbl:
  ∀fs w st w' st' evs.
    l1_flush fs (w, st) = SOME ((w', st'), evs) ⇒ st'.tbl = st.tbl ∧ st'.nxt = st.nxt
Proof
  Induct >> rw[l1_flush_def, AllCaseEqs()] >> res_tac >> gvs[after_send_b]
QED

Theorem l1_reap_tbl:
  ∀fs w st w' st' evs.
    l1_reap fs (w, st) = SOME ((w', st'), evs) ⇒ st'.tbl = st.tbl ∧ st'.nxt = st.nxt
Proof
  Induct >> rw[l1_reap_def, AllCaseEqs()] >> TRY (PairCases_on ‘ws’) >>
  res_tac >> imp_res_tac l1_close_b >> gvs[]
QED

Theorem pf_fetch_b:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ⇒ ps'.b = ps.b
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[] >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >> res_tac >> gvs[]
QED

(* The round's tail keeps the handle table *)
Theorem pf_tail_tbl:
  pf_tail lfd pol hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ⇒
  ps'.b.tbl = ps.b.tbl ∧ ps'.b.nxt = ps.b.nxt
Proof
  rw[pf_tail_def, AllCaseEqs()] >> gvs[] >>
  imp_res_tac l1_flush_tbl >> imp_res_tac pf_fetch_b >> imp_res_tac l1_reap_tbl >>
  gvs[hup_step_def]
QED

(* If f's inbox is not empty after the actions, it never was empty on the way,
   so f's handle stayed bound to f (an Accept binds a fresh handle) *)
Theorem pacts_tbl_keep:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧
    ALOOKUP ps.b.tbl h = SOME f ∧ inb_of ps' f ≠ [] ∧
    (∀i. ps.b.nxt ≤ i ∧ l1hdln (w2n lfd) i < dimword (:64) ⇒ h ≠ l1hdl lfd i) ⇒
    ALOOKUP ps'.b.tbl h = SOME f ∧ ps.b.nxt ≤ ps'.b.nxt
Proof
  Induct >- simp[pacts_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘pacts _ _ _ = _’ (strip_assume_tac o SIMP_RULE (srw_ss()) [pacts_def, AllCaseEqs()]) >>
  rpt BasicProvers.VAR_EQ_TAC >> PairCases_on ‘ws1’ >>
  rename1 ‘pacts lfd (w1, ps1) acts = SOME _’ >>
  qpat_assum ‘pdo _ _ _ = _’ (strip_assume_tac o MATCH_MP pdo_inb) >>
  pop_assum (qspec_then ‘f’ strip_assume_tac) >>
  pop_assum (qspec_then ‘h’ assume_tac) >>
  ‘∃d2. inb_of ps' f = DROP d2 (inb_of ps1 f)’ by metis_tac[pacts_inb_drop] >>
  ‘inb_of ps1 f ≠ []’ by (strip_tac >> fs[]) >>
  ‘inb_of ps f ≠ []’ by (strip_tac >> fs[]) >>
  ‘ALOOKUP ps1.b.tbl h = SOME f’
    by (qpat_x_assum ‘ALOOKUP ps.b.tbl h = SOME f ∧ _ ⇒ _’ mp_tac >> simp[] >>
        strip_tac >> first_x_assum irule >> strip_tac >> first_x_assum irule >> simp[]) >>
  first_x_assum (qspecl_then [‘w1’, ‘ps1’, ‘rs'’, ‘evs'’, ‘w'’, ‘ps'’] mp_tac) >>
  impl_tac >- (simp[] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  simp[]
QED

(* A round without a fetch on f, after which f's inbox is not empty, keeps
   f's handle bound to f *)
Theorem pround_tbl_keep:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧ ¬fetched f log ∧
  ALOOKUP ps.b.tbl h = SOME f ∧ inb_of ps' f ≠ [] ∧
  (∀i. ps.b.nxt ≤ i ∧ l1hdln (w2n lfd) i < dimword (:64) ⇒ h ≠ l1hdl lfd i) ⇒
  ALOOKUP ps'.b.tbl h = SOME f ∧ ps.b.nxt ≤ ps'.b.nxt
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> gvs[] >> PairCases_on ‘ws1’ >>
  rename1 ‘pf_tail _ _ _ (w1, ps1) = _’ >>
  ‘inb_of ps' f = inb_of ps1 f’ by metis_tac[pf_tail_inb] >>
  drule pf_tail_tbl >> strip_tac >>
  drule pacts_tbl_keep >> disch_then (qspecl_then [‘h’, ‘f’] mp_tac) >> simp[] >>
  impl_tac >- fs[] >> simp[]
QED
