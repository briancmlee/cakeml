(*
  (3b) of flush_live's drop disjunct, for the strong claim (D23, D34, D36):
  under stall_drains (the peer reads within K = pf_sendwait output polls,
  and once nothing is in flight the first output poll and the first send
  on the episode's fd are not retried) and [F2], the write timeout never
  drops an episode's fd, unless a recv on it failed hard in the drop's
  round (D19 (a)'s FReset) or its channel broke while the episode was open
  (D34's broken_open).

  The argument, over the drop's window of K stalled rounds i0 .. k
  (rdrop_timeout): each round has one poll, listing f for output, and no
  send on f after it takes bytes.
   - At a round whose poll starts with nothing in flight on c, D36 makes
     that poll and the next send on f not retried; an unbroken channel with
     nothing in flight shows POLLOUT ([F2]), so L1 sends on f after the
     poll: a non-retried send in the window, a contradiction.
   - So the first round's poll starts with bytes in flight, and
     stall_drains drains them within K − 1 output polls.  No send on f in
     the window takes bytes, so a channel's in-flight count only falls: the
     next round's poll starts with nothing in flight, the case above.

  TEMPORARY COPIES (remove when honestL1BStmts is resynced to L3-00): the
  definitions stall_drains36 and broken_open36 are verbatim copies of
  kernelStatements' stall_drains (with D36) and broken_open (final/L3-06-r2
  @051ab8890).

  MAIN: rdrop_broken.
*)
Theory honestL1PFDropBroken
Ancestors
  honestEchoL0NoClose honestEchoL0Excuse honestEchoL0LiveOwn honestEchoL0Spec honestEchoL0Drains
  honestEchoL0Inv honestEchoL0Out honestL1PFConn honestL1PFConnRun honestEchoL0Trace honestL1PFConnTrace honestL1PFOutLive honestL1PFLive
  honestL1PFFlushLive honestL1PFFlush honestL1PFDead honestL1PFOut honestL1BFaith honestL1BCorr
  honestL1BStmts honestL1PFRound honestL1PFRefine honestL1PFInv honestL1PFModel
  honestL1Model honestL0WorldInv honestL0Rely honestL0World
Libs
  preamble

(* TEMPORARY COPY: kernelStatements.stall_drains (D23, D30, D36) *)
Definition stall_drains36_def:
  stall_drains36 K w0 io j c ⇔
    (∀evs mid w.
      LPREFIX (fromList (evs ++ mid)) io ∧ ep_open j evs ∧
      world_at w0 (evs ++ mid) = SOME w ∧ c < LENGTH w.chans ∧
      0 < (EL c w.chans).inflight ⇒
      ∃more w'. LPREFIX (fromList (evs ++ mid ++ more)) io ∧
                n_out_polls (EL j (l0_accepted evs))
                  (ep_polls (EL j (l0_accepted evs)) mid more) < K ∧
                world_at w0 (evs ++ mid ++ more) = SOME w' ∧ c < LENGTH w'.chans ∧
                (EL c w'.chans).inflight = 0 ∧
                ∀more2 ev.
                  LPREFIX (fromList (evs ++ mid ++ more ++ more2 ++ [ev])) io ∧
                  ep_open j (evs ++ mid ++ more ++ more2) ∧
                  n_out_polls (EL j (l0_accepted evs))
                    (ep_polls (EL j (l0_accepted evs)) mid (more ++ more2)) < K ∧
                  ¬EXISTS (ev_on «sys_send» (EL j (l0_accepted evs))) more2 ∧
                  ev_on «sys_send» (EL j (l0_accepted evs)) ev ⇒
                  ¬retried ev) ∧
    ∀evs w mid ev.
      LPREFIX (fromList (evs ++ mid ++ [ev])) io ∧ ep_open j (evs ++ mid) ∧
      world_at w0 evs = SOME w ∧ c < LENGTH w.chans ∧ (EL c w.chans).inflight = 0 ∧
      n_out_polls (EL j (l0_accepted evs)) (ep_polls (EL j (l0_accepted evs)) evs mid) < K ∧
      ((¬EXISTS (out_poll (EL j (l0_accepted evs))) mid ∧ out_poll (EL j (l0_accepted evs)) ev) ∨
       (¬EXISTS (ev_on «sys_send» (EL j (l0_accepted evs))) mid ∧
        ev_on «sys_send» (EL j (l0_accepted evs)) ev)) ⇒
      ¬retried ev
End

(* TEMPORARY COPY: kernelStatements.broken_open (D34) *)
Definition broken_open36_def:
  broken_open36 w0 io j c ⇔
    ∃pre ev post f w.
      LPREFIX (fromList (pre ++ [ev] ++ post)) io ∧ LENGTH (l0_accepted pre) = j ∧
      l0_event_accepted ev = SOME f ∧ ¬EXISTS (l0_close_call f) post ∧
      world_at w0 (pre ++ [ev] ++ post) = SOME w ∧
      c < LENGTH w.chans ∧ (EL c w.chans).broken
End

(* ------------------------------------------------------------------------
   One round of the window
   ------------------------------------------------------------------------ *)

Theorem send_name_facts:
  ev_name e = ExtCall «sys_send» ⇒
  ¬ep_ends g e ∧ ¬l0_close_call g e ∧ ¬out_poll g e ∧ ¬closes_call g e
Proof
  Cases_on ‘e’ >> rw[ev_name_def] >>
  simp[ep_ends_def, l0_event_closed_def, l0_event_accepted_def, l0_close_call_def,
       out_poll_def, closes_call_def]
QED

Theorem poll_facts:
  out_poll f e ⇒ ¬ep_ends g e ∧ ¬closes_call g e ∧ ev_name e = ExtCall «sys_poll»
Proof
  rw[out_poll_def] >>
  simp[ep_ends_def, l0_event_closed_def, l0_event_accepted_def, closes_call_def, ev_name_def]
QED

Theorem not_poll_name:
  ev_name e ≠ ExtCall «sys_poll» ⇒ ¬out_poll f e
Proof
  Cases_on ‘e’ >> rw[out_poll_def, ev_name_def] >> metis_tac[]
QED

Theorem close_call_closes:
  l0_close_call f e ⇒ closes_call f e
Proof
  Cases_on ‘e’ >> rw[l0_close_call_def, closes_call_def]
QED

Theorem noclose_of:
  ¬EXISTS (closes_call f) l ⇒ ¬EXISTS (l0_close_call f) l
Proof
  simp[EVERY_MEM] >> metis_tac[close_call_closes]
QED

(* ------------------------------------------------------------------------
   The round's actions, from a stalled fd
   ------------------------------------------------------------------------ *)

Theorem sys_close_call3[local]:
  sys_close g w = SOME (out, w', ev) ⇒ (closes_call f ev ⇔ g = f)
Proof
  rw[sys_close_def] >> drule l0_do_cases >> rw[] >> simp[closes_call_def] >>
  ‘LENGTH (fd_bytes g) = 8’ by simp[] >> simp[] >> metis_tac[]
QED

(* An action that makes no close call on f keeps f's channel *)
Theorem pdo_chan_noclose:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ winv w ∧ l0_chan_of w f = SOME c ∧
  ¬EXISTS (closes_call f) evs ⇒
  l0_chan_of w' f = SOME c
Proof
  strip_tac >> Cases_on ‘a’
  >- gvs[pdo_def, AllCaseEqs()]
  >- (qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def] >>
      rw[AllCaseEqs()] >> gvs[] >>
      PairCases_on ‘z’ >> gvs[] >>
      drule l1_close_shape >> strip_tac >> gvs[] >>
      drule sys_close_call3 >> disch_then (qspec_then ‘f’ assume_tac) >> gvs[] >>
      irule sys_close_chan >> metis_tac[]) >>
  qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def, PULL_EXISTS] >> rpt gen_tac >>
  PairCases_on ‘z’ >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum ‘l1do _ _ _ = _’ mp_tac >> simp[l1do_def] >>
  rw[AllCaseEqs()] >> gvs[] >> metis_tac[sys_cflow]
QED

Theorem pacts_chan_noclose:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ winv w ∧ l0_chan_of w f = SOME c ∧
    ¬EXISTS (closes_call f) evs ⇒
    l0_chan_of w' f = SOME c
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  PairCases_on ‘ws1’ >> rename1 ‘pdo lfd (w, ps) a = SOME (r, (w1, ps1), evs1)’ >>
  ‘winv w1’ by metis_tac[pdo_winv] >>
  ‘l0_chan_of w1 f = SOME c’ by (irule pdo_chan_noclose >> fs[] >> metis_tac[]) >>
  first_x_assum irule >> fs[] >> metis_tac[]
QED

Theorem names_not_accepted:
  ev_name e = ExtCall «sys_send» ∨ ev_name e = ExtCall «sys_close» ⇒
  l0_event_accepted e ≠ SOME f
Proof
  Cases_on ‘e’ >> rename1 ‘IO_event nm _ _’ >> Cases_on ‘nm’ >>
  rw[ev_name_def, l0_event_accepted_def]
QED

Theorem closed_closes_call:
  l0_event_closed e = SOME f ⇒ closes_call f e
Proof
  Cases_on ‘e’ >> rename1 ‘IO_event nm _ _’ >> Cases_on ‘nm’ >>
  rw[l0_event_closed_def, closes_call_def, AllCaseEqs()]
QED

(* The actions of a round that stalls f: f's outbox is not empty after
   them, so L1 held f before them (only an Accept gives L1 an fd, from its
   queue, and the actions make no accept call), and they made no close
   call on f *)
Theorem pacts_stalled_owned:
  pacts lfd (w, ps) acts = SOME (rs, aevs, (wa, pa)) ∧ l0_rely w ∧
  own_ok lfd (k, opn) ps ∧ ps.b.nxt + naccepts acts < dimword (:64) ∧ okb ps.b ∧
  outbox_of pa.b f ≠ [] ⇒
  owned ps f ∧ ¬EXISTS (closes_call f) aevs ∧ ¬EXISTS (ep_ends f) aevs ∧ okb pa.b
Proof
  strip_tac >>
  ‘okb pa.b’ by (drule_all pacts_okb >> simp[]) >>
  ‘owned pa f’
    by (‘MEM f (MAP SND pa.b.tbl) ∨ MEM f pa.b.closing’ suffices_by (strip_tac >> simp[owned_def]) >>
        irule okb_held >> fs[]) >>
  drule_all pacts_cl >> disch_then (qspec_then ‘f’ assume_tac) >>
  qpat_x_assum ‘cl_ok _ _ _ _’ (fn th => qpat_assum ‘owned pa f’ (fn o1 =>
    MAP_EVERY assume_tac (CONJUNCTS (MATCH_MP (REWRITE_RULE [cl_ok_def] th) o1)))) >>
  drule pacts_names >> strip_tac >>
  ‘¬EXISTS (λe. l0_event_accepted e = SOME f) aevs’
    by (simp[EVERY_MEM] >> rpt strip_tac >>
        qpat_x_assum ‘EVERY _ aevs’ (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
        disch_then (qspec_then ‘e’ mp_tac) >> impl_tac >- first_assum ACCEPT_TAC >>
        disch_then (assume_tac o MATCH_MP names_not_accepted o BETA_RULE) >>
        pop_assum mp_tac >> simp[]) >>
  ‘¬EXISTS (closes_call f) aevs’
    by (simp[EVERY_MEM] >> rpt strip_tac >>
        qpat_x_assum ‘MEM _ aevs’ (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
        qpat_x_assum ‘aevs = _’ SUBST_ALL_TAC >>
        qpat_x_assum ‘cl_after _ _’ (mp_tac o REWRITE_RULE [cl_after_def]) >>
        disch_then (qspecl_then [‘l1’, ‘e’, ‘l2’] mp_tac) >> simp[] >>
        fs[EXISTS_APPEND]) >>
  rpt conj_tac
  >- (qpat_x_assum ‘_ ∨ _’ mp_tac >> simp[])
  >- first_assum ACCEPT_TAC
  >- (simp[EVERY_MEM, ep_ends_def] >> gen_tac >> strip_tac >> conj_tac
      >- (strip_tac >> drule closed_closes_call >> strip_tac >>
          qpat_x_assum ‘¬EXISTS (closes_call f) aevs’ mp_tac >>
          simp[EXISTS_MEM] >> goal_assum drule >> first_assum ACCEPT_TAC)
      >> strip_tac >>
      qpat_x_assum ‘¬EXISTS (λe. _) aevs’ mp_tac >>
      simp[EXISTS_MEM] >> goal_assum drule >> first_assum ACCEPT_TAC)
  >> first_assum ACCEPT_TAC
QED

Theorem round_stalled_pacts:
  round_stalled lfd pol hs (w, ps) acts f ⇒
  ∃rs aevs wa pa. pacts lfd (w, ps) acts = SOME (rs, aevs, (wa, pa)) ∧ outbox_of pa.b f ≠ []
Proof
  simp[round_stalled_def, tail_stalled_def, EXISTS_PROD] >> strip_tac >>
  goal_assum (first_assum o mp_then Any mp_tac) >>
  strip_tac >> drule l1_flush_le >> disch_then (qspec_then ‘f’ mp_tac) >> gvs[]
QED

(* The run's ownership facts at round r, in the form the round lemmas use *)
Theorem run_round_own:
  oassm lfd pol ifds m w0 ⇒
  ∃k opn. own_ok lfd (k, opn) (rstate lfd pol ifds m w0 r) ∧
          l0_ep_st (0, []) (revs lfd pol ifds m w0 r) = (k, opn) ∧
          okb (rstate lfd pol ifds m w0 r).b ∧ LENGTH (rstate lfd pol ifds m w0 r).acq ≤ 1 ∧
          wown lfd (rworld lfd pol ifds m w0 r) (rstate lfd pol ifds m w0 r) ∧
          (rstate lfd pol ifds m w0 r).b.nxt +
          naccepts (new_actions (log_of m) (rhist lfd pol ifds m w0 r)) < dimword (:64)
Proof
  strip_tac >> ‘run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0)’ by fs[oassm_def] >>
  drule_all run_own >> disch_then (qspec_then ‘r’ strip_assume_tac) >>
  Cases_on ‘l0_ep_st (0, []) (revs lfd pol ifds m w0 r)’ >> fs[] >>
  drule prun_some >> disch_then (qspec_then ‘r’ assume_tac) >>
  Cases_on ‘prun lfd pol ifds m w0 r’ >> rename1 ‘_ = (hh, rr)’ >> PairCases_on ‘rr’ >>
  gvs[rstate_def, rhist_def, run_ok_def, pl2_ok_def] >>
  first_x_assum drule >> simp[]
QED

(* L1 owns an fd whose output a round stalls *)
Theorem rstalled_owned:
  oassm lfd pol ifds m w0 ∧ rstalled lfd pol ifds m w0 r f ∧ f ≠ lfd ⇒
  owned (rstate lfd pol ifds m w0 r) f
Proof
  strip_tac >> drule run_round_own >> disch_then (qspec_then ‘r’ strip_assume_tac) >>
  qpat_x_assum ‘rstalled _ _ _ _ _ _ _’
    (strip_assume_tac o MATCH_MP round_stalled_pacts o REWRITE_RULE [rstalled_def]) >>
  ‘l0_rely (rworld lfd pol ifds m w0 r)’ by fs[wown_def] >>
  drule_all pacts_stalled_owned >> simp[]
QED

Theorem EXISTS_first:
  ∀l. EXISTS P l ⇒ ∃a x b. l = a ++ [x] ++ b ∧ P x ∧ ¬EXISTS P a
Proof
  Induct >> simp[] >> rpt strip_tac
  >- (qexistsl_tac [‘[]’, ‘h’, ‘l’] >> simp[]) >>
  Cases_on ‘P h’
  >- (qexistsl_tac [‘[]’, ‘h’, ‘l’] >> simp[]) >>
  qpat_x_assum ‘EXISTS P l ⇒ _’ drule >> strip_tac >>
  qexistsl_tac [‘h :: a’, ‘x’, ‘b’] >> fs[]
QED

(* A reap that makes no close call on f keeps f's channel and what was
   sent on it *)
Theorem l1_reap_chan_noclose:
  ∀fs w b w' b' evs.
    l1_reap fs (w, b) = SOME ((w', b'), evs) ∧ winv w ∧ l0_chan_of w f = SOME c ∧
    ¬EXISTS (closes_call f) evs ⇒
    l0_chan_of w' f = SOME c ∧ csent w' c = csent w c
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac >>
  gvs[AllCaseEqs()] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  PairCases_on ‘ws’ >>
  drule l1_close_shape >> strip_tac >> gvs[] >>
  drule sys_close_call3 >> disch_then (qspec_then ‘f’ assume_tac) >> gvs[] >>
  ‘winv ws0’ by metis_tac[sys_winv] >>
  drule_all (cj 5 sys_cflow) >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem sends_noclose:
  EVERY (λev. ev_name ev = ExtCall «sys_send») l ⇒ ¬EXISTS (closes_call f) l
Proof
  rw[EVERY_MEM, EXISTS_MEM] >> rpt strip_tac >> res_tac >>
  Cases_on ‘e’ >> fs[closes_call_def, ev_name_def]
QED

Theorem fetch_noclose:
  EVERY (λev. ev_name ev = ExtCall «sys_accept» ∨ ev_name ev = ExtCall «sys_recv») l ⇒
  ¬EXISTS (closes_call f) l
Proof
  rw[EVERY_MEM, EXISTS_MEM] >> rpt strip_tac >> res_tac >>
  Cases_on ‘e’ >> fs[closes_call_def, ev_name_def]
QED

Theorem closes_no_acc:
  EVERY (λev. ev_name ev = ExtCall «sys_close») l ⇒
  ¬EXISTS (λe. l0_event_accepted e = SOME f) l
Proof
  rw[EVERY_MEM, EXISTS_MEM] >> rpt strip_tac >> res_tac >>
  metis_tac[names_not_accepted]
QED

(* win_round for one pround *)
Theorem pround_win:
  pround lfd pol hs (w, ps) acts = SOME (sn, (w', ps'), log, evs) ∧ winv w ∧
  psmall lfd ps ∧ round_stalled lfd pol hs (w, ps) acts f ∧ f ≠ lfd ∧
  own_ok lfd (k, opn) ps ∧ ps.b.nxt + naccepts acts < dimword (:64) ∧ okb ps.b ∧
  nshut w ∧ (∀h. 0 < w.ch.takes c h 0 1) ∧ l0_chan_of w f = SOME c ∧
  wown lfd w ps ∧ LENGTH ps.acq ≤ 1 ⇒
  ∃pre pev post wa w1.
    evs = pre ++ [pev] ++ post ∧ out_poll f pev ∧
    EVERY (λe. ev_name e ≠ ExtCall «sys_poll») (pre ++ post) ∧
    (∀e. MEM e post ∧ ev_on «sys_send» f e ⇒ retried e) ∧
    ¬EXISTS (closes_call f) pre ∧ ¬EXISTS (ep_ends f) pre ∧
    fplays w wa pre ∧ fplays wa w1 [pev] ∧
    l0_chan_of wa f = SOME c ∧ c < LENGTH w1.chans ∧
    (olive lfd f ps ⇒ ¬EXISTS (ev_on «sys_send» f) pre ∧ csent wa c = csent w c) ∧
    ((EL c wa.chans).inflight = 0 ∧ ¬retried pev ∧ ¬(EL c w1.chans).broken ⇒
     ∃p1 ev p2. post = p1 ++ [ev] ++ p2 ∧ ev_on «sys_send» f ev ∧
                ¬EXISTS (ev_on «sys_send» f) p1 ∧ EVERY (λe. ev_name e = ExtCall «sys_send») p1) ∧
    (owned ps' f ⇒
     csent w' c = csent wa c ∧ l0_chan_of w' f = SOME c ∧ ¬EXISTS (closes_call f) (pev :: post))
Proof
  rpt strip_tac >> drule_all pround_cl >> disch_then (qspec_then ‘f’ assume_tac) >>
  qpat_x_assum ‘pround _ _ _ _ _ = _’ mp_tac >>
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >>
  gvs[pf_tail_def, AllCaseEqs(), round_stalled_def, tail_stalled_def] >>
  rename1 ‘pacts _ _ _ = SOME (rs, aevs, wa, pa)’ >>
  TRY (qpat_x_assum ‘l1_polls _ _ = SOME (rv, w1, pevs)’ mp_tac >>
       simp[l1_polls_def, AllCaseEqs()] >> strip_tac >> gvs[]) >>
  rename1 ‘sys_poll _ wa = SOME (out, w1, pev)’ >>
  qexistsl_tac [‘aevs’, ‘pev’, ‘fevs ++ gevs ++ cevs’, ‘wa’, ‘w1’] >>
  ‘winv wa’ by (drule_all pacts_winv >> simp[]) >>
  ‘psmall lfd pa’ by (drule_all pacts_psmall >> simp[]) >>
  ‘winv w1’ by (drule_all (cj 5 sys_winv) >> simp[]) >>
  ‘outbox_of pa.b f ≠ []’
    by (CCONTR_TAC >>
        qpat_x_assum ‘l1_flush _ _ = _’ (mp_tac o MATCH_MP l1_flush_le) >>
        qpat_x_assum ‘¬(outbox_of pa.b f ≠ [])’ mp_tac >>
        qpat_x_assum ‘outbox_of b2 f ≠ []’ mp_tac >> simp[]) >>
  drule_all pf_poll_set_out >> disch_then (qspecl_then [‘pol’, ‘hs’] strip_assume_tac) >>
  ‘EVERY (λ(g, e). small g ∧ e < 4) (pf_poll_set lfd pol pa hs)’
    by (irule pf_poll_set_small >> first_assum ACCEPT_TAC) >>
  drule_all sys_poll_out_ev >> strip_tac >>
  ‘l0_rely w’ by (qpat_x_assum ‘winv w’ mp_tac >> simp[winv_def]) >>
  ‘ps.b.nxt + naccepts acts < dimword (:64)’
    by (qpat_x_assum ‘naccepts acts + _ < _’ mp_tac >> simp[]) >>
  drule_all pacts_stalled_owned >> strip_tac >>
  ‘l0_chan_of wa f = SOME c’ by (drule_all pacts_chan_noclose >> simp[]) >>
  drule_at (Pos last) (cj 3 sys_cflow) >> disch_then drule_all >> strip_tac >>
  rpt conj_tac
  >- simp[]
  >- (drule polls_out_out_poll >> strip_tac)
  >- (qpat_x_assum ‘pacts _ _ _ = _’ (mp_tac o CONJUNCT1 o MATCH_MP pacts_names) >>
      simp[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
      qpat_x_assum ‘ev_name _ = ExtCall «sys_poll»’ (fn th => simp[th]))
  >- (simp[EVERY_APPEND] >> rpt conj_tac
      >- (qpat_x_assum ‘l1_flush _ _ = _’ (mp_tac o MATCH_MP l1_flush_names) >>
          simp[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
          qpat_x_assum ‘ev_name _ = ExtCall «sys_poll»’ (fn th => simp[th]))
      >- (qpat_x_assum ‘pf_fetch _ _ _ _ = _’ (mp_tac o MATCH_MP pf_fetch_names) >>
          simp[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
          qpat_x_assum ‘ev_name _ = ExtCall «sys_poll»’ (fn th => simp[th]))
      >> qpat_x_assum ‘l1_reap _ _ = _’ (mp_tac o MATCH_MP l1_reap_names) >>
      simp[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
      qpat_x_assum ‘ev_name _ = ExtCall «sys_poll»’ (fn th => simp[th]))
  >- (simp[MEM_APPEND] >> rpt strip_tac
      >- (drule_all l1_flush_stalled >> disch_then irule >>
          conj_tac >> first_assum ACCEPT_TAC)
      >- (drule ev_on_name >> strip_tac >>
          qpat_x_assum ‘pf_fetch _ _ _ _ = _’ (mp_tac o MATCH_MP pf_fetch_names) >>
          simp[EVERY_MEM] >> disch_then drule >>
          qpat_x_assum ‘ev_name _ = ExtCall «sys_send»’ (fn th => simp[th]))
      >> drule ev_on_name >> strip_tac >>
      qpat_x_assum ‘l1_reap _ _ = _’ (mp_tac o MATCH_MP l1_reap_names) >>
      simp[EVERY_MEM] >> disch_then drule >>
      qpat_x_assum ‘ev_name _ = ExtCall «sys_send»’ (fn th => simp[th]))
  >- (qpat_x_assum ‘¬EXISTS (closes_call f) aevs’ mp_tac >> simp[])
  >- (qpat_x_assum ‘¬EXISTS (ep_ends f) aevs’ mp_tac >> simp[])
  >- (drule fplays_pacts >> disch_then ACCEPT_TAC)
  >- (drule (cj 5 fplays_sys) >> disch_then ACCEPT_TAC)
  >- first_assum ACCEPT_TAC
  >- (irule chan_lt >> qexists_tac ‘f’ >> first_assum ACCEPT_TAC)
  >- (strip_tac >> drule_all pacts_live >> simp[])
  >- (strip_tac >>
  ‘(EL c w1.chans).inflight = 0’
    by (qpat_x_assum ‘cflow wa w1 c’ mp_tac >> simp[cflow_def] >>
        qpat_x_assum ‘csent w1 c = _’ (fn th => simp[th]) >>
        qpat_x_assum ‘(EL c wa.chans).inflight = 0’ (fn th => simp[th])) >>
  ‘nshut wa’
    by (drule_all (Q.INST [‘P’ |-> ‘nshut’] pacts_wpres |> SIMP_RULE std_ss [wpres_nshut]) >>
        simp[]) >>
  ‘¬(EL c w1.chans).shut’
    by (qpat_x_assum ‘l0_chan_of wa f = SOME c’ (assume_tac o MATCH_MP chan_of_used) >>
        qpat_x_assum ‘nshut wa’ (mp_tac o REWRITE_RULE [nshut_def]) >>
        disch_then drule >>
        qpat_x_assum ‘cflow wa w1 c’ mp_tac >> simp[cflow_def]) >>
  ‘wa.ch = w.ch’ by (drule pacts_ch >> simp[]) >>
  ‘MEM f (writable_fds (poll_revents (pf_poll_set lfd pol pa hs) out))’
    by (irule sys_poll_out >> conj_tac
        >- (qexistsl_tac [‘c’, ‘pev’, ‘wa’, ‘w1’] >> asm_rewrite_tac[])
        >> conj_tac >- first_assum ACCEPT_TAC
        >> qexists_tac ‘e’ >> asm_rewrite_tac[]) >>
  ‘¬MEM f pa.b.gone’
    by (strip_tac >> qpat_x_assum ‘okb pa.b’ (mp_tac o REWRITE_RULE [okb_def]) >>
        disch_then (qspec_then ‘f’ mp_tac) >> simp[]) >>
  drule_all l1_flush_live >> strip_tac >>
  qpat_x_assum ‘MEM f _ ∧ _ ⇒ _’ mp_tac >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (strip_assume_tac o MATCH_MP EXISTS_first) >>
  qexistsl_tac [‘a’, ‘x’, ‘b ++ gevs ++ cevs’] >> simp[] >>
  qpat_x_assum ‘l1_flush _ _ = _’ (mp_tac o MATCH_MP l1_flush_names) >>
  qpat_x_assum ‘fevs = _’ SUBST1_TAC >>
  qpat_x_assum ‘¬EXISTS _ a’ mp_tac >> simp[EVERY_APPEND])
  (* the end of the round, with f still owned *)
  >> strip_tac >>
  qpat_x_assum ‘cl_ok _ _ _ _’ (mp_tac o REWRITE_RULE [cl_ok_def]) >>
  impl_tac >- first_assum ACCEPT_TAC >> disch_then (assume_tac o CONJUNCT1) >>
  ‘¬closes_call f pev’
    by (qpat_x_assum ‘ev_name pev = _’ mp_tac >> Cases_on ‘pev’ >>
        simp[closes_call_def, ev_name_def]) >>
  ‘¬EXISTS (closes_call f) fevs’
    by (irule sends_noclose >> irule l1_flush_names >> goal_assum drule) >>
  ‘¬EXISTS (closes_call f) gevs’
    by (irule fetch_noclose >> irule pf_fetch_names >> goal_assum drule) >>
  ‘¬EXISTS (closes_call f) cevs’
    by (rewrite_tac[EXISTS_MEM] >> disch_then (qx_choose_then ‘ce’ strip_assume_tac) >>
        qpat_x_assum ‘MEM _ cevs’ (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
        qpat_x_assum ‘l1_reap _ _ = _’ (assume_tac o MATCH_MP l1_reap_names) >>
        qpat_x_assum ‘cevs = _’ SUBST_ALL_TAC >>
        qpat_x_assum ‘cl_after _ _’ (mp_tac o REWRITE_RULE [cl_after_def]) >>
        disch_then (qspecl_then [‘aevs ++ [pev] ++ fevs ++ gevs ++ l1’, ‘ce’, ‘l2’] mp_tac) >>
        impl_tac >- (conj_tac >- simp[] >> first_assum ACCEPT_TAC) >>
        disch_then (fn th => qpat_x_assum ‘EVERY _ (_ ++ _)’ (fn ev =>
          MP_TAC (MATCH_MP closes_no_acc
                   (CONJUNCT2 (CONJUNCT2 (REWRITE_RULE [EVERY_APPEND, EVERY_DEF] ev)))) >>
          REWRITE_TAC [th]))) >>
  ‘winv w2’ by (drule_all l1_flush_winv >> simp[]) >>
  ‘winv w3’ by (drule_all pf_fetch_winv >> simp[]) >>
  ‘∀ev. MEM ev fevs ∧ ev_on «sys_send» f ev ⇒ retried ev’
    by (rpt strip_tac >> drule_all l1_flush_stalled >> disch_then irule >>
        conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all l1_flush_cflow >> strip_tac >>
  drule_all l1_flush_live >> strip_tac >>
  qpat_x_assum ‘¬(∃ev. _) ⇒ _’ mp_tac >>
  impl_tac
  >- (rpt strip_tac >>
      qpat_x_assum ‘∀ev. MEM ev fevs ∧ _ ⇒ _’ (fn th => drule_all th) >>
      qpat_x_assum ‘¬retried _’ (fn th => simp[th])) >>
  strip_tac >>
  drule_all pf_fetch_cflow >> strip_tac >>
  drule_all l1_reap_chan_noclose >> strip_tac >>
  rpt conj_tac
  >- (qpat_x_assum ‘csent w' c = _’ SUBST1_TAC >>
      qpat_x_assum ‘csent w3 c = _’ SUBST1_TAC >>
      qpat_x_assum ‘csent w2 c = _’ SUBST1_TAC >>
      first_assum ACCEPT_TAC)
  >- first_assum ACCEPT_TAC
  >> qpat_x_assum ‘¬EXISTS (closes_call f) fevs’ mp_tac >>
  qpat_x_assum ‘¬EXISTS (closes_call f) gevs’ mp_tac >>
  qpat_x_assum ‘¬EXISTS (closes_call f) cevs’ mp_tac >>
  qpat_x_assum ‘¬closes_call f pev’ mp_tac >> simp[]
QED

(* A stalled round of f, from a round at which L1 owns f: its one poll
   lists f for output; every send on f after it is retried; the worlds just
   before and just after the poll; and, if the poll starts with nothing in
   flight on f's channel, went through, and left the channel unbroken, L1
   sends on f after it ([F2]).  The pacts before the poll make no close
   call on f, and (if f had output pending at the round's start) no send
   on f either.  If L1 still owns f at the round's end, no send on f in
   the round took bytes after the poll, f keeps its channel, and the round
   made no close call on f from the poll on *)
Theorem win_round:
  oassm lfd pol ifds m w0 ∧ nshut w0 ∧ F2 w0 ∧ f ≠ lfd ∧
  rstalled lfd pol ifds m w0 r f ∧ owned (rstate lfd pol ifds m w0 r) f ∧
  l0_chan_of (rworld lfd pol ifds m w0 r) f = SOME c ⇒
  ∃pre pev post wa w1.
    rrev lfd pol ifds m w0 r = pre ++ [pev] ++ post ∧ out_poll f pev ∧
    EVERY (λe. ev_name e ≠ ExtCall «sys_poll») (pre ++ post) ∧
    (∀e. MEM e post ∧ ev_on «sys_send» f e ⇒ retried e) ∧
    ¬EXISTS (closes_call f) pre ∧ ¬EXISTS (ep_ends f) pre ∧
    world_at w0 (revs lfd pol ifds m w0 r ++ pre) = SOME wa ∧
    world_at w0 (revs lfd pol ifds m w0 r ++ pre ++ [pev]) = SOME w1 ∧
    l0_chan_of wa f = SOME c ∧ c < LENGTH w1.chans ∧
    (olive lfd f (rstate lfd pol ifds m w0 r) ⇒
     ¬EXISTS (ev_on «sys_send» f) pre ∧
     csent wa c = csent (rworld lfd pol ifds m w0 r) c) ∧
    ((EL c wa.chans).inflight = 0 ∧ ¬retried pev ∧ ¬(EL c w1.chans).broken ⇒
     ∃p1 ev p2. post = p1 ++ [ev] ++ p2 ∧ ev_on «sys_send» f ev ∧
                ¬EXISTS (ev_on «sys_send» f) p1 ∧ EVERY (λe. ev_name e = ExtCall «sys_send») p1) ∧
    (owned (rstate lfd pol ifds m w0 (SUC r)) f ⇒
     csent (rworld lfd pol ifds m w0 (SUC r)) c = csent wa c ∧
     l0_chan_of (rworld lfd pol ifds m w0 (SUC r)) f = SOME c ∧
     ¬EXISTS (closes_call f) (pev :: post))
Proof
  strip_tac >>
  ‘run_ok lfd pol ifds m w0 ∧ winv w0’ by fs[oassm_def] >>
  drule prun_round' >> disch_then (qspecl_then [‘f’, ‘r’] strip_assume_tac) >>
  drule run_round_own >> disch_then (qspec_then ‘r’ strip_assume_tac) >>
  ‘winv (rworld lfd pol ifds m w0 r)’ by (drule_all winv_run >> simp[]) >>
  ‘psmall lfd (rstate lfd pol ifds m w0 r)’ by (drule psmall_run >> simp[]) >>
  ‘nshut (rworld lfd pol ifds m w0 r)’ by (drule_all run_nshut >> simp[]) >>
  ‘∀h. 0 < (rworld lfd pol ifds m w0 r).ch.takes c h 0 1’
    by (drule run_ch >> disch_then (qspec_then ‘r’ SUBST1_TAC) >>
        qpat_x_assum ‘F2 w0’ mp_tac >> simp[honestL1BStmtsTheory.F2_def, honestL1PFFlushTheory.F2_def]) >>
  qpat_x_assum ‘rstalled _ _ _ _ _ _ _’ (assume_tac o REWRITE_RULE [rstalled_def]) >>
  drule_all pround_win >> strip_tac >>
  qexistsl_tac [‘pre’, ‘pev’, ‘post’, ‘wa’, ‘w1’] >>
  drule run_world_at >> disch_then (qspec_then ‘r’ strip_assume_tac) >>
  ‘l0_rely (rworld lfd pol ifds m w0 r)’ by fs[winv_def] >>
  qpat_x_assum ‘fplays (rworld _ _ _ _ _ _) _ _’ (mp_tac o REWRITE_RULE [fplays_def]) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qpat_x_assum ‘fplays wa _ _’ (mp_tac o REWRITE_RULE [fplays_def]) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  ‘world_at w0 (revs lfd pol ifds m w0 r ++ pre) = SOME wa’
    by (rewrite_tac[world_at_append] >>
        qpat_x_assum ‘world_at w0 _ = SOME (rworld _ _ _ _ _ _)’ SUBST1_TAC >>
        rewrite_tac[OPTION_BIND_def] >> BETA_TAC >> first_assum ACCEPT_TAC) >>
  ‘world_at w0 (revs lfd pol ifds m w0 r ++ pre ++ [pev]) = SOME w1’
    by (rewrite_tac[Once world_at_append] >>
        qpat_x_assum ‘world_at w0 (_ ++ pre) = _’ SUBST1_TAC >>
        rewrite_tac[OPTION_BIND_def] >> BETA_TAC >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED



(* ------------------------------------------------------------------------
   The main argument
   ------------------------------------------------------------------------ *)

Theorem n_out_polls_APPEND[simp]:
  n_out_polls f (a ++ b) = n_out_polls f a + n_out_polls f b
Proof
  simp[n_out_polls_def, FILTER_APPEND]
QED

Theorem n_out_polls_SPLITP_le[local]:
  ∀mid. n_out_polls f (FST (SPLITP P mid)) ≤ n_out_polls f mid
Proof
  Induct >> rw[SPLITP] >> fs[n_out_polls_def] >> rw[]
QED

Theorem n_out_polls_ep_polls_le:
  n_out_polls f (ep_polls f pre mid) ≤ n_out_polls f mid
Proof
  rw[ep_polls_def, n_out_polls_SPLITP_le] >> simp[n_out_polls_def]
QED

Theorem LPREFIX_fromList_pfx:
  LPREFIX (fromList evs) io ∧ evs1 ≼ evs ⇒ LPREFIX (fromList evs1) io
Proof
  rw[] >> irule LPREFIX_TRANS >> qexists_tac ‘fromList evs’ >>
  simp[LPREFIX_fromList, from_toList]
QED

Theorem out_poll_not_send:
  out_poll f e ⇒ ¬ev_on «sys_send» g e
Proof
  rw[out_poll_def] >> simp[ev_on_def]
QED

Theorem pfx_of_EL[local]:
  ∀a b. LENGTH a ≤ LENGTH b ∧ (∀i. i < LENGTH a ⇒ EL i a = EL i b) ⇒ a ≼ b
Proof
  Induct >> simp[] >> rpt strip_tac >> Cases_on ‘b’ >> fs[] >>
  conj_tac >- (first_x_assum (qspec_then ‘0’ mp_tac) >> simp[]) >>
  first_x_assum irule >> rw[] >> first_x_assum (qspec_then ‘SUC i’ mp_tac) >> simp[]
QED

Theorem LPREFIX_cmp:
  LPREFIX (fromList a) io ∧ LPREFIX (fromList b) io ⇒ a ≼ b ∨ b ≼ a
Proof
  rw[LPREFIX_NTH, LNTH_fromList] >> Cases_on ‘LENGTH a ≤ LENGTH b’ >|
  [disj1_tac, disj2_tac] >> irule pfx_of_EL >> fs[] >> rpt strip_tac >>
  ‘i < LENGTH a ∧ i < LENGTH b’ by decide_tac >>
  first_x_assum (qspec_then ‘i’ mp_tac) >>
  first_x_assum (qspec_then ‘i’ mp_tac) >> simp[less_opt_def] >> rpt strip_tac >>
  qpat_x_assum ‘SOME (EL i b) = _’ (assume_tac o SYM) >> fs[]
QED

Theorem out_poll_not_close:
  out_poll f e ⇒ ¬l0_close_call g e
Proof
  rw[out_poll_def] >> simp[l0_close_call_def]
QED

Theorem SPLITP_APPEND_none:
  ∀a b. ¬EXISTS P a ⇒ FST (SPLITP P (a ++ b)) = a ++ FST (SPLITP P b)
Proof
  Induct >> rw[SPLITP]
QED

(* One stalled round, on the trace, with f's episode j *)
Theorem round_facts:
  oassm lfd pol ifds m w0 ∧ nshut w0 ∧ F2 w0 ∧ f ≠ lfd ∧
  rstalled lfd pol ifds m w0 r f ∧ owned (rstate lfd pol ifds m w0 r) f ∧
  l0_chan_of (rworld lfd pol ifds m w0 r) f = SOME c ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 r))) f = SOME j ⇒
  ∃pre pev post wa w1.
    revs lfd pol ifds m w0 (SUC r) = revs lfd pol ifds m w0 r ++ pre ++ [pev] ++ post ∧
    out_poll f pev ∧ ¬EXISTS (out_poll f) pre ∧ ¬EXISTS (out_poll f) post ∧
    (∀e. MEM e post ∧ ev_on «sys_send» f e ⇒ retried e) ∧
    world_at w0 (revs lfd pol ifds m w0 r ++ pre) = SOME wa ∧
    world_at w0 (revs lfd pol ifds m w0 r ++ pre ++ [pev]) = SOME w1 ∧
    l0_chan_of wa f = SOME c ∧ c < LENGTH wa.chans ∧ c < LENGTH w1.chans ∧
    ep_open j (revs lfd pol ifds m w0 r ++ pre) ∧
    EL j (l0_accepted (revs lfd pol ifds m w0 r ++ pre)) = f ∧
    (∃A ev B. revs lfd pol ifds m w0 r ++ pre ++ [pev] = A ++ [ev] ++ B ∧
              LENGTH (l0_accepted A) = j ∧ l0_event_accepted ev = SOME f ∧
              ¬EXISTS (l0_close_call f) B) ∧
    ¬EXISTS (l0_close_call f) pre ∧
    (olive lfd f (rstate lfd pol ifds m w0 r) ⇒
     csent wa c = csent (rworld lfd pol ifds m w0 r) c) ∧
    ((EL c wa.chans).inflight = 0 ∧ ¬retried pev ∧ ¬(EL c w1.chans).broken ⇒
     ∃p1 ev p2. post = p1 ++ [ev] ++ p2 ∧ ev_on «sys_send» f ev ∧
                ¬EXISTS (ev_on «sys_send» f) p1 ∧ ¬EXISTS (out_poll f) p1 ∧
                ep_open j (revs lfd pol ifds m w0 r ++ pre ++ [pev] ++ p1)) ∧
    (owned (rstate lfd pol ifds m w0 (SUC r)) f ∧
     ¬MEM f (rstate lfd pol ifds m w0 (SUC r)).b.gone ⇒
     csent (rworld lfd pol ifds m w0 (SUC r)) c = csent wa c ∧
     l0_chan_of (rworld lfd pol ifds m w0 (SUC r)) f = SOME c ∧
     ¬EXISTS (l0_close_call f) post)
Proof
  strip_tac >>
  ‘run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0)’ by fs[oassm_def] >>
  qspecl_then [‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘f’, ‘r’, ‘c’] mp_tac
    (Q.GENL [‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘f’, ‘r’, ‘c’] win_round) >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl_tac [‘pre’, ‘pev’, ‘post’, ‘wa’, ‘w1’] >>
  ‘revs lfd pol ifds m w0 (SUC r) = revs lfd pol ifds m w0 r ++ rrev lfd pol ifds m w0 r’
    by (drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘r’] strip_assume_tac) >> simp[]) >>
  ‘¬ep_ends f pev ∧ ¬closes_call f pev’ by metis_tac[poll_facts] >>
  (* the tie at the poll *)
  ‘ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 r ++ pre))) f = SOME j’
    by (REWRITE_TAC [l0_ep_st_simps] >>
        qspecl_then [‘pre’, ‘l0_ep_st (0,[]) (revs lfd pol ifds m w0 r)’]
          mp_tac (REWRITE_RULE [GSYM EXISTS_ep_ends] ep_st_no_end) >>
        impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  drule ep_state_open >> strip_tac >>
  (* the accept of f's episode, and no close call on f since *)
  drule_all held_noclose >> strip_tac >>
  rename1 ‘revs lfd pol ifds m w0 r = A0 ++ [ev0] ++ B0’ >>
  ‘¬EXISTS (l0_close_call f) pre’ by (irule noclose_of >> first_assum ACCEPT_TAC) >>
  rpt conj_tac
  >- simp[]
  >- first_assum ACCEPT_TAC
  >- (CCONTR_TAC >> fs[EXISTS_MEM] >> imp_res_tac poll_facts >> fs[EVERY_MEM] >> res_tac)
  >- (CCONTR_TAC >> fs[EXISTS_MEM] >> imp_res_tac poll_facts >> fs[EVERY_MEM] >> res_tac)
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- metis_tac[chan_lt]
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (‘¬EXISTS (l0_close_call f) B0’ by (irule noclose_of >> first_assum ACCEPT_TAC) >>
      ‘¬l0_close_call f pev’ by (strip_tac >> imp_res_tac close_call_closes) >>
      qexistsl_tac [‘A0’, ‘ev0’, ‘B0 ++ pre ++ [pev]’] >> simp[] >>
      fs[EVERY_MEM, EXISTS_MEM])
  >- first_assum ACCEPT_TAC
  >- (strip_tac >> qpat_x_assum ‘olive _ _ _ ⇒ _’ mp_tac >>
      impl_tac >- first_assum ACCEPT_TAC >> strip_tac >> first_assum ACCEPT_TAC)
  >- (strip_tac >>
      qpat_x_assum ‘_ ∧ ¬retried _ ∧ _ ⇒ _’ mp_tac >> impl_tac >- simp[] >> strip_tac >>
      ‘¬EXISTS (out_poll f) p1 ∧ ¬EXISTS (ep_ends f) ([pev] ++ p1)’
        by (fs[EVERY_MEM, EXISTS_MEM] >> metis_tac[send_name_facts]) >>
      ‘ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 r ++ pre ++ [pev] ++ p1))) f = SOME j’
        by (REWRITE_TAC [l0_ep_st_simps] >>
            qspecl_then [‘[pev] ++ p1’, ‘l0_ep_st (0,[]) (revs lfd pol ifds m w0 r ++ pre)’]
              mp_tac (REWRITE_RULE [GSYM EXISTS_ep_ends] ep_st_no_end) >>
            impl_tac >- first_assum ACCEPT_TAC >>
            fs[l0_ep_st_simps]) >>
      drule ep_state_open >> strip_tac >>
      qexistsl_tac [‘p1’, ‘ev’, ‘p2’] >> rpt conj_tac >> first_assum ACCEPT_TAC)
  >> strip_tac >>
  qpat_x_assum ‘owned (rstate _ _ _ _ _ (SUC _)) f ⇒ _’ mp_tac >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
  irule noclose_of >> qpat_x_assum ‘¬EXISTS (closes_call f) (pev::post)’ mp_tac >>
  REWRITE_TAC [EXISTS_DEF, DE_MORGAN_THM] >> strip_tac
QED

(* The drop's window, round by round (from rdrop_timeout and win_round):
   Q r is the trace up to round r's poll *)
Theorem window_facts:
  oassm lfd pol ifds m w0 ∧ nshut w0 ∧ F2 w0 ∧ rdrop lfd pol ifds m w0 k f ∧ f ≠ lfd ∧
  ¬hard_recv f (rrev lfd pol ifds m w0 k) ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 k))) f = SOME j ∧
  l0_chan_of (rworld lfd pol ifds m w0 k) f = SOME c ⇒
  ∃i0 Q PV PO WA W1.
    k + 1 = i0 + pf_sendwait ∧
    ∀r. i0 ≤ r ∧ r ≤ k ⇒
      revs lfd pol ifds m w0 (SUC r) = Q r ++ [PV r] ++ PO r ∧
      out_poll f (PV r) ∧ ¬EXISTS (out_poll f) (PO r) ∧
      (∀e. MEM e (PO r) ∧ ev_on «sys_send» f e ⇒ retried e) ∧
      world_at w0 (Q r) = SOME (WA r) ∧ world_at w0 (Q r ++ [PV r]) = SOME (W1 r) ∧
      c < LENGTH (WA r).chans ∧ c < LENGTH (W1 r).chans ∧
      ep_open j (Q r) ∧ EL j (l0_accepted (Q r)) = f ∧
      (∃A ev B. Q r ++ [PV r] = A ++ [ev] ++ B ∧ LENGTH (l0_accepted A) = j ∧
                l0_event_accepted ev = SOME f ∧ ¬EXISTS (l0_close_call f) B) ∧
      ((EL c (WA r).chans).inflight = 0 ∧ ¬retried (PV r) ∧ ¬(EL c (W1 r).chans).broken ⇒
       ∃p1 ev p2. PO r = p1 ++ [ev] ++ p2 ∧ ev_on «sys_send» f ev ∧
                  ¬EXISTS (ev_on «sys_send» f) p1 ∧ ¬EXISTS (out_poll f) p1 ∧
                  ep_open j (Q r ++ [PV r] ++ p1)) ∧
      (r < k ⇒
       ∃G. Q (SUC r) = Q r ++ [PV r] ++ G ∧ ¬EXISTS (out_poll f) G ∧
           ¬EXISTS (l0_close_call f) G ∧ csent (WA (SUC r)) c = csent (WA r) c)
Proof
  strip_tac >>
  ‘run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0)’ by fs[oassm_def] >>
  ‘¬MEM (FReset f) (rlog lfd pol ifds m w0 k)’
    by (strip_tac >>
        drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
        ‘winv (rworld lfd pol ifds m w0 k)’ by metis_tac[winv_run] >>
        drule_all pround_freset >> fs[]) >>
  drule_all rdrop_window_held >> strip_tac >>
  qabbrev_tac ‘i0 = SUC k − pf_sendwait’ >>
  ‘k + 1 = i0 + pf_sendwait ∧ i0 < k’ by fs[Abbr ‘i0’, pf_sendwait_def] >>
  (* f is held, with output pending, after each window round but the last *)
  ‘∀r. i0 < r ∧ r ≤ k ⇒
       (MEM f (MAP SND (rstate lfd pol ifds m w0 r).b.tbl) ∨
        MEM f (rstate lfd pol ifds m w0 r).b.closing) ∧
       outbox_of (rstate lfd pol ifds m w0 r).b f ≠ [] ∧
       ¬MEM f (rstate lfd pol ifds m w0 r).b.gone’
    by (rpt gen_tac >> strip_tac >>
        qpat_assum ‘∀i. i0 ≤ i ∧ i < k ⇒ _’ (qspec_then ‘r − 1’ mp_tac) >>
        ‘SUC (r − 1) = r’ by simp[] >> pop_assum SUBST1_TAC >>
        disch_then irule >> fs[Abbr ‘i0’]) >>
  ‘∀r. i0 ≤ r ∧ r ≤ k ⇒ rstalled lfd pol ifds m w0 r f’
    by (rpt strip_tac >> first_x_assum irule >> fs[Abbr ‘i0’]) >>
  ‘∀r. i0 ≤ r ∧ r ≤ k ⇒ owned (rstate lfd pol ifds m w0 r) f’
    by (rpt strip_tac >> Cases_on ‘i0 < r’
        >- (simp[owned_def] >> metis_tac[]) >>
        ‘r = i0’ by simp[] >> gvs[] >> irule rstalled_owned >> simp[] >> metis_tac[]) >>
  (* the episode tie at each window round *)
  ‘∀r. i0 ≤ r ∧ r ≤ k ⇒ ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 r))) f = SOME j’
    by (rpt strip_tac >>
        ‘revs lfd pol ifds m w0 k = revs lfd pol ifds m w0 r ++ rrounds lfd pol ifds m w0 r (k − r)’
          by (drule revs_rrounds >> disch_then (qspecl_then [‘r’, ‘k − r’] mp_tac) >>
              ‘r + (k − r) = k’ by simp[] >> simp[]) >>
        ‘¬EXISTS (ep_ends f) (rrounds lfd pol ifds m w0 r (k − r))’
          by (‘∀d a. (∀i. a < i ∧ i ≤ a + d ⇒ held f (rstate lfd pol ifds m w0 i)) ⇒
                     ¬EXISTS (ep_ends f) (rrounds lfd pol ifds m w0 a d)’
                by (match_mp_tac held_no_end >> simp[]) >>
              pop_assum irule >> rpt strip_tac >>
              qpat_x_assum ‘∀r. i0 < r ∧ r ≤ k ⇒ _’ (qspec_then ‘i’ mp_tac) >> simp[]) >>
        qpat_x_assum ‘ALOOKUP _ f = SOME j’ mp_tac >>
        qpat_x_assum ‘revs _ _ _ _ _ k = _’ SUBST1_TAC >>
        REWRITE_TAC [l0_ep_st_simps] >>
        qspecl_then [‘rrounds lfd pol ifds m w0 r (k − r)’,
                     ‘l0_ep_st (0,[]) (revs lfd pol ifds m w0 r)’]
          mp_tac (REWRITE_RULE [GSYM EXISTS_ep_ends] ep_st_no_end) >>
        impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  (* f's channel is the same through the window *)
  ‘∃c'. l0_chan_of (rworld lfd pol ifds m w0 i0) f = SOME c'’
    by (drule run_held_chan >> disch_then irule >>
        qpat_x_assum ‘∀r. i0 ≤ r ∧ r ≤ k ⇒ owned _ f’ (qspec_then ‘i0’ mp_tac) >>
        simp[owned_def] >> metis_tac[]) >>
  ‘∀d. i0 + d ≤ k ⇒ l0_chan_of (rworld lfd pol ifds m w0 (i0 + d)) f = SOME c'’
    by (Induct >- simp[] >> strip_tac >>
        qpat_x_assum ‘i0 + d ≤ k ⇒ _’ mp_tac >> impl_tac >- simp[] >> strip_tac >>
        qspecl_then [‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘f’, ‘i0 + d’, ‘c'’, ‘j’] mp_tac
          (Q.GENL [‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘f’, ‘r’, ‘c’, ‘j’] round_facts) >>
        impl_tac >- simp[] >> strip_tac >>
        qpat_x_assum ‘owned _ f ∧ _ ⇒ _’ mp_tac >>
        ‘i0 + SUC d = SUC (i0 + d)’ by simp[] >> pop_assum SUBST_ALL_TAC >>
        impl_tac
        >- (qpat_x_assum ‘∀r. i0 < r ∧ r ≤ k ⇒ _’ (qspec_then ‘SUC (i0 + d)’ mp_tac) >>
            simp[owned_def]) >>
        simp[]) >>
  ‘c' = c’
    by (pop_assum (qspec_then ‘k − i0’ mp_tac) >> ‘i0 + (k − i0) = k’ by simp[] >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  (* each window round *)
  ‘∀r. i0 ≤ r ∧ r ≤ k ⇒ ∃pre pev post wa w1.
     revs lfd pol ifds m w0 (SUC r) = revs lfd pol ifds m w0 r ++ pre ++ [pev] ++ post ∧
     out_poll f pev ∧ ¬EXISTS (out_poll f) pre ∧ ¬EXISTS (out_poll f) post ∧
     (∀e. MEM e post ∧ ev_on «sys_send» f e ⇒ retried e) ∧
     world_at w0 (revs lfd pol ifds m w0 r ++ pre) = SOME wa ∧
     world_at w0 (revs lfd pol ifds m w0 r ++ pre ++ [pev]) = SOME w1 ∧
     l0_chan_of wa f = SOME c ∧ c < LENGTH wa.chans ∧ c < LENGTH w1.chans ∧
     ep_open j (revs lfd pol ifds m w0 r ++ pre) ∧
     EL j (l0_accepted (revs lfd pol ifds m w0 r ++ pre)) = f ∧
     (∃A ev B. revs lfd pol ifds m w0 r ++ pre ++ [pev] = A ++ [ev] ++ B ∧
               LENGTH (l0_accepted A) = j ∧ l0_event_accepted ev = SOME f ∧
               ¬EXISTS (l0_close_call f) B) ∧
     ¬EXISTS (l0_close_call f) pre ∧
     (olive lfd f (rstate lfd pol ifds m w0 r) ⇒
      csent wa c = csent (rworld lfd pol ifds m w0 r) c) ∧
     ((EL c wa.chans).inflight = 0 ∧ ¬retried pev ∧ ¬(EL c w1.chans).broken ⇒
      ∃p1 ev p2. post = p1 ++ [ev] ++ p2 ∧ ev_on «sys_send» f ev ∧
                 ¬EXISTS (ev_on «sys_send» f) p1 ∧ ¬EXISTS (out_poll f) p1 ∧
                 ep_open j (revs lfd pol ifds m w0 r ++ pre ++ [pev] ++ p1)) ∧
     (owned (rstate lfd pol ifds m w0 (SUC r)) f ∧
      ¬MEM f (rstate lfd pol ifds m w0 (SUC r)).b.gone ⇒
      csent (rworld lfd pol ifds m w0 (SUC r)) c = csent wa c ∧
      l0_chan_of (rworld lfd pol ifds m w0 (SUC r)) f = SOME c ∧
      ¬EXISTS (l0_close_call f) post)’
    by (rpt strip_tac >>
        qspecl_then [‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘f’, ‘r’, ‘c’, ‘j’] mp_tac
          (Q.GENL [‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘f’, ‘r’, ‘c’, ‘j’] round_facts) >>
        impl_tac
        >- (simp[] >>
            qpat_x_assum ‘∀d. i0 + d ≤ k ⇒ _’ (qspec_then ‘r − i0’ mp_tac) >>
            ‘i0 + (r − i0) = r’ by simp[] >> simp[]) >>
        disch_then ACCEPT_TAC) >>
  pop_assum (strip_assume_tac o SIMP_RULE std_ss [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]) >>
  qexistsl_tac [‘i0’, ‘λr. revs lfd pol ifds m w0 r ++ f' r’, ‘f''’, ‘f'''’, ‘f''''’, ‘f'''''’] >>
  conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  qpat_assum ‘∀r. i0 ≤ r ∧ r ≤ k ⇒ revs _ _ _ _ _ (SUC r) = _ ∧ _’ (qspec_then ‘r’ mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (qexistsl_tac [‘A’, ‘ev’, ‘B’] >> rpt conj_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (strip_tac >> qpat_x_assum ‘_ ∧ ¬retried _ ∧ _ ⇒ _’ mp_tac >>
       impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
       strip_tac >> goal_assum drule >> rpt conj_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
  (* the gap to the next round's poll *)
  strip_tac >>
  qpat_assum ‘∀r. i0 ≤ r ∧ r ≤ k ⇒ revs _ _ _ _ _ (SUC r) = _ ∧ _’ (qspec_then ‘SUC r’ mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  ‘owned (rstate lfd pol ifds m w0 (SUC r)) f ∧
   outbox_of (rstate lfd pol ifds m w0 (SUC r)).b f ≠ [] ∧
   ¬MEM f (rstate lfd pol ifds m w0 (SUC r)).b.gone’
    by (qpat_x_assum ‘∀r. i0 < r ∧ r ≤ k ⇒ _’ (qspec_then ‘SUC r’ mp_tac) >>
        impl_tac >- simp[] >> rw[owned_def] >> simp[]) >>
  qpat_x_assum ‘owned (rstate _ _ _ _ _ (SUC r)) f ∧ _ ⇒ _’ mp_tac >>
  impl_tac >- simp[] >> strip_tac >>
  qpat_x_assum ‘olive _ _ (rstate _ _ _ _ _ (SUC r)) ⇒ _’ mp_tac >>
  impl_tac >- simp[olive_def] >> strip_tac >>
  qexists_tac ‘f''' r ++ f' (SUC r)’ >>
  qpat_assum ‘revs _ _ _ _ _ (SUC r) = _’ SUBST1_TAC >>
  rpt conj_tac
  >- REWRITE_TAC [APPEND_ASSOC]
  >> asm_rewrite_tac [EXISTS_APPEND]
QED

(* MAIN ((3b)): a write-timeout drop of episode j's fd f in round k is a
   hard input error observed in round k, or f's channel broke while the
   episode was open *)
Theorem rdrop_broken:
  oassm lfd pol ifds m w0 ∧ nshut w0 ∧ F2 w0 ∧ pftrace lfd pol ifds m w0 io ∧
  stall_drains36 pf_sendwait w0 io j c ∧
  rdrop lfd pol ifds m w0 k f ∧ f ≠ lfd ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 k))) f = SOME j ∧
  l0_chan_of (rworld lfd pol ifds m w0 k) f = SOME c ⇒
  hard_recv f (rrev lfd pol ifds m w0 k) ∨ broken_open36 w0 io j c
Proof
  strip_tac >> Cases_on ‘hard_recv f (rrev lfd pol ifds m w0 k)’ >> simp[] >>
  drule_all window_facts >> strip_tac >>
  ‘run_ok lfd pol ifds m w0’ by fs[oassm_def] >>
  qpat_x_assum ‘stall_drains36 _ _ _ _ _’
    (strip_assume_tac o REWRITE_RULE [stall_drains36_def]) >>
  (* a round whose poll starts with nothing in flight *)
  sg ‘∀r. i0 ≤ r ∧ r ≤ k ∧ (EL c (WA r).chans).inflight = 0 ⇒ broken_open36 w0 io j c’
  >- (rpt strip_tac >>
      qpat_x_assum ‘∀r. i0 ≤ r ∧ r ≤ k ⇒ _’ (qspec_then ‘r’ mp_tac) >>
      impl_tac >- simp[] >> strip_tac >>
      ‘LPREFIX (fromList (Q r ++ [PV r] ++ PO r)) io’
        by metis_tac[pftrace_revs] >>
      ‘¬retried (PV r)’
        by (qpat_x_assum ‘∀evs w mid ev. _’ (qspecl_then [‘Q r’, ‘WA r’, ‘[]’, ‘PV r’] mp_tac) >>
            impl_tac >- (simp[ep_polls_def, n_out_polls_def, SPLITP, pf_sendwait_def] >>
                         irule LPREFIX_fromList_pfx >>
                         qexists_tac ‘Q r ++ [PV r] ++ PO r’ >> simp[]) >>
            simp[]) >>
      Cases_on ‘(EL c (W1 r).chans).broken’
      >- (simp[broken_open36_def] >>
          qexistsl_tac [‘A’, ‘ev’, ‘B’, ‘f’, ‘W1 r’] >>
          qpat_x_assum ‘Q r ++ [PV r] = _’ (SUBST_ALL_TAC o SYM) >>
          rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          TRY (irule LPREFIX_fromList_pfx >> qexists_tac ‘Q r ++ [PV r] ++ PO r’ >> simp[] >>
               NO_TAC) >>
          fs[EVERY_MEM, EXISTS_MEM]) >>
      qpat_x_assum ‘(EL c (WA r).chans).inflight = 0 ∧ _ ⇒ _’ mp_tac >>
      impl_tac >- simp[] >> strip_tac >>
      ‘retried ev'’ by (qpat_x_assum ‘∀e. MEM e (PO r) ∧ _ ⇒ _’ irule >> simp[]) >>
      ‘n_out_polls f (ep_polls f (Q r) ([PV r] ++ p1)) < pf_sendwait’
        by (irule LESS_EQ_LESS_TRANS >> qexists_tac ‘n_out_polls f ([PV r] ++ p1)’ >>
            REWRITE_TAC [n_out_polls_ep_polls_le] >>
            ‘FILTER (out_poll f) p1 = []’ by fs[FILTER_EQ_NIL, EVERY_MEM, EXISTS_MEM] >>
            qpat_x_assum ‘out_poll f (PV r)’ mp_tac >>
            qpat_x_assum ‘FILTER _ p1 = []’ mp_tac >>
            rpt (pop_assum kall_tac) >> simp[n_out_polls_def, pf_sendwait_def]) >>
      qpat_x_assum ‘∀evs w mid ev. _’
        (qspecl_then [‘Q r’, ‘WA r’, ‘[PV r] ++ p1’, ‘ev'’] mp_tac) >>
      impl_tac
      >- (qpat_assum ‘EL j (l0_accepted (Q r)) = f’ (fn th => REWRITE_TAC [th]) >>
          rpt conj_tac >>
          TRY (FIRST [simp[] >> NO_TAC,
                 REWRITE_TAC [APPEND_ASSOC] >> first_assum ACCEPT_TAC,
                 irule LPREFIX_fromList_pfx >> qexists_tac ‘Q r ++ [PV r] ++ PO r’ >> simp[] >>
                 NO_TAC,
                 irule LESS_EQ_LESS_TRANS >> qexists_tac ‘n_out_polls f ([PV r] ++ p1)’ >>
                 conj_tac >- REWRITE_TAC [n_out_polls_ep_polls_le] >>
                 ‘FILTER (out_poll f) p1 = []’ by fs[FILTER_EQ_NIL, EVERY_MEM, EXISTS_MEM] >>
                 fs[n_out_polls_def, FILTER_APPEND, pf_sendwait_def] >> NO_TAC,
                 disj2_tac >> REWRITE_TAC [EXISTS_APPEND, EXISTS_DEF] >>
                 metis_tac[out_poll_not_send]])) >>
      simp[]) >>
  (* the window's polls from Q i0 on: one per round, and no close call *)
  sg ‘∀d. i0 + d ≤ k ⇒ ∃Z. Q (i0 + d) = Q i0 ++ Z ∧ n_out_polls f Z = d ∧
                          ¬EXISTS (l0_close_call f) Z’
  >- (Induct >- simp[n_out_polls_def] >>
      strip_tac >>
      qpat_x_assum ‘i0 + d ≤ k ⇒ _’ mp_tac >> impl_tac >- simp[] >> strip_tac >>
      qpat_assum ‘∀r. i0 ≤ r ∧ r ≤ k ⇒ _’ (qspec_then ‘i0 + d’ mp_tac) >>
      impl_tac >- simp[] >> strip_tac >>
      qpat_x_assum ‘i0 + d < k ⇒ _’ mp_tac >> impl_tac >- simp[] >> strip_tac >>
      qexists_tac ‘Z ++ [PV (i0 + d)] ++ G’ >>
      ‘i0 + SUC d = SUC (i0 + d)’ by simp[] >> pop_assum SUBST1_TAC >>
      qpat_x_assum ‘Q (SUC _) = _’ SUBST1_TAC >>
      qpat_x_assum ‘Q (i0 + d) = _’ SUBST1_TAC >>
      ‘FILTER (out_poll f) G = []’ by fs[FILTER_EQ_NIL, EVERY_MEM, EXISTS_MEM] >>
      ‘¬l0_close_call f (PV (i0 + d))’ by metis_tac[out_poll_not_close] >>
      qpat_x_assum ‘out_poll f (PV (i0 + d))’ mp_tac >>
      qpat_x_assum ‘¬l0_close_call f (PV (i0 + d))’ mp_tac >>
      qpat_x_assum ‘FILTER _ G = []’ mp_tac >>
      qpat_x_assum ‘¬EXISTS (l0_close_call f) G’ mp_tac >>
      qpat_x_assum ‘¬EXISTS (l0_close_call f) Z’ mp_tac >>
      qpat_x_assum ‘n_out_polls f Z = d’ mp_tac >>
      rpt (pop_assum kall_tac) >> simp[n_out_polls_def, ADD1]) >>
  (* the first round's poll starts with bytes in flight, which drain *)
  ‘i0 ≤ k’ by fs[pf_sendwait_def] >>
  qpat_assum ‘∀r. i0 ≤ r ∧ r ≤ k ⇒ _’ (qspec_then ‘i0’ mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  Cases_on ‘(EL c (WA i0).chans).inflight = 0’
  >- (first_x_assum irule >> qexists_tac ‘i0’ >> simp[]) >>
  ‘LPREFIX (fromList (Q i0)) io’
    by (‘LPREFIX (fromList (revs lfd pol ifds m w0 (SUC i0))) io’ by metis_tac[pftrace_revs] >>
        irule LPREFIX_fromList_pfx >> goal_assum (first_assum o mp_then Any mp_tac) >>
        qpat_x_assum ‘revs _ _ _ _ _ (SUC i0) = _’ SUBST1_TAC >>
        REWRITE_TAC [GSYM APPEND_ASSOC, IS_PREFIX_APPEND3]) >>
  qpat_x_assum ‘∀evs mid w. _’ (qspecl_then [‘Q i0’, ‘[]’, ‘WA i0’] mp_tac) >>
  impl_tac >- simp[] >>
  qpat_assum ‘EL j (l0_accepted (Q i0)) = f’ (fn th => REWRITE_TAC [th]) >>
  simp[] >> strip_tac >>
  qabbrev_tac ‘D = Q i0 ++ more’ >>
  (* the last window round whose poll starts at or before D *)
  sg ‘∀d. i0 + d ≤ k ⇒
          (∃r. i0 ≤ r ∧ r < k ∧ Q r ≼ D ∧ ¬(Q (SUC r) ≼ D)) ∨ Q (i0 + d) ≼ D’
  >- (Induct >- simp[Abbr ‘D’, IS_PREFIX_APPEND3] >> strip_tac >>
      qpat_x_assum ‘i0 + d ≤ k ⇒ _’ mp_tac >> impl_tac >- simp[] >> strip_tac
      >- (disj1_tac >> metis_tac[]) >>
      Cases_on ‘Q (i0 + SUC d) ≼ D’ >- simp[] >>
      disj1_tac >> qexists_tac ‘i0 + d’ >>
      ‘SUC (i0 + d) = i0 + SUC d’ by simp[] >> pop_assum SUBST1_TAC >>
      simp[]) >>
  pop_assum (qspec_then ‘k − i0’ mp_tac) >> impl_tac >- simp[] >>
  ‘i0 + (k − i0) = k’ by simp[] >> pop_assum SUBST1_TAC >> strip_tac
  >- ((* D lies between round r's poll and round r + 1's *)
      qpat_assum ‘∀r. i0 ≤ r ∧ r ≤ k ⇒ _’ (qspec_then ‘SUC r’ mp_tac) >>
      impl_tac >- simp[] >> strip_tac >>
      qpat_assum ‘∀r. i0 ≤ r ∧ r ≤ k ⇒ _’ (qspec_then ‘r’ mp_tac) >>
      impl_tac >- simp[] >> strip_tac >>
      qpat_x_assum ‘r < k ⇒ _’ mp_tac >> impl_tac >- simp[] >> strip_tac >>
      ‘LPREFIX (fromList (Q (SUC r))) io’
        by (‘LPREFIX (fromList (revs lfd pol ifds m w0 (SUC (SUC r)))) io’
              by metis_tac[pftrace_revs] >>
            irule LPREFIX_fromList_pfx >> goal_assum (first_assum o mp_then Any mp_tac) >>
            qpat_x_assum ‘revs _ _ _ _ _ (SUC (SUC r)) = _’ SUBST1_TAC >>
            REWRITE_TAC [GSYM APPEND_ASSOC, IS_PREFIX_APPEND3]) >>
      ‘D ≼ Q (SUC r)’ by metis_tac[LPREFIX_cmp] >>
      ‘smono c (WA r) w'’
        by (irule world_at_smono >> fs[IS_PREFIX_APPEND] >> metis_tac[]) >>
      ‘smono c w' (WA (SUC r))’
        by (irule world_at_smono >> fs[IS_PREFIX_APPEND] >> metis_tac[]) >>
      ‘(EL c (WA (SUC r)).chans).inflight = 0’
        by (qpat_x_assum ‘smono c (WA r) w'’ mp_tac >>
            qpat_x_assum ‘smono c w' (WA (SUC r))’ mp_tac >>
            qpat_x_assum ‘csent (WA (SUC r)) c = csent (WA r) c’ mp_tac >>
            qpat_x_assum ‘c < LENGTH (WA r).chans’ mp_tac >>
            qpat_x_assum ‘(EL c w'.chans).inflight = 0’ mp_tac >>
            rpt (pop_assum kall_tac) >> rw[smono_def, csent_def] >>
            ‘(EL c w'.chans).sent = (EL c (WA (SUC r)).chans).sent’
              by metis_tac[IS_PREFIX_ANTISYM] >>
            fs[]) >>
      qpat_x_assum ‘∀r. i0 ≤ r ∧ r ≤ k ∧ _ ⇒ _’ irule >> qexists_tac ‘SUC r’ >> simp[]) >>
  (* D at or after round k's poll start *)
  qpat_assum ‘∀r. i0 ≤ r ∧ r ≤ k ⇒ _’ (qspec_then ‘k’ mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  ‘LPREFIX (fromList (Q k ++ [PV k])) io’
    by (‘LPREFIX (fromList (revs lfd pol ifds m w0 (SUC k))) io’ by metis_tac[pftrace_revs] >>
        irule LPREFIX_fromList_pfx >> goal_assum (first_assum o mp_then Any mp_tac) >>
        qpat_x_assum ‘revs _ _ _ _ _ (SUC k) = _’ SUBST1_TAC >>
        REWRITE_TAC [IS_PREFIX_APPEND3]) >>
  Cases_on ‘Q k ++ [PV k] ≼ D’
  >- ((* the drain needed all K of the window's polls: impossible *)
      qpat_x_assum ‘∀d. i0 + d ≤ k ⇒ ∃Z. _’ (qspec_then ‘k − i0’ mp_tac) >>
      impl_tac >- simp[] >>
      ‘i0 + (k − i0) = k’ by simp[] >> pop_assum SUBST1_TAC >> strip_tac >>
      qpat_x_assum ‘Q k ++ [PV k] ≼ D’
        (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
      qpat_x_assum ‘Abbrev (D = _)’ (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
      ‘more = Z ++ [PV k] ++ l’
        by (qpat_x_assum ‘D = Q k ++ [PV k] ++ l’ mp_tac >>
            qpat_x_assum ‘D = Q i0 ++ more’ SUBST1_TAC >>
            qpat_x_assum ‘Q k = _’ SUBST1_TAC >>
            REWRITE_TAC [GSYM APPEND_ASSOC, APPEND_11] >> simp[]) >>
      ‘¬EXISTS (l0_close_call f) (Z ++ [PV k])’
        by (‘¬l0_close_call f (PV k)’
              by (qpat_assum ‘out_poll f (PV k)’ (fn th => simp[MATCH_MP out_poll_not_close th])) >>
            qpat_x_assum ‘¬EXISTS (l0_close_call f) Z’ mp_tac >> pop_assum mp_tac >>
            rpt (pop_assum kall_tac) >> simp[]) >>
      qpat_x_assum ‘n_out_polls f (ep_polls f [] more) < _’ mp_tac >>
      simp[ep_polls_def] >>
      drule SPLITP_APPEND_none >> disch_then (qspec_then ‘l’ mp_tac) >>
      simp[] >> disch_then kall_tac >> fs[n_out_polls_def, pf_sendwait_def]) >>
  (* D is round k's poll start *)
  ‘D ≼ Q k ++ [PV k]’ by metis_tac[LPREFIX_cmp] >>
  ‘D = Q k’
    by (imp_res_tac IS_PREFIX_LENGTH >>
        Cases_on ‘LENGTH D = LENGTH (Q k ++ [PV k])’
        >- metis_tac[IS_PREFIX_LENGTH_ANTI] >>
        fs[] >>
        ‘LENGTH D = LENGTH (Q k)’ by decide_tac >>
        metis_tac[IS_PREFIX_LENGTH_ANTI]) >>
  ‘w' = WA k’ by fs[] >>
  qpat_x_assum ‘∀r. i0 ≤ r ∧ r ≤ k ∧ _ ⇒ _’ irule >> qexists_tac ‘k’ >> fs[]
QED
