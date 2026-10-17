(*
  The proxy's pairing liveness (proxyHLStmts.proxy_guar_hl, its last
  clause): every accepted front gets a backend that comes up or is
  refused, unless connects return no socket infinitely often.

  The world-level frame (cfix): while a round does not read backend c,
  c keeps its fd f and channel j, and j's status is unchanged; so the
  round's first read of c answers ERefused exactly when j was Refused at
  the round's start, and otherwise c was Up then (READ).  Across polls,
  Up and Refused are final.
*)
Theory moonshotProxyLive
Ancestors
  moonshotProxySafe moonshotProxyRel moonshotProxy moonshotClient proxyHLStmts
  moonshotClientSpec endpointHLModel endpointWorld asyncHLModel asyncLevel1 asyncCore
  socketV2FFI
Libs
  preamble

Overload PH[local] = “λlfd b hw lv W0. ehhist lfd lv (pifds lfd b hw) (pprog lfd b hw) W0”
Overload PS[local] = “λlfd b hw lv W0 n. pstate lfd b hw (ehhist lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n)”

(* ------------------------------------------------------------------------
   The frame: backend c at fd f, channel j
   ------------------------------------------------------------------------ *)

Definition cfix_def:
  cfix lfd c f j (w : eworld) (hs : ehstate) ⇔
    ALOOKUP hs.tbl c = SOME f ∧ ALOOKUP w.open_fds f = SOME j ∧ j < LENGTH w.chans ∧
    (∀h. MEM (h, f) hs.tbl ⇒ h = c) ∧ (∀f'. MEM (f', j) w.open_fds ⇒ f' = f) ∧
    (∃a q. w.listening = [(lfd, a, q)] ∧ ¬MEM j q) ∧ alloc_ok w.alloc ∧
    (∀k. hs.nxt ≤ k ∧ hdln (w2n lfd) k < dimword (:64) ⇒ hdl lfd k ≠ c)
End

Theorem alloc_not_f:
  alloc_ok w.alloc ∧ ALOOKUP w.open_fds f = SOME j ∧ LENGTH (ep_used w) < dimword (:64) ⇒
  w.alloc j' (ep_used w) ≠ f
Proof
  rw[alloc_ok_def] >> first_x_assum (qspecl_then [‘j'’, ‘ep_used w’] mp_tac) >>
  simp[] >> simp[ep_used_def, MEM_MAP] >> rpt strip_tac >>
  imp_res_tac ALOOKUP_MEM >> first_x_assum (qspec_then ‘(f, j)’ mp_tac) >> simp[]
QED

Theorem hdln_mono:
  k0 < k ⇒ hdln n k0 < hdln n k
Proof
  rw[hdln_def]
QED

(* A fresh handle (issued later, and in range) is not c *)
Theorem cfix_new_handle:
  cfix lfd c f j w hs ∧ hdln (w2n lfd) hs.nxt < dimword (:64) ⇒
  hdl lfd hs.nxt ≠ c ∧
  ∀k. hs.nxt + 1 ≤ k ∧ hdln (w2n lfd) k < dimword (:64) ⇒ hdl lfd k ≠ c
Proof
  rw[cfix_def]
QED

(* Another handle's fd and channel are not c's *)
Theorem cfix_other:
  cfix lfd c f j w hs ∧ ALOOKUP hs.tbl h = SOME f' ∧ h ≠ c ∧ ALOOKUP w.open_fds f' = SOME j' ⇒
  f' ≠ f ∧ j' ≠ j
Proof
  rw[cfix_def] >> imp_res_tac ALOOKUP_MEM >> strip_tac >> gvs[] >> res_tac >> gvs[]
QED

(* A channel update keeps the frame, and j's status unless it is j's own
   update and changes the status *)
Theorem cfix_upd:
  cfix lfd c f j w hs ∧ (j' = j ⇒ ∀x. (g x).status = x.status) ⇒
  cfix lfd c f j (upd_chan j' g w) hs ∧
  (EL j (upd_chan j' g w).chans).status = (EL j w.chans).status
Proof
  rw[cfix_def, upd_chan_def, EL_LUPDATE] >> rw[] >> gvs[]
QED

Theorem cfix_upd_other:
  cfix lfd c f j w hs ∧ j' ≠ j ⇒ cfix lfd c f j (upd_chan j' g w) hs
Proof
  strip_tac >> irule (cj 1 cfix_upd) >> simp[]
QED

Theorem upd_chan_open_fds:
  (upd_chan j g w with open_fds := x) = upd_chan j g (w with open_fds := x)
Proof
  simp[upd_chan_def]
QED

Theorem cfix_close:
  cfix lfd c f j w hs ∧ h ≠ c ∧ f' ≠ f ⇒
  cfix lfd c f j (w with open_fds := ADELKEY f' w.open_fds) (eh_del h hs)
Proof
  rw[cfix_def, eh_del_def, ALOOKUP_ADELKEY] >> fs[ADELKEY_def, MEM_FILTER] >> metis_tac[]
QED

Theorem ehdo_cfix:
  cfix lfd c f j w hs ∧ ehdo lfd v (w, hs) x = SOME (r, (w1, hs1)) ∧ (∀k. x ≠ ERead c k) ⇒
  cfix lfd c f j w1 hs1 ∧ (EL j w1.chans).status = (EL j w.chans).status
Proof
  strip_tac >> Cases_on ‘x’ >> fs[ehdo_def]
  >- (‘∃a q. w.listening = [(lfd, a, q)]’ by fs[cfix_def] >>
      gvs[ep_accept_def, AllCaseEqs(), ep_alloc_def] >>
      ‘ALOOKUP w.open_fds f = SOME j ∧ alloc_ok w.alloc’ by fs[cfix_def] >>
      ‘w.alloc j' (ep_used w) ≠ f’ by (match_mp_tac alloc_not_f >> fs[wordsTheory.dimword_64]) >>
      ‘hdln (w2n c') hs.nxt < dimword (:64)’ by fs[wordsTheory.dimword_64] >>
      drule_all cfix_new_handle >> strip_tac >>
      fs[cfix_def, eh_new_def, AFUPDKEY_def] >> rw[] >> gvs[])
  >- (Cases_on ‘ALOOKUP hs.tbl c'’ >> gvs[] >> rename1 ‘ALOOKUP hs.tbl c' = SOME f'’ >>
      gvs[ep_conn_err_def, ep_chan_of_def, ep_read_def, ep_close_def, AllCaseEqs()] >>
      drule_all cfix_other >> strip_tac >>
      (conj_tac >- simp[upd_chan_open_fds, cfix_upd_other, cfix_close]) >>
      simp[upd_chan_def, EL_LUPDATE])
  >- (Cases_on ‘ALOOKUP hs.tbl c'’ >> gvs[] >>
      gvs[ep_send_def, ep_chan_of_def, AllCaseEqs()] >>
      irule cfix_upd >> simp[])
  >- (gvs[ep_connect_def, AllCaseEqs(), ep_alloc_def] >>
      TRY (fs[cfix_def] >> NO_TAC) >>
      fs[ep_used_def] >>
      ‘w.alloc (LENGTH w.chans) (ep_used w) ≠ f’
        by (irule alloc_not_f >> fs[cfix_def] >> gvs[ep_used_def]) >>
      ‘hdln (w2n lfd) hs.nxt < dimword (:64)’ by fs[wordsTheory.dimword_64] >>
      drule_all cfix_new_handle >> strip_tac >>
      fs[ep_used_def, cfix_def, eh_new_def, EL_APPEND1] >> rw[] >> gvs[])
  >> gvs[]
QED

(* A round's actions that do not read c keep the frame and j's status *)
Theorem ehacts_cfix:
  ∀acts k w hs rs w1 hs1.
    cfix lfd c f j w hs ∧ ehacts lfd lv n k (w, hs) acts = SOME (rs, (w1, hs1)) ∧
    (∀k'. ¬MEM (ERead c k') acts) ⇒
    cfix lfd c f j w1 hs1 ∧ (EL j w1.chans).status = (EL j w.chans).status
Proof
  Induct >- simp[ehacts_def] >>
  rpt gen_tac >> strip_tac >> qpat_x_assum ‘ehacts _ _ _ _ _ _ = _’ mp_tac >>
  simp[Once ehacts_def] >> rpt (CASE_TAC >> simp[]) >> strip_tac >> gvs[] >>
  rename1 ‘ehdo _ _ _ h = SOME (q, r)’ >> PairCases_on ‘r’ >>
  ‘cfix lfd c f j r0 r1 ∧ (EL j r0.chans).status = (EL j w.chans).status’
    by (irule ehdo_cfix >> qexistsl_tac [‘hs’, ‘q’, ‘lv n k’, ‘h’] >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED

(* ------------------------------------------------------------------------
   READ: the round's first read of backend c tells Up from Refused
   ------------------------------------------------------------------------ *)

(* A read of c while j is Refused answers ERefused *)
Theorem ehdo_read_refused:
  cfix lfd c f j w hs ∧ (EL j w.chans).status = Refused ∧
  ehdo lfd v (w, hs) (ERead c k) = SOME (r, st) ⇒ r = ERefused
Proof
  rw[cfix_def] >> gvs[ehdo_def, ep_conn_err_def, ep_chan_of_def, AllCaseEqs()]
QED

Theorem split_first_read:
  ∀l. MEM (ERead c k) l ⇒
      ∃pre k' post. l = pre ++ [ERead c k'] ++ post ∧ ∀k''. ¬MEM (ERead c k'') pre
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on ‘∃k1. h = ERead c k1’
  >- (pop_assum strip_assume_tac >> qexistsl_tac [‘[]’, ‘k1’, ‘l’] >>
      asm_rewrite_tac [APPEND, MEM]) >>
  ‘MEM (ERead c k) l’ by (qpat_x_assum ‘MEM _ (_ :: _)’ mp_tac >> rw[] >> metis_tac[]) >>
  first_x_assum drule >> strip_tac >> qexistsl_tac [‘h :: pre’, ‘k'’, ‘post’] >>
  rw[] >> metis_tac[]
QED

(* The first read of c in a round's actions answers ERefused when j was
   Refused at the round's start *)
Theorem ehacts_first_read:
  cfix lfd c f j w hs ∧ (EL j w.chans).status = Refused ∧
  ehacts lfd lv n 0 (w, hs) acts = SOME (rs, st2) ∧ MEM (ERead c k) acts ⇒
  ∃k'. MEM (ERead c k', ERefused) (ZIP (acts, rs))
Proof
  strip_tac >> drule split_first_read >> strip_tac >> gvs[] >>
  qpat_x_assum ‘ehacts _ _ _ _ _ _ = _’ (mp_tac o REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  strip_tac >> drule ehacts_APPEND_inv >> strip_tac >>
  PairCases_on ‘st1’ >> drule_all ehacts_cfix >> strip_tac >>
  qpat_x_assum ‘ehacts _ _ _ _ _ (_ :: _) = _’ mp_tac >> simp[Once ehacts_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  ‘r = ERefused’ by (irule ehdo_read_refused >> metis_tac[]) >>
  ‘LENGTH rs1 = LENGTH pre ∧ LENGTH rs' = LENGTH post’ by (imp_res_tac ehacts_LENGTH >> fs[]) >>
  REWRITE_TAC [GSYM APPEND_ASSOC, APPEND] >> fs[GSYM ZIP_APPEND, ZIP_def] >> metis_tac[]
QED

Theorem pacts_read_rdy:
  MEM (ERead h k) (MAP SND (pacts lfd b hw st rdy)) ⇒ h ∈ rdy
Proof
  ONCE_REWRITE_TAC [pacts_SND] >> simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rw[] >> gvs[plevels_def, MEM_MAP] >>
  gvs[pone_def, pconnects_def, pwrites_def, preads_def, AllCaseEqs()] >>
  every_case_tac >> gvs[]
QED

Theorem PS_read_rdy:
  proxy_world lfd a W0 ∧ MEM (ERead h k) (MAP SND (PS lfd b hw lv W0 m).last) ⇒
  h ∈ prdy (PH lfd b hw lv W0 m)
Proof
  strip_tac >> drule pinv_all >> disch_then (qspecl_then [‘lv’, ‘hw’, ‘b’, ‘m’] mp_tac) >>
  simp[pinv_def] >> strip_tac >> gvs[] >> drule pacts_read_rdy >> simp[]
QED

(* The frame from the relation: a pair's handle with an open channel *)
Theorem prel_cfix:
  prel lfd st rdy ps w hs ∧ hch w hs c j ∧ MEM c (FLAT (MAP phds st.pc)) ⇒
  ∃f. cfix lfd c f j w hs
Proof
  rw[hch_def] >> qexists_tac ‘f’ >> fs[prel_def, cfix_def] >> rpt conj_tac
  >- (rpt strip_tac >> qspecl_then [‘hs.tbl’, ‘h’, ‘c’, ‘f’] mp_tac ALOOKUP_SND_inj >>
      simp[ALOOKUP_ALL_DISTINCT_MEM])
  >- (rpt strip_tac >>
      ‘ALOOKUP w.open_fds f' = SOME j’ by simp[ALOOKUP_ALL_DISTINCT_MEM] >>
      qspecl_then [‘w.open_fds’, ‘f'’, ‘f’, ‘j’] mp_tac ALOOKUP_SND_inj >> simp[])
  >- (strip_tac >> fs[EVERY_MEM] >> first_x_assum drule >> strip_tac >>
      imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP, EXISTS_PROD] >> metis_tac[])
  >> rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
  mp_tac (Q.INST [‘i’ |-> ‘k'’] honestL1StepsTheory.hdl_fresh) >> fs[wordsTheory.dimword_64]
QED

(* One round of the run: its actions' results and its poll *)
Theorem PS_round:
  proxy_world lfd a W0 ⇒
  ∃rs w1 hs1 rdy'.
    ehacts lfd lv m 0 (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 m)
      (MAP SND (PS lfd b hw lv W0 m).last) = SOME (rs, (w1, hs1)) ∧
    ehpoll lfd hs1 (pifds lfd b hw (PH lfd b hw lv W0 m)) w1 =
      (rdy', ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 (SUC m)) ∧
    PH lfd b hw lv W0 (SUC m) = PH lfd b hw lv W0 m ++ [ssnap rdy' rs]
Proof
  strip_tac >> drule pinv_all >> disch_then (qspecl_then [‘lv’, ‘hw’, ‘b’, ‘m’] assume_tac) >>
  drule pinv_SUC >> rewrite_tac [pprog_new_actions] >> strip_tac >>
  qmatch_asmsub_abbrev_tac ‘ehacts lfd lv m 0 st0 acts ≠ NONE’ >>
  Cases_on ‘ehacts lfd lv m 0 st0 acts’ >> fs[] >> PairCases_on ‘x’ >>
  rename1 ‘_ = SOME (rs, w1, hs1)’ >>
  Cases_on ‘ehpoll lfd hs1 (pifds lfd b hw (PH lfd b hw lv W0 m)) w1’ >>
  rename1 ‘_ = (rdy', r2)’ >> PairCases_on ‘r2’ >>
  qspecl_then [‘lfd’, ‘lv’, ‘pifds lfd b hw’, ‘pprog lfd b hw’, ‘W0’, ‘m’, ‘rs’, ‘w1’, ‘hs1’,
               ‘rdy'’, ‘r20’, ‘r21’] mp_tac
    (Q.GENL [‘lfd’, ‘lv’, ‘ifds’, ‘m’, ‘w0’, ‘n’, ‘rs’, ‘w1’, ‘hs1’, ‘rdy’, ‘w2’, ‘hs2’]
       honestL1EPRefineTheory.ehround_step) >>
  impl_tac >- gvs[Abbr ‘st0’, Abbr ‘acts’, ehacts_tot_def, pprog_new_actions] >>
  strip_tac >> qexistsl_tac [‘rs’, ‘w1’, ‘hs1’, ‘rdy'’] >> gvs[Abbr ‘st0’, Abbr ‘acts’]
QED

Theorem PH_pairs_SUC:
  PH lfd b hw lv W0 (SUC m) = PH lfd b hw lv W0 m ++ [ssnap rdy' rs] ⇒
  hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 (SUC m)) =
  hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 m) ++ ZIP (MAP SND (PS lfd b hw lv W0 m).last, rs)
Proof
  strip_tac >> asm_rewrite_tac [] >>
  simp[hl_pairs_SNOC, asyncM3WorldTheory.ssnap_def, pprog_new_actions]
QED

(* At a round that reads backend c (the actions from st' with st's pairs),
   c's channel is Up or Refused *)
Theorem prel_read_settled:
  prel lfd st rdy ps w hs ∧ i < LENGTH st.pc ∧ (EL i st.pc).bh = SOME c ∧
  MEM (ERead c k) (MAP SND (pacts lfd b hw st' rdy)) ∧ st'.pc = st.pc ⇒
  ∃f j. cfix lfd c f j w hs ∧ ((EL j w.chans).status = Up ∨ (EL j w.chans).status = Refused)
Proof
  strip_tac >>
  ‘c ∈ rdy’ by (drule pacts_read_rdy >> simp[]) >>
  ‘(EL i st.pc).bo’
    by (‘MEM c (phds (EL i st.pc))’ by fs[phds_def] >>
        qpat_x_assum ‘MEM (ERead _ _) _’ (strip_assume_tac o MATCH_MP pacts_read_open) >>
        qpat_x_assum ‘st'.pc = st.pc’ (fn th => fs[th]) >>
        ‘MEM c (phds (EL i' st.pc))’ by fs[phds_def] >>
        ‘i = i'’ by (drule prel_distinct >> disch_then irule >> simp[] >> qexists_tac ‘c’ >> simp[]) >>
        rpt BasicProvers.VAR_EQ_TAC >>
        FIRST [fs[] >> NO_TAC, drule_all prel_fh_bh >> disch_then drule >> fs[]]) >>
  ‘MEM c (FLAT (MAP phds st.pc))’
    by (simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> qexists_tac ‘EL i st.pc’ >>
        simp[EL_MEM, phds_def]) >>
  drule_all prel_pok >> rewrite_tac [pok_def] >> strip_tac >>
  qpat_x_assum ‘option_CASE _ _ _’ mp_tac >> asm_rewrite_tac [] >> simp[] >> strip_tac >>
  drule_all prel_cfix >> strip_tac >> qexistsl_tac [‘f’, ‘j’] >> simp[] >> gvs[]
QED

(* MAIN of this part (READ): a round that reads backend c finds it Up at
   the round's start, or is answered ERefused *)
Theorem proxy_read_back_settled:
  proxy_world lfd a W0 ∧ i < LENGTH (PS lfd b hw lv W0 m).pc ∧
  (EL i (PS lfd b hw lv W0 m).pc).bh = SOME c ∧
  MEM (ERead c k) (MAP SND (PS lfd b hw lv W0 m).last) ⇒
  up_at lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 m c ∨
  hl_refused c (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 (SUC m)))
Proof
  strip_tac >>
  drule pinv_all >> disch_then (qspecl_then [‘lv’, ‘hw’, ‘b’, ‘m’] mp_tac) >>
  simp[pinv_def] >> strip_tac >>
  qpat_x_assum ‘MEM (ERead _ _) _’ (fn th => assume_tac th >> mp_tac th) >>
  qpat_x_assum ‘(PS _ _ _ _ _ _).last = _’ (fn th => REWRITE_TAC [th]) >> strip_tac >>
  drule_all prel_read_settled >> strip_tac
  >- (disj1_tac >> fs[cfix_def, up_at_def, chan_status_def, ep_chan_of_def]) >>
  disj2_tac >>
  drule PS_round >> disch_then (qspecl_then [‘m’, ‘lv’, ‘hw’, ‘b’] strip_assume_tac) >>
  drule PH_pairs_SUC >> disch_then (fn th => REWRITE_TAC [th]) >>
  qpat_x_assum ‘ehacts _ _ _ _ _ _ = _’ mp_tac >>
  qmatch_goalsub_abbrev_tac ‘ehacts lfd lv m 0 ws acts’ >> PairCases_on ‘ws’ >> strip_tac >>
  RULE_ASSUM_TAC (REWRITE_RULE [pairTheory.FST, pairTheory.SND]) >>
  drule_all ehacts_first_read >> strip_tac >>
  simp[hl_refused_def] >> metis_tac[]
QED
