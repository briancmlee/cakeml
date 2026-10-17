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

(* ------------------------------------------------------------------------
   The connect phase: while pair i has no backend, each round's connect
   returns no socket
   ------------------------------------------------------------------------ *)

Theorem ehacts_connect_res:
  ∀acts k st rs st'. ehacts lfd lv n k st acts = SOME (rs, st') ∧
    MEM (EConnect a, r) (ZIP (acts, rs)) ⇒ ∃oc. r = EConnected oc
Proof
  Induct >- simp[ehacts_def] >> rpt gen_tac >> simp[Once ehacts_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >- (PairCases_on ‘st’ >> gvs[ehdo_def, AllCaseEqs()]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem sel_mem:
  ∀ts rs. LENGTH rs = LENGTH ts ∧ MEM (x, r) (ZIP (MAP SND (seltag i ts), selres i ts rs)) ⇒
    MEM (x, r) (ZIP (MAP SND ts, rs))
Proof
  Induct >- simp[] >> rpt gen_tac >> PairCases_on ‘h’ >> Cases_on ‘rs’ >> simp[] >>
  rw[] >> gvs[] >> metis_tac[]
QED

Theorem MEM_FILTER_LENGTH:
  MEM x l ∧ P x ⇒ 0 < LENGTH (FILTER P l)
Proof
  rpt strip_tac >> ‘MEM x (FILTER P l)’ by simp[MEM_FILTER] >>
  Cases_on ‘FILTER P l’ >> gvs[]
QED

(* A round in which pair i has no backend, before and after, has a
   connect that returned no socket *)
Theorem proxy_connect_round:
  proxy_world lfd a W0 ∧ i < LENGTH (PS lfd b hw lv W0 m).pc ∧
  (EL i (PS lfd b hw lv W0 m).pc).bh = NONE ∧
  (EL i (PS lfd b hw lv W0 (SUC m)).pc).bh = NONE ⇒
  hl_nosock (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 m)) <
  hl_nosock (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 (SUC m)))
Proof
  strip_tac >>
  drule PS_prel_n >> disch_then (qspecl_then [‘m’, ‘lv’, ‘hw’, ‘b’] assume_tac) >>
  drule_all prel_pok >> rewrite_tac [pok_def] >> strip_tac >>
  qpat_x_assum ‘option_CASE _ _ _’ mp_tac >> asm_rewrite_tac [] >> simp[] >> strip_tac >>
  drule PS_round >> disch_then (qspecl_then [‘m’, ‘lv’, ‘hw’, ‘b’] strip_assume_tac) >>
  drule PH_pairs_SUC >> disch_then (fn th => REWRITE_TAC [th]) >>
  qspecl_then [‘lfd’, ‘b’, ‘hw’, ‘lv’, ‘W0’, ‘m’] strip_assume_tac
    (Q.GENL [‘lfd’, ‘b’, ‘hw’, ‘lv’, ‘W0’, ‘n’] PS_SUC_fields) >>
  ‘s = ssnap rdy' rs’ by (qpat_x_assum ‘PH _ _ _ _ _ (SUC m) = _ ++ [s]’ mp_tac >>
                          asm_rewrite_tac [] >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  qpat_x_assum ‘pst_pc (PS _ _ _ _ _ (SUC m)) = _’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [asyncM3WorldTheory.ssnap_def]) >>
  drule pinv_all >> disch_then (qspecl_then [‘lv’, ‘hw’, ‘b’, ‘m’] mp_tac) >>
  simp[pinv_def] >> strip_tac >>
  qabbrev_tac ‘ts = (PS lfd b hw lv W0 m).last’ >>
  qabbrev_tac ‘p0 = EL i (PS lfd b hw lv W0 m).pc’ >>
  ‘LENGTH rs = LENGTH ts’ by (imp_res_tac ehacts_LENGTH >> fs[]) >>
  qspecl_then [‘ts’, ‘PS lfd b hw lv W0 m with lv := []’, ‘rs’] mp_tac
    (Q.GEN ‘i’ pupd_slot |> Q.SPEC ‘i’) >>
  impl_tac >- simp[] >> simp[] >> strip_tac >>
  ‘seltag i ts = [(i, EConnect b)]’
    by (qunabbrev_tac ‘ts’ >> asm_rewrite_tac [] >>
        ‘i < LENGTH st'.pc’ by simp[] >> drule seltag_pacts >> disch_then (fn th => REWRITE_TAC [th]) >>
        ‘EL i st'.pc = p0’ by simp[Abbr ‘p0’] >> asm_rewrite_tac [] >>
        simp[pone_def, pconnects_def, pwrites_def, preads_def]) >>
  ‘LENGTH (selres i ts rs) = 1’
    by (‘LENGTH (selres i ts rs) = LENGTH (seltag i ts)’ by (irule LENGTH_selres >> simp[]) >>
        pop_assum SUBST1_TAC >> qpat_x_assum ‘seltag i ts = _’ SUBST1_TAC >> simp[]) >>
  Cases_on ‘selres i ts rs’ >> gvs[] >>
  rename1 ‘selres i ts rs = [r]’ >>
  ‘MEM (EConnect b, r) (ZIP (MAP SND ts, rs))’
    by (irule sel_mem >> conj_tac >- first_assum ACCEPT_TAC >> qexists_tac ‘i’ >> asm_rewrite_tac [MEM, ZIP_def, MAP]) >>
  ‘∃oc. r = EConnected oc’
    by (irule ehacts_connect_res >> qpat_x_assum ‘ehacts _ _ _ _ _ _ = _’ (irule_at Any) >>
        qexists_tac ‘b’ >> simp[]) >>
  Cases_on ‘oc’ >> gvs[presf_def, pres_def] >>
  simp[hl_nosock_def, FILTER_APPEND] >>
  irule MEM_FILTER_LENGTH >> qexists_tac ‘(EConnect b, EConnected NONE)’ >> simp[]
QED

(* So, if pair i never gets a backend, connects return no socket without
   bound *)
Theorem proxy_connect_forever:
  proxy_world lfd a W0 ∧ i < LENGTH (PS lfd b hw lv W0 n).pc ∧
  (∀m. n ≤ m ⇒ (EL i (PS lfd b hw lv W0 m).pc).bh = NONE) ⇒
  ∀k. ∃n'. k ≤ hl_nosock (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n'))
Proof
  strip_tac >>
  ‘∀d. i < LENGTH (PS lfd b hw lv W0 (n + d)).pc’
    by (gen_tac >> irule (cj 1 pkeep_EL) >>
        qexists_tac ‘(PS lfd b hw lv W0 n).pc’ >> simp[] >>
        irule pc_mono >> simp[] >> metis_tac[]) >>
  ‘∀d. d ≤ hl_nosock (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 (n + d)))’
    by (Induct >> simp[] >>
        ‘hl_nosock (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 (n + d))) <
         hl_nosock (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 (SUC (n + d))))’
          by (mp_tac (Q.INST [‘m’ |-> ‘n + d’] proxy_connect_round) >>
              impl_tac >- (rpt conj_tac >>
                           FIRST [first_assum ACCEPT_TAC, first_assum (qspec_then ‘d’ ACCEPT_TAC),
                                  qpat_assum ‘∀m. n ≤ m ⇒ _’ irule >> simp[]]) >>
              simp[]) >>
        fs[ADD_CLAUSES]) >>
  gen_tac >> qexists_tac ‘n + k’ >> simp[]
QED

(* ------------------------------------------------------------------------
   The backend phase: a backend that is never read stays Connecting, which
   connect fairness forbids
   ------------------------------------------------------------------------ *)

(* A read in the history was issued by an earlier round *)
Theorem hl_pairs_read_round:
  MEM (ERead h k, r) (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 m)) ⇒
  ∃r0. r0 < m ∧ MEM (ERead h k) (MAP SND (PS lfd b hw lv W0 r0).last)
Proof
  simp[hl_pairs_def, MEM_FLAT, MEM_GENLIST, PULL_EXISTS, ehhist_LENGTH] >> rpt strip_tac >>
  rename1 ‘r0 < m’ >> qexists_tac ‘r0’ >> simp[] >>
  drule moonshotProxyTheory.MEM_ZIP_FST >>
  ‘TAKE r0 (PH lfd b hw lv W0 m) = PH lfd b hw lv W0 r0’ by simp[ehhist_TAKE] >>
  simp[pprog_new_actions]
QED

Theorem PS_noread_hist:
  (∀m k. ¬MEM (ERead c k) (MAP SND (PS lfd b hw lv W0 m).last)) ⇒
  ¬hl_up c (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n)) ∧
  ¬hl_eof c (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n)) ∧
  ¬hl_refused c (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n))
Proof
  rw[hl_up_def, hl_eof_def, hl_refused_def] >> CCONTR_TAC >> fs[] >>
  drule hl_pairs_read_round >> metis_tac[]
QED

(* A slot's front, and its backend once it has one, never change *)
Theorem PS_slot_const:
  proxy_world lfd a W0 ∧ i < LENGTH (PS lfd b hw lv W0 n).pc ∧
  i < LENGTH (PS lfd b hw lv W0 n').pc ⇒
  (EL i (PS lfd b hw lv W0 n).pc).fh = (EL i (PS lfd b hw lv W0 n').pc).fh ∧
  ∀c c'. (EL i (PS lfd b hw lv W0 n).pc).bh = SOME c ∧
         (EL i (PS lfd b hw lv W0 n').pc).bh = SOME c' ⇒ c = c'
Proof
  strip_tac >>
  ‘pkeep (PS lfd b hw lv W0 n).pc (PS lfd b hw lv W0 (MAX n n')).pc’
    by (irule pc_mono >> simp[] >> qexists_tac ‘a’ >> simp[]) >>
  ‘pkeep (PS lfd b hw lv W0 n').pc (PS lfd b hw lv W0 (MAX n n')).pc’
    by (irule pc_mono >> simp[] >> qexists_tac ‘a’ >> simp[]) >>
  qspecl_then [‘(PS lfd b hw lv W0 n).pc’, ‘(PS lfd b hw lv W0 (MAX n n')).pc’, ‘i’] mp_tac
    (Q.GENL [‘pc’, ‘pc'’, ‘i’] pkeep_EL) >>
  qspecl_then [‘(PS lfd b hw lv W0 n').pc’, ‘(PS lfd b hw lv W0 (MAX n n')).pc’, ‘i’] mp_tac
    (Q.GENL [‘pc’, ‘pc'’, ‘i’] pkeep_EL) >>
  asm_rewrite_tac [] >> rpt strip_tac >> res_tac >> fs[]
QED

(* A read of a slot's backend is a read by that slot *)
Theorem read_c_slot:
  proxy_world lfd a W0 ∧ i < LENGTH (PS lfd b hw lv W0 n0).pc ∧
  (EL i (PS lfd b hw lv W0 n0).pc).bh = SOME c ∧
  MEM (ERead c k) (MAP SND (PS lfd b hw lv W0 m).last) ⇒
  i < LENGTH (PS lfd b hw lv W0 m).pc ∧ (EL i (PS lfd b hw lv W0 m).pc).bh = SOME c
Proof
  strip_tac >>
  ‘MEM c (phds (EL i (PS lfd b hw lv W0 n0).pc))’ by fs[phds_def] >>
  qpat_x_assum ‘MEM (ERead _ _) _’ (strip_assume_tac o MATCH_MP PS_read_open) >>
  ‘MEM c (phds (EL i' (PS lfd b hw lv W0 m).pc))’ by fs[phds_def] >>
  ‘i' = i’
    by (mp_tac (Q.INST [‘i’ |-> ‘i'’, ‘j’ |-> ‘i’, ‘n’ |-> ‘m’, ‘n'’ |-> ‘n0’, ‘h’ |-> ‘c’]
                  pslot_same) >> simp[]) >>
  gvs[] >>
  qspecl_then [‘n0’, ‘m’] mp_tac (Q.GENL [‘n’, ‘n'’] PS_slot_const) >>
  asm_rewrite_tac [] >> disch_then (assume_tac o CONJUNCT1) >>
  drule PS_prel_n >> disch_then (qspecl_then [‘n0’, ‘lv’, ‘hw’, ‘b’] assume_tac) >>
  drule_all prel_fh_bh >> simp[]
QED

Theorem pacts_reads_back:
  i < LENGTH st.pc ∧ (EL i st.pc).bh = SOME c ∧ (EL i st.pc).fo ∧ (EL i st.pc).bo ∧
  ¬(EL i st.pc).bup ∧ c ∈ rdy ⇒
  MEM (ERead c pread) (MAP SND (pacts lfd b hw st rdy))
Proof
  strip_tac >>
  ‘MEM (ERead c pread) (pone b hw st.lv (MAP SND st.last) (FLAT (MAP pwrites st.pc)) rdy (EL i st.pc))’
    by fs[pone_def, preads_def] >>
  ONCE_REWRITE_TAC [pacts_SND] >> simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[EL_MEM]
QED

Theorem PS_pok:
  proxy_world lfd a W0 ∧ i < LENGTH (PS lfd b hw lv W0 m).pc ⇒
  pok (FST (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 m))
      (SND (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 m))
      (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 m)) (prdy (PH lfd b hw lv W0 m))
      (EL i (PS lfd b hw lv W0 m).pc)
Proof
  strip_tac >> drule PS_prel_n >> disch_then (qspecl_then [‘m’, ‘lv’, ‘hw’, ‘b’] assume_tac) >>
  drule_all prel_pok >> simp[]
QED

Theorem pok_some:
  pok w hs ps rdy p ∧ p.bh = SOME c ⇒
  (p.fo ⇔ ¬hl_eof p.fh ps) ∧ (p.bo ⇔ ¬hl_eof c ps ∧ ¬hl_refused c ps) ∧
  (p.bup ⇔ hl_up c ps) ∧
  (p.bo ⇒ ∃j. hch w hs c j ∧
              ((EL j w.chans).status = Up ∨ (EL j w.chans).status = Refused ∨
               (EL j w.chans).status = Connecting ∧ c ∉ rdy))
Proof
  strip_tac >> gvs[pok_def] >> strip_tac >> gvs[] >> metis_tac[]
QED

(* A read of a slot's front is a read by that slot, made while its backend
   was up *)
Theorem read_fh_slot:
  proxy_world lfd a W0 ∧ i < LENGTH (PS lfd b hw lv W0 n0).pc ∧
  MEM (ERead (EL i (PS lfd b hw lv W0 n0).pc).fh k) (MAP SND (PS lfd b hw lv W0 r).last) ⇒
  i < LENGTH (PS lfd b hw lv W0 r).pc ∧
  ∃c. (EL i (PS lfd b hw lv W0 r).pc).bh = SOME c ∧ (EL i (PS lfd b hw lv W0 r).pc).bup
Proof
  strip_tac >>
  qpat_x_assum ‘MEM (ERead _ _) _’ (strip_assume_tac o MATCH_MP PS_read_open) >>
  qabbrev_tac ‘h = (EL i (PS lfd b hw lv W0 n0).pc).fh’ >>
  ‘MEM h (phds (EL i (PS lfd b hw lv W0 n0).pc)) ∧ MEM h (phds (EL i' (PS lfd b hw lv W0 r).pc))’
    by fs[phds_def, Abbr ‘h’] >>
  ‘i' = i’
    by (mp_tac (Q.INST [‘i’ |-> ‘i'’, ‘j’ |-> ‘i’, ‘n’ |-> ‘r’, ‘n'’ |-> ‘n0’] pslot_same) >>
        simp[]) >>
  gvs[] >>
  qspecl_then [‘n0’, ‘r’] mp_tac (Q.GENL [‘n’, ‘n'’] PS_slot_const) >>
  asm_rewrite_tac [] >> disch_then (assume_tac o CONJUNCT1) >>
  drule PS_prel_n >> disch_then (qspecl_then [‘r’, ‘lv’, ‘hw’, ‘b’] assume_tac) >>
  drule_all prel_fh_bh >> gvs[]
QED

(* From the round its slot got backend c on, if c is never read: the
   front and c stay open, c has not answered, and c is never ready *)
Theorem proxy_quiet_back:
  proxy_world lfd a W0 ∧ i < LENGTH (PS lfd b hw lv W0 n0).pc ∧
  (EL i (PS lfd b hw lv W0 n0).pc).bh = SOME c ∧
  (∀m k. ¬MEM (ERead c k) (MAP SND (PS lfd b hw lv W0 m).last)) ∧ n0 ≤ m ⇒
  i < LENGTH (PS lfd b hw lv W0 m).pc ∧ (EL i (PS lfd b hw lv W0 m).pc).bh = SOME c ∧
  (EL i (PS lfd b hw lv W0 m).pc).fo ∧ (EL i (PS lfd b hw lv W0 m).pc).bo ∧
  ¬(EL i (PS lfd b hw lv W0 m).pc).bup ∧ c ∉ prdy (PH lfd b hw lv W0 m)
Proof
  strip_tac >>
  ‘pkeep (PS lfd b hw lv W0 n0).pc (PS lfd b hw lv W0 m).pc’
    by (irule pc_mono >> simp[] >> qexists_tac ‘a’ >> simp[]) >>
  drule_all pkeep_EL >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  ‘∀n. ¬hl_up c (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n)) ∧
       ¬hl_eof c (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n)) ∧
       ¬hl_refused c (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n))’
    by (gen_tac >> qpat_assum ‘∀m k. _’ (fn th => ACCEPT_TAC (MATCH_MP PS_noread_hist th))) >>
  ‘∀r. i < LENGTH (PS lfd b hw lv W0 r).pc ∧ (EL i (PS lfd b hw lv W0 r).pc).bh = SOME c ⇒
       ¬(EL i (PS lfd b hw lv W0 r).pc).bup’
    by (rpt strip_tac >> drule_all PS_pok >> strip_tac >> drule_all pok_some >> simp[]) >>
  ‘¬hl_eof (EL i (PS lfd b hw lv W0 m).pc).fh (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 m))’
    by (simp[hl_eof_def] >> rpt strip_tac >>
        drule hl_pairs_read_round >> strip_tac >>
        qspecl_then [‘n0’, ‘r0’, ‘n’] mp_tac (Q.GENL [‘n0’, ‘r’, ‘k’] read_fh_slot) >>
        asm_rewrite_tac [] >> strip_tac >>
        ‘c' = c’
          by (qspecl_then [‘r0’, ‘n0’] mp_tac (Q.GENL [‘n’, ‘n'’] PS_slot_const) >>
              asm_rewrite_tac [] >> simp[]) >>
        qpat_x_assum ‘∀r. _ ∧ _ ⇒ ¬_’ (qspec_then ‘r0’ mp_tac) >> gvs[]) >>
  qspecl_then [‘m’, ‘i’] mp_tac (Q.GENL [‘m’, ‘i’] PS_pok) >> asm_rewrite_tac [] >> strip_tac >>
  drule_all pok_some >> strip_tac >>
  ‘(EL i (PS lfd b hw lv W0 m).pc).fo ∧ (EL i (PS lfd b hw lv W0 m).pc).bo ∧
   ¬(EL i (PS lfd b hw lv W0 m).pc).bup’ by simp[] >>
  asm_rewrite_tac [] >> strip_tac >>
  drule pinv_all >> disch_then (qspecl_then [‘lv’, ‘hw’, ‘b’, ‘m’] assume_tac) >>
  qpat_x_assum ‘pinv _ _ _ _ _ _’ (strip_assume_tac o SIMP_RULE (srw_ss()) [pinv_def, LET_THM]) >>
  ‘MEM (ERead c pread) (MAP SND (pacts lfd b hw st' (prdy (PH lfd b hw lv W0 m))))’
    by (irule pacts_reads_back >> asm_rewrite_tac [] >> qexists_tac ‘i’ >> asm_rewrite_tac []) >>
  metis_tac[]
QED

(* A round that does not read c (a slot's open backend) keeps c's fd; if
   c's channel is Refused after the poll, c is ready *)
Theorem proxy_quiet_round:
  proxy_world lfd a W0 ∧ i < LENGTH (PS lfd b hw lv W0 m).pc ∧
  (EL i (PS lfd b hw lv W0 m).pc).bh = SOME c ∧ (EL i (PS lfd b hw lv W0 m).pc).bo ∧
  (∀k. ¬MEM (ERead c k) (MAP SND (PS lfd b hw lv W0 m).last)) ⇒
  ∃f. ALOOKUP (SND (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 m)).tbl c = SOME f ∧
      ALOOKUP (SND (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 (SUC m))).tbl c = SOME f ∧
      ∀j. ep_chan_of (FST (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 (SUC m))) f = SOME j ∧
          (EL j (FST (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 (SUC m))).chans).status =
            Refused ⇒
          c ∈ prdy (PH lfd b hw lv W0 (SUC m))
Proof
  strip_tac >>
  drule PS_prel_n >> disch_then (qspecl_then [‘m’, ‘lv’, ‘hw’, ‘b’] assume_tac) >>
  ‘∃j. hch (FST (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 m))
          (SND (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 m)) c j’
    by (drule_all prel_pok >> rewrite_tac [pok_def] >> strip_tac >>
        qpat_x_assum ‘option_CASE _ _ _’ mp_tac >> asm_rewrite_tac [] >> simp[] >>
        rpt strip_tac >> qexists_tac ‘j’ >> first_assum ACCEPT_TAC) >>
  ‘MEM c (FLAT (MAP phds (PS lfd b hw lv W0 m).pc))’
    by (simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> qexists_tac ‘EL i (PS lfd b hw lv W0 m).pc’ >>
        simp[EL_MEM, phds_def]) >>
  drule_all prel_cfix >> strip_tac >>
  ‘MEM c (pifds lfd b hw (PH lfd b hw lv W0 m))’
    by (simp[pifds_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >> disj2_tac >>
        qexists_tac ‘EL i (PS lfd b hw lv W0 m).pc’ >> asm_simp_tac (srw_ss()) [EL_MEM, popen_def]) >>
  drule PS_round >> disch_then (qspecl_then [‘m’, ‘lv’, ‘hw’, ‘b’] strip_assume_tac) >>
  qpat_x_assum ‘ehacts _ _ _ _ _ _ = _’ mp_tac >>
  qmatch_goalsub_abbrev_tac ‘ehacts lfd lv m 0 ws acts’ >> PairCases_on ‘ws’ >> strip_tac >>
  RULE_ASSUM_TAC (REWRITE_RULE [pairTheory.FST, pairTheory.SND]) >>
  drule_at (Pos (el 2)) ehacts_cfix >> disch_then drule >>
  impl_tac >- (qunabbrev_tac ‘acts’ >> first_assum ACCEPT_TAC) >> strip_tac >>
  qexists_tac ‘f’ >>
  ‘ALOOKUP ws1.tbl c = SOME f ∧ ALOOKUP hs1.tbl c = SOME f’
    by (qpat_x_assum ‘cfix _ _ _ _ ws0 ws1’ mp_tac >> qpat_x_assum ‘cfix _ _ _ _ w1 hs1’ mp_tac >>
        simp[cfix_def]) >>
  qpat_x_assum ‘ehpoll _ _ _ _ = _’ mp_tac >>
  Cases_on ‘ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 (SUC m)’ >>
  simp[ehpoll_def] >> strip_tac >>
  qpat_x_assum ‘PH _ _ _ _ _ (SUC m) = _’ SUBST1_TAC >>
  rpt VAR_EQ_TAC >> asm_simp_tac (srw_ss()) [] >> rpt strip_tac >>
  simp[prdy_def, asyncM3WorldTheory.ssnap_def, MEM_FILTER] >>
  asm_simp_tac (srw_ss()) [ep_readable_def]
QED

(* An open backend's channel is Up, Refused or Connecting *)
Theorem quiet_status:
  proxy_world lfd a W0 ∧ i < LENGTH (PS lfd b hw lv W0 m).pc ∧
  (EL i (PS lfd b hw lv W0 m).pc).bh = SOME c ∧ (EL i (PS lfd b hw lv W0 m).pc).bo ∧
  ALOOKUP (SND (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 m)).tbl c = SOME f ⇒
  chan_status (FST (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 m)) f = SOME Up ∨
  chan_status (FST (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 m)) f = SOME Refused ∨
  chan_status (FST (ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 m)) f = SOME Connecting
Proof
  strip_tac >> drule_all PS_pok >> strip_tac >> drule_all pok_some >> strip_tac >>
  first_x_assum drule >> rewrite_tac [hch_def] >> strip_tac >>
  gvs[chan_status_def, ep_chan_of_def]
QED

(* MAIN of this part: a backend that is never read comes up *)
Theorem proxy_back_live:
  proxy_world lfd a W0 ∧ conn_fair lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 ∧
  i < LENGTH (PS lfd b hw lv W0 n0).pc ∧ (EL i (PS lfd b hw lv W0 n0).pc).bh = SOME c ∧
  (∀m k. ¬MEM (ERead c k) (MAP SND (PS lfd b hw lv W0 m).last)) ⇒
  ∃m. up_at lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 m c
Proof
  strip_tac >> CCONTR_TAC >> fs[] >>
  ‘∀m. n0 ≤ m ⇒
       i < LENGTH (PS lfd b hw lv W0 m).pc ∧ (EL i (PS lfd b hw lv W0 m).pc).bh = SOME c ∧
       (EL i (PS lfd b hw lv W0 m).pc).fo ∧ (EL i (PS lfd b hw lv W0 m).pc).bo ∧
       ¬(EL i (PS lfd b hw lv W0 m).pc).bup ∧ c ∉ prdy (PH lfd b hw lv W0 m)’
    by (rpt gen_tac >> strip_tac >> irule proxy_quiet_back >> simp[] >> metis_tac[]) >>
  qabbrev_tac ‘SW = ehst lfd lv (pifds lfd b hw) (pprog lfd b hw) W0’ >>
  ‘∀m. n0 ≤ m ⇒
       ∃f. ALOOKUP (SND (SW m)).tbl c = SOME f ∧ ALOOKUP (SND (SW (SUC m))).tbl c = SOME f ∧
           ∀j. ep_chan_of (FST (SW (SUC m))) f = SOME j ∧
               (EL j (FST (SW (SUC m))).chans).status = Refused ⇒
               c ∈ prdy (PH lfd b hw lv W0 (SUC m))’
    by (rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
        qunabbrev_tac ‘SW’ >> irule proxy_quiet_round >> simp[] >> metis_tac[]) >>
  ‘∃f0. ALOOKUP (SND (SW n0)).tbl c = SOME f0’ by metis_tac[LESS_EQ_REFL] >>
  ‘∀d. ALOOKUP (SND (SW (n0 + d))).tbl c = SOME f0’
    by (Induct >> simp[] >>
        first_x_assum (qspec_then ‘n0 + d’ mp_tac) >> simp[] >> strip_tac >>
        ‘n0 + SUC d = SUC (n0 + d)’ by simp[] >> pop_assum SUBST1_TAC >> gvs[]) >>
  ‘∀m. SUC n0 ≤ m ⇒ chan_status (FST (SW m)) f0 = SOME Connecting’
    by (rpt strip_tac >>
        ‘ALOOKUP (SND (SW m)).tbl c = SOME f0’
          by (first_x_assum (qspec_then ‘m − n0’ mp_tac) >> simp[]) >>
        qpat_assum ‘∀m. n0 ≤ m ⇒ i < _ ∧ _’ (qspec_then ‘m’ mp_tac) >> impl_tac >- simp[] >> strip_tac >>
        qspecl_then [‘m’, ‘f0’] mp_tac (Q.GENL [‘m’, ‘f’] quiet_status) >>
        impl_tac >- (qunabbrev_tac ‘SW’ >> asm_rewrite_tac [] >> qexists_tac ‘a’ >> fs[]) >>
        qunabbrev_tac ‘SW’ >> strip_tac
        >- (qpat_x_assum ‘∀m. ¬up_at _ _ _ _ _ _ _’ (qspec_then ‘m’ mp_tac) >>
            simp[up_at_def] >> qexists_tac ‘f0’ >> asm_rewrite_tac [])
        >- (‘n0 ≤ m − 1 ∧ SUC (m − 1) = m’ by simp[] >>
            qpat_x_assum ‘∀m. n0 ≤ m ⇒ ∃f. _’ (qspec_then ‘m − 1’ mp_tac) >>
            asm_rewrite_tac [] >> strip_tac >>
            ‘f = f0’ by fs[] >> pop_assum SUBST_ALL_TAC >>
            qpat_x_assum ‘chan_status _ _ = SOME Refused’ mp_tac >>
            simp[chan_status_def, CaseEq "option"] >> strip_tac >>
            first_x_assum drule >> asm_rewrite_tac [])
        >> first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘conn_fair _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [conn_fair_def]) >>
  first_x_assum (qspecl_then [‘SUC n0’, ‘c’, ‘f0’] mp_tac) >>
  impl_tac
  >- (qunabbrev_tac ‘SW’ >> conj_tac
      >- (qpat_x_assum ‘∀d. _’ (qspec_then ‘1’ mp_tac) >> simp[ADD1])
      >> qpat_x_assum ‘∀m. SUC n0 ≤ m ⇒ _’ (qspec_then ‘SUC n0’ mp_tac) >> simp[]) >>
  strip_tac >> qpat_x_assum ‘∀m. SUC n0 ≤ m ⇒ _’ (qspec_then ‘n'’ mp_tac) >>
  qunabbrev_tac ‘SW’ >> simp[]
QED

(* ------------------------------------------------------------------------
   Pairing liveness, and the claim
   ------------------------------------------------------------------------ *)

Theorem prel_acc:
  prel lfd st rdy ps w hs ⇒ (MEM hd (hl_acc_handles ps) ⇔ ∃p. MEM p st.pc ∧ p.fh = hd)
Proof
  rw[prel_def]
QED

(* MAIN: every accepted front gets a backend that comes up or is refused,
   unless connects return no socket without bound *)
Theorem proxy_pair_live:
  proxy_world lfd a W0 ∧ conn_fair lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 ⇒
  ∀n hd. MEM hd (hl_acc_handles (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n))) ⇒
         (∃n' c. ppair lfd b hw lv W0 hd = SOME c ∧
                 (ever_up lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n' c ∨
                  hl_refused c (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n')))) ∨
         ∀k. ∃n'. k ≤ hl_nosock (hl_pairs (pprog lfd b hw) (PH lfd b hw lv W0 n'))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule PS_prel_n >> disch_then (qspecl_then [‘n’, ‘lv’, ‘hw’, ‘b’] assume_tac) >>
  ‘∃p. MEM p (PS lfd b hw lv W0 n).pc ∧ p.fh = hd’
    by (drule prel_acc >> disch_then (fn th => fs[GSYM th])) >>
  qpat_x_assum ‘MEM p _’ (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  rename1 ‘i < LENGTH (PS lfd b hw lv W0 n).pc’ >>
  ‘∀m. n ≤ m ⇒ i < LENGTH (PS lfd b hw lv W0 m).pc’
    by (rpt strip_tac >> irule (cj 1 pkeep_EL) >>
        qexists_tac ‘(PS lfd b hw lv W0 n).pc’ >> simp[] >>
        irule pc_mono >> simp[] >> metis_tac[]) >>
  Cases_on ‘∃m c. n ≤ m ∧ (EL i (PS lfd b hw lv W0 m).pc).bh = SOME c’
  >- (disj1_tac >> fs[] >>
      ‘i < LENGTH (PS lfd b hw lv W0 m).pc’ by simp[] >>
      ‘ppair lfd b hw lv W0 hd = SOME c’
        by (drule ppair_SOME >> disch_then (fn th => REWRITE_TAC [th]) >>
            qexistsl_tac [‘m’, ‘i’] >> simp[] >>
            mp_tac (Q.INST [‘n'’ |-> ‘m’] PS_slot_const) >> gvs[]) >>
      Cases_on ‘∃m' k. MEM (ERead c k) (MAP SND (PS lfd b hw lv W0 m').last)’
      >- (fs[] >> drule_all read_c_slot >> strip_tac >>
          drule_all proxy_read_back_settled >> strip_tac
          >- (qexists_tac ‘m'’ >> disj1_tac >> simp[ever_up_def] >> qexists_tac ‘m'’ >> simp[])
          >> qexists_tac ‘SUC m'’ >> disj2_tac >> first_assum ACCEPT_TAC) >>
      fs[] >> drule_all proxy_back_live >> strip_tac >>
      rename1 ‘up_at _ _ _ _ _ m1 c’ >>
      qexists_tac ‘m1’ >> disj1_tac >> simp[ever_up_def] >> qexists_tac ‘m1’ >> simp[]) >>
  disj2_tac >> irule proxy_connect_forever >>
  conj_tac >- (qexistsl_tac [‘i’, ‘n’] >> asm_rewrite_tac [] >> rpt strip_tac >>
                Cases_on ‘(EL i (PS lfd b hw lv W0 m).pc).bh’ >> fs[] >> metis_tac[]) >>
  qexists_tac ‘a’ >> first_assum ACCEPT_TAC
QED

(* The proxy meets its handle-layer guarantee *)
Theorem proxy_hl_claim_holds:
  proxy_hl_claim pprog pifds
Proof
  rw[proxy_hl_claim_def] >> irule proxy_guar_hl_of_live >> metis_tac[proxy_pair_live]
QED
