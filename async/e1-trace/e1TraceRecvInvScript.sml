(*
  The shared E1 trace layer (m4-server): the READ twin of e1TraceChan's
  gchinv.  On the endpoint handle layer, generic in the program, what a
  channel received is what the program read on the handle bound to it,
  then what is still in its inbox (an unbound channel has read nothing);
  a handle bound to no channel has read nothing.

  So what the program read on handle hd is a prefix of what its channel
  received (rinv_read_prefix), which e1TraceRead's G2 equates with what
  the episode received on the raw L0 trace.
*)
Theory e1TraceRecvInv
Ancestors
  e1TraceChan moonshotClient moonshotClientSpec endpointHLModel endpointWorld asyncHLModel alist
Libs
  preamble

Definition rinv_def:
  rinv B ps (w : eworld) ⇔
    (∀j. j < LENGTH w.chans ⇒
         (case ALOOKUP B j of SOME hd => hl_read hd ps | NONE => []) ++ (EL j w.chans).inbox =
         (EL j w.chans).recv) ∧
    (∀hd. ¬MEM hd (MAP SND B) ⇒ hl_read hd ps = [])
End

Theorem rinv_read_prefix:
  rinv B ps w ∧ j < LENGTH w.chans ∧ ALOOKUP B j = SOME hd ⇒
  hl_read hd ps ≼ (EL j w.chans).recv
Proof
  rw[rinv_def] >> first_x_assum drule >> simp[] >> disch_then (SUBST1_TAC o GSYM) >>
  simp[]
QED

(* ------------------------------------------------------------------------
   The frame
   ------------------------------------------------------------------------ *)

Theorem rinv_frame:
  rinv B ps w ∧ LENGTH w'.chans = LENGTH w.chans ∧
  (∀j. j < LENGTH w.chans ⇒
       (EL j w'.chans).recv = (EL j w.chans).recv ∧ (EL j w'.chans).inbox = (EL j w.chans).inbox) ∧
  (∀hd. hl_read hd ps' = hl_read hd ps) ⇒
  rinv B ps' w'
Proof
  simp[rinv_def] >> strip_tac >> simp[]
QED

(* What leaves recv and inbox alone *)
Definition rkeeps_def:
  rkeeps (w : eworld) w1 ⇔
    LENGTH w1.chans = LENGTH w.chans ∧
    ∀j. j < LENGTH w.chans ⇒
        (EL j w1.chans).recv = (EL j w.chans).recv ∧ (EL j w1.chans).inbox = (EL j w.chans).inbox
End

Theorem rkeeps_trans:
  rkeeps w w1 ∧ rkeeps w1 w2 ⇒ rkeeps w w2
Proof
  rw[rkeeps_def]
QED

Theorem rkeeps_refl[simp]:
  rkeeps w w
Proof
  rw[rkeeps_def]
QED

Theorem rinv_frame_keeps:
  rinv B ps w ∧ rkeeps w w' ∧ (∀hd. hl_read hd ps' = hl_read hd ps) ⇒ rinv B ps' w'
Proof
  rw[rkeeps_def] >> irule rinv_frame >> qpat_assum ‘rinv _ _ _’ (irule_at Any) >> simp[]
QED

Theorem ep_conn_err_rkeeps:
  ep_conn_err f w = SOME w1 ⇒ rkeeps w w1
Proof
  rw[ep_conn_err_def, AllCaseEqs()] >> gvs[ep_chan_of_def, AllCaseEqs()] >>
  rw[rkeeps_def] >> rw[]
QED

Theorem ep_close_rkeeps:
  ep_close f w = SOME w1 ⇒ rkeeps w w1
Proof
  rw[ep_close_def, AllCaseEqs()] >> gvs[ep_chan_of_def, AllCaseEqs()] >>
  rw[rkeeps_def] >> rw[upd_chan_def, EL_LUPDATE] >> rw[]
QED

Theorem ep_send_rkeeps:
  ep_send f bs w = SOME (k, w1) ⇒ rkeeps w w1
Proof
  rw[ep_send_def, AllCaseEqs()] >> gvs[ep_chan_of_def, AllCaseEqs()] >>
  rw[rkeeps_def] >> rw[]
QED

(* ------------------------------------------------------------------------
   Each action
   ------------------------------------------------------------------------ *)

Theorem ehdo_read_rinv:
  ehdo lfd v (w, hs) (ERead h n) = SOME (r, (w', hs')) ∧ gchinv lfd B ps (w, hs) ∧
  rinv B ps w ⇒
  rinv B (ps ++ [(ERead h n, r)]) w'
Proof
  strip_tac >> qpat_x_assum ‘ehdo _ _ _ _ = _’ mp_tac >> simp[ehdo_def] >>
  strip_tac >> qpat_x_assum ‘_ = SOME _’ mp_tac >>
  Cases_on ‘ALOOKUP hs.tbl h’ >> simp[]
  >- (strip_tac >> gvs[] >> irule rinv_frame_keeps >> qpat_assum ‘rinv _ _ _’ (irule_at Any) >> simp[] >>
      rw[hl_read_def]) >>
  rename1 ‘ALOOKUP hs.tbl h = SOME f’ >>
  Cases_on ‘ep_conn_err f w’ >> simp[]
  >~ [‘ep_conn_err f w = SOME w1’]
  >- (strip_tac >> gvs[] >> drule ep_conn_err_rkeeps >> drule ep_close_rkeeps >>
      rpt strip_tac >> irule rinv_frame_keeps >> qpat_assum ‘rinv _ _ _’ (irule_at Any) >>
      simp[] >> irule rkeeps_trans >> qexists_tac ‘w1’ >> simp[]) >>
  Cases_on ‘ep_read f n w’ >> simp[] >> rename1 ‘ep_read f n w = SOME x’ >>
  PairCases_on ‘x’ >> rename1 ‘ep_read f n w = SOME (ro, w1)’ >>
  ‘ro = NONE ∨ ro = SOME [] ⇒ w1 = w’
    by (strip_tac >> gvs[ep_read_def, AllCaseEqs()] >> Cases_on ‘n’ >> gvs[] >>
        Cases_on ‘(EL j w.chans).inbox’ >> gvs[]) >>
  Cases_on ‘ro = NONE’
  >- (gvs[] >> strip_tac >> gvs[] >>
      irule rinv_frame_keeps >> qpat_assum ‘rinv _ _ _’ (irule_at Any) >> simp[]) >>
  Cases_on ‘ro = SOME []’
  >- (gvs[] >> strip_tac >> gvs[] >> drule ep_close_rkeeps >> strip_tac >>
      irule rinv_frame_keeps >> qpat_assum ‘rinv _ _ _’ (irule_at Any) >> simp[]) >>
  ‘∃b bs. ro = SOME (b::bs)’ by (Cases_on ‘ro’ >> gvs[] >> rename1 ‘ep_read _ _ _ = SOME (SOME l, _)’ >> Cases_on ‘l’ >> gvs[]) >>
  gvs[] >> strip_tac >> gvs[] >>
  (* a read that got r *)
  drule_all tbl_chan >> strip_tac >> rename1 ‘ep_chan_of w f = SOME c0’ >>
  ‘ALL_DISTINCT (MAP SND B)’ by fs[gchinv_def] >>
  qpat_x_assum ‘ep_read _ _ _ = _’ mp_tac >> simp[ep_read_def] >>
  Cases_on ‘(EL c0 w.chans).inbox = []’ >> simp[] >- (rw[] >> gvs[]) >> strip_tac >> gvs[] >>
  qpat_x_assum ‘rinv _ _ _’ mp_tac >> rewrite_tac[rinv_def] >> strip_tac >> conj_tac
  >- (qx_gen_tac ‘i’ >> strip_tac >> simp[upd_chan_def, EL_LUPDATE] >>
      qpat_x_assum ‘∀j. j < LENGTH w.chans ⇒ _’ (qspec_then ‘i’ mp_tac) >> simp[] >>
      Cases_on ‘i = c0’
      >- (gvs[] >> disch_then (SUBST1_TAC o GSYM) >>
          ‘(EL c0 w.chans).inbox = TAKE n (EL c0 w.chans).inbox ++ DROP n (EL c0 w.chans).inbox’
            by simp[TAKE_DROP] >>
          pop_assum (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th]))) >> simp[]) >>
      ‘i < LENGTH w.chans’ by fs[] >>
      simp[] >> disch_then (SUBST1_TAC o GSYM) >> CASE_TAC >> simp[] >>
      rename1 ‘ALOOKUP B i = SOME hd’ >>
      ‘hd ≠ h’ suffices_by simp[] >> strip_tac >> gvs[] >>
      ‘MEM (i, h) B’ by (irule ALOOKUP_MEM >> simp[]) >>
      metis_tac[bind_inj]) >>
  rpt strip_tac >> ‘hd ≠ h’ by (strip_tac >> gvs[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  simp[]
QED

Theorem ehdo_write_rinv:
  ehdo lfd v (w, hs) (EWrite h bs) = SOME (r, (w', hs')) ∧ rinv B ps w ⇒
  rinv B (ps ++ [(EWrite h bs, r)]) w'
Proof
  strip_tac >> qpat_x_assum ‘ehdo _ _ _ _ = _’ mp_tac >> simp[ehdo_def] >>
  Cases_on ‘ALOOKUP hs.tbl h’ >> simp[]
  >- (strip_tac >> gvs[] >> irule rinv_frame_keeps >> qpat_assum ‘rinv _ _ _’ (irule_at Any) >> simp[]) >>
  rw[] >> pairarg_tac >> gvs[] >> drule ep_send_rkeeps >> strip_tac >>
  irule rinv_frame_keeps >> qpat_assum ‘rinv _ _ _’ (irule_at Any) >> simp[]
QED

(* Binding an unbound channel j to the next handle *)
Theorem rinv_bind:
  rinv B ps w ∧ gchinv lfd B ps (w, hs) ∧ hdln (w2n lfd) hs.nxt < dimword (:64) ∧
  LENGTH w.chans ≤ LENGTH w'.chans ∧ j < LENGTH w'.chans ∧ ¬MEM j (MAP FST B) ∧
  (∀i. i < LENGTH w'.chans ⇒
       if i < LENGTH w.chans then
         (EL i w'.chans).recv = (EL i w.chans).recv ∧ (EL i w'.chans).inbox = (EL i w.chans).inbox
       else (EL i w'.chans).recv = [] ∧ (EL i w'.chans).inbox = []) ∧
  (∀hd. hl_read hd ps' = hl_read hd ps) ⇒
  rinv (B ++ [(j, hdl lfd hs.nxt)]) ps' w'
Proof
  strip_tac >>
  ‘hs.nxt + 1 < dimword (:64)’ by (irule hdln_suc_lt >> metis_tac[]) >>
  drule_all gchinv_next_unbound >> strip_tac >>
  ‘ALOOKUP B j = NONE’ by simp[ALOOKUP_NONE] >>
  ‘∀j hd. MEM (j, hd) B ⇒ j < LENGTH w.chans’
    by (rpt strip_tac >> qpat_assum ‘gchinv _ _ _ _’ (mp_tac o REWRITE_RULE [gchinv_def]) >>
        strip_tac >> qpat_x_assum ‘∀j hd. MEM (j, hd) B ⇒ _’ drule >> simp[]) >>
  qpat_x_assum ‘rinv _ _ _’ mp_tac >> rewrite_tac[rinv_def] >> strip_tac >>
  ‘hl_read (hdl lfd hs.nxt) ps' = []’ by simp[] >>
  conj_tac
  >- (rpt strip_tac >> rename1 ‘i < LENGTH w'.chans’ >> simp[ALOOKUP_APPEND] >>
      qpat_x_assum ‘∀i. i < LENGTH w'.chans ⇒ _’ (qspec_then ‘i’ mp_tac) >> simp[] >>
      Cases_on ‘i < LENGTH w.chans’ >> simp[]
      >- (strip_tac >>
          qpat_x_assum ‘∀j. j < LENGTH w.chans ⇒ _’ (qspec_then ‘i’ mp_tac) >> simp[] >>
          Cases_on ‘ALOOKUP B i’ >> simp[] >> rw[] >> simp[]) >>
      strip_tac >>
      ‘ALOOKUP B i = NONE’
        by (simp[ALOOKUP_NONE, MEM_MAP, FORALL_PROD] >> rpt strip_tac >>
            qpat_x_assum ‘∀j hd. MEM (j, hd) B ⇒ j < LENGTH w.chans’ drule >> simp[]) >>
      simp[] >> rw[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem ehdo_connect_rinv:
  ehdo lfd v (w, hs) (EConnect a) = SOME (r, (w', hs')) ∧ gchinv lfd B ps (w, hs) ∧
  rinv B ps w ⇒
  rinv (B ++ ebind w (EConnect a) r) (ps ++ [(EConnect a, r)]) w'
Proof
  strip_tac >>
  ‘∀hd. hl_read hd (ps ++ [(EConnect a, r)]) = hl_read hd ps’ by (Cases_on ‘r’ >> simp[]) >>
  qpat_x_assum ‘ehdo _ _ _ _ = _’ mp_tac >> simp[ehdo_def] >>
  Cases_on ‘ep_connect a w’ >> rename1 ‘ep_connect a w = (fo, w1)’ >>
  Cases_on ‘fo’ >> simp[]
  >- (strip_tac >> gvs[ebind_def] >>
      qpat_x_assum ‘ep_connect _ _ = _’ mp_tac >>
      simp[ep_connect_def, ep_alloc_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
      irule rinv_frame_keeps >> qpat_assum ‘rinv _ _ _’ (irule_at Any) >>
      simp[rkeeps_def, hl_read_def]) >>
  rename1 ‘ep_connect a w = (SOME f, w1)’ >> strip_tac >> gvs[ebind_def] >>
  qpat_x_assum ‘ep_connect _ _ = _’ mp_tac >>
  simp[ep_connect_def, ep_alloc_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  irule rinv_bind >> qpat_assum ‘rinv _ _ _’ (irule_at Any) >> simp[hl_read_def] >>
  conj_tac
  >- (simp[MEM_MAP, FORALL_PROD] >> rpt strip_tac >>
      qpat_x_assum ‘gchinv _ _ _ _’ (strip_assume_tac o REWRITE_RULE [gchinv_def]) >>
      qpat_x_assum ‘∀j hd. MEM (j, hd) B ⇒ _’ drule >> simp[]) >>
  rpt strip_tac >> IF_CASES_TAC >> simp[EL_APPEND1] >> ‘i = LENGTH w.chans’ by decide_tac >>
  simp[EL_APPEND2, new_chan_def]
QED

Theorem ehdo_accept_rinv:
  ehdo lfd v (w, hs) (EAccept l) = SOME (r, (w', hs')) ∧ gchinv lfd B ps (w, hs) ∧
  rinv B ps w ⇒
  rinv (B ++ ebind w (EAccept l) r) (ps ++ [(EAccept l, r)]) w'
Proof
  strip_tac >>
  ‘∀hd. hl_read hd (ps ++ [(EAccept l, r)]) = hl_read hd ps’ by (Cases_on ‘r’ >> simp[]) >>
  qpat_x_assum ‘ehdo _ _ _ _ = _’ mp_tac >> simp[ehdo_def, ep_accept_def] >>
  qpat_assum ‘gchinv _ _ _ _’ (strip_assume_tac o REWRITE_RULE [gchinv_def]) >>
  Cases_on ‘w.listening’ >> simp[] >>
  rename1 ‘w.listening = x :: xs’ >> PairCases_on ‘x’ >>
  ‘xs = []’ by (Cases_on ‘xs’ >> gvs[]) >>
  rw[] >> gvs[AllCaseEqs(), ebind_def] >>
  TRY (irule rinv_frame_keeps >> qpat_assum ‘rinv _ _ _’ (irule_at Any) >> simp[] >> NO_TAC) >>
  gvs[ep_alloc_def] >>
  irule rinv_bind >> qpat_assum ‘rinv _ _ _’ (irule_at Any) >> simp[hl_read_def]
QED

Theorem ehdo_rinv:
  ehdo lfd v (w, hs) x = SOME (r, (w', hs')) ∧ gchinv lfd B ps (w, hs) ∧ rinv B ps w ⇒
  rinv (B ++ ebind w x r) (ps ++ [(x, r)]) w'
Proof
  Cases_on ‘x’ >> strip_tac
  >- (drule_all ehdo_accept_rinv >> simp[])
  >- (drule_all ehdo_read_rinv >> simp[])
  >- (drule_all ehdo_write_rinv >> simp[])
  >- (drule_all ehdo_connect_rinv >> simp[])
  >> qpat_x_assum ‘ehdo _ _ _ _ = _’ mp_tac >> simp[ehdo_def] >> strip_tac >> gvs[] >>
  irule rinv_frame_keeps >> qpat_assum ‘rinv _ _ _’ (irule_at Any) >> simp[]
QED

Theorem ehacts_rinv:
  ∀acts k (st : eworld # ehstate) rs st' B ps.
    ehacts lfd lv n k st acts = SOME (rs, st') ∧ gchinv lfd B ps st ∧ rinv B ps (FST st) ⇒
    rinv (B ++ ehbacts lfd lv n k st acts) (ps ++ ZIP (acts, rs)) (FST st')
Proof
  Induct >> simp[ehacts_def, ehbacts_def] >> rpt gen_tac >>
  PairCases_on ‘st’ >> simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  PairCases_on ‘st1'’ >>
  drule_all ehdo_gchinv >> strip_tac >>
  drule_all ehdo_rinv >> strip_tac >>
  ‘ps ++ (h,r)::ZIP (acts,rs') = (ps ++ [(h,r)]) ++ ZIP (acts,rs')’ by simp[] >>
  pop_assum SUBST1_TAC >> REWRITE_TAC[APPEND_ASSOC] >>
  first_x_assum irule >> simp[]
QED

(* ------------------------------------------------------------------------
   The poll
   ------------------------------------------------------------------------ *)

Theorem ep_deliver_rinv:
  gchinv lfd B ps (w, hs) ∧ rinv B ps w ⇒ rinv B ps (ep_deliver w e)
Proof
  strip_tac >> Cases_on ‘e’ >> simp[ep_deliver_def] >>
  TRY (rw[] >> irule rinv_frame_keeps >> qpat_assum ‘rinv _ _ _’ (irule_at Any) >> simp[rkeeps_def] >> rw[] >> NO_TAC)
  >- (qpat_assum ‘gchinv _ _ _ _’ (strip_assume_tac o REWRITE_RULE [gchinv_def]) >>
      Cases_on ‘w.listening’ >> simp[] >>
      rename1 ‘w.listening = x :: xs’ >> PairCases_on ‘x’ >>
      ‘xs = []’ by (Cases_on ‘xs’ >> gvs[]) >>
      rw[] >> gvs[AFUPDKEY_def] >>
      qpat_x_assum ‘rinv _ _ _’ mp_tac >> rewrite_tac[rinv_def] >> strip_tac >> simp[] >>
      rpt strip_tac >> Cases_on ‘j < LENGTH w.chans’ >> simp[EL_APPEND1] >>
      ‘j = LENGTH w.chans’ by decide_tac >>
      ‘ALOOKUP B j = NONE’
        by (simp[ALOOKUP_NONE, MEM_MAP, FORALL_PROD] >> rpt strip_tac >>
            qpat_x_assum ‘∀j hd. MEM (j, hd) B ⇒ _’ drule >> simp[]) >>
      simp[EL_APPEND2, new_chan_def]) >>
  (* PData *)
  rw[] >> qpat_x_assum ‘rinv _ _ _’ mp_tac >> rewrite_tac[rinv_def] >> strip_tac >> simp[] >>
  rpt strip_tac >> rename1 ‘i < LENGTH _’ >> simp[upd_chan_def, EL_LUPDATE] >>
  qpat_x_assum ‘∀j. j < LENGTH w.chans ⇒ _’ (qspec_then ‘i’ mp_tac) >> simp[] >>
  rw[] >> simp[]
QED

Theorem FOLDL_deliver_rinv:
  ∀es w. gchinv lfd B ps (w, hs) ∧ rinv B ps w ⇒ rinv B ps (FOLDL ep_deliver w es)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >> conj_tac
  >- (irule ep_deliver_rinv >> simp[] >> qexistsl_tac [‘hs’, ‘lfd’] >> simp[])
  >> irule ep_deliver_gchinv >> simp[]
QED

Theorem gchinv_clock:
  gchinv lfd B ps (w with clock := c, hs) ⇔ gchinv lfd B ps (w, hs)
Proof
  rewrite_tac[gchinv_def] >> simp[]
QED

Theorem ep_tick_rinv:
  gchinv lfd B ps (w, hs) ∧ rinv B ps w ⇒ rinv B ps (ep_tick w)
Proof
  simp[ep_tick_def] >> strip_tac >> irule FOLDL_deliver_rinv >> conj_tac
  >- (irule rinv_frame_keeps >> qpat_assum ‘rinv _ _ _’ (irule_at Any) >> simp[rkeeps_def])
  >> qexistsl_tac [‘hs’, ‘lfd’] >> simp[gchinv_clock]
QED

Theorem ehpoll_rinv:
  ehpoll lfd hs hfds w = (rdy, w', hs') ∧ gchinv lfd B ps (w, hs) ∧ rinv B ps w ⇒
  rinv B ps w'
Proof
  simp[ehpoll_def] >> strip_tac >> gvs[] >> irule ep_tick_rinv >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The run
   ------------------------------------------------------------------------ *)

Theorem ehrounds_rinv:
  W0.chans = [] ∧ W0.open_fds = [] ∧ alloc_ok W0.alloc ∧ LENGTH W0.listening ≤ 1 ∧
  EVERY (λ(l, a, q). q = []) W0.listening ∧
  (∀n. ehacts lfd lv n 0 (ehst lfd lv ifds m W0 n)
         (new_actions (log_of m) (ehhist lfd lv ifds m W0 n)) ≠ NONE) ⇒
  ∀n. rinv (ehbinds lfd lv ifds m W0 n) (hl_pairs m (ehhist lfd lv ifds m W0 n))
           (FST (ehst lfd lv ifds m W0 n))
Proof
  strip_tac >> drule_all ehrounds_gchinv >> strip_tac >> Induct
  >- simp[ehst_def, ehhist_def, ehrounds_def, ehbinds_def, rinv_def, hl_pairs_def] >>
  first_x_assum (qspec_then ‘n’ mp_tac) >>
  qpat_x_assum ‘∀n. ehacts _ _ _ _ _ _ ≠ NONE’ (qspec_then ‘n’ mp_tac) >>
  pop_assum mp_tac >>
  simp[ehbinds_def] >> simp[ehst_def, ehhist_def, ehrounds_def] >>
  Cases_on ‘ehrounds lfd lv ifds m W0 n’ >> rename1 ‘(h, st)’ >> PairCases_on ‘st’ >>
  simp[ehacts_tot_def] >> rpt strip_tac >>
  Cases_on ‘ehacts lfd lv n 0 (st0, st1) (new_actions (log_of m) h)’ >> gvs[] >>
  rename1 ‘SOME x’ >> PairCases_on ‘x’ >> gvs[] >>
  Cases_on ‘ehpoll lfd x2 (ifds h) x1’ >> rename1 ‘ehpoll _ _ _ _ = (rdy, ws)’ >>
  PairCases_on ‘ws’ >> gvs[] >>
  simp[hl_pairs_SNOC, asyncM3WorldTheory.ssnap_def] >>
  drule_all ehacts_gchinv >> strip_tac >>
  drule ehacts_rinv >>
  disch_then (qspecl_then [‘ehbinds lfd lv ifds m W0 n’, ‘hl_pairs m h’] mp_tac) >>
  simp[] >> strip_tac >>
  drule_all ehpoll_rinv >> simp[]
QED

(* What the program read on a handle is a prefix of what its channel
   received, at every round *)
Theorem ehrounds_read_prefix:
  W0.chans = [] ∧ W0.open_fds = [] ∧ alloc_ok W0.alloc ∧ LENGTH W0.listening ≤ 1 ∧
  EVERY (λ(l, a, q). q = []) W0.listening ∧
  (∀n. ehacts lfd lv n 0 (ehst lfd lv ifds m W0 n)
         (new_actions (log_of m) (ehhist lfd lv ifds m W0 n)) ≠ NONE) ∧
  ALOOKUP (ehbinds lfd lv ifds m W0 n) j = SOME hd ⇒
  j < LENGTH (FST (ehst lfd lv ifds m W0 n)).chans ∧
  hl_read hd (hl_pairs m (ehhist lfd lv ifds m W0 n)) ≼
  (EL j (FST (ehst lfd lv ifds m W0 n)).chans).recv
Proof
  strip_tac >>
  drule_all ehrounds_gchinv >> disch_then (qspec_then ‘n’ assume_tac) >>
  drule_all ehrounds_rinv >> disch_then (qspec_then ‘n’ assume_tac) >>
  Cases_on ‘ehst lfd lv ifds m W0 n’ >> fs[] >>
  ‘j < LENGTH q.chans’
    by (imp_res_tac ALOOKUP_MEM >> fs[gchinv_def] >> res_tac) >>
  simp[] >> irule rinv_read_prefix >> metis_tac[]
QED
