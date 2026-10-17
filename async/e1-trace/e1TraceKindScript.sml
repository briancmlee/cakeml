(*
  The shared E1 trace layer (m4-server): handle KINDS on the endpoint
  handle layer, generic in the program.  A handle bound to channel j was
  returned by a connect exactly when channel j has a peer address (cpa),
  and by an accept exactly when it has none; every channel with a peer
  address is bound; listening queues hold channels without one.

  With e1TraceRole.e1_roles (channel j has a peer address iff raw episode j
  came from a sys_connect) this ties the program's connect / accept
  handles to the raw trace's connect / accept episodes.
*)
Theory e1TraceKind
Ancestors
  e1TraceRole e1TraceRecvInv e1TraceChan honestL1EPRefine moonshotClientSpec endpointHLModel endpointWorld alist asyncHLModel moonshotClient
Libs
  preamble

(* The handles accepted, in order (proxyHLStmts.hl_acc_handles) *)
Definition acc_hdls_def:
  acc_hdls ps =
    FLAT (MAP (λ(x, r). case (x, r) of
                        | (EAccept l, EAccepted (SOME hd)) => [hd]
                        | _ => []) ps)
End

Theorem acc_hdls_APPEND[simp]:
  acc_hdls (l1 ++ l2) = acc_hdls l1 ++ acc_hdls l2
Proof
  simp[acc_hdls_def]
QED

Theorem conn_handles_APPEND[simp]:
  hl_conn_handles (l1 ++ l2) = hl_conn_handles l1 ++ hl_conn_handles l2
Proof
  simp[hl_conn_handles_def, hl_connects_def]
QED

Definition kinv_def:
  kinv B ps (w : eworld) ⇔
    (∀j hd. MEM (j, hd) B ⇒
            (MEM hd (hl_conn_handles ps) ⇔ cpa (EL j w.chans)) ∧
            (MEM hd (acc_hdls ps) ⇔ ¬cpa (EL j w.chans))) ∧
    (∀hd. MEM hd (hl_conn_handles ps) ∨ MEM hd (acc_hdls ps) ⇒ MEM hd (MAP SND B)) ∧
    (∀j. j < LENGTH w.chans ∧ cpa (EL j w.chans) ⇒ MEM j (MAP FST B)) ∧
    EVERY (λ(l, a, q). EVERY (λj. ¬cpa (EL j w.chans)) q) w.listening
End

Theorem cpa_el_prefix:
  MAP cpa c' = MAP cpa c ++ l ∧ j < LENGTH c ⇒ (cpa (EL j c') ⇔ cpa (EL j c))
Proof
  strip_tac >>
  ‘LENGTH c' = LENGTH c + LENGTH l’
    by (qpat_x_assum ‘MAP cpa c' = _’ (mp_tac o AP_TERM “LENGTH : bool list -> num”) >> simp[]) >>
  ‘EL j (MAP cpa c') = EL j (MAP cpa c ++ l)’ by simp[] >>
  pop_assum mp_tac >> simp[EL_MAP, EL_APPEND1]
QED

(* The frame: no new binding, no new handle, peer addresses and queues kept;
   new channels have no peer address *)
Theorem kinv_frame:
  kinv B ps w ∧ gchinv lfd B ps (w, hs) ∧
  MAP cpa w'.chans = MAP cpa w.chans ++ l ∧ EVERY (λb. ¬b) l ∧ w'.listening = w.listening ∧
  hl_conn_handles ps' = hl_conn_handles ps ∧ acc_hdls ps' = acc_hdls ps ⇒
  kinv B ps' w'
Proof
  rewrite_tac[kinv_def] >> strip_tac >>
  qpat_x_assum ‘hl_conn_handles ps' = _’ SUBST_ALL_TAC >>
  qpat_x_assum ‘acc_hdls ps' = _’ SUBST_ALL_TAC >>
  qpat_x_assum ‘w'.listening = _’ SUBST_ALL_TAC >>
  ‘LENGTH w'.chans = LENGTH w.chans + LENGTH l’
    by (qpat_x_assum ‘MAP cpa w'.chans = _’ (mp_tac o AP_TERM “LENGTH : bool list -> num”) >>
        simp[]) >>
  qpat_assum ‘gchinv _ _ _ _’ (strip_assume_tac o REWRITE_RULE [gchinv_def]) >>
  ‘∀j. j < LENGTH w.chans ⇒ (cpa (EL j w'.chans) ⇔ cpa (EL j w.chans))’
    by (rpt strip_tac >> irule cpa_el_prefix >> simp[] >> qexists_tac ‘l’ >> simp[]) >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      ‘j < LENGTH w.chans’ by (qpat_x_assum ‘∀j hd. MEM (j, hd) B ⇒ j < _ ∧ _’ drule >> simp[]) >>
      qpat_x_assum ‘∀j hd. MEM (j, hd) B ⇒ (_ ⇔ _) ∧ _’ drule >> simp[])
  >- first_assum ACCEPT_TAC
  >- (rpt strip_tac >> Cases_on ‘j < LENGTH w.chans’
      >- (qpat_x_assum ‘∀j. j < LENGTH w.chans ∧ cpa _ ⇒ _’ irule >> gvs[]) >>
      ‘EL j (MAP cpa w'.chans) = EL j (MAP cpa w.chans ++ l)’ by simp[] >>
      pop_assum mp_tac >> simp[EL_MAP, EL_APPEND2] >>
      qpat_x_assum ‘EVERY _ l’ mp_tac >> simp[EVERY_EL] >>
      disch_then (qspec_then ‘j - LENGTH w.chans’ mp_tac) >> simp[]) >>
  qpat_x_assum ‘EVERY _ w.listening’ mp_tac >>
  qpat_x_assum ‘EVERY _ w.listening’ mp_tac >>
  simp[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >> res_tac >> gvs[]
QED

(* ------------------------------------------------------------------------
   Each action
   ------------------------------------------------------------------------ *)

Theorem ehdo_listening:
  ehdo lfd v (w, hs) x = SOME (r, (w', hs')) ∧ (∀l. x ≠ EAccept l) ⇒ w'.listening = w.listening
Proof
  Cases_on ‘x’ >> simp[ehdo_def]
  >- (strip_tac >> gvs[AllCaseEqs()] >>
      gvs[ep_conn_err_def, ep_close_def, ep_read_def, upd_chan_def, AllCaseEqs()])
  >- (rw[AllCaseEqs()] >> pairarg_tac >> gvs[ep_send_def, upd_chan_def, AllCaseEqs()])
  >- (simp[ep_connect_def, ep_alloc_def, AllCaseEqs()] >> rw[] >> simp[])
  >> rw[] >> simp[]
QED

Theorem accept_hdls_one[simp]:
  hl_conn_handles [(EAccept l, EAccepted o')] = [] ∧
  acc_hdls [(EAccept l, EAccepted o')] = case o' of NONE => [] | SOME h => [h]
Proof
  Cases_on ‘o'’ >> simp[hl_conn_handles_def, hl_connects_def, acc_hdls_def]
QED

Theorem kinv_snoc_nohdl:
  hl_conn_handles ps' = [] ∧ acc_hdls ps' = [] ⇒ (kinv B (ps ++ ps') w ⇔ kinv B ps w)
Proof
  simp[kinv_def]
QED

Theorem ehdo_accept_kinv:
  ehdo lfd v (w, hs) (EAccept l) = SOME (r, (w', hs')) ∧ gchinv lfd B ps (w, hs) ∧
  kinv B ps w ⇒
  kinv (B ++ ebind w (EAccept l) r) (ps ++ [(EAccept l, r)]) w'
Proof
  strip_tac >> qpat_x_assum ‘ehdo _ _ _ _ = _’ mp_tac >> simp[ehdo_def, ep_accept_def] >>
  qpat_assum ‘gchinv _ _ _ _’ (strip_assume_tac o REWRITE_RULE [gchinv_def]) >>
  Cases_on ‘w.listening’ >> simp[] >>
  rename1 ‘w.listening = x :: xs’ >> PairCases_on ‘x’ >>
  ‘xs = []’ by (Cases_on ‘xs’ >> gvs[]) >>
  rw[] >> gvs[AllCaseEqs(), ebind_def] >>
  TRY (qpat_x_assum ‘kinv _ _ _’ mp_tac >> simp[kinv_snoc_nohdl] >> NO_TAC) >>
  (qpat_x_assum ‘ep_alloc _ _ = _’ mp_tac >> simp[ep_alloc_def] >> strip_tac >>
      qpat_x_assum ‘_ = w''’ (SUBST_ALL_TAC o SYM) >>
      ‘¬MEM (hdl lfd hs.nxt) (MAP SND B)’
        by (irule gchinv_next_unbound >> qpat_assum ‘gchinv _ _ _ _’ (irule_at Any) >>
            irule hdln_suc_lt >> qexists_tac ‘lfd’ >> simp[]) >>
      ‘¬cpa (EL j w.chans)’
        by (qpat_x_assum ‘kinv _ _ _’ mp_tac >> simp[kinv_def] >> strip_tac >>
            qpat_x_assum ‘EVERY _ w.listening’ mp_tac >> simp[]) >>
      qpat_x_assum ‘kinv _ _ _’ mp_tac >>
      simp[kinv_def, AFUPDKEY_def] >> strip_tac >>
      ‘¬MEM (hdl lfd hs.nxt) (hl_conn_handles ps) ∧ ¬MEM (hdl lfd hs.nxt) (acc_hdls ps)’
        by (conj_tac >> strip_tac >>
            qpat_x_assum ‘¬MEM (hdl _ _) (MAP SND B)’ mp_tac >> simp[] >>
            qpat_x_assum ‘∀hd. _ ∨ _ ⇒ MEM hd (MAP SND B)’ irule >> simp[]) >>
      conj_tac
      >- (rpt gen_tac >> strip_tac
          >- (‘hd ≠ hdl lfd hs.nxt’
                by (strip_tac >> qpat_x_assum ‘¬MEM (hdl _ _) (MAP SND B)’ mp_tac >>
                    simp[MEM_MAP, EXISTS_PROD] >> qexists_tac ‘j'’ >> gvs[]) >>
              qpat_x_assum ‘∀j hd. MEM (j, hd) B ⇒ (_ ⇔ _) ∧ _’ drule >> simp[]) >>
          qpat_x_assum ‘hd = _’ SUBST_ALL_TAC >> qpat_x_assum ‘j' = _’ SUBST_ALL_TAC >>
          simp[]) >>
      rpt strip_tac >> simp[] >> disj1_tac >>
      qpat_x_assum ‘∀hd. _ ∨ _ ⇒ MEM hd (MAP SND B)’ irule >> simp[])
QED

Theorem connect_hdls_one[simp]:
  hl_conn_handles [(EConnect a, EConnected o')] = (case o' of NONE => [] | SOME h => [h]) ∧
  acc_hdls [(EConnect a, EConnected o')] = []
Proof
  Cases_on ‘o'’ >> simp[hl_conn_handles_def, hl_connects_def, acc_hdls_def]
QED

Theorem ehdo_connect_kinv:
  ehdo lfd v (w, hs) (EConnect a) = SOME (EConnected (SOME h), (w', hs')) ∧
  gchinv lfd B ps (w, hs) ∧ kinv B ps w ⇒
  kinv (B ++ ebind w (EConnect a) (EConnected (SOME h))) (ps ++ [(EConnect a, EConnected (SOME h))]) w'
Proof
  strip_tac >> qpat_x_assum ‘ehdo _ _ _ _ = _’ mp_tac >> simp[ehdo_def] >>
  Cases_on ‘ep_connect a w’ >> rename1 ‘ep_connect a w = (fo, w1)’ >>
  Cases_on ‘fo’ >> simp[] >> strip_tac >>
  qpat_x_assum ‘ep_connect _ _ = _’ mp_tac >>
  simp[ep_connect_def, ep_alloc_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum ‘w1 = _’ kall_tac >>
  qpat_x_assum ‘_ = w'’ (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum ‘hdl _ _ = h’ (SUBST_ALL_TAC o SYM) >>
  ‘¬MEM (hdl lfd hs.nxt) (MAP SND B)’
    by (irule gchinv_next_unbound >> qpat_assum ‘gchinv _ _ _ _’ (irule_at Any) >>
        irule hdln_suc_lt >> qexists_tac ‘lfd’ >> simp[]) >>
  ‘¬MEM (LENGTH w.chans) (MAP FST B)’
    by (qpat_assum ‘gchinv _ _ _ _’ (strip_assume_tac o REWRITE_RULE [gchinv_def]) >>
        simp[MEM_MAP, FORALL_PROD] >> rpt strip_tac >>
        qpat_x_assum ‘∀j hd. MEM (j, hd) B ⇒ j < _ ∧ _’ drule >> simp[]) >>
  qpat_x_assum ‘kinv _ _ _’ mp_tac >>
  simp[kinv_def, ebind_def] >> strip_tac >>
  qpat_assum ‘gchinv _ _ _ _’ (strip_assume_tac o REWRITE_RULE [gchinv_def]) >>
  ‘¬MEM (hdl lfd hs.nxt) (hl_conn_handles ps) ∧ ¬MEM (hdl lfd hs.nxt) (acc_hdls ps)’
    by (conj_tac >> strip_tac >>
        qpat_x_assum ‘¬MEM (hdl _ _) (MAP SND B)’ mp_tac >> simp[] >>
        qpat_x_assum ‘∀hd. _ ∨ _ ⇒ MEM hd (MAP SND B)’ irule >> simp[]) >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac
      >- (‘j < LENGTH w.chans’ by (qpat_x_assum ‘∀j hd. MEM (j, hd) B ⇒ j < _ ∧ _’ drule >> simp[]) >>
          ‘hd ≠ hdl lfd hs.nxt’
            by (strip_tac >> qpat_x_assum ‘¬MEM (hdl _ _) (MAP SND B)’ mp_tac >>
                simp[MEM_MAP, EXISTS_PROD] >> qexists_tac ‘j’ >> gvs[]) >>
          qpat_x_assum ‘∀j hd. MEM (j, hd) B ⇒ (_ ⇔ _) ∧ _’ drule >> simp[EL_APPEND1]) >>
      qpat_x_assum ‘hd = _’ SUBST_ALL_TAC >> qpat_x_assum ‘j = _’ SUBST_ALL_TAC >>
      simp[EL_APPEND2, cpa_def, new_chan_def])
  >- (rpt strip_tac >> simp[] >> disj1_tac >>
      qpat_x_assum ‘∀hd. _ ∨ _ ⇒ MEM hd (MAP SND B)’ irule >> simp[])
  >- (rpt strip_tac >> Cases_on ‘j < LENGTH w.chans’ >> simp[] >>
      qpat_x_assum ‘∀j. j < LENGTH w.chans ∧ cpa _ ⇒ _’ irule >> gvs[EL_APPEND1]) >>
  qpat_x_assum ‘EVERY _ w.listening’ mp_tac >>
  qpat_x_assum ‘EVERY _ w.listening’ mp_tac >>
  simp[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >> res_tac >> gvs[EL_APPEND1]
QED

Theorem ehdo_kinv:
  ehdo lfd v (w, hs) x = SOME (r, (w', hs')) ∧ gchinv lfd B ps (w, hs) ∧ kinv B ps w ⇒
  kinv (B ++ ebind w x r) (ps ++ [(x, r)]) w'
Proof
  strip_tac >>
  Cases_on ‘(∃l. x = EAccept l) ∨ (∃a. x = EConnect a ∧ ∃h. r = EConnected (SOME h))’
  >- (pop_assum strip_assume_tac >> qpat_x_assum ‘x = _’ SUBST_ALL_TAC
      >- (irule ehdo_accept_kinv >> rpt (first_assum (irule_at Any))) >>
      qpat_x_assum ‘r = _’ SUBST_ALL_TAC >>
      irule ehdo_connect_kinv >> rpt (first_assum (irule_at Any))) >>
  ‘ebind w x r = []’ by (gvs[ebind_def] >> Cases_on ‘x’ >> gvs[] >> Cases_on ‘r’ >> gvs[] >>
                         rename1 ‘EConnected oh’ >> Cases_on ‘oh’ >> gvs[]) >>
  simp[] >> irule kinv_frame >>
  qpat_assum ‘kinv _ _ _’ (irule_at Any) >> qpat_assum ‘gchinv _ _ _ _’ (irule_at Any) >>
  drule ehdo_cpa >> strip_tac >>
  qexists_tac ‘REPLICATE (LENGTH (conn_hdls [r])) T’ >> simp[] >>
  ‘conn_hdls [r] = []’
    by (Cases_on ‘r’ >> simp[conn_hdls_def] >> rename1 ‘EConnected oh’ >> Cases_on ‘oh’ >>
        simp[conn_hdls_def] >> Cases_on ‘x’ >> gvs[ehdo_def, AllCaseEqs()] >>
        pairarg_tac >> gvs[]) >>
  simp[] >> rpt conj_tac >>
  FIRST [irule ehdo_listening >> qpat_assum ‘ehdo _ _ _ _ = _’ (irule_at Any) >> gvs[] >> NO_TAC,
         Cases_on ‘x’ >> Cases_on ‘r’ >> gvs[hl_conn_handles_def, hl_connects_def, acc_hdls_def] >>
         TRY (rename1 ‘EConnected oh’ >> Cases_on ‘oh’ >> gvs[]) >> NO_TAC]
QED

Theorem ehacts_kinv:
  ∀acts k (st : eworld # ehstate) rs st' B ps.
    ehacts lfd lv n k st acts = SOME (rs, st') ∧ gchinv lfd B ps st ∧ kinv B ps (FST st) ⇒
    kinv (B ++ ehbacts lfd lv n k st acts) (ps ++ ZIP (acts, rs)) (FST st')
Proof
  Induct >> simp[ehacts_def, ehbacts_def] >> rpt gen_tac >>
  PairCases_on ‘st’ >> simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  PairCases_on ‘st1'’ >>
  drule_all ehdo_gchinv >> strip_tac >>
  drule_all ehdo_kinv >> strip_tac >>
  ‘ps ++ (h,r)::ZIP (acts,rs') = (ps ++ [(h,r)]) ++ ZIP (acts,rs')’ by simp[] >>
  pop_assum SUBST1_TAC >> REWRITE_TAC[APPEND_ASSOC] >>
  first_x_assum irule >> simp[]
QED

(* ------------------------------------------------------------------------
   The poll
   ------------------------------------------------------------------------ *)

Theorem ep_deliver_kinv:
  gchinv lfd B ps (w, hs) ∧ kinv B ps w ⇒ kinv B ps (ep_deliver w e)
Proof
  strip_tac >> ‘cext w (ep_deliver w e)’ by simp[ep_deliver_cext] >>
  pop_assum (strip_assume_tac o REWRITE_RULE [cext_def]) >>
  Cases_on ‘∃a. e = Incoming a’
  >- (pop_assum strip_assume_tac >> qpat_x_assum ‘e = _’ SUBST_ALL_TAC >>
      qpat_x_assum ‘MAP cpa _ = _’ kall_tac >>
      simp[ep_deliver_def] >>
      qpat_assum ‘gchinv _ _ _ _’ (strip_assume_tac o REWRITE_RULE [gchinv_def]) >>
      Cases_on ‘w.listening’ >> simp[] >>
      rename1 ‘w.listening = x :: xs’ >> PairCases_on ‘x’ >>
      ‘xs = []’ by (Cases_on ‘xs’ >> gvs[]) >>
      rw[] >> simp[AFUPDKEY_def] >>
      qpat_x_assum ‘kinv _ _ _’ mp_tac >> rewrite_tac[kinv_def] >> strip_tac >> simp[] >>
      rpt conj_tac
      >- (rpt gen_tac >> strip_tac >>
          ‘j < LENGTH w.chans’ by (qpat_x_assum ‘∀j hd. MEM (j, hd) B ⇒ j < _ ∧ _’ drule >> simp[]) >>
          qpat_x_assum ‘∀j hd. MEM (j, hd) B ⇒ (_ ⇔ _) ∧ _’ drule >> simp[EL_APPEND1])
      >- first_assum ACCEPT_TAC
      >- (rpt strip_tac >> Cases_on ‘j < LENGTH w.chans’
          >- (qpat_x_assum ‘∀j. j < LENGTH w.chans ∧ cpa _ ⇒ _’ irule >> gvs[EL_APPEND1]) >>
          ‘j = LENGTH w.chans’ by decide_tac >>
          gvs[EL_APPEND2, cpa_def, new_chan_def])
      >- (qpat_x_assum ‘EVERY _ [_]’ mp_tac >>
          qpat_assum ‘w.listening = _’ (fn th =>
            qpat_x_assum ‘EVERY _ w.listening’ (mp_tac o REWRITE_RULE [th])) >>
          simp[EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[EL_APPEND1]) >>
      simp[EL_APPEND2, cpa_def, new_chan_def]) >>
  irule kinv_frame >> qpat_assum ‘kinv _ _ _’ (irule_at Any) >>
  qpat_assum ‘gchinv _ _ _ _’ (irule_at Any) >>
  qexists_tac ‘l’ >> simp[] >>
  Cases_on ‘e’ >> gvs[ep_deliver_def] >> rw[]
QED

Theorem FOLDL_deliver_kinv:
  ∀es w. gchinv lfd B ps (w, hs) ∧ kinv B ps w ⇒ kinv B ps (FOLDL ep_deliver w es)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >> conj_tac
  >- (irule ep_deliver_kinv >> simp[] >> qexistsl_tac [‘hs’, ‘lfd’] >> simp[])
  >> irule ep_deliver_gchinv >> simp[]
QED

Theorem kinv_cong:
  w'.chans = w.chans ∧ w'.listening = w.listening ⇒ (kinv B ps w' ⇔ kinv B ps w)
Proof
  simp[kinv_def]
QED

Theorem ep_tick_kinv:
  gchinv lfd B ps (w, hs) ∧ kinv B ps w ⇒ kinv B ps (ep_tick w)
Proof
  simp[ep_tick_def] >> strip_tac >> irule FOLDL_deliver_kinv >> conj_tac
  >- (‘kinv B ps (w with clock := w.clock + 1) ⇔ kinv B ps w’ by (irule kinv_cong >> simp[]) >>
      simp[])
  >> qexistsl_tac [‘hs’, ‘lfd’] >> simp[gchinv_clock]
QED

Theorem ehpoll_kinv:
  ehpoll lfd hs hfds w = (rdy, w', hs') ∧ gchinv lfd B ps (w, hs) ∧ kinv B ps w ⇒
  kinv B ps w'
Proof
  simp[ehpoll_def] >> strip_tac >> gvs[] >> irule ep_tick_kinv >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [‘hs’, ‘lfd’] >> first_assum ACCEPT_TAC
QED

(* ------------------------------------------------------------------------
   The run
   ------------------------------------------------------------------------ *)

Theorem ehrounds_kinv:
  W0.chans = [] ∧ W0.open_fds = [] ∧ alloc_ok W0.alloc ∧ LENGTH W0.listening ≤ 1 ∧
  EVERY (λ(l, a, q). q = []) W0.listening ∧
  (∀n. ehacts lfd lv n 0 (ehst lfd lv ifds m W0 n)
         (new_actions (log_of m) (ehhist lfd lv ifds m W0 n)) ≠ NONE) ⇒
  ∀n. kinv (ehbinds lfd lv ifds m W0 n) (hl_pairs m (ehhist lfd lv ifds m W0 n))
           (FST (ehst lfd lv ifds m W0 n))
Proof
  strip_tac >> drule_all ehrounds_gchinv >> strip_tac >> Induct
  >- (simp[ehst_def, ehhist_def, ehrounds_def, ehbinds_def, kinv_def, hl_pairs_def,
           acc_hdls_def, hl_conn_handles_def, hl_connects_def] >>
      qpat_x_assum ‘EVERY _ W0.listening’ mp_tac >>
      simp[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >> res_tac >> gvs[]) >>
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
  drule ehacts_kinv >>
  disch_then (qspecl_then [‘ehbinds lfd lv ifds m W0 n’, ‘hl_pairs m h’] mp_tac) >>
  simp[] >> strip_tac >>
  drule_all ehpoll_kinv >> simp[]
QED
