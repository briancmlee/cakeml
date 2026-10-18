(*
  PROVISIONAL Q-17 (L-C, the E1 half).  On the endpoint handle layer,
  generic in the program: at a round boundary a channel's inbox holds at
  most one L1 recv (pf_chunk bytes), so what an episode received on the
  raw trace is at most what the program read on its handle, plus pf_chunk.

  The world invariant winv: a channel that is not Up has an empty inbox;
  an unbound channel is pending at the listener; and a bound handle that
  the layer has dropped (an EOF read, or a refused connect reported) has
  an empty inbox that stays empty (peer_eof or Failed: no data arrives).
  At a round boundary, ev_rel gives the inbox of a handle the layer still
  holds: L1's inb_of (L-A: at most pf_chunk), or empty while connecting.
*)
Theory proxyInbox
Ancestors
  proxyBound e1TraceLag e1TraceRecvInv e1TraceRead e1TraceChan honestL1EPRefine
  moonshotClientSpec endpointHLModel endpointWorld alist
Libs
  preamble

(* ------------------------------------------------------------------------
   The invariant
   ------------------------------------------------------------------------ *)

Definition fz_def:
  fz (c : chan) ⇔ c.inbox = [] ∧ (c.peer_eof ∨ c.status = Failed)
End

Definition winv_def:
  winv B (w : eworld, hs : ehstate) ⇔
    (∀j. j < LENGTH w.chans ∧ (EL j w.chans).status ≠ Up ⇒ (EL j w.chans).inbox = []) ∧
    (∀j. j < LENGTH w.chans ∧ ¬MEM j (MAP FST B) ⇒ EXISTS (λ(l, a, q). MEM j q) w.listening) ∧
    (∀j hd. MEM (j, hd) B ∧ ALOOKUP hs.tbl hd = NONE ⇒ j < LENGTH w.chans ∧ fz (EL j w.chans))
End

(* A channel step that keeps the invariant: no channel becomes un-Up, an
   empty inbox of a channel that takes no data stays empty, peer_eof and
   Failed stick *)
Definition ckeep_def:
  ckeep (c : chan) (c1 : chan) ⇔
    (c1.status ≠ Up ⇒ c.status ≠ Up) ∧
    (c.inbox = [] ∧ (c.status ≠ Up ∨ c.peer_eof) ⇒ c1.inbox = []) ∧
    (c.peer_eof ⇒ c1.peer_eof) ∧ (c.status = Failed ⇒ c1.status = Failed)
End

Definition wck_def:
  wck (w : eworld) (w1 : eworld) ⇔
    LENGTH w1.chans = LENGTH w.chans ∧ w1.listening = w.listening ∧
    ∀j. j < LENGTH w.chans ⇒ ckeep (EL j w.chans) (EL j w1.chans)
End

Theorem ckeep_refl[simp]:
  ckeep c c
Proof
  rw[ckeep_def]
QED

Theorem wck_refl[simp]:
  wck w w
Proof
  rw[wck_def]
QED

Theorem ckeep_fz:
  ckeep c c1 ∧ fz c ⇒ fz c1
Proof
  rw[ckeep_def, fz_def] >> gvs[]
QED

(* The general step: the channels kept, and a handle the step drops has
   its channels frozen *)
Theorem winv_step:
  winv B (w, hs) ∧ wck w w1 ∧
  (∀j hd. MEM (j, hd) B ∧ ALOOKUP hs1.tbl hd = NONE ∧ ALOOKUP hs.tbl hd ≠ NONE ⇒
          j < LENGTH w1.chans ∧ fz (EL j w1.chans)) ⇒
  winv B (w1, hs1)
Proof
  rewrite_tac[winv_def, wck_def] >> strip_tac >> rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (‘j < LENGTH w.chans’ by fs[] >>
      qpat_x_assum ‘∀j. j < LENGTH w.chans ⇒ ckeep _ _’ drule >> rewrite_tac[ckeep_def] >>
      metis_tac[])
  >- (‘j < LENGTH w.chans’ by fs[] >> metis_tac[])
  >> Cases_on ‘ALOOKUP hs.tbl hd’
  >- (qpat_x_assum ‘∀j hd. MEM (j, hd) B ∧ ALOOKUP hs.tbl hd = NONE ⇒ _’ drule >> simp[] >>
      strip_tac >> irule ckeep_fz >> qexists_tac ‘EL j w.chans’ >> simp[])
  >> qpat_x_assum ‘∀j hd. MEM (j, hd) B ∧ ALOOKUP hs1.tbl hd = NONE ∧ _ ⇒ _’
       (qspecl_then [‘j’, ‘hd’] mp_tac) >> simp[]
QED

(* ------------------------------------------------------------------------
   The world's calls
   ------------------------------------------------------------------------ *)

Theorem ep_read_wck:
  ep_read f n w = SOME (r, w1) ⇒ wck w w1 ∧ w1.open_fds = w.open_fds
Proof
  rw[ep_read_def, AllCaseEqs()] >> gvs[ep_chan_of_def, AllCaseEqs()] >>
  rw[wck_def] >> rw[ckeep_def]
QED

Theorem ep_send_wck:
  ep_send f bs w = SOME (k, w1) ⇒ wck w w1
Proof
  rw[ep_send_def, AllCaseEqs()] >> gvs[ep_chan_of_def, AllCaseEqs()] >>
  rw[wck_def] >> rw[ckeep_def]
QED

Theorem ep_close_wck:
  ep_close f w = SOME w1 ⇒ wck w w1 ∧ ∀j. j < LENGTH w.chans ∧ fz (EL j w.chans) ⇒ fz (EL j w1.chans)
Proof
  rw[ep_close_def, AllCaseEqs()] >> gvs[ep_chan_of_def, AllCaseEqs()] >>
  rw[wck_def, upd_chan_def, EL_LUPDATE] >> rw[ckeep_def] >> gvs[fz_def]
QED

Theorem ep_conn_err_wck:
  ep_conn_err f w = SOME w1 ⇒ wck w w1 ∧ w1.open_fds = w.open_fds
Proof
  rw[ep_conn_err_def, AllCaseEqs()] >> gvs[ep_chan_of_def, AllCaseEqs()] >>
  rw[wck_def] >> rw[ckeep_def]
QED

(* A refused connect, reported: its channel is Failed, its inbox empty *)
Theorem ep_conn_err_fz:
  winv B (w, hs) ∧ ep_conn_err f w = SOME w1 ⇒
  ∃j. ep_chan_of w f = SOME j ∧ j < LENGTH w1.chans ∧ fz (EL j w1.chans)
Proof
  rw[ep_conn_err_def, AllCaseEqs()] >> qexists_tac ‘j’ >>
  gvs[ep_chan_of_def, AllCaseEqs(), fz_def] >>
  qpat_x_assum ‘winv _ _’ mp_tac >> rewrite_tac[winv_def] >> strip_tac >>
  first_x_assum irule >> simp[]
QED

(* A read that got EOF: the channel's inbox is empty, and it is peer_eof or
   Failed *)
Theorem ep_read_eof_fz:
  ep_read f n w = SOME (SOME [], w1) ∧ 0 < n ⇒
  w1 = w ∧ ∃j. ep_chan_of w f = SOME j ∧ j < LENGTH w.chans ∧ fz (EL j w.chans)
Proof
  rw[ep_read_def, AllCaseEqs()] >> gvs[ep_chan_of_def, AllCaseEqs(), fz_def] >>
  Cases_on ‘(EL j w.chans).inbox’ >> gvs[] >> Cases_on ‘n’ >> gvs[]
QED

(* ------------------------------------------------------------------------
   One action
   ------------------------------------------------------------------------ *)

(* The layer drops handle h (its channel frozen) *)
Theorem winv_del:
  winv B (w, hs) ∧ (∀j'. MEM (j', h) B ⇒ j' = j) ∧
  wck w w2 ∧ j < LENGTH w2.chans ∧ fz (EL j w2.chans) ⇒
  winv B (w2, eh_del h hs)
Proof
  strip_tac >> irule winv_step >> qexistsl_tac [‘hs’, ‘w’] >> simp[] >>
  rpt gen_tac >> simp[eh_del_def, ALOOKUP_ADELKEY] >> rw[] >> gvs[] >>
  res_tac >> gvs[]
QED

(* The channel of a handle the layer holds is the only one bound to it *)
Theorem tbl_bind_uniq:
  gchinv lfd B ps (w, hs) ∧ ALOOKUP hs.tbl h = SOME f ⇒
  ∃j. ep_chan_of w f = SOME j ∧ ∀j'. MEM (j', h) B ⇒ j' = j
Proof
  strip_tac >> drule_all tbl_chan >> strip_tac >> qexists_tac ‘j’ >> simp[] >>
  ‘ALL_DISTINCT (MAP SND B)’ by fs[gchinv_def] >>
  rpt strip_tac >>
  qpat_x_assum ‘MEM (j', h) B’ mp_tac >> qpat_x_assum ‘MEM (j, h) B’ mp_tac >>
  qpat_x_assum ‘ALL_DISTINCT _’ mp_tac >> rpt (pop_assum kall_tac) >> metis_tac[bind_inj]
QED

Theorem ehdo_read_winv:
  ehdo lfd v (w, hs) (ERead h n) = SOME (r, (w', hs')) ∧ gchinv lfd B ps (w, hs) ∧ winv B (w, hs) ⇒
  winv B (w', hs')
Proof
  strip_tac >> qpat_x_assum ‘ehdo _ _ _ _ = _’ mp_tac >> simp[ehdo_def] >>
  strip_tac >> qpat_x_assum ‘_ = SOME _’ mp_tac >>
  Cases_on ‘ALOOKUP hs.tbl h’ >> simp[] >- (strip_tac >> gvs[]) >>
  rename1 ‘ALOOKUP hs.tbl h = SOME f’ >>
  Cases_on ‘ep_conn_err f w’ >> simp[]
  >~ [‘ep_conn_err f w = SOME w1’]
  >- (strip_tac >> gvs[] >>
      drule_all tbl_bind_uniq >> strip_tac >>
      drule_all ep_conn_err_fz >> strip_tac >>
      qpat_x_assum ‘ep_chan_of w f = SOME j'’ mp_tac >> asm_rewrite_tac[optionTheory.SOME_11] >>
      disch_then (SUBST_ALL_TAC o SYM) >>
      drule ep_conn_err_wck >> strip_tac >>
      drule ep_close_wck >> strip_tac >>
      ‘winv B (w1, hs)’ by (irule winv_step >> qexistsl_tac [‘hs’, ‘w’] >> simp[]) >>
      irule winv_del >> conj_tac
      >- (qexists_tac ‘j’ >> rpt conj_tac >>
          FIRST [first_assum ACCEPT_TAC >> NO_TAC,
                 qpat_x_assum ‘∀j. j < LENGTH w1.chans ∧ fz _ ⇒ _’ irule >> conj_tac >>
                   first_assum ACCEPT_TAC >> NO_TAC,
                 qpat_x_assum ‘wck w1 w'’ mp_tac >> rewrite_tac[wck_def] >> strip_tac >>
                   asm_rewrite_tac[]]) >>
      qexists_tac ‘w1’ >> conj_tac >> first_assum ACCEPT_TAC) >>
  Cases_on ‘ep_read f n w’ >> simp[] >> rename1 ‘ep_read f n w = SOME x’ >>
  PairCases_on ‘x’ >> rename1 ‘ep_read f n w = SOME (ro, w1)’ >>
  drule ep_read_wck >> strip_tac >>
  Cases_on ‘ro = SOME []’
  >- (gvs[] >> strip_tac >> gvs[] >>
      drule_all tbl_bind_uniq >> strip_tac >>
      drule_all ep_read_eof_fz >> strip_tac >>
      qpat_x_assum ‘w1 = w’ SUBST_ALL_TAC >>
      qpat_x_assum ‘ep_chan_of w f = SOME j'’ mp_tac >> asm_rewrite_tac[optionTheory.SOME_11] >>
      disch_then (SUBST_ALL_TAC o SYM) >>
      drule ep_close_wck >> strip_tac >>
      irule winv_del >> conj_tac
      >- (qexists_tac ‘j’ >> rpt conj_tac >>
          FIRST [first_assum ACCEPT_TAC >> NO_TAC,
                 qpat_x_assum ‘∀j. j < LENGTH w.chans ∧ fz _ ⇒ _’ irule >> conj_tac >>
                   first_assum ACCEPT_TAC >> NO_TAC,
                 qpat_x_assum ‘wck w w'’ mp_tac >> rewrite_tac[wck_def] >> strip_tac >>
                   asm_rewrite_tac[]]) >>
      qexists_tac ‘w’ >> conj_tac >> first_assum ACCEPT_TAC) >>
  Cases_on ‘ro’ >> TRY (Cases_on ‘x’) >> fs[] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  irule winv_step >> qexistsl_tac [‘hs’, ‘w’] >> simp[]
QED

Theorem ehdo_write_winv:
  ehdo lfd v (w, hs) (EWrite h bs) = SOME (r, (w', hs')) ∧ winv B (w, hs) ⇒ winv B (w', hs')
Proof
  strip_tac >> qpat_x_assum ‘ehdo _ _ _ _ = _’ mp_tac >> simp[ehdo_def] >>
  Cases_on ‘ALOOKUP hs.tbl h’ >> simp[] >- (strip_tac >> gvs[]) >>
  rw[] >> pairarg_tac >> gvs[] >> drule ep_send_wck >> strip_tac >>
  irule winv_step >> qexistsl_tac [‘hs’, ‘w’] >> simp[]
QED

(* Binding channel j to the next handle, which the layer now holds *)
Theorem winv_bind:
  winv B (w, hs) ∧ gchinv lfd B ps (w, hs) ∧ hdln (w2n lfd) hs.nxt < dimword (:64) ∧
  LENGTH w.chans ≤ LENGTH w'.chans ∧ j < LENGTH w'.chans ∧
  (∀i. i < LENGTH w.chans ⇒ EL i w'.chans = EL i w.chans) ∧
  (∀i. LENGTH w.chans ≤ i ∧ i < LENGTH w'.chans ⇒ (EL i w'.chans).inbox = [] ∧ i = j) ∧
  (∀i. i < LENGTH w'.chans ∧ i ≠ j ∧ EXISTS (λ(l, a, q). MEM i q) w.listening ⇒
       EXISTS (λ(l, a, q). MEM i q) w'.listening) ∧
  ALOOKUP hs'.tbl (hdl lfd hs.nxt) ≠ NONE ∧
  (∀hd. hd ≠ hdl lfd hs.nxt ∧ ALOOKUP hs'.tbl hd = NONE ⇒ ALOOKUP hs.tbl hd = NONE) ⇒
  winv (B ++ [(j, hdl lfd hs.nxt)]) (w', hs')
Proof
  strip_tac >>
  ‘∀j hd. MEM (j, hd) B ⇒ j < LENGTH w.chans’
    by (rpt strip_tac >> qpat_assum ‘gchinv _ _ _ _’ (mp_tac o REWRITE_RULE [gchinv_def]) >>
        strip_tac >> qpat_x_assum ‘∀j hd. MEM (j, hd) B ⇒ _’ drule >> simp[]) >>
  qpat_x_assum ‘winv _ _’ mp_tac >> rewrite_tac[winv_def] >> strip_tac >> rpt conj_tac >>
  rpt gen_tac >> strip_tac
  >- (rename1 ‘i < LENGTH w'.chans’ >> Cases_on ‘i < LENGTH w.chans’
      >- (‘EL i w'.chans = EL i w.chans’
            by (qpat_x_assum ‘∀i. i < LENGTH w.chans ⇒ EL i w'.chans = _’ irule >>
                first_assum ACCEPT_TAC) >>
          pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
          qpat_x_assum ‘∀j. j < LENGTH w.chans ∧ _ ⇒ (EL j w.chans).inbox = []’ irule >>
          conj_tac >> first_assum ACCEPT_TAC) >>
      ‘LENGTH w.chans ≤ i’ by decide_tac >>
      qpat_x_assum ‘∀i. LENGTH w.chans ≤ i ∧ _ ⇒ _’ (qspec_then ‘i’ mp_tac) >> simp[])
  >- (rename1 ‘i < LENGTH w'.chans’ >>
      ‘i ≠ j’ by (strip_tac >> qpat_x_assum ‘¬MEM _ _’ mp_tac >> simp[]) >>
      ‘i < LENGTH w.chans’
        by (CCONTR_TAC >>
            qpat_x_assum ‘∀i. LENGTH w.chans ≤ i ∧ _ ⇒ _’ (qspec_then ‘i’ mp_tac) >> simp[]) >>
      ‘¬MEM i (MAP FST B)’ by (qpat_x_assum ‘¬MEM _ _’ mp_tac >> simp[]) >>
      qpat_x_assum ‘∀i. i < LENGTH w'.chans ∧ i ≠ j ∧ _ ⇒ _’ irule >> simp[] >>
      qpat_x_assum ‘∀j. j < LENGTH w.chans ∧ ¬MEM j _ ⇒ _’ irule >> simp[]) >>
  rename1 ‘MEM (i, hd) (B ++ _)’ >>
  ‘hd ≠ hdl lfd hs.nxt’ by (strip_tac >> rpt BasicProvers.VAR_EQ_TAC >> fs[]) >>
  ‘MEM (i, hd) B’ by (qpat_x_assum ‘MEM _ (B ++ _)’ mp_tac >> simp[]) >>
  ‘ALOOKUP hs.tbl hd = NONE’ by (qpat_x_assum ‘∀hd. hd ≠ _ ∧ _ ⇒ _’ irule >> simp[]) >>
  ‘i < LENGTH w.chans’ by (qpat_x_assum ‘∀j hd. MEM (j, hd) B ⇒ j < _’ drule >> simp[]) >>
  qpat_x_assum ‘∀j hd. MEM (j, hd) B ∧ ALOOKUP hs.tbl hd = NONE ⇒ _’ drule_all >> strip_tac >>
  ‘EL i w'.chans = EL i w.chans’
    by (qpat_x_assum ‘∀i. i < LENGTH w.chans ⇒ EL i w'.chans = _’ irule >> first_assum ACCEPT_TAC) >>
  simp[]
QED

Theorem ehdo_connect_winv:
  ehdo lfd v (w, hs) (EConnect a) = SOME (r, (w', hs')) ∧ gchinv lfd B ps (w, hs) ∧ winv B (w, hs) ⇒
  winv (B ++ ebind w (EConnect a) r) (w', hs')
Proof
  strip_tac >> qpat_x_assum ‘ehdo _ _ _ _ = _’ mp_tac >> simp[ehdo_def] >>
  Cases_on ‘ep_connect a w’ >> rename1 ‘ep_connect a w = (fo, w1)’ >>
  Cases_on ‘fo’ >> simp[]
  >- (strip_tac >> gvs[ebind_def] >>
      qpat_x_assum ‘ep_connect _ _ = _’ mp_tac >>
      simp[ep_connect_def, ep_alloc_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
      irule winv_step >> qexistsl_tac [‘hs’, ‘w’] >> simp[wck_def]) >>
  rename1 ‘ep_connect a w = (SOME f, w1)’ >> strip_tac >> gvs[ebind_def] >>
  qpat_x_assum ‘ep_connect _ _ = _’ mp_tac >>
  simp[ep_connect_def, ep_alloc_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  irule winv_bind >> qpat_assum ‘winv _ _’ (irule_at Any) >>
  qpat_assum ‘gchinv _ _ _ _’ (irule_at Any) >>
  simp[eh_new_def, EL_APPEND1] >> rpt conj_tac >>
  FIRST [rpt strip_tac >> ‘i = LENGTH w.chans’ by decide_tac >> simp[EL_APPEND2, new_chan_def] >> NO_TAC,
         rpt strip_tac >> decide_tac >> NO_TAC,
         metis_tac[]]
QED

Theorem ehdo_accept_winv:
  ehdo lfd v (w, hs) (EAccept l) = SOME (r, (w', hs')) ∧ gchinv lfd B ps (w, hs) ∧ winv B (w, hs) ⇒
  winv (B ++ ebind w (EAccept l) r) (w', hs')
Proof
  strip_tac >> qpat_x_assum ‘ehdo _ _ _ _ = _’ mp_tac >> simp[ehdo_def, ep_accept_def] >>
  qpat_assum ‘gchinv _ _ _ _’ (strip_assume_tac o REWRITE_RULE [gchinv_def]) >>
  Cases_on ‘w.listening’ >> simp[] >>
  rename1 ‘w.listening = x :: xs’ >> PairCases_on ‘x’ >>
  ‘xs = []’ by (Cases_on ‘xs’ >> gvs[]) >>
  rw[] >> gvs[AllCaseEqs(), ebind_def] >>
  TRY (irule winv_step >> qexistsl_tac [‘hs’, ‘w’] >> simp[] >> NO_TAC) >>
  gvs[ep_alloc_def] >>
  irule winv_bind >> qpat_assum ‘winv _ _’ (irule_at Any) >>
  qpat_assum ‘gchinv _ _ _ _’ (irule_at Any) >>
  simp[eh_new_def, AFUPDKEY_def] >> rpt conj_tac >>
  FIRST [rpt strip_tac >> decide_tac >> NO_TAC,
         rpt strip_tac >> gvs[] >> NO_TAC,
         metis_tac[]]
QED

Theorem ehdo_winv:
  ehdo lfd v (w, hs) x = SOME (r, (w', hs')) ∧ gchinv lfd B ps (w, hs) ∧ winv B (w, hs) ⇒
  winv (B ++ ebind w x r) (w', hs')
Proof
  Cases_on ‘x’ >> strip_tac
  >- (drule_all ehdo_accept_winv >> simp[])
  >- (drule_all ehdo_read_winv >> simp[])
  >- (drule_all ehdo_write_winv >> simp[])
  >- (drule_all ehdo_connect_winv >> simp[])
  >> qpat_x_assum ‘ehdo _ _ _ _ = _’ mp_tac >> simp[ehdo_def] >> strip_tac >> gvs[]
QED

Theorem ehacts_winv:
  ∀acts k (st : eworld # ehstate) rs st' B ps.
    ehacts lfd lv n k st acts = SOME (rs, st') ∧ gchinv lfd B ps st ∧ winv B st ⇒
    winv (B ++ ehbacts lfd lv n k st acts) st'
Proof
  Induct >> simp[ehacts_def, ehbacts_def] >> rpt gen_tac >>
  PairCases_on ‘st’ >> simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  PairCases_on ‘st1'’ >>
  drule_all ehdo_gchinv >> strip_tac >>
  drule_all ehdo_winv >> strip_tac >>
  REWRITE_TAC[APPEND_ASSOC] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The poll
   ------------------------------------------------------------------------ *)

Theorem ep_deliver_winv:
  gchinv lfd B ps (w, hs) ∧ winv B (w, hs) ⇒ winv B (ep_deliver w e, hs)
Proof
  strip_tac >> Cases_on ‘e’ >> simp[ep_deliver_def] >>
  TRY (rw[] >> irule winv_step >> qexistsl_tac [‘hs’, ‘w’] >> simp[] >>
       rw[wck_def, upd_chan_def, EL_LUPDATE] >> rw[ckeep_def] >> NO_TAC)
  >> qpat_assum ‘gchinv _ _ _ _’ (strip_assume_tac o REWRITE_RULE [gchinv_def]) >>
  Cases_on ‘w.listening’ >> simp[] >>
  rename1 ‘w.listening = x :: xs’ >> PairCases_on ‘x’ >>
  ‘xs = []’ by (Cases_on ‘xs’ >> gvs[]) >>
  rw[] >> gvs[AFUPDKEY_def] >>
  qpat_x_assum ‘winv _ _’ mp_tac >> rewrite_tac[winv_def] >> strip_tac >> rpt conj_tac >>
  rpt gen_tac >> strip_tac
  >- (Cases_on ‘j < LENGTH w.chans’ >> gvs[EL_APPEND1] >>
      ‘j = LENGTH w.chans’ by decide_tac >> gvs[EL_APPEND2, new_chan_def])
  >- (Cases_on ‘j < LENGTH w.chans’ >> gvs[] >> res_tac >> gvs[] >> decide_tac)
  >> res_tac >> simp[EL_APPEND1]
QED

Theorem FOLDL_deliver_winv:
  ∀es w. gchinv lfd B ps (w, hs) ∧ winv B (w, hs) ⇒ winv B (FOLDL ep_deliver w es, hs)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >> conj_tac
  >- (irule ep_deliver_winv >> simp[] >> qexistsl_tac [‘lfd’, ‘ps’] >> simp[])
  >> irule ep_deliver_gchinv >> simp[]
QED

Theorem winv_clock:
  winv B (w with clock := c, hs) ⇔ winv B (w, hs)
Proof
  rewrite_tac[winv_def] >> simp[]
QED

Theorem ehpoll_winv:
  ehpoll lfd hs hfds w = (rdy, w', hs') ∧ gchinv lfd B ps (w, hs) ∧ winv B (w, hs) ⇒
  winv B (w', hs')
Proof
  simp[ehpoll_def, ep_tick_def] >> strip_tac >> gvs[] >>
  ‘winv B (FOLDL ep_deliver (w with clock := w.clock + 1) (w.env w.clock w.hist), hs)’
    by (irule FOLDL_deliver_winv >> rewrite_tac[winv_clock] >> conj_tac >- first_assum ACCEPT_TAC >>
        qexistsl_tac [‘lfd’, ‘ps’] >> rewrite_tac[gchinv_clock] >> first_assum ACCEPT_TAC) >>
  pop_assum mp_tac >> rewrite_tac[winv_def] >> strip_tac >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘∀j hd. MEM (j, hd) B ∧ _ ⇒ _ ∧ fz _’ (qspecl_then [‘j’, ‘hd’] mp_tac) >>
  impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> qpat_x_assum ‘ALOOKUP _ _ = NONE’ mp_tac >> simp[]) >>
  simp[]
QED

(* ------------------------------------------------------------------------
   The run
   ------------------------------------------------------------------------ *)

Theorem ehrounds_winv:
  W0.chans = [] ∧ W0.open_fds = [] ∧ alloc_ok W0.alloc ∧ LENGTH W0.listening ≤ 1 ∧
  EVERY (λ(l, a, q). q = []) W0.listening ∧
  (∀n. ehacts lfd lv n 0 (ehst lfd lv ifds m W0 n)
         (new_actions (log_of m) (ehhist lfd lv ifds m W0 n)) ≠ NONE) ⇒
  ∀n. winv (ehbinds lfd lv ifds m W0 n) (ehst lfd lv ifds m W0 n)
Proof
  strip_tac >> drule_all ehrounds_gchinv >> strip_tac >> Induct
  >- simp[ehst_def, ehrounds_def, ehbinds_def, winv_def] >>
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
  drule_all ehacts_gchinv >> strip_tac >>
  drule ehacts_winv >>
  disch_then (qspecl_then [‘ehbinds lfd lv ifds m W0 n’, ‘hl_pairs m h’] mp_tac) >>
  simp[] >> strip_tac >>
  drule_all ehpoll_winv >> simp[]
QED

(* ------------------------------------------------------------------------
   At a round boundary: every inbox is at most pf_chunk
   ------------------------------------------------------------------------ *)

Theorem e1_inbox_le:
  e1run_ok lfd a pol ifds m w0 calls ∧
  erounds lfd pol ifds m (w0, einit) n = SOME (h, ws, evs, logs) ∧
  j < LENGTH (FST (ehst lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) n)).chans ⇒
  LENGTH (EL j (FST (ehst lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) n)).chans).inbox
    ≤ pf_chunk
Proof
  strip_tac >>
  qabbrev_tac ‘W0 = pew lfd a pol ifds m w0 calls’ >>
  qabbrev_tac ‘lv = elv lfd pol ifds m w0’ >>
  ‘W0.chans = [] ∧ W0.open_fds = [] ∧ alloc_ok W0.alloc ∧ LENGTH W0.listening ≤ 1 ∧
   EVERY (λ(l, a, q). q = []) W0.listening ∧
   ∀n. ehacts lfd lv n 0 (ehst lfd lv ifds m W0 n)
         (new_actions (log_of m) (ehhist lfd lv ifds m W0 n)) ≠ NONE’
    by (irule e1run_ok_ehrounds >> simp[Abbr ‘W0’, Abbr ‘lv’] >> metis_tac[]) >>
  drule_all ehrounds_gchinv >> disch_then (qspec_then ‘n’ assume_tac) >>
  drule_all ehrounds_winv >> disch_then (qspec_then ‘n’ assume_tac) >>
  qpat_x_assum ‘e1run_ok _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [e1run_ok_def]) >>
  ‘inb_ok (SND ws).p’ by (drule_all erounds_inb >> simp[]) >>
  qspecl_then [‘w0’, ‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘a’, ‘calls’] mp_tac
    (Q.GENL [‘w0’, ‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘a’, ‘calls’] l1ep_refines_ehl) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [‘n’, ‘h’, ‘ws’, ‘evs’, ‘logs’] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum ‘Abbrev (W0 = _)’ (fn th => REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] (GSYM th)] >> assume_tac th) >>
  qpat_x_assum ‘Abbrev (lv = _)’ (fn th => REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] (GSYM th)] >> assume_tac th) >>
  strip_tac >>
  Cases_on ‘ehst lfd lv ifds m W0 n’ >> rename1 ‘_ = (w, hs)’ >>
  qpat_x_assum ‘ehst _ _ _ _ _ _ = _’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th, FST, SND]) >>
                                              REWRITE_TAC [th, FST, SND]) >>
  qabbrev_tac ‘cm = FST (ecm lfd pol ifds m w0 n)’ >>
  qabbrev_tac ‘es = SND ws’ >>
  qabbrev_tac ‘B = ehbinds lfd lv ifds m W0 n’ >>
  qpat_x_assum ‘winv _ _’ (strip_assume_tac o REWRITE_RULE [winv_def]) >>
  Cases_on ‘MEM j (MAP FST B)’
  >- (fs[MEM_MAP] >> rename1 ‘MEM y B’ >> PairCases_on ‘y’ >> gvs[] >> rename1 ‘MEM (j, hd) B’ >>
      Cases_on ‘ALOOKUP hs.tbl hd’
      >- (qpat_x_assum ‘∀j hd. MEM (j, hd) B ∧ ALOOKUP hs.tbl hd = NONE ⇒ _’ drule >>
          simp[fz_def]) >>
      rename1 ‘ALOOKUP hs.tbl hd = SOME f’ >>
      drule_all tbl_bind_uniq >> strip_tac >>
      ‘j = j'’ by (first_x_assum irule >> first_assum ACCEPT_TAC) >>
      pop_assum (SUBST_ALL_TAC o SYM) >>
      ‘ALOOKUP w.open_fds f = SOME j’ by
        (qpat_x_assum ‘ep_chan_of w f = SOME j’ mp_tac >> rewrite_tac[ep_chan_of_def] >>
         CASE_TAC >> simp[]) >>
      qpat_x_assum ‘ehs_rel _ _’ mp_tac >> rewrite_tac[ehs_rel_def] >> strip_tac >>
      qpat_x_assum ‘∀h. ALOOKUP hs.tbl h = _’ (qspec_then ‘hd’ mp_tac) >>
      qpat_x_assum ‘ALOOKUP hs.tbl hd = SOME f’ (fn th => REWRITE_TAC [th]) >>
      Cases_on ‘ALOOKUP es.p.b.tbl hd’ >>
      REWRITE_TAC [optionTheory.option_case_def, optionTheory.SOME_11] >> strip_tac
      >- (pop_assum (assume_tac o SYM) >>
          drule_all ev_rel_ctbl >> strip_tac >>
          ‘cl cm f = j’ by
            (qpat_x_assum ‘ALOOKUP w.open_fds f = SOME (cl cm f)’ mp_tac >>
             qpat_x_assum ‘ALOOKUP w.open_fds f = SOME j’ (fn th => REWRITE_TAC [th, optionTheory.SOME_11]) >>
             disch_then (ACCEPT_TAC o SYM)) >>
          qpat_x_assum ‘cl cm f = j’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
          qpat_x_assum ‘(EL j w.chans).inbox = []’ SUBST1_TAC >> simp[]) >>
      pop_assum (mp_tac o BETA_RULE) >> rewrite_tac[optionTheory.SOME_11] >> disch_then (SUBST_ALL_TAC o SYM) >>
      drule_all ev_rel_tbl >> strip_tac >>
      ‘cl cm f = j’ by
        (qpat_x_assum ‘ALOOKUP w.open_fds f = SOME (cl cm f)’ mp_tac >>
         qpat_x_assum ‘ALOOKUP w.open_fds f = SOME j’ (fn th => REWRITE_TAC [th, optionTheory.SOME_11]) >>
         disch_then (ACCEPT_TAC o SYM)) >>
      qpat_x_assum ‘cl cm f = j’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
      qpat_x_assum ‘(EL j w.chans).inbox = _’ SUBST1_TAC >>
      irule inb_ok_inb_of >> first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘∀j. j < LENGTH w.chans ∧ ¬MEM j (MAP FST B) ⇒ _’ drule_all >>
  qpat_x_assum ‘ev_rel _ _ _ _ _’ mp_tac >> rewrite_tac[ev_rel_def] >> strip_tac >>
  simp[MEM_MAP] >> strip_tac >>
  qpat_x_assum ‘∀f. MEM f es.p.acq ⇒ _’ drule >> simp[]
QED

(* An episode's raw receives, at a round boundary: what the program read on
   its handle, then at most pf_chunk *)
Theorem e1_recvd_le:
  e1run_ok lfd a pol ifds m w0 calls ∧
  erounds lfd pol ifds m (w0, einit) n = SOME (h, ws, evs, logs) ∧
  ALOOKUP (ehbinds lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) N) j = SOME hd ⇒
  LENGTH (l0_ep_recvd j evs) ≤
  LENGTH (hl_read hd (hl_pairs m (ehhist lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) n))) +
  pf_chunk
Proof
  strip_tac >>
  qabbrev_tac ‘W0 = pew lfd a pol ifds m w0 calls’ >>
  qabbrev_tac ‘lv = elv lfd pol ifds m w0’ >>
  ‘W0.chans = [] ∧ W0.open_fds = [] ∧ alloc_ok W0.alloc ∧ LENGTH W0.listening ≤ 1 ∧
   EVERY (λ(l, a, q). q = []) W0.listening ∧
   ∀n. ehacts lfd lv n 0 (ehst lfd lv ifds m W0 n)
         (new_actions (log_of m) (ehhist lfd lv ifds m W0 n)) ≠ NONE’
    by (irule e1run_ok_ehrounds >> simp[Abbr ‘W0’, Abbr ‘lv’] >> metis_tac[]) >>
  ‘l0_ep_recvd j evs = chrecv (FST (ehst lfd lv ifds m W0 n)) j’
    by (qpat_x_assum ‘e1run_ok _ _ _ _ _ _ _’ mp_tac >> rewrite_tac [e1run_ok_def] >>
        strip_tac >> simp[Abbr ‘W0’, Abbr ‘lv’] >>
        irule e1_l0_ep_recvd >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  pop_assum SUBST1_TAC >>
  rewrite_tac[chrecv_def] >> IF_CASES_TAC >> simp[] >>
  ‘LENGTH (EL j (FST (ehst lfd lv ifds m W0 n)).chans).inbox ≤ pf_chunk’
    by (simp[Abbr ‘W0’, Abbr ‘lv’] >> irule e1_inbox_le >> simp[] >> metis_tac[]) >>
  drule_all ehrounds_rinv >> disch_then (qspec_then ‘n’ mp_tac) >>
  rewrite_tac[rinv_def] >> strip_tac >>
  first_x_assum drule >> disch_then (SUBST1_TAC o GSYM) >>
  Cases_on ‘ALOOKUP (ehbinds lfd lv ifds m W0 n) j’ >> simp[] >>
  ‘x = hd’ by (irule ehbinds_lookup_same >> metis_tac[]) >>
  simp[]
QED
