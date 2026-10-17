(*
  The shared E1 trace layer (honest-ffi): ACCEPTED channels are bound or
  queued.  On the endpoint handle layer, generic in the program, a channel
  without a peer address (one that arrived on a listener) is either bound
  to a handle (ehbinds: the program accepted it) or still waiting in a
  listening queue (qinv, ehrounds_qinv).

  With e1TraceRole.e1_roles (channel j has no peer address iff raw episode
  j came from a sys_accept) this says every raw accept episode is, at each
  round boundary, bound or queued; a program that keeps accepting while
  the queue is not empty therefore binds it one round later.
*)
Theory e1TraceAccBind
Ancestors
  e1TraceKind e1TraceRole e1TraceUpto e1TraceChan honestL1EPRefine endpointHLModel endpointWorld alist
Libs
  preamble

Definition qinv_def:
  qinv B (w : eworld) ⇔
    ∀j. j < LENGTH w.chans ∧ ¬cpa (EL j w.chans) ⇒
        MEM j (MAP FST B) ∨ EXISTS (λ(l, a, q). MEM j q) w.listening
End

(* The frame: the listening queues kept, new channels have a peer address *)
Theorem qinv_frame:
  qinv B w ∧ MAP cpa w'.chans = MAP cpa w.chans ++ l ∧ EVERY I l ∧
  w'.listening = w.listening ⇒
  qinv (B ++ B') w'
Proof
  rewrite_tac[qinv_def] >> strip_tac >>
  qpat_x_assum ‘w'.listening = _’ SUBST_ALL_TAC >>
  ‘LENGTH w'.chans = LENGTH w.chans + LENGTH l’
    by (qpat_x_assum ‘MAP cpa w'.chans = _’ (mp_tac o AP_TERM “LENGTH : bool list -> num”) >>
        simp[]) >>
  rpt strip_tac >> Cases_on ‘j < LENGTH w.chans’
  >- (‘cpa (EL j w'.chans) ⇔ cpa (EL j w.chans)’
        by (irule cpa_el_prefix >> simp[] >> qexists_tac ‘l’ >> simp[]) >>
      qpat_x_assum ‘∀j. j < LENGTH w.chans ∧ _ ⇒ _’ (qspec_then ‘j’ mp_tac) >>
      impl_tac >- gvs[] >> simp[MAP_APPEND] >> metis_tac[]) >>
  ‘EL j (MAP cpa w'.chans) = EL j (MAP cpa w.chans ++ l)’ by simp[] >>
  pop_assum mp_tac >> simp[EL_MAP, EL_APPEND2] >>
  qpat_x_assum ‘EVERY _ l’ mp_tac >> simp[EVERY_EL] >>
  disch_then (qspec_then ‘j - LENGTH w.chans’ mp_tac) >> simp[]
QED

Theorem ehdo_accept_qinv:
  ehdo lfd v (w, hs) (EAccept l) = SOME (r, (w', hs')) ∧ LENGTH w.listening ≤ 1 ∧
  qinv B w ⇒
  qinv (B ++ ebind w (EAccept l) r) w'
Proof
  strip_tac >> qpat_x_assum ‘ehdo _ _ _ _ = _’ mp_tac >> simp[ehdo_def, ep_accept_def] >>
  Cases_on ‘w.listening’ >> simp[] >>
  rename1 ‘w.listening = x :: xs’ >> PairCases_on ‘x’ >>
  ‘xs = []’ by (Cases_on ‘xs’ >> gvs[]) >> pop_assum SUBST_ALL_TAC >>
  Cases_on ‘x0 = l’ >> simp[] >> Cases_on ‘x2’ >> simp[]
  >- (strip_tac >> gvs[ebind_def] >> qpat_x_assum ‘qinv _ _’ mp_tac >> simp[qinv_def]) >>
  rename1 ‘ep_alloc w j’ >>
  Cases_on ‘ep_alloc w j’ >> simp[]
  >- (strip_tac >> gvs[ebind_def] >> qpat_x_assum ‘qinv _ _’ mp_tac >> simp[qinv_def]) >>
  rename1 ‘ep_alloc w j = SOME fw’ >> PairCases_on ‘fw’ >> simp[] >>
  strip_tac >> gvs[ebind_def] >>
  qpat_x_assum ‘ep_alloc _ _ = _’ mp_tac >> simp[ep_alloc_def] >> strip_tac >>
  gvs[] >> qpat_x_assum ‘qinv _ _’ mp_tac >> simp[qinv_def, AFUPDKEY_def] >>
  rpt strip_tac >> first_x_assum drule_all >> rw[] >> simp[]
QED

Theorem ehdo_qinv:
  ehdo lfd v (w, hs) x = SOME (r, (w', hs')) ∧ LENGTH w.listening ≤ 1 ∧ qinv B w ⇒
  qinv (B ++ ebind w x r) w'
Proof
  strip_tac >>
  Cases_on ‘∃l. x = EAccept l’
  >- (pop_assum strip_assume_tac >> qpat_x_assum ‘x = _’ SUBST_ALL_TAC >>
      irule ehdo_accept_qinv >> rpt (first_assum (irule_at Any))) >>
  irule qinv_frame >> qpat_assum ‘qinv _ _’ (irule_at Any) >>
  drule ehdo_cpa >> strip_tac >>
  qexists_tac ‘REPLICATE (LENGTH (conn_hdls [r])) T’ >> simp[EVERY_REPLICATE] >>
  irule ehdo_listening >> qpat_assum ‘ehdo _ _ _ _ = _’ (irule_at Any) >> gvs[]
QED

Theorem ehacts_qinv:
  ∀acts k (st : eworld # ehstate) rs st' B ps.
    ehacts lfd lv n k st acts = SOME (rs, st') ∧ gchinv lfd B ps st ∧ qinv B (FST st) ⇒
    qinv (B ++ ehbacts lfd lv n k st acts) (FST st')
Proof
  Induct >> simp[ehacts_def, ehbacts_def] >> rpt gen_tac >>
  PairCases_on ‘st’ >> simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  PairCases_on ‘st1'’ >>
  ‘LENGTH st0.listening ≤ 1’ by fs[gchinv_def] >>
  drule_all ehdo_gchinv >> strip_tac >>
  drule_all ehdo_qinv >> strip_tac >>
  REWRITE_TAC[APPEND_ASSOC] >>
  first_x_assum irule >> simp[] >> qexists_tac ‘ps ++ [(h, r)]’ >> simp[]
QED

Theorem ep_deliver_qinv:
  LENGTH w.listening ≤ 1 ∧ qinv B w ⇒ qinv B (ep_deliver w e)
Proof
  strip_tac >> ‘cext w (ep_deliver w e)’ by simp[ep_deliver_cext] >>
  Cases_on ‘∃a. e = Incoming a’
  >- (pop_assum strip_assume_tac >> qpat_x_assum ‘e = _’ SUBST_ALL_TAC >>
      simp[ep_deliver_def] >>
      Cases_on ‘w.listening’ >> simp[] >>
      rename1 ‘w.listening = x :: xs’ >> PairCases_on ‘x’ >>
      ‘xs = []’ by (Cases_on ‘xs’ >> gvs[]) >>
      rw[] >> simp[AFUPDKEY_def] >>
      qpat_x_assum ‘qinv _ _’ mp_tac >> simp[qinv_def] >> rpt strip_tac >>
      Cases_on ‘j < LENGTH w.chans’
      >- (first_x_assum (qspec_then ‘j’ mp_tac) >> gvs[EL_APPEND1]) >>
      ‘j = LENGTH w.chans’ by decide_tac >> simp[]) >>
  ‘B = B ++ []’ by simp[] >> pop_assum SUBST1_TAC >>
  irule qinv_frame >> qpat_assum ‘qinv _ _’ (irule_at Any) >>
  qexists_tac ‘[]’ >> simp[] >>
  Cases_on ‘e’ >> gvs[ep_deliver_def] >> rw[] >> simp[upd_chan_cpa] >> simp[upd_chan_def]
QED

Theorem ep_deliver_listening_LENGTH:
  LENGTH (ep_deliver w e).listening = LENGTH w.listening
Proof
  Cases_on ‘e’ >> rw[ep_deliver_def, upd_chan_def] >> every_case_tac >>
  simp[AFUPDKEY_def] >> Induct_on ‘w.listening’ >> rw[] >>
  qpat_x_assum ‘_ = w.listening’ (SUBST_ALL_TAC o SYM) >> simp[AFUPDKEY_def] >>
  PairCases_on ‘h’ >> rw[AFUPDKEY_def] >> pairarg_tac >> simp[]
QED

Theorem FOLDL_deliver_qinv:
  ∀es w. LENGTH w.listening ≤ 1 ∧ qinv B w ⇒ qinv B (FOLDL ep_deliver w es)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >> conj_tac
  >- simp[ep_deliver_listening_LENGTH]
  >> irule ep_deliver_qinv >> simp[]
QED

Theorem ehpoll_qinv:
  ehpoll lfd hs hfds w = (rdy, w', hs') ∧ LENGTH w.listening ≤ 1 ∧ qinv B w ⇒ qinv B w'
Proof
  simp[ehpoll_def, ep_tick_def] >> strip_tac >> gvs[] >> irule FOLDL_deliver_qinv >>
  gvs[qinv_def]
QED

(* MAIN: at every round boundary, a channel without a peer address is bound
   or queued *)
Theorem ehrounds_qinv:
  W0.chans = [] ∧ W0.open_fds = [] ∧ alloc_ok W0.alloc ∧ LENGTH W0.listening ≤ 1 ∧
  EVERY (λ(l, a, q). q = []) W0.listening ∧
  (∀n. ehacts lfd lv n 0 (ehst lfd lv ifds m W0 n)
         (new_actions (log_of m) (ehhist lfd lv ifds m W0 n)) ≠ NONE) ⇒
  ∀n. qinv (ehbinds lfd lv ifds m W0 n) (FST (ehst lfd lv ifds m W0 n))
Proof
  strip_tac >> drule_all ehrounds_gchinv >> strip_tac >> Induct
  >- simp[ehst_def, ehrounds_def, qinv_def] >>
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
  drule ehacts_qinv >>
  disch_then (qspecl_then [‘ehbinds lfd lv ifds m W0 n’, ‘hl_pairs m h’] mp_tac) >>
  simp[] >> strip_tac >>
  irule ehpoll_qinv >> qpat_assum ‘ehpoll _ _ _ _ = _’ (irule_at Any) >>
  fs[gchinv_def]
QED

(* ------------------------------------------------------------------------
   Through E1: on the world built from the run, a raw accept episode j is,
   at each round boundary, bound or the one connection L1 holds (acq)
   ------------------------------------------------------------------------ *)

Theorem e1_acc_queued:
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧ MEM 0w (l0_used w0) ∧
  (∀n. SND (ecm lfd pol ifds m w0 n) + 1 < dimword (:64)) ∧
  (∀n. ehacts lfd (elv lfd pol ifds m w0) n 0
         (ehst lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) n)
         (new_actions (log_of m)
            (ehhist lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) n)) ≠ NONE) ∧
  erounds lfd pol ifds m (w0, einit) n = SOME (h, ws, evs, logs) ∧
  j < LENGTH (ep_conn evs) ∧ ¬EL j (ep_conn evs) ⇒
  MEM j (MAP FST (ehbinds lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) n)) ∨
  (FST (ehst lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) n)).listening =
    [(lfd, a, [j])]
Proof
  strip_tac >>
  qabbrev_tac ‘EW = FST (ehst lfd (elv lfd pol ifds m w0) ifds m (pew lfd a pol ifds m w0 calls) n)’ >>
  ‘MAP cpa EW.chans = ep_conn evs’
    by (qunabbrev_tac ‘EW’ >> mp_tac e1_roles >> impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
        disch_then drule >> simp[]) >>
  ‘j < LENGTH EW.chans ∧ ¬cpa (EL j EW.chans)’
    by (‘LENGTH EW.chans = LENGTH (ep_conn evs)’
          by (qpat_x_assum ‘MAP cpa _ = _’ (mp_tac o AP_TERM “LENGTH : bool list -> num”) >> simp[]) >>
        conj_tac >- simp[] >>
        ‘EL j (MAP cpa EW.chans) = EL j (ep_conn evs)’ by simp[] >>
        pop_assum mp_tac >> simp[EL_MAP]) >>
  mp_tac (Q.INST [‘W0’ |-> ‘pew lfd a pol ifds m w0 calls’, ‘lv’ |-> ‘elv lfd pol ifds m w0’]
            ehrounds_qinv) >>
  impl_tac
  >- (simp[pew_def, erun_alloc_ok] >> first_assum ACCEPT_TAC) >>
  disch_then (qspec_then ‘n’ mp_tac) >> simp[qinv_def] >>
  disch_then (qspec_then ‘j’ mp_tac) >> impl_tac >- (qunabbrev_tac ‘EW’ >> simp[]) >>
  strip_tac >- simp[] >> disj2_tac >>
  mp_tac l1ep_refines_ehl >> impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [‘n’, ‘h’, ‘ws’, ‘evs’, ‘logs’] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  drule ecm_count >> strip_tac >>
  qpat_x_assum ‘ev_rel _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [ev_rel_def]) >>
  qpat_x_assum ‘EXISTS _ _’ mp_tac >> qunabbrev_tac ‘EW’ >> asm_rewrite_tac [] >>
  Cases_on ‘(SND ws).p.acq’ >> simp[] >> Cases_on ‘t’ >> gvs[]
QED
