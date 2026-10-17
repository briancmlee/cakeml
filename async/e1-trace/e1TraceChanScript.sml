(*
  The shared E1 trace layer (close-v2's part (a2)): on the endpoint handle
  layer, generic in the program, each channel belongs to at most one
  handle, the one it was BOUND to when it was made (a connect) or taken
  (an accept), and what the channel was sent is what the history says the
  program wrote on that handle.

  The bindings are a function of the run (ehbinds: each action's, from
  the state it ran in), growing with n, so a channel's handle is fixed for
  the whole run (ehbinds_lookup_mono); a claim on the raw L0 trace can name an
  episode's handle, through E1's episode j = channel j (moonshotSentGlue).
*)
Theory e1TraceChan
Ancestors
  moonshotClient moonshotClientSpec endpointHLModel endpointWorld asyncHLModel socketV2FFI alist
  honestL1EPTotal
Libs
  preamble

(* ------------------------------------------------------------------------
   The bindings
   ------------------------------------------------------------------------ *)

(* The binding an action makes, from the world it ran in *)
Definition ebind_def:
  ebind (w : eworld) x r =
    case (x, r) of
    | (EConnect _, EConnected (SOME hd)) => [(LENGTH w.chans, hd)]
    | (EAccept l, EAccepted (SOME hd)) =>
        (case FILTER (λ(l', a, q). l' = l) w.listening of
         | (_, _, j :: _) :: _ => [(j, hd)]
         | _ => [])
    | _ => []
End

(* A round's bindings, action by action, as ehacts runs them *)
Definition ehbacts_def:
  ehbacts lfd (lv : num -> num -> num) (n : num) (k : num) st [] = [] ∧
  ehbacts lfd lv n k st (x :: acts) =
    case ehdo lfd (lv n k) st x of
    | NONE => []
    | SOME (r, st1) => ebind (FST st) x r ++ ehbacts lfd lv n (k + 1) st1 acts
End

(* The bindings of the first n rounds *)
Definition ehbinds_def:
  ehbinds lfd lv ifds m W0 0 = [] ∧
  ehbinds lfd lv ifds m W0 (SUC n) =
    ehbinds lfd lv ifds m W0 n ++
    ehbacts lfd lv n 0 (ehst lfd lv ifds m W0 n)
      (new_actions (log_of m) (ehhist lfd lv ifds m W0 n))
End

(* ------------------------------------------------------------------------
   The invariant
   ------------------------------------------------------------------------ *)

(* B: the bindings so far (channel, handle); ps: the history's pairs *)
Definition gchinv_def:
  gchinv lfd B ps (w : eworld, hs : ehstate) ⇔
    alloc_ok w.alloc ∧ hs.nxt < dimword (:64) ∧ LENGTH w.listening ≤ 1 ∧
    ALL_DISTINCT (MAP FST B) ∧ ALL_DISTINCT (MAP SND B) ∧
    (∀j hd. MEM (j, hd) B ⇒ j < LENGTH w.chans ∧ ∃k. k < hs.nxt ∧ hd = hdl lfd k) ∧
    (∀hd f. ALOOKUP hs.tbl hd = SOME f ⇒ ∃j. MEM (j, hd) B ∧ ALOOKUP w.open_fds f = SOME j) ∧
    (∀j. j < LENGTH w.chans ⇒
         (EL j w.chans).sent = case ALOOKUP B j of SOME hd => hl_sent hd ps | NONE => []) ∧
    (∀hd. ¬MEM hd (MAP SND B) ⇒ hl_sent hd ps = []) ∧
    EVERY (λ(l, a, q). ALL_DISTINCT q ∧
                       ∀j. MEM j q ⇒ j < LENGTH w.chans ∧ ¬MEM j (MAP FST B)) w.listening
End

Theorem hdl_lt_11:
  i < n ∧ j < n ∧ n < dimword (:64) ∧ hdl lfd i = hdl lfd j ⇒ i = j
Proof
  rpt strip_tac >> qspecl_then [‘i’, ‘j’, ‘lfd’] mp_tac (Q.GENL [‘i’, ‘j’, ‘lfd’] hdl_11) >>
  impl_tac >- (rpt conj_tac >> TRY (first_x_assum ACCEPT_TAC) >> decide_tac) >> simp[]
QED

Theorem upd_chan_simps[simp]:
  LENGTH (upd_chan j g w).chans = LENGTH w.chans ∧
  (upd_chan j g w).open_fds = w.open_fds ∧
  (upd_chan j g w).alloc = w.alloc ∧
  (upd_chan j g w).listening = w.listening ∧
  (j < LENGTH w.chans ⇒
   EL i (upd_chan j g w).chans = if i = j then g (EL j w.chans) else EL i w.chans)
Proof
  rw[upd_chan_def, EL_LUPDATE]
QED

(* Two bindings with one channel, or one handle, are one *)
Theorem bind_fun:
  ALL_DISTINCT (MAP FST B) ∧ MEM (j, h) B ∧ MEM (j, h') B ⇒ h' = h
Proof
  rpt strip_tac >> imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >> gvs[]
QED

Theorem bind_inj:
  ALL_DISTINCT (MAP SND B) ∧ MEM (j, h) B ∧ MEM (j', h) B ⇒ j' = j
Proof
  rpt strip_tac >>
  ‘ALL_DISTINCT (MAP FST (MAP (λ(x, y). (y, x)) B))’
    by (‘MAP FST (MAP (λ(x, y). (y, x)) B) = MAP SND B’
          by (simp[MAP_MAP_o] >> irule MAP_CONG >> simp[FORALL_PROD]) >> simp[]) >>
  ‘MEM (h, j) (MAP (λ(x, y). (y, x)) B) ∧ MEM (h, j') (MAP (λ(x, y). (y, x)) B)’
    by (simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >> gvs[]
QED

(* An action that sends nothing, binds nothing, and leaves the channels'
   bytes, the listeners and the allocator alone; the open handles keep
   their fds (or are forgotten) *)
Theorem gchinv_frame:
  gchinv lfd B ps (w, hs) ∧
  LENGTH w'.chans = LENGTH w.chans ∧
  (∀j. j < LENGTH w.chans ⇒ (EL j w'.chans).sent = (EL j w.chans).sent) ∧
  w'.alloc = w.alloc ∧ w'.listening = w.listening ∧ hs'.nxt = hs.nxt ∧
  (∀hd. hl_sent hd ps' = hl_sent hd ps) ∧
  (∀hd f. ALOOKUP hs'.tbl hd = SOME f ⇒
          ALOOKUP hs.tbl hd = SOME f ∧ ALOOKUP w'.open_fds f = ALOOKUP w.open_fds f) ⇒
  gchinv lfd B ps' (w', hs')
Proof
  simp[gchinv_def] >> strip_tac >> conj_tac
  >- (rpt strip_tac >> first_x_assum drule >> simp[])
  >> rpt strip_tac >>
  qpat_x_assum ‘∀hd f. ALOOKUP hs'.tbl hd = SOME f ⇒ _’ drule >> strip_tac >>
  qpat_x_assum ‘∀hd f. ALOOKUP hs.tbl hd = SOME f ⇒ _’ drule >> metis_tac[]
QED

(* Forgetting handle h, whose fd f is closed *)
Theorem eh_del_close_tbl:
  gchinv lfd B ps (w, hs) ∧ ALOOKUP hs.tbl h = SOME f ∧
  ALOOKUP (eh_del h hs).tbl hd = SOME f' ⇒
  ALOOKUP hs.tbl hd = SOME f' ∧ ALOOKUP (ADELKEY f w.open_fds) f' = ALOOKUP w.open_fds f'
Proof
  simp[eh_del_def, ALOOKUP_ADELKEY] >> strip_tac >>
  Cases_on ‘hd = h’ >> gvs[] >>
  simp[ALOOKUP_ADELKEY] >> rw[] >>
  gvs[gchinv_def] >>
  first_assum (qspecl_then [‘h’, ‘f’] mp_tac) >>
  first_x_assum (qspecl_then [‘hd’, ‘f’] mp_tac) >> simp[] >> rpt strip_tac >> gvs[] >>
  metis_tac[bind_fun]
QED

(* ------------------------------------------------------------------------
   Each action
   ------------------------------------------------------------------------ *)

(* What reads, refusal reports and closes leave *)
Definition wkeeps_def:
  wkeeps (w : eworld) w1 ⇔
    LENGTH w1.chans = LENGTH w.chans ∧
    (∀j. j < LENGTH w.chans ⇒ (EL j w1.chans).sent = (EL j w.chans).sent) ∧
    w1.alloc = w.alloc ∧ w1.listening = w.listening
End

Theorem wkeeps_trans:
  wkeeps w w1 ∧ wkeeps w1 w2 ⇒ wkeeps w w2
Proof
  rw[wkeeps_def]
QED

Theorem ep_conn_err_keeps:
  ep_conn_err f w = SOME w1 ⇒ wkeeps w w1 ∧ w1.open_fds = w.open_fds
Proof
  rw[ep_conn_err_def, AllCaseEqs()] >> gvs[ep_chan_of_def, AllCaseEqs()] >>
  rw[wkeeps_def] >> rw[]
QED

Theorem ep_read_keeps:
  ep_read f n w = SOME (x, w1) ⇒ wkeeps w w1 ∧ w1.open_fds = w.open_fds
Proof
  rw[ep_read_def, AllCaseEqs()] >> gvs[ep_chan_of_def, AllCaseEqs()] >>
  rw[wkeeps_def] >> rw[]
QED

Theorem ep_close_keeps:
  ep_close f w = SOME w1 ⇒ wkeeps w w1 ∧ w1.open_fds = ADELKEY f w.open_fds
Proof
  rw[ep_close_def, AllCaseEqs()] >> gvs[ep_chan_of_def, AllCaseEqs()] >>
  rw[wkeeps_def] >> rw[upd_chan_def, EL_LUPDATE] >> rw[]
QED

(* Closing h's fd and forgetting h *)
Theorem gchinv_close:
  gchinv lfd B ps (w, hs) ∧ ALOOKUP hs.tbl h = SOME f ∧
  wkeeps w w1 ∧ w1.open_fds = w.open_fds ∧ ep_close f w1 = SOME w2 ∧
  (∀hd. hl_sent hd ps' = hl_sent hd ps) ⇒
  gchinv lfd B ps' (w2, eh_del h hs)
Proof
  strip_tac >> drule ep_close_keeps >> strip_tac >>
  ‘wkeeps w w2’ by metis_tac[wkeeps_trans] >>
  irule gchinv_frame >> qexistsl_tac [‘hs’, ‘ps’, ‘w’] >> gvs[wkeeps_def] >>
  simp[eh_del_def] >> rpt gen_tac >> strip_tac >>
  ‘ALOOKUP (eh_del h hs).tbl hd = SOME f'’ by simp[eh_del_def] >>
  drule_all eh_del_close_tbl >> simp[]
QED

Theorem ehdo_read_gchinv:
  ehdo lfd v (w, hs) (ERead h n) = SOME (r, (w', hs')) ∧ gchinv lfd B ps (w, hs) ⇒
  gchinv lfd B (ps ++ [(ERead h n, r)]) (w', hs')
Proof
  strip_tac >>
  ‘∀hd. hl_sent hd (ps ++ [(ERead h n, r)]) = hl_sent hd ps’ by (Cases_on ‘r’ >> simp[]) >>
  qpat_x_assum ‘ehdo _ _ _ _ = _’ mp_tac >> simp[ehdo_def] >>
  Cases_on ‘ALOOKUP hs.tbl h’ >> simp[] >>
  TRY (strip_tac >> gvs[] >> irule gchinv_frame >> qexistsl_tac [‘hs’, ‘ps’, ‘w’] >> simp[] >>
       NO_TAC) >>
  rename1 ‘ALOOKUP hs.tbl h = SOME f’ >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  TRY (drule ep_conn_err_keeps >> strip_tac) >>
  TRY (drule ep_read_keeps >> strip_tac) >>
  FIRST [irule gchinv_close >> simp[] >> metis_tac[wkeeps_def] >> NO_TAC,
         irule gchinv_frame >> qexistsl_tac [‘hs’, ‘ps’, ‘w’] >> gvs[wkeeps_def]]
QED

(* A bound handle's channel *)
Theorem tbl_chan:
  gchinv lfd B ps (w, hs) ∧ ALOOKUP hs.tbl h = SOME f ⇒
  ∃j. MEM (j, h) B ∧ ALOOKUP B j = SOME h ∧ j < LENGTH w.chans ∧
      ALOOKUP w.open_fds f = SOME j ∧ ep_chan_of w f = SOME j
Proof
  simp[gchinv_def] >> strip_tac >> first_x_assum drule >> strip_tac >>
  qexists_tac ‘j’ >> simp[] >>
  ‘j < LENGTH w.chans’ by metis_tac[] >>
  simp[ep_chan_of_def] >> irule ALOOKUP_ALL_DISTINCT_MEM >> simp[]
QED

Theorem ehdo_write_gchinv:
  ehdo lfd v (w, hs) (EWrite h bs) = SOME (r, (w', hs')) ∧ gchinv lfd B ps (w, hs) ⇒
  gchinv lfd B (ps ++ [(EWrite h bs, r)]) (w', hs')
Proof
  strip_tac >> qpat_x_assum ‘ehdo _ _ _ _ = _’ mp_tac >> simp[ehdo_def] >>
  Cases_on ‘ALOOKUP hs.tbl h’ >> simp[] >>
  TRY (strip_tac >> gvs[] >> irule gchinv_frame >> qexistsl_tac [‘hs’, ‘ps’, ‘w’] >> simp[] >>
       NO_TAC) >>
  rename1 ‘ALOOKUP hs.tbl h = SOME f’ >>
  rw[] >> pairarg_tac >> gvs[] >>
  drule_all tbl_chan >> strip_tac >>
  qpat_x_assum ‘ep_send _ _ _ = _’ mp_tac >> simp[ep_send_def] >> strip_tac >> gvs[] >>
  qpat_x_assum ‘gchinv _ _ _ _’ mp_tac >> simp[gchinv_def] >> strip_tac >> conj_tac
  >- (rpt strip_tac >> qpat_x_assum ‘∀j hd. MEM _ B ⇒ _’ drule >> simp[]) >>
  conj_tac
  >- (rw[] >> gvs[] >>
      Cases_on ‘ALOOKUP B j'’ >> simp[] >>
      rename1 ‘ALOOKUP B j' = SOME hd’ >>
      ‘MEM (j', hd) B’ by metis_tac[ALOOKUP_MEM] >>
      ‘hd ≠ h’ by (strip_tac >> gvs[] >> metis_tac[bind_inj]) >> simp[]) >>
  rpt strip_tac >> ‘hd ≠ h’ by (strip_tac >> gvs[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  simp[]
QED

Theorem hdln_suc_lt:
  hdln (w2n (lfd : word64)) n < dimword (:64) ⇒ n + 1 < dimword (:64)
Proof
  rw[hdln_def] >> Cases_on ‘lfd’ >> gvs[]
QED

(* The next handle is no bound one *)
Theorem gchinv_next_unbound:
  gchinv lfd B ps (w, hs) ∧ hs.nxt + 1 < dimword (:64) ⇒ ¬MEM (hdl lfd hs.nxt) (MAP SND B)
Proof
  rw[gchinv_def, MEM_MAP, FORALL_PROD] >> CCONTR_TAC >> gvs[] >>
  rename1 ‘MEM (j, hdl lfd hs.nxt) B’ >>
  qpat_x_assum ‘∀j hd. MEM (j, hd) B ⇒ _’ (qspecl_then [‘j’, ‘hdl lfd hs.nxt’] mp_tac) >>
  simp[] >> CCONTR_TAC >> gvs[] >>
  ‘hs.nxt = k’
    by (qspecl_then [‘hs.nxt’, ‘k’, ‘hs.nxt + 1’, ‘lfd’] mp_tac
          (Q.GENL [‘i’, ‘j’, ‘n’, ‘lfd’] hdl_lt_11) >> simp[]) >>
  gvs[]
QED

(* Binding an unbound channel j, in a world that may have grown by
   channels sent nothing, to the next handle, with a fresh fd *)
Theorem gchinv_bind:
  gchinv lfd B ps (w, hs) ∧ hdln (w2n lfd) hs.nxt < dimword (:64) ∧
  LENGTH w.chans ≤ LENGTH w'.chans ∧ j < LENGTH w'.chans ∧ ¬MEM j (MAP FST B) ∧
  (∀i. i < LENGTH w'.chans ⇒
       (EL i w'.chans).sent = if i < LENGTH w.chans then (EL i w.chans).sent else []) ∧
  w'.alloc = w.alloc ∧ LENGTH w'.listening ≤ 1 ∧
  EVERY (λ(l, a, q). ALL_DISTINCT q ∧
                     ∀i. MEM i q ⇒ i < LENGTH w'.chans ∧ ¬MEM i (MAP FST B) ∧ i ≠ j)
        w'.listening ∧
  ¬MEM f (MAP FST w.open_fds) ∧ w'.open_fds = (f, j) :: w.open_fds ∧
  hs'.tbl = (hdl lfd hs.nxt, f) :: hs.tbl ∧ hs'.nxt = hs.nxt + 1 ∧
  (∀hd. hl_sent hd ps' = hl_sent hd ps) ⇒
  gchinv lfd (B ++ [(j, hdl lfd hs.nxt)]) ps' (w', hs')
Proof
  strip_tac >>
  ‘hs.nxt + 1 < dimword (:64)’ by (irule hdln_suc_lt >> metis_tac[]) >>
  drule_all gchinv_next_unbound >> strip_tac >>
  ‘(EL j w'.chans).sent = []’
    by (qpat_x_assum ‘∀i. i < LENGTH w'.chans ⇒ _’ (qspec_then ‘j’ mp_tac) >>
        rw[] >> gvs[gchinv_def] >>
        qpat_x_assum ‘∀j. j < LENGTH w.chans ⇒ (EL j w.chans).sent = _’ (qspec_then ‘j’ mp_tac) >>
        simp[] >> CASE_TAC >> imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP, FORALL_PROD] >>
        metis_tac[FST]) >>
  qpat_x_assum ‘gchinv _ _ _ _’ mp_tac >> rewrite_tac[gchinv_def] >> strip_tac >>
  rpt conj_tac
  >- gvs[]
  >- gvs[]
  >- gvs[]
  >- gvs[ALL_DISTINCT_APPEND]
  >- gvs[ALL_DISTINCT_APPEND]
  >- (rpt gen_tac >> simp[] >> strip_tac >> gvs[]
      >- (qpat_x_assum ‘∀j hd. MEM (j, hd) B ⇒ _’ drule >> strip_tac >> simp[] >>
          qexists_tac ‘k’ >> simp[])
      >> qexists_tac ‘hs.nxt’ >> simp[])
  >- (rpt gen_tac >> qpat_x_assum ‘hs'.tbl = _’ SUBST1_TAC >> simp[] >>
      IF_CASES_TAC >> strip_tac >- gvs[] >>
      qpat_x_assum ‘∀hd f. ALOOKUP hs.tbl hd = SOME f ⇒ _’ drule >> strip_tac >>
      rename1 ‘ALOOKUP w.open_fds g = SOME i’ >>
      ‘g ≠ f’ by (strip_tac >> gvs[] >> imp_res_tac ALOOKUP_MEM >>
                  gvs[MEM_MAP, FORALL_PROD] >> metis_tac[FST]) >>
      qexists_tac ‘i’ >> simp[])
  >- (rpt strip_tac >> rename1 ‘i < LENGTH w'.chans’ >>
      ‘ALOOKUP B j = NONE’ by simp[ALOOKUP_NONE] >>
      simp[ALOOKUP_APPEND] >>
      Cases_on ‘i = j’
      >- (simp[] >> qpat_x_assum ‘w'.chans❲j❳.sent = []’ SUBST1_TAC >>
          qpat_x_assum ‘∀hd. hl_sent hd ps' = _’ (fn th => REWRITE_TAC [th]) >>
          qpat_x_assum ‘∀hd. ¬MEM hd (MAP SND B) ⇒ _’ (drule_then ACCEPT_TAC o GSYM)) >>
      simp[] >>
      qpat_x_assum ‘∀i. i < LENGTH w'.chans ⇒ _’ (qspec_then ‘i’ mp_tac) >> simp[] >>
      IF_CASES_TAC >> simp[]
      >- (qpat_x_assum ‘∀j. j < LENGTH w.chans ⇒ _’ (qspec_then ‘i’ mp_tac) >> simp[] >>
          CASE_TAC >> simp[]) >>
      ‘ALOOKUP B i = NONE’ suffices_by simp[] >>
      simp[ALOOKUP_NONE, MEM_MAP, FORALL_PROD] >> rpt strip_tac >>
      qpat_x_assum ‘∀j hd. MEM (j, hd) B ⇒ _’ drule >> simp[])
  >- (rpt strip_tac >> gvs[])
  >> gvs[]
QED

Theorem ehdo_connect_gchinv:
  ehdo lfd v (w, hs) (EConnect a) = SOME (r, (w', hs')) ∧ gchinv lfd B ps (w, hs) ⇒
  gchinv lfd (B ++ ebind w (EConnect a) r) (ps ++ [(EConnect a, r)]) (w', hs')
Proof
  strip_tac >>
  ‘∀hd. hl_sent hd (ps ++ [(EConnect a, r)]) = hl_sent hd ps’ by (Cases_on ‘r’ >> simp[]) >>
  qpat_x_assum ‘ehdo _ _ _ _ = _’ mp_tac >> simp[ehdo_def] >>
  Cases_on ‘ep_connect a w’ >> rename1 ‘ep_connect a w = (fo, w1)’ >>
  Cases_on ‘fo’ >> simp[]
  >- (strip_tac >> gvs[ebind_def] >>
      qpat_x_assum ‘ep_connect _ _ = _’ mp_tac >>
      simp[ep_connect_def, ep_alloc_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
      irule gchinv_frame >> qexistsl_tac [‘hs’, ‘ps’, ‘w’] >> simp[]) >>
  rename1 ‘ep_connect a w = (SOME f, w1)’ >> strip_tac >> gvs[ebind_def] >>
  qpat_x_assum ‘ep_connect _ _ = _’ mp_tac >>
  simp[ep_connect_def, ep_alloc_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule gchinv_bind >> disch_then irule >> simp[eh_new_def] >>
  qpat_assum ‘gchinv _ _ _ _’ (strip_assume_tac o REWRITE_RULE [gchinv_def]) >>
  rpt conj_tac >>
  FIRST [
    first_assum ACCEPT_TAC,
    qpat_x_assum ‘alloc_ok _’ mp_tac >> simp[alloc_ok_def] >>
    disch_then drule >> simp[ep_used_def] >> NO_TAC,
    simp[MEM_MAP, FORALL_PROD] >> rpt strip_tac >>
    qpat_x_assum ‘∀j hd. MEM (j, hd) B ⇒ _’ drule >> simp[] >> NO_TAC,
    rw[EL_APPEND1, EL_APPEND2] >> ‘i = LENGTH w.chans’ by decide_tac >>
    simp[EL_APPEND2, new_chan_def] >> NO_TAC,
    qpat_x_assum ‘EVERY _ w.listening’ mp_tac >> simp[EVERY_MEM, FORALL_PROD] >>
    rpt strip_tac >> res_tac >> simp[] >> NO_TAC]
QED

Theorem ehdo_accept_gchinv:
  ehdo lfd v (w, hs) (EAccept l) = SOME (r, (w', hs')) ∧ gchinv lfd B ps (w, hs) ⇒
  gchinv lfd (B ++ ebind w (EAccept l) r) (ps ++ [(EAccept l, r)]) (w', hs')
Proof
  strip_tac >>
  ‘∀hd. hl_sent hd (ps ++ [(EAccept l, r)]) = hl_sent hd ps’ by (Cases_on ‘r’ >> simp[]) >>
  qpat_x_assum ‘ehdo _ _ _ _ = _’ mp_tac >> simp[ehdo_def, ep_accept_def] >>
  qpat_assum ‘gchinv _ _ _ _’ (strip_assume_tac o REWRITE_RULE [gchinv_def]) >>
  Cases_on ‘w.listening’ >> simp[] >>
  rename1 ‘w.listening = x :: xs’ >> PairCases_on ‘x’ >>
  ‘xs = []’ by (Cases_on ‘xs’ >> gvs[]) >>
  rw[] >> gvs[AllCaseEqs(), ebind_def] >>
  TRY (irule gchinv_frame >> qexistsl_tac [‘hs’, ‘ps’, ‘w’] >> simp[] >> NO_TAC) >>
  gvs[ep_alloc_def] >>
  drule gchinv_bind >> disch_then irule >> simp[eh_new_def, AFUPDKEY_def] >>
  qpat_x_assum ‘alloc_ok _’ mp_tac >> simp[alloc_ok_def] >>
  disch_then drule >> simp[ep_used_def]
QED

Theorem ebind_simps[simp]:
  ebind w (ERead h n) r = [] ∧ ebind w (EWrite h bs) r = [] ∧ ebind w (ELevel h) r = []
Proof
  Cases_on ‘r’ >> simp[ebind_def]
QED

Theorem ehdo_gchinv:
  ehdo lfd v (w, hs) x = SOME (r, (w', hs')) ∧ gchinv lfd B ps (w, hs) ⇒
  gchinv lfd (B ++ ebind w x r) (ps ++ [(x, r)]) (w', hs')
Proof
  Cases_on ‘x’ >> strip_tac
  >- (drule_all ehdo_accept_gchinv >> simp[])
  >- (drule_all ehdo_read_gchinv >> simp[])
  >- (drule_all ehdo_write_gchinv >> simp[])
  >- (drule_all ehdo_connect_gchinv >> simp[])
  >> qpat_x_assum ‘ehdo _ _ _ _ = _’ mp_tac >> simp[ehdo_def] >> strip_tac >> gvs[] >>
  irule gchinv_frame >> simp[] >> qexistsl_tac [‘hs’, ‘ps’, ‘w’] >> simp[]
QED

Theorem ehacts_gchinv:
  ∀acts k (st : eworld # ehstate) rs st' B ps.
    ehacts lfd lv n k st acts = SOME (rs, st') ∧ gchinv lfd B ps st ⇒
    gchinv lfd (B ++ ehbacts lfd lv n k st acts) (ps ++ ZIP (acts, rs)) st'
Proof
  Induct >> simp[ehacts_def, ehbacts_def] >> rpt gen_tac >>
  PairCases_on ‘st’ >> simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  PairCases_on ‘st1'’ >> drule_all ehdo_gchinv >> strip_tac >>
  ‘ps ++ (h,r)::ZIP (acts,rs') = (ps ++ [(h,r)]) ++ ZIP (acts,rs')’ by simp[] >>
  pop_assum SUBST1_TAC >> REWRITE_TAC[APPEND_ASSOC] >>
  first_x_assum irule >> simp[]
QED

(* ------------------------------------------------------------------------
   The poll
   ------------------------------------------------------------------------ *)

(* An arrival: a new channel (an incoming connection, queued unbound) or
   a change to a channel that leaves what it was sent *)
Theorem ep_deliver_gchinv:
  gchinv lfd B ps (w, hs) ⇒ gchinv lfd B ps (ep_deliver w e, hs)
Proof
  strip_tac >> Cases_on ‘e’ >> simp[ep_deliver_def] >>
  TRY (rw[] >> irule gchinv_frame >> qexistsl_tac [‘hs’, ‘ps’, ‘w’] >> simp[] >>
       rw[] >> NO_TAC) >>
  qpat_assum ‘gchinv _ _ _ _’ (strip_assume_tac o REWRITE_RULE [gchinv_def]) >>
  Cases_on ‘w.listening’ >> simp[] >>
  rename1 ‘w.listening = x :: xs’ >> PairCases_on ‘x’ >>
  ‘xs = []’ by (Cases_on ‘xs’ >> gvs[]) >>
  rw[] >> gvs[AFUPDKEY_def] >>
  rewrite_tac[gchinv_def] >> simp[] >>
  ‘¬MEM (LENGTH w.chans) (MAP FST B)’
    by (simp[MEM_MAP, FORALL_PROD] >> rpt strip_tac >>
        qpat_x_assum ‘∀j hd. MEM (j, hd) B ⇒ _’ drule >> simp[]) >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum ‘∀j hd. MEM (j, hd) B ⇒ _’ drule >> simp[])
  >- (rpt strip_tac >> Cases_on ‘j < LENGTH w.chans’ >> simp[EL_APPEND1] >>
      ‘j = LENGTH w.chans’ by decide_tac >>
      ‘ALOOKUP B j = NONE’ by simp[ALOOKUP_NONE] >>
      simp[EL_APPEND2, new_chan_def])
  >- (simp[ALL_DISTINCT_APPEND] >> strip_tac >>
      qpat_x_assum ‘∀j. MEM j x2 ⇒ _’ drule >> simp[])
  >> rpt strip_tac >> gvs[] >>
  qpat_x_assum ‘∀j. MEM j x2 ⇒ _’ drule >> simp[]
QED

Theorem FOLDL_deliver_gchinv:
  ∀es w. gchinv lfd B ps (w, hs) ⇒ gchinv lfd B ps (FOLDL ep_deliver w es, hs)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  irule ep_deliver_gchinv >> simp[]
QED

Theorem ep_tick_gchinv:
  gchinv lfd B ps (w, hs) ⇒ gchinv lfd B ps (ep_tick w, hs)
Proof
  simp[ep_tick_def] >> strip_tac >> irule FOLDL_deliver_gchinv >>
  fs[gchinv_def] >> metis_tac[]
QED

Theorem ehpoll_gchinv:
  ehpoll lfd hs hfds w = (rdy, w', hs') ∧ gchinv lfd B ps (w, hs) ⇒
  gchinv lfd B ps (w', hs')
Proof
  simp[ehpoll_def] >> strip_tac >> gvs[] >>
  drule ep_tick_gchinv >> strip_tac >> fs[gchinv_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The run
   ------------------------------------------------------------------------ *)

Theorem ehrounds_gchinv:
  W0.chans = [] ∧ W0.open_fds = [] ∧ alloc_ok W0.alloc ∧ LENGTH W0.listening ≤ 1 ∧
  EVERY (λ(l, a, q). q = []) W0.listening ∧
  (∀n. ehacts lfd lv n 0 (ehst lfd lv ifds m W0 n)
         (new_actions (log_of m) (ehhist lfd lv ifds m W0 n)) ≠ NONE) ⇒
  ∀n. gchinv lfd (ehbinds lfd lv ifds m W0 n) (hl_pairs m (ehhist lfd lv ifds m W0 n))
             (ehst lfd lv ifds m W0 n)
Proof
  strip_tac >> Induct
  >- (simp[ehst_def, ehhist_def, ehrounds_def, ehbinds_def, gchinv_def, ehinit_def,
           hl_pairs_def] >>
      qpat_x_assum ‘EVERY _ _’ mp_tac >> simp[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >> res_tac >> gvs[]) >>
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
  drule_all ehpoll_gchinv >> simp[]
QED

(* The bindings only grow, so a channel's handle, once bound, stays *)
Theorem ehbinds_prefix:
  ∀d n. ehbinds lfd lv ifds m W0 n ≼ ehbinds lfd lv ifds m W0 (n + d)
Proof
  Induct >> simp[] >> rpt gen_tac >>
  ‘n + SUC d = SUC (n + d)’ by decide_tac >> pop_assum SUBST1_TAC >>
  simp[ehbinds_def] >> irule IS_PREFIX_TRANS >>
  qexists_tac ‘ehbinds lfd lv ifds m W0 (n + d)’ >> simp[]
QED

Theorem ehbinds_lookup_mono:
  ALOOKUP (ehbinds lfd lv ifds m W0 n) j = SOME hd ∧ n ≤ n' ⇒
  ALOOKUP (ehbinds lfd lv ifds m W0 n') j = SOME hd
Proof
  strip_tac >>
  qspecl_then [‘n' - n’, ‘n’] mp_tac ehbinds_prefix >>
  ‘n + (n' - n) = n'’ by decide_tac >> simp[IS_PREFIX_APPEND] >>
  strip_tac >> simp[ALOOKUP_APPEND]
QED
