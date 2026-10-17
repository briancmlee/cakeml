(*
  Route (d), S4 (design/46): echo_l0_safe.  Every finite prefix of the
  program's trace lies between the end of some round and the end of the
  next (the loop's rounds may be empty once it stops for lack of handle
  room); at a round boundary and inside a round, what each episode sent is
  a prefix of what it received (honestEchoL0Run's round_safe).
*)
Theory honestEchoL0Safe
Ancestors
  llist ffi honestL0 honestL0World honestL0WorldProps honestL0Rely
  asyncHLModel honestL1Model honestL1Steps honestL1PFModel
  asyncM3World honestEchoL0Spec honestEchoL0Trace honestEchoL0Events
  honestEchoL0Model honestEchoL0Inv honestEchoL0Round honestEchoL0Out honestEchoL0Run
  asyncCore asyncLevel1 asyncTranscript honestL1PFProg honestL1PFSpec
  asyncServer asyncServerSafety asyncM4GTrans
  honestEchoL0Prog honestEchoL0Main honestEchoL0Sem honestL1PFInv honestL1Inv
Libs
  preamble

Theorem FLAT_GENLIST_mono[local]:
  ∀d n. FLAT (GENLIST f n) ≼ FLAT (GENLIST f (n + d))
Proof
  Induct >> simp[] >> rpt gen_tac >>
  first_x_assum (qspec_then ‘n’ mp_tac) >>
  simp[GSYM ADD_SUC, GENLIST, SNOC_APPEND] >>
  rw[rich_listTheory.IS_PREFIX_APPEND] >> simp[]
QED

(* Every finite prefix of a trace made of rounds lies between the end of
   some round and the end of the next (rounds may be empty) *)
Theorem LPREFIX_rounds_any:
  LPREFIX (fromList evs) (LFLATTEN (LGENLIST (λi. fromList (f i)) NONE)) ⇒
  ∃n. FLAT (GENLIST f n) ≼ evs ∧ evs ≼ FLAT (GENLIST f (SUC n))
Proof
  strip_tac >>
  Cases_on ‘∃m. ¬(FLAT (GENLIST f m) ≼ evs)’
  >- (qpat_x_assum ‘∃m. _’ (strip_assume_tac o HO_MATCH_MP arithmeticTheory.WOP) >>
      rename1 ‘¬(FLAT (GENLIST f m) ≼ evs)’ >>
      Cases_on ‘m’ >> gvs[] >> rename1 ‘GENLIST f (SUC n)’ >>
      qexists_tac ‘n’ >> simp[] >>
      Cases_on ‘LENGTH evs ≤ LENGTH (FLAT (GENLIST f (SUC n)))’
      >- (irule LPREFIX_comparable >> metis_tac[rounds_LPREFIX]) >>
      ‘FLAT (GENLIST f (SUC n)) ≼ evs’
        by (irule LPREFIX_comparable >> simp[] >> metis_tac[rounds_LPREFIX]) >>
      gvs[]) >>
  gvs[] >>
  (* every round boundary is inside evs: the rounds are eventually empty *)
  ‘∃N. ∀p. N ≤ p ⇒ f p = []’
    by (CCONTR_TAC >> gvs[] >>
        ‘∀m. ∃n. m ≤ LENGTH (FLAT (GENLIST f n))’
          by (Induct >> simp[] >> gvs[] >>
              first_x_assum (qspec_then ‘n’ strip_assume_tac) >>
              qexists_tac ‘SUC p’ >> simp[GENLIST, SNOC_APPEND] >>
              ‘FLAT (GENLIST f n) ≼ FLAT (GENLIST f (n + (p − n)))’
                by simp[FLAT_GENLIST_mono] >>
              gvs[] >> imp_res_tac rich_listTheory.IS_PREFIX_LENGTH >>
              Cases_on ‘f p’ >> gvs[]) >>
        first_x_assum (qspec_then ‘SUC (LENGTH evs)’ strip_assume_tac) >>
        qpat_x_assum ‘∀m. FLAT _ ≼ evs’ (qspec_then ‘n’ assume_tac) >>
        imp_res_tac rich_listTheory.IS_PREFIX_LENGTH >> fs[]) >>
  qexists_tac ‘N’ >> simp[GENLIST, SNOC_APPEND] >>
  ‘LFLATTEN (LGENLIST (λi. fromList (f i)) NONE) = fromList (FLAT (GENLIST f N))’
    by (ONCE_REWRITE_TAC [Q.SPEC ‘N’ (Q.GEN ‘n’ LFLATTEN_LGENLIST_chunk)] >>
        ‘LFLATTEN (LGENLIST (λi. fromList (f (N + i))) NONE) = LNIL’
          by simp[LFLATTEN_EQ_NIL, every_LGENLIST] >>
        simp[LAPPEND_NIL_2ND]) >>
  gvs[LPREFIX_fromList, from_toList]
QED

(* S4 at a round boundary *)
Theorem boundary_safe:
  ri lfd (srelabel (server k)) (h, (w, ps), evs) ∧ hdln (w2n lfd) j < dimword (:64) ⇒
  ep_sn j (0, []) evs ≼ ep_rd j (0, []) evs
Proof
  strip_tac >> qpat_x_assum ‘ri _ _ _’ (strip_assume_tac o REWRITE_RULE [ri_def]) >>
  first_x_assum (qspec_then ‘j’ mp_tac) >> simp[] >> strip_tac >>
  ‘ep_sn j (0, []) evs ≼ hwritten (l1hdl lfd j) (texec (srelabel (server k)) h)’
    by (gvs[oi_def] >> imp_res_tac isPREFIX_APPEND_L) >>
  drule trans_texec >> strip_tac >>
  ‘ALL_DISTINCT (haccepted (trans (srelabel (server k)) h))’
    by (‘ALL_DISTINCT (GENLIST (λi. l1hdl lfd i) ps.b.nxt)’
          by (irule ALL_DISTINCT_hdl >> fs[]) >>
        qpat_assum ‘trans _ _ = _’ (fn th => REWRITE_TAC [th]) >>
        qpat_assum ‘haccepted (texec _ _) = _’
          (fn th => REWRITE_TAC [haccepted_APPEND, haccepted_NONE, th, APPEND_NIL]) >>
        first_assum ACCEPT_TAC) >>
  ‘hwritten (l1hdl lfd j) (trans (srelabel (server k)) h) =
   hread (l1hdl lfd j) (trans (srelabel (server k)) h)’
    by (irule server_handle_echo >> first_assum ACCEPT_TAC) >>
  ‘hwritten (l1hdl lfd j) (texec (srelabel (server k)) h) ≼
   hread (l1hdl lfd j) (texec (srelabel (server k)) h)’
    by (qpat_x_assum ‘hwritten _ (trans _ _) = _’ mp_tac >>
        qpat_assum ‘trans _ _ = _’ (fn th => REWRITE_TAC [th]) >>
        simp[hwritten_APPEND, hread_APPEND] >> strip_tac >>
        pop_assum (SUBST1_TAC o SYM) >> simp[]) >>
  irule isPREFIX_TRANS >>
  qexists_tac ‘hwritten (l1hdl lfd j) (texec (srelabel (server k)) h)’ >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule isPREFIX_TRANS >>
  qexists_tac ‘hread (l1hdl lfd j) (texec (srelabel (server k)) h)’ >>
  conj_tac >- first_assum ACCEPT_TAC >>
  fs[]
QED

(* An episode the prefix has not accepted has sent nothing *)
Theorem fresh_safe:
  LENGTH (l0_accepted pre) ≤ j ⇒ ep_sn j (0, []) pre = []
Proof
  strip_tac >> irule ep_fold_fresh >> simp[ep_ok_def, FST_l0_ep_st]
QED

Theorem prun_FLAT:
  (∀n. prounds_t lfd hw ifds m ws0 n ≠ NONE) ⇒
  ∀n. FLAT (GENLIST (pround_evs lfd hw ifds m ws0) n) = FST (SND (SND (prun lfd hw ifds m ws0 n)))
Proof
  strip_tac >> Induct >> simp[GENLIST, SNOC_APPEND] >>
  drule prun_SUC >> disch_then (qspec_then ‘n’ mp_tac) >> rw[] >> simp[]
QED

Theorem prun_ri:
  ri lfd (srelabel (server k)) ([], ws0, []) ∧
  (∀n. prounds_t lfd hw ifds (srelabel (server k)) ws0 n ≠ NONE) ⇒
  ∀n. ri lfd (srelabel (server k))
         (FST (prun lfd hw ifds (srelabel (server k)) ws0 n),
          FST (SND (prun lfd hw ifds (srelabel (server k)) ws0 n)),
          FST (SND (SND (prun lfd hw ifds (srelabel (server k)) ws0 n))))
Proof
  rpt strip_tac >> first_x_assum (qspec_then ‘n’ mp_tac) >>
  Cases_on ‘prounds_t lfd hw ifds (srelabel (server k)) ws0 n’ >> simp[prun_def] >>
  PairCases_on ‘x’ >> simp[] >> drule ri_echo >> disch_then drule >> simp[]
QED

(* ------------------------------------------------------------------------
   An episode not yet handed out has sent nothing (D31: no accept guard)
   ------------------------------------------------------------------------ *)

(* A fd L1 holds belongs to a handed-out episode *)
Theorem own_held:
  own_ok lfd (k, opn) ps ∧ (MEM f (MAP SND ps.b.tbl) ∨ MEM f ps.b.closing) ⇒
  ∃i. i < ps.b.nxt ∧ ALOOKUP opn f = SOME i
Proof
  rw[own_ok_def, MEM_MAP, EXISTS_PROD] >> res_tac >> metis_tac[]
QED

Theorem after_send_nfields[local]:
  (after_send f r st).tbl = st.tbl ∧ (after_send f r st).nxt = st.nxt ∧
  (after_send f r st).closing = st.closing
Proof
  rw[after_send_def] >> every_case_tac >> simp[set_outbox_def]
QED

(* The reap closes only: it sends nothing *)
Theorem l1_reap_sn:
  ∀fs w b w' b' evs.
    l1_reap fs (w, b) = SOME ((w', b'), evs) ∧ l0_rely w ⇒ ∀j s. ep_sn j s evs = []
Proof
  Induct >> simp[l1_reap_def, ep_fold_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  PairCases_on ‘ws’ >> drule l1_close_shape >> strip_tac >> gvs[] >>
  drule_all sys_close_event >> strip_tac >>
  ‘l0_rely ws0’ by (gvs[sys_close_def] >> metis_tac[l0_do_rely]) >>
  first_x_assum drule_all >> simp[ep_fold_def, ep_fold_APPEND]
QED

(* The flush sends from outboxes, which belong to held fds *)
Theorem l1_flush_sn:
  ∀fs w b w' b' evs.
    l1_flush fs (w, b) = SOME ((w', b'), evs) ∧ l0_rely w ∧ okb b ∧
    own_ok lfd (k, opn) (ps with b := b) ⇒
    ∀j. b.nxt ≤ j ⇒ ep_sn j (k, opn) evs = []
Proof
  Induct >> simp[l1_flush_def, ep_fold_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> simp[]
  >- (strip_tac >>
      first_x_assum (qspecl_then [‘w’, ‘b’, ‘w'’, ‘b'’, ‘evs’] mp_tac) >> simp[]) >>
  simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >> gvs[] >>
  rename1 ‘sys_send h _ w = SOME (out, w1, ev)’ >>
  drule_all sys_send_event >> strip_tac >>
  ‘MEM h (MAP SND b.tbl) ∨ MEM h b.closing’ by metis_tac[okb_held] >>
  ‘∃i. i < b.nxt ∧ ALOOKUP opn h = SOME i’
    by (mp_tac (Q.INST [‘ps’ |-> ‘ps with b := b’, ‘f’ |-> ‘h’] own_held) >> simp[]) >>
  ‘l0_rely w1’ by (gvs[sys_send_def] >> metis_tac[l0_do_rely]) >>
  ‘okb (after_send h (l0_res_of out) b)’ by (irule okb_after_send >> simp[]) >>
  ‘own_ok lfd (k, opn) (ps with b := after_send h (l0_res_of out) b)’
    by (mp_tac (Q.INST [‘ps'’ |-> ‘ps with b := after_send h (l0_res_of out) b’,
                        ‘ps’ |-> ‘ps with b := b’, ‘es’ |-> ‘(k, opn)’] own_ok_cong) >>
        simp[after_send_nfields]) >>
  first_x_assum (qspecl_then [‘w1’, ‘after_send h (l0_res_of out) b’, ‘w'’, ‘b'’, ‘evs'’]
    mp_tac) >>
  simp[after_send_nfields] >> strip_tac >>
  rpt strip_tac >> simp[ep_fold_def, l0_ep_step_def]
QED

(* One action: a send only through a handle in the table *)
Theorem pdo_sn:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ l0_rely w ∧ own_ok lfd (k, opn) ps ⇒
  ∀j. ps.b.nxt ≤ j ⇒ ep_sn j (k, opn) evs = []
Proof
  strip_tac >> Cases_on ‘a’
  >- (drule pdo_accept_in >> strip_tac >> gvs[ep_fold_def])
  >- (drule_all pdo_no_recv >> strip_tac >>
      qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def] >>
      rw[AllCaseEqs()] >> gvs[ep_fold_def] >>
      PairCases_on ‘z’ >> gvs[] >>
      drule l1_close_shape >> strip_tac >> gvs[] >>
      drule_all sys_close_event >> strip_tac >> simp[ep_fold_def]) >>
  qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def, PULL_EXISTS] >> rpt gen_tac >>
  PairCases_on ‘z’ >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum ‘l1do _ _ _ = _’ mp_tac >> simp[l1do_def] >>
  rw[AllCaseEqs()] >> gvs[ep_fold_def] >>
  drule_all sys_send_event >> strip_tac >>
  drule_all own_tbl_lookup >> strip_tac >>
  rpt strip_tac >> simp[ep_fold_def]
QED

(* The round's actions: a send only on an episode handed out by the end *)
Theorem pacts_sn:
  ∀acts w ps rs evs w' ps' opn.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ l0_rely w ∧
    own_ok lfd (k, opn) ps ∧ ps.b.nxt + naccepts acts < dimword (:64) ⇒
    ∀j. ps'.b.nxt ≤ j ⇒ ep_sn j (k, opn) evs = []
Proof
  Induct >> simp[pacts_def, ep_fold_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  PairCases_on ‘ws1’ >> rename1 ‘pdo lfd (w, ps) a = SOME (r, (w1, ps1), evs1)’ >>
  ‘ps.b.nxt < dimword (:64)’ by simp[] >>
  ‘ps1.b.nxt + naccepts acts < dimword (:64)’
    by (drule pdo_nxt_acc >>
        ‘naccepts (a :: acts) = naccepts [a] + naccepts acts’ by (Cases_on ‘a’ >> simp[]) >>
        fs[]) >>
  drule_all pdo_in >> strip_tac >>
  drule_all pdo_rely >> strip_tac >>
  drule pdo_nxt >> strip_tac >>
  drule pacts_nxt >> strip_tac >>
  Cases_on ‘l0_ep_st (k, opn) evs1’ >> gvs[] >>
  rpt strip_tac >> simp[ep_fold_APPEND] >> conj_tac
  >- (mp_tac (Q.INST [‘ps'’ |-> ‘ps1’, ‘w'’ |-> ‘w1’, ‘evs’ |-> ‘evs1’] pdo_sn) >>
      impl_tac >- fs[] >> disch_then irule >> fs[]) >>
  first_x_assum (qspecl_then [‘w1’, ‘ps1’, ‘rs'’, ‘evs'’, ‘w'’, ‘ps'’, ‘r'’] mp_tac) >>
  impl_tac >- fs[] >> disch_then irule >> fs[]
QED

Theorem l1p_b_id[local]:
  (ps : l1p) with b := ps.b = ps
Proof
  simp[l1p_component_equality]
QED

(* The tail of a round: sends only from outboxes *)
Theorem pf_tail_sn:
  pf_tail lfd hw hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ∧
  wown lfd w ps ∧ own_ok lfd (k, opn) ps ∧ LENGTH ps.acq ≤ 1 ∧
  ps.b.nxt < dimword (:64) ∧ okb ps.b ⇒
  ∀j. ps.b.nxt ≤ j ⇒ ep_sn j (k, opn) evs = []
Proof
  strip_tac >> qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >>
  simp[pf_tail_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  rename1 ‘l1_polls _ w = SOME (rv, w1, pevs)’ >>
  rename1 ‘l1_flush _ _ = SOME ((w2, b2), fevs)’ >>
  rename1 ‘pf_fetch _ _ _ _ = SOME ((w3, ps3'), log, gevs)’ >>
  rename1 ‘l1_reap _ _ = SOME ((w4, b4), cevs)’ >>
  ‘l0_rely w ∧ fds_lt w’ by gvs[wown_def] >>
  ‘ep_ok (k, opn)’ by gvs[own_ok_def] >>
  (* poll *)
  drule_all l1_polls_in >> disch_then (qspec_then ‘(k, opn)’ strip_assume_tac) >>
  ‘∀j s. ep_sn j s pevs = []’ by (drule_all polls_sn >> simp[]) >>
  drule_all l1_polls_wown >> strip_tac >>
  (* flush *)
  drule_all l1_flush_in >> disch_then (qspec_then ‘(k, opn)’ strip_assume_tac) >>
  ‘wown lfd w2 (ps with b := b2)’ by (irule l1_flush_wown >> metis_tac[]) >>
  ‘own_ok lfd (k, opn) (ps with b := ps.b)’ by simp[l1p_b_id] >>
  mp_tac (Q.SPECL [‘writable_fds rv’, ‘w1’, ‘ps.b’, ‘w2’, ‘b2’, ‘fevs’] l1_flush_sn) >>
  impl_tac >- fs[] >> strip_tac >>
  (* fetch *)
  ‘fds_lt w2 ∧ (∀f. MEM f (MAP SND b2.tbl) ∨ MEM f b2.closing ⇒ MEM f (l0_used w2))’
    by (gvs[wown_def, owned_def] >> metis_tac[]) >>
  qspecl_then [‘FILTER (λf. MEM f (in_fds (pf_poll_set lfd hw ps hs))) (readable_fds rv)’,
               ‘w2’, ‘ps with b := b2’, ‘k’, ‘opn’, ‘w3’, ‘ps3'’, ‘log’, ‘gevs’]
    mp_tac pf_fetch_obp >> simp[] >>
  (impl_tac >- (qpat_x_assum ‘∀f. MEM f (MAP SND b2.tbl) ∨ _ ⇒ _’ mp_tac >> gvs[])) >>
  strip_tac >>
  ‘own_ok lfd (k, opn) (ps with b := b2)’
    by (mp_tac (Q.INST [‘ps'’ |-> ‘ps with b := b2’, ‘es’ |-> ‘(k, opn)’] own_ok_cong) >>
        simp[]) >>
  drule pf_fetch_in >> disch_then (qspecl_then [‘k’, ‘opn’] mp_tac) >> simp[] >>
  impl_tac
  >- (rw[MEM_FILTER] >> TRY (drule in_fds_poll_set >> simp[] >> NO_TAC) >> fs[]) >>
  strip_tac >>
  (* reap *)
  ‘l0_rely w3’ by gvs[wown_def] >>
  drule_all l1_reap_sn >> strip_tac >>
  qpat_x_assum ‘_ = evs’ (SUBST_ALL_TAC o SYM) >>
  rpt strip_tac >> fs[ep_fold_APPEND]
QED

(* A round: a send only on an episode handed out by its end *)
Theorem pround_sn:
  pround lfd hw hs (w, ps) acts = SOME (sn, (w', ps'), log, evs) ∧
  wown lfd w ps ∧ own_ok lfd (k, opn) ps ∧ LENGTH ps.acq ≤ 1 ∧ okb ps.b ∧
  ps.b.nxt + naccepts acts < dimword (:64) ⇒
  ∀j. ps'.b.nxt ≤ j ⇒ ep_sn j (k, opn) evs = []
Proof
  strip_tac >> qpat_x_assum ‘pround _ _ _ _ _ = _’ mp_tac >>
  simp[pround_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  rename1 ‘pacts _ _ _ = SOME (rs, evs1, ws1)’ >> PairCases_on ‘ws1’ >>
  rename1 ‘pf_tail _ _ _ _ = SOME (rdy, _, log2, tevs)’ >>
  ‘l0_rely w’ by gvs[wown_def] >>
  drule_all pacts_in >> strip_tac >>
  drule_all pacts_wown >> strip_tac >>
  drule_all pacts_okb >> strip_tac >>
  drule pacts_nxt_acc >> strip_tac >>
  drule pacts_nxt >> strip_tac >>
  Cases_on ‘l0_ep_st (k, opn) evs1’ >> gvs[] >>
  rename1 ‘own_ok lfd (k, opn1) ws11’ >>
  ‘LENGTH ws11.acq ≤ 1’ by (Cases_on ‘acts’ >> gvs[own_ok_def]) >>
  ‘ws11.b.nxt < dimword (:64)’ by fs[] >>
  drule_all pf_tail_in >> strip_tac >>
  rpt strip_tac >> fs[ep_fold_APPEND] >> conj_tac
  >- (qspecl_then [‘acts’, ‘w’, ‘ps’, ‘rs’, ‘evs1’, ‘ws10’, ‘ws11’, ‘opn’] mp_tac pacts_sn >>
      impl_tac >- fs[] >> disch_then irule >> fs[]) >>
  mp_tac (Q.INST [‘w’ |-> ‘ws10’, ‘ps’ |-> ‘ws11’, ‘opn’ |-> ‘opn1’, ‘evs’ |-> ‘tevs’,
                  ‘log’ |-> ‘log2’] pf_tail_sn) >>
  impl_tac >- fs[] >> disch_then irule >> fs[]
QED

(* MAIN: along the run of the echo server, an episode not yet
   handed out has had nothing sent *)
Theorem unhanded_sn:
  ri lfd (srelabel (server k)) ([], ws0, []) ⇒
  ∀n h w ps evs logs.
    prounds_t lfd hw ifds (srelabel (server k)) ws0 n = SOME (h, (w, ps), evs, logs) ⇒
    ∀j. ps.b.nxt ≤ j ⇒ ep_sn j (0, []) evs = []
Proof
  strip_tac >> Induct >- (simp[prounds_t_def] >> rw[] >> simp[ep_fold_def]) >>
  rpt gen_tac >> simp[prounds_t_def] >>
  Cases_on ‘prounds_t lfd hw ifds (srelabel (server k)) ws0 n’ >> simp[] >>
  PairCases_on ‘x’ >> simp[] >>
  first_x_assum (qspecl_then [‘x0’, ‘x1’, ‘x2’, ‘x3’, ‘x4’] mp_tac) >> simp[] >> strip_tac >>
  ‘ri lfd (srelabel (server k)) (x0, (x1, x2), x3)’ by metis_tac[ri_echo] >>
  IF_CASES_TAC >> simp[] >- (
    simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >> gvs[] >>
    qabbrev_tac ‘acts = new_actions (log_of (srelabel (server k))) x0’ >>
    ‘x2.b.nxt + naccepts acts < dimword (:64)’ by gvs[hdl_room_def] >>
    qpat_x_assum ‘ri _ _ _’ (strip_assume_tac o REWRITE_RULE [ri_def]) >>
    Cases_on ‘l0_ep_st (0, []) x3’ >> rename1 ‘l0_ep_st _ x3 = (kk, opn)’ >> gvs[] >>
    ‘x2.b.nxt + naccepts acts < dimword (:64)’ by fs[] >>
    drule_all pround_acc >> strip_tac >>
    rpt strip_tac >> simp[ep_fold_APPEND] >>
    TRY (conj_tac >- (first_x_assum irule >> fs[])) >>
    qpat_x_assum ‘pround _ _ _ _ _ = _’
      (fn th => mp_tac (Q.INST [‘k’ |-> ‘kk’]
                         (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] pround_sn) th))) >>
    rpt (impl_tac >- fs[]) >> disch_then irule >> fs[]) >>
  rw[] >> gvs[]
QED

Theorem prun_unhanded:
  ri lfd (srelabel (server k)) ([], ws0, []) ∧
  (∀n. prounds_t lfd hw ifds (srelabel (server k)) ws0 n ≠ NONE) ⇒
  ∀n j. (SND (FST (SND (prun lfd hw ifds (srelabel (server k)) ws0 n)))).b.nxt ≤ j ⇒
        ep_sn j (0, []) (FST (SND (SND (prun lfd hw ifds (srelabel (server k)) ws0 n)))) = []
Proof
  strip_tac >> rpt gen_tac >> first_x_assum (qspec_then ‘n’ mp_tac) >>
  Cases_on ‘prounds_t lfd hw ifds (srelabel (server k)) ws0 n’ >> simp[prun_def] >>
  PairCases_on ‘x’ >> simp[] >> strip_tac >>
  drule unhanded_sn >> disch_then drule >> simp[]
QED

(* MAIN, S4 for the loop: on every finite prefix of the
   loop's trace, what each episode sent is a prefix of what it received *)
Theorem echo_run_safe:
  ri lfd (srelabel (server k)) ([], ws0, []) ∧
  (∀n. prounds_t lfd hw ifds (srelabel (server k)) ws0 n ≠ NONE) ∧
  LPREFIX (fromList evs)
    (LFLATTEN (LGENLIST (λi. fromList (pround_evs lfd hw ifds (srelabel (server k)) ws0 i)) NONE)) ⇒
  ∀j. ep_sn j (0, []) evs ≼ ep_rd j (0, []) evs
Proof
  strip_tac >> gen_tac >>
  Cases_on ‘hdln (w2n lfd) j < dimword (:64)’
  >- ((* a valid handle: as echo_run_safe, which needs no guard here *)
      drule LPREFIX_rounds_any >> strip_tac >>
      drule_all prun_FLAT >> strip_tac >> gvs[] >>
      drule_all prun_ri >> strip_tac >>
      qabbrev_tac ‘R = prun lfd hw ifds (srelabel (server k)) ws0’ >>
      ‘ri lfd (srelabel (server k)) (FST (R n), FST (SND (R n)), FST (SND (SND (R n))))’
        by simp[Abbr ‘R’] >>
      drule prun_SUC >> disch_then (qspec_then ‘n’ mp_tac) >> simp[] >>
      IF_CASES_TAC >> simp[] >> strip_tac
      >- (Cases_on ‘R n’ >> PairCases_on ‘r’ >> gvs[] >>
          PairCases_on ‘ws'’ >>
          qpat_x_assum ‘∀n. ri _ _ _’ (qspec_then ‘SUC n’ mp_tac) >> simp[] >> strip_tac >>
          irule round_safe >> simp[] >> metis_tac[]) >>
      ‘evs = FST (SND (SND (R n)))’ by (irule isPREFIX_ANTISYM >> gvs[]) >>
      Cases_on ‘R n’ >> PairCases_on ‘r’ >> gvs[] >>
      irule boundary_safe >> qexistsl [‘q’, ‘k’, ‘lfd’, ‘r1’, ‘r0’] >> fs[]) >>
  (* no valid handle: the episode is not handed out by the round's end *)
  drule LPREFIX_rounds_any >> strip_tac >>
  drule_all prun_FLAT >> strip_tac >> gvs[] >>
  drule_all prun_ri >> strip_tac >>
  drule prun_unhanded >> disch_then drule >> strip_tac >>
  qabbrev_tac ‘R = prun lfd hw ifds (srelabel (server k)) ws0’ >>
  qpat_x_assum ‘∀n. ri _ _ _’ (qspec_then ‘SUC n’ assume_tac) >>
  qpat_x_assum ‘∀n j. _ ≤ j ⇒ _’ (qspec_then ‘SUC n’ assume_tac) >>
  Cases_on ‘R (SUC n)’ >> PairCases_on ‘r’ >> gvs[] >>
  qpat_x_assum ‘ri _ _ _’ (strip_assume_tac o REWRITE_RULE [ri_def]) >>
  ‘r1.b.nxt ≤ j’
    by (CCONTR_TAC >>
        ‘hdln (w2n lfd) j < 18446744073709551616’
          by (irule hdln_bound >> qexists_tac ‘r1.b.nxt’ >> fs[]) >>
        fs[]) >>
  ‘ep_sn j (0, []) evs ≼ ep_sn j (0, []) r2’ by simp[ep_fold_prefix] >>
  ‘ep_sn j (0, []) r2 = []’ by fs[] >>
  gvs[]
QED

(* The listener the program listens on is in use *)
Theorem listen_used:
  l0_rely w ∧ sys_listen_echo w = SOME (out, w1, ev) ∧ listen_fd out = SOME k ⇒
  MEM (n2w k : word64) (l0_used w1)
Proof
  rw[sys_listen_echo_def, l0_do_def, l0_ffi_fn_def] >>
  gvs[AllCaseEqs(), l0_call_def, echo_port_conf_def]
  >- (‘dec_res (enc_res (Ok (w2n f)) ++ []) = SOME (Ok (w2n f))’
        by (irule dec_enc_res >> simp[l0_res_ok_def] >>
            assume_tac (INST_TYPE [alpha |-> “:64”] wordsTheory.w2n_lt) >> fs[]) >>
      gvs[listen_fd_def, l0_res_of_def] >>
      gvs[l0_listen_def, AllCaseEqs(), l0_used_def]) >>
  PairCases_on ‘ke’ >>
  ‘n2w (err_code ke1) ≠ (0w:word8)’
    by (mp_tac (Q.INST [‘e’ |-> ‘ke1’] err_code_range) >> simp[wordsTheory.n2w_11]) >>
  gvs[enc_listen_fail_def, listen_fd_def, l0_res_of_def, dec_res_def, AllCaseEqs()]
QED

(* The run invariant holds at the start of the loop *)
Theorem ri_echo_base:
  l0_rely w0 ∧ fds_lt w0 ∧ sys_listen_echo w0 = SOME (out, w1, ev) ∧ listen_fd out = SOME k ⇒
  ri (n2w k) (srelabel (server k)) ([], (w1, pinit), [])
Proof
  strip_tac >>
  ‘l0_rely w1 ∧ fds_lt w1’
    by (gvs[sys_listen_echo_def] >>
        metis_tac[l0_do_rely, l0_do_fds_lt, EVAL “«sys_listen» = «sys_connect»”]) >>
  drule_all listen_used >> strip_tac >>
  simp[ri_def, wown_def, owned_def, own_ok_def, ep_ok_def, pinit_def, l1init_def,
       okb_def, outbox_of_def, texec_def, haccepted_def, ep_fold_def, oi_def, obp_def,
       epfd_def, live_def, inbp_def, hread_def, hwritten_def, inb_of_def, hdln_def] >>
  rw[]
QED

(* The listen event belongs to no episode *)
Theorem listen_event[local]:
  sys_listen_echo w = SOME (out, w1, ev) ⇒
  send_fd ev = NONE ∧ recv_fd ev = NONE ∧ l0_event_accepted ev = NONE ∧
  l0_event_closed ev = NONE
Proof
  rw[sys_listen_echo_def, l0_do_def, AllCaseEqs()] >>
  simp[send_fd_def, recv_fd_def, l0_event_accepted_def, l0_event_closed_def]
QED

(* MAIN: the program's trace when the listen succeeds is safe *)
Theorem echo_l0_run_safe:
  l0_rely w0 ∧ fds_lt w0 ∧ sys_listen_echo w0 = SOME (out, w1, ev) ∧ listen_fd out = SOME k ⇒
  echo_safe_l0 (LCONS ev (echo_l0_run k w1))
Proof
  strip_tac >> drule_all ri_echo_base >> strip_tac >>
  ‘k < 2147483648’ by metis_tac[listen_fd_small] >>
  ‘∀n. prounds_t (n2w k) echo_hw (asyncM4LiveInterest$live [n2w k] (log_of (srelabel (server k)))) (srelabel (server k)) (w1, pinit) n ≠ NONE’
    by (‘l0_rely w1’ by (gvs[sys_listen_echo_def] >> metis_tac[l0_do_rely]) >>
        ‘psmall (n2w k) pinit’
          by simp[psmall_def, pinit_def, l1init_def, small_fds_def, small_def] >>
        gen_tac >>
        qspecl_then [‘w1’, ‘pinit’, ‘n2w k’, ‘echo_hw’, ‘asyncM4LiveInterest$live [n2w k] (log_of (srelabel (server k)))’, ‘srelabel (server k)’]
          mp_tac (Q.GENL [‘w0’, ‘ps0’, ‘lfd’, ‘hw’, ‘ifds’, ‘m’] prounds_t_total) >>
        simp[server_pt_ok] >> disch_then (qspec_then ‘n’ strip_assume_tac) >> simp[]) >>
  rw[echo_safe_l0_def, l0_sent_fold, l0_read_fold] >>
  gvs[LPREFIX_LCONS] >> TRY (simp[ep_fold_def] >> NO_TAC) >>
  Cases_on ‘evs’ >> gvs[] >>
  drule listen_event >> strip_tac >>
  ‘l0_ep_step (0, []) ev = (0, [])’ by simp[l0_ep_step_def] >>
  simp[ep_fold_def] >>
  irule echo_run_safe >> simp[] >> metis_tac[]
QED

(* MAIN: echo_l0_safe, the statement the user approved *)
Theorem echo_l0_safe:
  l0_server_world w0 ⇒
  ∃io. (semantics_prog (init_state (l0_ffi w0)) init_env echo_l0_prog (Diverge io) ∧
        echo_safe_l0 io) ∨
       (∃out w1 ev. sys_listen_echo w0 = SOME (out, w1, ev) ∧ listen_fd out = NONE ∧
                    io = [|ev|] ∧
                    semantics_prog (init_state (l0_ffi w0)) init_env echo_l0_prog
                      (Terminate Success [ev]))
Proof
  rw[l0_server_world_def] >>
  drule_all echo_l0_semantics_prog >> strip_tac
  >- (qexists_tac ‘[|ev|]’ >> disj2_tac >> simp[]) >>
  qexists_tac ‘LCONS ev (echo_l0_run k w1)’ >> disj1_tac >> simp[] >>
  irule echo_l0_run_safe >> simp[] >> metis_tac[]
QED

