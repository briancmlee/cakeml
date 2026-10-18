(*
  The close step of echo_live_l0 (design/47 D, D27): the program's close
  call on an episode's fd, made while the episode is open.

  L1 lets go of an fd it holds (its table or closing list) only by a close
  call on it in that round (release_close): l1_close is a sys_close call
  whatever its result, and a round's other steps keep the table and the
  closing list.  The first close call on f in that round is made while
  f's episode is still open (release_open): before it, no event of the
  round closes f, and no accept returns f (after an accept returns f, the
  round makes no close call on f: pround_acc_noclose).

  MAIN: release_close, release_open (with run_acc_noclose).
*)
Theory honestEchoL0CloseStep
Ancestors
  honestEchoL0TraceWrap honestEchoL0NoClose honestEchoL0AccOnce honestEchoL0Excuse
  honestEchoL0LiveOwn honestEchoL0Inv honestEchoL0Trace honestL1PFModel honestL1PFRefine
  honestL1PFRound honestL1PFInv honestL1PFLive honestL1Model honestL0Rely honestL0World
  honestL1PFConnRun honestL1PFFlush honestEchoL0Round honestEchoL0Events honestL1BStmts
  honestL1PFOut honestEchoL0Spec
Libs
  preamble

(* ------------------------------------------------------------------------
   Close calls
   ------------------------------------------------------------------------ *)

Theorem sys_close_lcall[local]:
  sys_close g w = SOME (out, w', ev) ⇒ (l0_close_call f ev ⇔ g = f)
Proof
  rw[sys_close_def] >> drule l0_do_cases >> rw[] >> simp[l0_close_call_def] >>
  ‘LENGTH (fd_bytes g) = 8’ by simp[] >> simp[] >> metis_tac[]
QED

Theorem lcall_closes:
  l0_close_call f ev ⇒ closes_call f ev
Proof
  Cases_on ‘ev’ >> rw[l0_close_call_def, closes_call_def]
QED

Theorem closed_lcall:
  l0_event_closed ev = SOME f ⇒ l0_close_call f ev
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bs’ >> Cases_on ‘nm’ >>
  rw[l0_event_closed_def, l0_close_call_def, AllCaseEqs()]
QED

(* ------------------------------------------------------------------------
   A round keeps what L1 holds unless it calls close on it
   ------------------------------------------------------------------------ *)

Theorem pdo_held:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ own_ok lfd (k, opn) ps ∧
  ps.b.nxt < dimword (:64) ∧ held f ps ∧ ¬EXISTS (l0_close_call f) evs ⇒
  held f ps'
Proof
  Cases_on ‘a’ >> simp[pdo_def]
  >- (rw[AllCaseEqs()] >> gvs[])
  >- (disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
      Cases_on ‘ALOOKUP ps.b.tbl c’ >> fs[] >> TRY (gvs[] >> NO_TAC) >>
      rename1 ‘ALOOKUP _ c = SOME g’ >>
      ‘∀g'. MEM (c, g') ps.b.tbl ⇒ g' = g’
        by (rpt strip_tac >> drule own_tbl_entry_fd >> disch_then irule >>
            fs[dimword_def] >> qexists_tac ‘c’ >> simp[]) >>
      ‘g ≠ f ⇒ held f (ps with b := ps.b with tbl := ADELKEY c ps.b.tbl)’
        by (rpt strip_tac >> gvs[MEM_MAP, ADELKEY_def, MEM_FILTER, EXISTS_PROD] >>
            metis_tac[]) >>
      gvs[AllCaseEqs()] >>
      TRY (Cases_on ‘g = f’ >> fs[] >> NO_TAC) >>
      PairCases_on ‘z’ >> gvs[] >> drule l1_close_shape >> strip_tac >> gvs[] >>
      drule sys_close_lcall >> disch_then (qspec_then ‘f’ assume_tac) >> gvs[] >>
      gvs[forget_def, set_outbox_def, MEM_FILTER])
  >> rpt strip_tac >> PairCases_on ‘z’ >> gvs[] >> drule l1do_write_tbl >> simp[]
QED

Theorem pacts_held:
  ∀acts w ps rs evs w' ps' opn.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ l0_rely w ∧
    own_ok lfd (k, opn) ps ∧ ps.b.nxt < dimword (:64) ∧
    held f ps ∧ ¬EXISTS (l0_close_call f) evs ⇒
    held f ps'
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >>
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  qpat_x_assum ‘_ = SOME _’ mp_tac >> simp[AllCaseEqs(), PULL_EXISTS] >>
  rpt gen_tac >> PairCases_on ‘ws1’ >> simp[] >> strip_tac >> rveq >>
  rename1 ‘pdo lfd (w, ps) a = SOME (r, (w1, ps1), evs1)’ >>
  ‘ps.b.nxt < dimword (:64)’ by simp[] >>
  ‘ps1.b.nxt < dimword (:64)’ by (drule pdo_nxt_room >> fs[]) >>
  ‘¬EXISTS (l0_close_call f) evs1 ∧ ¬EXISTS (l0_close_call f) evs'’
    by (qpat_x_assum ‘EVERY _ (_ ++ _)’ mp_tac >> simp[EVERY_APPEND]) >>
  ‘held f ps1’ by (drule_all pdo_held >> simp[]) >>
  drule_all pdo_in >> strip_tac >>
  drule_all pdo_rely >> strip_tac >>
  Cases_on ‘l0_ep_st (k, opn) evs1’ >> fs[] >>
  first_x_assum irule >> metis_tac[]
QED

Theorem l1_reap_held:
  ∀fs w b w' b' evs.
    l1_reap fs (w, b) = SOME ((w', b'), evs) ∧ MEM f b.closing ∧
    ¬EXISTS (l0_close_call f) evs ⇒
    MEM f b'.closing
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  PairCases_on ‘ws’ >> drule l1_close_shape >> strip_tac >> gvs[] >>
  drule sys_close_lcall >> disch_then (qspec_then ‘f’ assume_tac) >> gvs[] >>
  first_x_assum drule >> fs[forget_def, set_outbox_def, MEM_FILTER]
QED

Theorem pround_held:
  pround lfd pol hs (w, ps) acts = SOME (sn, (w', ps'), log, evs) ∧
  wown lfd w ps ∧ own_ok lfd (k, opn) ps ∧ ps.b.nxt < dimword (:64) ∧
  held f ps ∧ ¬EXISTS (l0_close_call f) evs ⇒
  held f ps'
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  qpat_x_assum ‘pround _ _ _ _ _ = _’ mp_tac >>
  simp[pround_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  rename1 ‘pacts _ _ _ = SOME (rs, evs1, ws1)’ >> PairCases_on ‘ws1’ >>
  ‘l0_rely w’ by fs[wown_def] >>
  ‘¬EXISTS (l0_close_call f) evs1 ∧ ¬EXISTS (l0_close_call f) tevs’
    by (qpat_x_assum ‘¬EXISTS _ evs’ mp_tac >>
        qpat_x_assum ‘_ ++ _ = evs’ (SUBST1_TAC o SYM) >> simp[EXISTS_APPEND]) >>
  ‘held f ws11’ by (drule_all pacts_held >> simp[]) >>
  qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >>
  simp[pf_tail_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘_ = tevs’ (SUBST_ALL_TAC o SYM) >> fs[EXISTS_APPEND] >>
  drule l1_flush_fields >> strip_tac >>
  drule honestL1PFConnRunTheory.pf_fetch_b >> strip_tac >>
  drule honestL1PFFlushTheory.l1_reap_tbl >> strip_tac >>
  qpat_x_assum ‘_ = ps'’ (SUBST_ALL_TAC o SYM) >> simp[] >>
  TRY (disj1_tac >> fs[] >> NO_TAC) >>
  disj2_tac >> drule l1_reap_held >> disch_then irule >> fs[]
QED

(* MAIN: L1 lets go of an fd it holds only by a close call on it in that
   round *)
Theorem release_close:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  held f (rstate lfd pol ifds m w0 n) ∧ ¬held f (rstate lfd pol ifds m w0 (SUC n)) ⇒
  EXISTS (l0_close_call f) (rrev lfd pol ifds m w0 n)
Proof
  strip_tac >> drule_all run_own >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  drule prun_round' >> disch_then (qspecl_then [‘f’, ‘n’] strip_assume_tac) >>
  drule prun_some >> disch_then (qspec_then ‘n’ assume_tac) >>
  ‘(rstate lfd pol ifds m w0 n).b.nxt < dimword (:64)’ by (drule rstate_nxt >> simp[]) >>
  Cases_on ‘l0_ep_st (0, []) (revs lfd pol ifds m w0 n)’ >> fs[] >>
  ‘¬EXISTS (l0_close_call f) (rrev lfd pol ifds m w0 n) ⇒
   held f (rstate lfd pol ifds m w0 (SUC n))’
    by (strip_tac >> qpat_x_assum ‘pround _ _ _ _ _ = _’ assume_tac >>
        drule_then irule pround_held >> simp[] >>
        conj_tac >- (qpat_x_assum ‘¬EXISTS _ _’ mp_tac >> simp[NOT_EXISTS, o_DEF]) >>
        qexistsl [‘q’, ‘r’] >> simp[]) >>
  qpat_x_assum ‘_ ⇒ held _ _’ mp_tac >>
  qpat_x_assum ‘¬MEM f (MAP SND (rstate _ _ _ _ _ (SUC n)).b.tbl)’ mp_tac >>
  qpat_x_assum ‘¬MEM f (rstate _ _ _ _ _ (SUC n)).b.closing’ mp_tac >>
  rpt (pop_assum kall_tac) >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   After an accept returns f in a round, the round makes no close call on f
   ------------------------------------------------------------------------ *)

Theorem closes_name[local]:
  closes_call f e ⇒ ev_name e = ExtCall «sys_close»
Proof
  Cases_on ‘e’ >> rw[closes_call_def, ev_name_def]
QED

Theorem names_noclose[local]:
  EVERY (λev. ev_name ev = ExtCall «sys_accept» ∨ ev_name ev = ExtCall «sys_recv») evs ⇒
  EVERY (λe. ¬closes_call f e) evs
Proof
  rw[EVERY_MEM] >> res_tac >> strip_tac >> drule closes_name >> fs[]
QED

(* The same reasoning as pround_acc_after: the accept is in the fetch, of an
   fd not in use before the fetch, so not in L1's closing list; the fetch
   makes no close call, and the reap closes only closing fds *)
Theorem pround_acc_noclose:
  pround lfd pol hs (w, ps) acts = SOME (sn, (w', ps'), log, evs) ∧
  wown lfd w ps ∧ own_ok lfd (k, opn) ps ∧ LENGTH ps.acq ≤ 1 ∧
  ps.b.nxt < dimword (:64) ∧
  evs = a ++ [ev] ++ b ∧ l0_event_accepted ev = SOME f ⇒
  EVERY (λe. ¬closes_call f e) b
Proof
  strip_tac >> qpat_x_assum ‘pround _ _ _ _ _ = _’ mp_tac >>
  simp[pround_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  rename1 ‘pacts _ _ _ = SOME (rs, evs1, ws1)’ >> PairCases_on ‘ws1’ >>
  ‘l0_rely w’ by gvs[wown_def] >>
  drule_all pacts_noacc >> strip_tac >>
  drule_all pacts_in >> strip_tac >>
  drule_all pacts_wown >> strip_tac >>
  drule pacts_nxt_acc >> strip_tac >>
  drule pacts_nxt_room >> impl_tac >- fs[] >> strip_tac >>
  drule pacts_nxt >> strip_tac >>
  Cases_on ‘l0_ep_st (k, opn) evs1’ >> gvs[] >>
  rename1 ‘own_ok lfd (k1, opn1) ws11’ >>
  ‘LENGTH ws11.acq ≤ 1’ by (Cases_on ‘acts’ >> gvs[own_ok_def]) >>
  ‘ws11.b.nxt < dimword (:64)’ by fs[] >>
  qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >>
  simp[pf_tail_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  rename1 ‘l1_polls _ ws10 = SOME (rv, w1, pevs)’ >>
  rename1 ‘l1_flush _ _ = SOME ((w2, b2), fevs)’ >>
  rename1 ‘pf_fetch _ _ _ _ = SOME ((w3, ps3'), log2, gevs)’ >>
  ‘l0_rely ws10’ by gvs[wown_def] >>
  drule_all l1_polls_noend >> strip_tac >>
  drule_all l1_polls_in >> disch_then (qspec_then ‘(k1, opn1)’ strip_assume_tac) >>
  drule_all l1_polls_wown >> strip_tac >>
  drule_all l1_flush_noend >> strip_tac >>
  drule_all l1_flush_in >> disch_then (qspec_then ‘(k1, opn1)’ strip_assume_tac) >>
  ‘wown lfd w2 (ws11 with b := b2)’ by (irule l1_flush_wown >> metis_tac[]) >>
  ‘own_ok lfd (k1, opn1) (ws11 with b := b2)’
    by (mp_tac (Q.INST [‘ps'’ |-> ‘ws11 with b := b2’, ‘ps’ |-> ‘ws11’, ‘es’ |-> ‘(k1, opn1)’]
                  own_ok_cong) >> simp[]) >>
  ‘l0_rely w3’ by (drule pf_fetch_in >> disch_then (qspecl_then [‘k1’, ‘opn1’] mp_tac) >>
                   impl_tac
                   >- (simp[] >> rw[MEM_FILTER] >>
                       TRY (drule in_fds_poll_set >> simp[] >> NO_TAC) >> fs[]) >>
                   gvs[wown_def]) >>
  drule_all l1_reap_noacc >> strip_tac >>
  (* the accept is in the fetch *)
  qpat_x_assum ‘_ = tevs’ (SUBST_ALL_TAC o SYM) >>
  ‘∃a' b'. gevs = a' ++ [ev] ++ b' ∧ b = b' ++ cevs’
    by (qspecl_then [‘λe. l0_event_accepted e ≠ NONE’, ‘gevs’, ‘cevs’, ‘ev’, ‘b’,
                     ‘evs1 ++ pevs ++ fevs’, ‘a’] mp_tac
          (Q.GENL [‘P’, ‘Y’, ‘Z’, ‘ev’, ‘b’] seg_mid) >>
        impl_tac >- (fs[] >> fs[EXISTS_MEM, EVERY_MEM] >> rpt strip_tac >>
                     Cases_on ‘l0_event_accepted e’ >> gvs[] >> metis_tac[]) >>
        simp[]) >>
  ‘¬MEM f (l0_used w2)’
    by (qspecl_then [‘pol’,
                     ‘FILTER (λf. MEM f (in_fds (pf_poll_set lfd pol ws11 hs))) (readable_fds rv)’,
                     ‘w2’, ‘ws11 with b := b2’, ‘k1’, ‘opn1’, ‘w3’, ‘ps3'’, ‘log2’, ‘a'’, ‘ev’, ‘b'’] mp_tac
          (Q.GEN ‘hw’ pf_fetch_acc_after) >>
        impl_tac
        >- (simp[] >> rw[MEM_FILTER] >> TRY (drule in_fds_poll_set >> simp[] >> NO_TAC) >> fs[]) >>
        simp[]) >>
  ‘EVERY (λe. ¬closes_call f e) b'’
    by (drule pf_fetch_names >> strip_tac >> drule names_noclose >>
        disch_then (qspec_then ‘f’ mp_tac) >>
        qpat_x_assum ‘gevs = _’ SUBST1_TAC >> simp[EVERY_APPEND]) >>
  ‘¬MEM f ps3'.b.closing’
    by (drule honestL1PFConnRunTheory.pf_fetch_b >> strip_tac >> simp[] >> strip_tac >>
        ‘owned (ws11 with b := b2) f’ by simp[owned_def] >>
        qpat_x_assum ‘wown lfd w2 _’ mp_tac >> simp[wown_def] >> metis_tac[]) >>
  ‘EVERY (λe. ¬closes_call f e) cevs’
    by (drule l1_reap_noclose >> simp[]) >>
  qpat_x_assum ‘b = _’ SUBST1_TAC >> simp[EVERY_APPEND]
QED

(* The same along the run *)
Theorem run_acc_noclose:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  rrev lfd pol ifds m w0 i = a ++ [ev] ++ b ∧ l0_event_accepted ev = SOME f ⇒
  EVERY (λe. ¬closes_call f e) b
Proof
  strip_tac >>
  drule_all run_own >> strip_tac >>
  first_x_assum (qspec_then ‘i’ strip_assume_tac) >>
  drule prun_round' >> disch_then (qspecl_then [‘f’, ‘i’] strip_assume_tac) >>
  drule prun_some >> disch_then (qspec_then ‘i’ assume_tac) >>
  ‘(rstate lfd pol ifds m w0 i).b.nxt < dimword (:64)’ by (drule rstate_nxt >> simp[]) >>
  Cases_on ‘l0_ep_st (0, []) (revs lfd pol ifds m w0 i)’ >>
  ‘own_ok lfd (q, r) (rstate lfd pol ifds m w0 i)’ by metis_tac[] >>
  drule_all pround_acc_noclose >> simp[]
QED

(* ------------------------------------------------------------------------
   The first close call on a released fd is made while its episode is open
   ------------------------------------------------------------------------ *)

Theorem first_split[local]:
  ∀l. EXISTS P l ⇒ ∃pre e post. l = pre ++ [e] ++ post ∧ P e ∧ ¬EXISTS P pre
Proof
  Induct >> rw[]
  >- (qexistsl_tac [‘[]’, ‘h’, ‘l’] >> simp[]) >>
  Cases_on ‘P h’
  >- (qexistsl_tac [‘[]’, ‘h’, ‘l’] >> simp[]) >>
  fs[] >> qexistsl_tac [‘h :: pre’, ‘e’, ‘post’] >> simp[]
QED

Theorem ep_open_append[local]:
  ∀pre evs. ep_open j evs ∧ EL j (l0_accepted evs) = f ∧ EVERY (λx. ¬ep_ends f x) pre ⇒
            ep_open j (evs ++ pre) ∧ EL j (l0_accepted (evs ++ pre)) = f
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  ‘evs ++ h :: pre = (evs ++ [h]) ++ pre’ by simp[] >>
  pop_assum SUBST1_TAC >>
  first_x_assum irule >> drule_all ep_open_snoc >> simp[]
QED

Theorem release_open:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  held f (rstate lfd pol ifds m w0 n) ∧ ¬held f (rstate lfd pol ifds m w0 (SUC n)) ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 n))) f = SOME j ⇒
  ∃pre e post.
    rrev lfd pol ifds m w0 n = pre ++ [e] ++ post ∧ l0_close_call f e ∧
    ¬EXISTS (l0_close_call f) pre ∧
    ep_open j (revs lfd pol ifds m w0 n ++ pre) ∧
    EL j (l0_accepted (revs lfd pol ifds m w0 n ++ pre)) = f
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  ‘EXISTS (l0_close_call f) (rrev lfd pol ifds m w0 n)’
    by (irule release_close >> simp[] >> metis_tac[]) >>
  drule first_split >> strip_tac >>
  qexistsl_tac [‘pre’, ‘e’, ‘post’] >> simp[] >>
  qpat_x_assum ‘ALOOKUP _ _ = _’ (strip_assume_tac o MATCH_MP ep_state_open) >>
  conj_tac >- (qpat_x_assum ‘¬EXISTS _ pre’ mp_tac >> simp[NOT_EXISTS, o_DEF]) >>
  irule ep_open_append >> simp[] >>
  simp[EVERY_MEM, ep_ends_def] >> rpt strip_tac
  >- (drule closed_lcall >> strip_tac >> qpat_x_assum ‘¬EXISTS _ pre’ mp_tac >>
      simp[EXISTS_MEM] >> qexists_tac ‘x’ >> simp[]) >>
  qpat_x_assum ‘MEM x pre’ (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
  rename1 ‘pre = a ++ x :: b’ >>
  qspecl_then [‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘n’, ‘a’, ‘x’, ‘b ++ [e] ++ post’, ‘f’]
    mp_tac (Q.GENL [‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘i’, ‘a’, ‘ev’, ‘b’, ‘f’] run_acc_noclose) >>
  simp[EVERY_APPEND] >> metis_tac[lcall_closes]
QED
