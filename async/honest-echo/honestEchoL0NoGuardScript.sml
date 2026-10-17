(*
  Echo safety without the accept guard (for the user's decision on
  dropping `LENGTH (l0_accepted evs) < 2^64 − 1` from echo_safe_l0; the
  approved statement is unchanged here).

  Under D25 the loop can run with every handle handed out (nxt = 2^64 − 1)
  and one prefetched connection pending: an episode with no valid handle.
  The run invariant ri covers only episodes with a valid handle.  This
  theory adds: an episode not yet handed out (index at or past nxt) has
  had nothing sent (unhanded_sn), since L1 sends only on fds of its table
  or closing list, whose episodes are below nxt.  With it, every episode
  is safe on every prefix, with no guard (echo_l0_run_safe_ng).
*)
Theory honestEchoL0NoGuard
Ancestors
  llist ffi honestL0 honestL0World honestL0WorldProps honestL0Rely
  asyncHLModel honestL1Model honestL1Steps honestL1PFModel
  asyncM3World honestEchoL0Spec honestEchoL0Trace honestEchoL0Events
  honestEchoL0Model honestEchoL0Inv honestEchoL0Round honestEchoL0Out honestEchoL0Run
  asyncCore asyncLevel1 asyncTranscript honestL1PFProg honestL1PFSpec
  asyncServer asyncServerSafety asyncM4GTrans
  honestEchoL0Prog honestEchoL0Main honestEchoL0Sem honestL1PFInv honestL1Inv
  honestEchoL0Safe
Libs
  preamble

(* ------------------------------------------------------------------------
   Sends land on handed-out episodes only
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

(* MAIN: along the guarded run of the echo server, an episode not yet
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

(* MAIN, S4 for the loop with no guard: on every finite prefix of the
   loop's trace, what each episode sent is a prefix of what it received *)
Theorem echo_run_safe_ng:
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

(* The listen event belongs to no episode (as honestEchoL0Safe's, local
   there) *)
Theorem listen_event_ng[local]:
  sys_listen_echo w = SOME (out, w1, ev) ⇒
  send_fd ev = NONE ∧ recv_fd ev = NONE ∧ l0_event_accepted ev = NONE ∧
  l0_event_closed ev = NONE
Proof
  rw[sys_listen_echo_def, l0_do_def, AllCaseEqs()] >>
  simp[send_fd_def, recv_fd_def, l0_event_accepted_def, l0_event_closed_def]
QED

(* MAIN: the program's trace when the listen succeeds is safe, with no
   guard on the number of connections *)
Theorem echo_l0_run_safe_ng:
  l0_rely w0 ∧ fds_lt w0 ∧ sys_listen_echo w0 = SOME (out, w1, ev) ∧ listen_fd out = SOME k ⇒
  ∀evs j. LPREFIX (fromList evs) (LCONS ev (echo_l0_run k w1)) ⇒ l0_sent j evs ≼ l0_read j evs
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
  rw[l0_sent_fold, l0_read_fold] >>
  gvs[LPREFIX_LCONS] >> TRY (simp[ep_fold_def] >> NO_TAC) >>
  Cases_on ‘evs’ >> gvs[] >>
  drule listen_event_ng >> strip_tac >>
  ‘l0_ep_step (0, []) ev = (0, [])’ by simp[l0_ep_step_def] >>
  simp[ep_fold_def] >>
  irule echo_run_safe_ng >> simp[] >> metis_tac[]
QED

(* MAIN: echo_l0_safe with no guard on the number of connections (the
   approved statement, with `LENGTH (l0_accepted evs) < 2^64 − 1` dropped) *)
Theorem echo_l0_safe_ng:
  l0_server_world w0 ⇒
  ∃io. (semantics_prog (init_state (l0_ffi w0)) init_env echo_l0_prog (Diverge io) ∧
        ∀evs j. LPREFIX (fromList evs) io ⇒ l0_sent j evs ≼ l0_read j evs) ∨
       (∃out w1 ev. sys_listen_echo w0 = SOME (out, w1, ev) ∧ listen_fd out = NONE ∧
                    io = [|ev|] ∧
                    semantics_prog (init_state (l0_ffi w0)) init_env echo_l0_prog
                      (Terminate Success [ev]))
Proof
  rw[l0_server_world_def] >>
  drule_all echo_l0_semantics_prog >> strip_tac
  >- (qexists_tac ‘[|ev|]’ >> disj2_tac >> simp[]) >>
  qexists_tac ‘LCONS ev (echo_l0_run k w1)’ >> disj1_tac >> simp[] >>
  rpt strip_tac >> drule_all echo_l0_run_safe_ng >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Handles and accepts (for the D25 stop on the trace)
   ------------------------------------------------------------------------ *)

Theorem ri_nxt_accepted:
  ri lfd m (h, (w, ps), evs) ⇒ ps.b.nxt + LENGTH ps.acq = LENGTH (l0_accepted evs)
Proof
  rw[ri_def] >> Cases_on ‘l0_ep_st (0, []) evs’ >>
  ‘q = LENGTH (l0_accepted evs)’ by metis_tac[FST_l0_ep_st, FST, ADD] >>
  gvs[own_ok_def]
QED

(* When the echo loop's guard fails, the trace has accepted all but at most
   the round's accepts of the 2^64 − 1 handles *)
Theorem echo_guard_stop:
  ri lfd (srelabel (server k)) ([], ws0, []) ∧
  prounds_t lfd hw ifds (srelabel (server k)) ws0 n = SOME (h, (w, ps), evs, logs) ∧
  ¬hdl_room lfd ps (naccepts (new_actions (log_of (srelabel (server k))) h)) ⇒
  2 ** 64 ≤ LENGTH (l0_accepted evs) + naccepts (new_actions (log_of (srelabel (server k))) h)
Proof
  strip_tac >> drule_all ri_echo >> strip_tac >>
  drule ri_nxt_accepted >> gvs[hdl_room_def]
QED
