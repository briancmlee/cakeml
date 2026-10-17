(*
  D37 (the D33 amendment): the echo loop makes no close call on fds 0, 1
  or 2 when they are in use at its start (they are once the program's
  sys_fdok checks answered 1: honestL0Fdok's fdok_shift).

  The invariant, kept: fds 0-2 stay in use, and L1 owns none of them.  L1
  closes only fds it owns (a table fd at EOF, a closing fd at the reap), so
  every close call is on another fd and 0-2 stay in use; the fds L1 comes
  to own are accepted ones, fresh, so not 0-2.
*)
Theory honestEchoL0Stdio
Ancestors
  llist ffi honestL0 honestL0World honestL0WorldProps honestL0Rely
  honestL1Model honestL1PFModel honestL1PFRound honestL1PFRefine
  honestL1PFConn honestL1PFConnRun honestL1PFSpec
  honestEchoL0Spec honestEchoL0Trace honestEchoL0Inv honestEchoL0Round
  honestEchoL0Run honestEchoL0LiveOwn honestEchoL0Prog honestL1PFProg honestL0Outcome
Libs
  preamble

Definition stdio_fd_def:
  stdio_fd (f : word64) ⇔ f = 0w ∨ f = 1w ∨ f = 2w
End

(* The event, if a close call, is not on fd 0, 1 or 2 *)
Definition ev_nostdio_def:
  ev_nostdio ev ⇔
    ∀conf bs. ev = IO_event (ExtCall «sys_close») conf bs ∧ LENGTH conf = 8 ⇒
              ¬stdio_fd (bytes_fd conf)
End

(* fds 0-2 are in use, and L1 owns none of them *)
Definition kept_def:
  kept w ps ⇔
    (∀f. stdio_fd f ⇒ MEM f (l0_used w)) ∧ (∀f. owned ps f ⇒ ¬stdio_fd f)
End

Theorem kept_mono:
  kept w ps ⇒ (∀g. stdio_fd g ⇒ MEM g (l0_used w')) ⇒ (∀g. owned ps' g ⇒ owned ps g) ⇒
  kept w' ps'
Proof
  rw[kept_def] >> metis_tac[]
QED

Theorem no_close_stdio_EVERY:
  no_close_stdio evs ⇔ EVERY ev_nostdio evs
Proof
  rw[no_close_stdio_def, EVERY_MEM, ev_nostdio_def, stdio_fd_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Calls
   ------------------------------------------------------------------------ *)

Theorem ev_nostdio_name:
  ev_name ev ≠ ExtCall «sys_close» ⇒ ev_nostdio ev
Proof
  Cases_on ‘ev’ >> rw[ev_nostdio_def, ev_name_def]
QED

Theorem names_nostdio[local]:
  EVERY (λe. ev_name e = ExtCall n) evs ∧ n ≠ «sys_close» ⇒ EVERY ev_nostdio evs
Proof
  rw[EVERY_MEM] >> res_tac >> irule ev_nostdio_name >> simp[]
QED

Theorem sys_close_nostdio:
  sys_close g w = SOME (out, w', ev) ∧ ¬stdio_fd g ⇒ ev_nostdio ev
Proof
  rw[sys_close_def] >> drule l0_do_cases >> rw[] >> simp[ev_nostdio_def]
QED

Theorem l1_close_kept:
  l1_close f (w, b) = SOME ((w', b'), evs) ∧ l0_rely w ∧ ¬stdio_fd f ∧
  (∀g. stdio_fd g ⇒ MEM g (l0_used w)) ⇒
  (∀g. stdio_fd g ⇒ MEM g (l0_used w')) ∧ EVERY ev_nostdio evs
Proof
  strip_tac >> drule_all l1_close_l0 >> strip_tac >>
  drule l1_close_shape >> strip_tac >> gvs[] >>
  conj_tac
  >- (rpt strip_tac >> qpat_x_assum ‘∀g. g ≠ f ∧ _ ⇒ _’ irule >>
      conj_tac >- (strip_tac >> gvs[]) >> metis_tac[]) >>
  irule sys_close_nostdio >> metis_tac[]
QED

Theorem l1_reap_nostdio[local]:
  ∀fs w b w' b' evs.
    l1_reap fs (w, b) = SOME ((w', b'), evs) ∧ (∀f. MEM f fs ⇒ ¬stdio_fd f) ⇒
    EVERY ev_nostdio evs
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  PairCases_on ‘ws’ >> drule l1_close_shape >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  irule sys_close_nostdio >> metis_tac[]
QED

Theorem l1_reap_kept:
  l1_reap fs (w, b) = SOME ((w', b'), evs) ∧ l0_rely w ∧ (∀f. MEM f fs ⇒ ¬stdio_fd f) ∧
  (∀g. stdio_fd g ⇒ MEM g (l0_used w)) ⇒
  (∀g. stdio_fd g ⇒ MEM g (l0_used w')) ∧ EVERY ev_nostdio evs
Proof
  strip_tac >> drule_all l1_reap_l0 >> strip_tac >>
  conj_tac >- (rpt strip_tac >> qpat_x_assum ‘∀g. MEM g (l0_used w) ∧ ¬MEM g fs ⇒ _’ irule >>
               metis_tac[]) >>
  irule l1_reap_nostdio >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The fetch: accepts (fresh fds) and receives
   ------------------------------------------------------------------------ *)

Theorem pf_fetch_kept:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧
    l0_rely w ∧ fds_lt w ∧ kept w ps ⇒
    kept w' ps' ∧ l0_rely w' ∧ fds_lt w'
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum irule >> metis_tac[]) >>
  IF_CASES_TAC
  >- ((* accept *)
      simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> pairarg_tac >> gvs[] >>
      simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >> gvs[] >>
      rename1 ‘sys_accept lfd w = SOME (out, w1, ev)’ >>
      ‘l0_rely w1 ∧ fds_lt w1’
        by (gvs[sys_accept_def] >>
            metis_tac[l0_do_rely, l0_do_fds_lt, EVAL “«sys_accept» = «sys_connect»”]) >>
      ‘∀g. MEM g (l0_used w) ⇒ MEM g (l0_used w1)’
        by (gvs[sys_accept_def] >> drule l0_do_used >> simp[]) >>
      first_x_assum drule >> simp[] >> disch_then irule >>
      Cases_on ‘l0_res_of out’ >> gvs[]
      >- (rename1 ‘l0_res_of out = Ok kk’ >>
          drule_all sys_accept_fresh >> strip_tac >>
          qpat_x_assum ‘kept w ps’ mp_tac >> rw[kept_def, owned_def] >> metis_tac[]) >>
      qpat_assum ‘kept w ps’ (irule o GEN_ALL o MATCH_MP kept_mono) >>
      every_case_tac >> gvs[kept_def, owned_def]) >>
  (* receive *)
  simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> pairarg_tac >> gvs[] >>
  simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >> gvs[] >>
  rename1 ‘sys_recv h pf_chunk w = SOME (out, w1, ev)’ >>
  ‘l0_rely w1 ∧ fds_lt w1 ∧ l0_used w1 = l0_used w’
    by (gvs[sys_recv_def] >> imp_res_tac l0_do_used >>
        metis_tac[l0_do_rely, l0_do_fds_lt, EVAL “«sys_recv» = «sys_connect»”]) >>
  first_x_assum drule >> simp[] >> disch_then irule >>
  qpat_assum ‘kept w ps’ (irule o GEN_ALL o MATCH_MP kept_mono) >>
  Cases_on ‘l0_res_of out’ >> gvs[] >> every_case_tac >> gvs[kept_def, owned_def]
QED

(* ------------------------------------------------------------------------
   An action, the actions, the tail, a round
   ------------------------------------------------------------------------ *)

Theorem pdo_kept:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ wown lfd w ps ∧
  own_ok lfd (k, opn) ps ∧ ps.b.nxt < dimword (:64) ∧ kept w ps ⇒
  kept w' ps' ∧ EVERY ev_nostdio evs
Proof
  Cases_on ‘a’
  >- ((* Accept: the pending fd becomes a handle's *)
      strip_tac >> drule pdo_accept_in >> strip_tac >> gvs[] >>
      qpat_assum ‘kept w ps’ (irule o GEN_ALL o MATCH_MP kept_mono) >> gvs[kept_def] >>
      rw[owned_def] >> gvs[])
  >- ((* Read: at EOF the fd is closed and dropped *)
      strip_tac >> qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def] >> strip_tac >>
      gvs[AllCaseEqs()]
      >~ [‘set_inb’] >- (qpat_assum ‘kept w ps’ (irule o GEN_ALL o MATCH_MP kept_mono) >> gvs[kept_def, owned_def]) >>
      ‘ps.b.nxt < dimword (:64)’ by simp[] >>
      drule_all owned_drop >>
      disch_then (qspec_then ‘FILTER (λy. f ≠ y) ps.eof’ strip_assume_tac) >>
      ‘owned ps f’ by (imp_res_tac ALOOKUP_MEM >> simp[owned_def, MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
      ‘¬stdio_fd f ∧ ∀g. stdio_fd g ⇒ MEM g (l0_used w)’ by gvs[kept_def] >>
      ‘l0_rely w’ by gvs[wown_def] >>
      TRY (PairCases_on ‘z’ >> gvs[] >>
           drule l1_close_shape >> strip_tac >> gvs[] >>
           drule_all l1_close_kept >> strip_tac >>
           conj_tac >- (qpat_assum ‘kept w ps’ (irule o GEN_ALL o MATCH_MP kept_mono) >>
                        simp[] >> metis_tac[]) >>
           gvs[] >> NO_TAC) >>
      simp[] >> qpat_assum ‘kept w ps’ (irule o GEN_ALL o MATCH_MP kept_mono) >> simp[])
  >> (* Write: sends only *)
  strip_tac >> ‘l0_rely w’ by gvs[wown_def] >>
  drule_all pdo_write_in >> disch_then (qspec_then ‘(0, [])’ strip_assume_tac) >>
  ‘owned ps' = owned ps’ by simp[owned_def, FUN_EQ_THM] >>
  qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def] >> strip_tac >>
  PairCases_on ‘z’ >> gvs[] >>
  drule_all l1do_write_l0 >> strip_tac >>
  conj_tac >- (qpat_assum ‘kept w ps’ (irule o GEN_ALL o MATCH_MP kept_mono) >> gvs[kept_def]) >>
  qpat_x_assum ‘l1do _ _ _ = _’ mp_tac >> simp[l1do_def] >>
  rw[AllCaseEqs()] >> gvs[] >>
  irule ev_nostdio_name >> imp_res_tac sys_send_name >> simp[]
QED

Theorem pacts_kept:
  ∀acts w ps rs evs w' ps' opn.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ wown lfd w ps ∧
    own_ok lfd (k, opn) ps ∧ ps.b.nxt + naccepts acts < dimword (:64) ∧ kept w ps ⇒
    kept w' ps' ∧ EVERY ev_nostdio evs
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  PairCases_on ‘ws1’ >> rename1 ‘pdo lfd (w, ps) a = SOME (r, (w1, ps1), evs1)’ >>
  ‘ps.b.nxt < dimword (:64)’ by simp[] >>
  ‘ps1.b.nxt + naccepts acts < dimword (:64)’
    by (drule pdo_nxt_acc >>
        ‘naccepts (a :: acts) = naccepts [a] + naccepts acts’ by (Cases_on ‘a’ >> simp[]) >>
        fs[]) >>
  ‘l0_rely w’ by gvs[wown_def] >>
  drule_all pdo_kept >> strip_tac >>
  drule_all pdo_wown >> strip_tac >>
  drule_all pdo_in >> strip_tac >>
  Cases_on ‘l0_ep_st (k, opn) evs1’ >> gvs[] >>
  first_x_assum (qspecl_then [‘w1’, ‘ps1’, ‘rs'’, ‘evs'’, ‘w'’, ‘ps'’, ‘r'’] mp_tac) >>
  impl_tac >- fs[] >> simp[]
QED

Theorem pf_tail_kept:
  pf_tail lfd hw hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ∧
  wown lfd w ps ∧ own_ok lfd (k, opn) ps ∧ LENGTH ps.acq ≤ 1 ∧
  ps.b.nxt < dimword (:64) ∧ kept w ps ⇒
  kept w' ps' ∧ EVERY ev_nostdio evs
Proof
  strip_tac >> qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >>
  simp[pf_tail_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  rename1 ‘l1_polls _ w = SOME (rv, w1, pevs)’ >>
  rename1 ‘l1_flush _ _ = SOME ((w2, b2), fevs)’ >>
  rename1 ‘pf_fetch _ _ _ _ = SOME ((w3, ps3'), log2, gevs)’ >>
  rename1 ‘l1_reap _ _ = SOME ((w4, b4), cevs)’ >>
  ‘l0_rely w ∧ fds_lt w’ by gvs[wown_def] >>
  drule_all l1_polls_l0 >> strip_tac >>
  drule_all l1_flush_l0 >> strip_tac >>
  ‘fds_lt w2’ by (qpat_x_assum ‘fds_lt w’ mp_tac >> simp[fds_lt_def] >> metis_tac[]) >>
  ‘kept w2 (ps with b := b2)’
    by (qpat_x_assum ‘kept w ps’ mp_tac >>
        qpat_x_assum ‘l0_used w1 = _’ mp_tac >> qpat_x_assum ‘l0_used w2 = _’ mp_tac >>
        qpat_x_assum ‘b2.tbl = _’ mp_tac >> qpat_x_assum ‘b2.closing = _’ mp_tac >>
        rpt strip_tac >> fs[kept_def, owned_def] >> metis_tac[]) >>
  drule_all pf_fetch_kept >> strip_tac >>
  qabbrev_tac ‘ps3 = stall_step (pf_held ps3') (outbox_of ps.b) log2 ps3'’ >>
  ‘ps3.b.tbl = ps3'.b.tbl ∧ ps3.b.closing = ps3'.b.closing ∧ ps3.acq = ps3'.acq’
    by simp[Abbr ‘ps3’] >>
  ‘kept w3 ps3’
    by (qpat_x_assum ‘kept w3 ps3'’ mp_tac >> simp[Abbr ‘ps3’, kept_def, owned_def] >>
        strip_tac >> first_assum ACCEPT_TAC) >>
  ‘∀f. MEM f ps3'.b.closing ⇒ ¬stdio_fd f’
    by (qpat_x_assum ‘kept w3 ps3'’ mp_tac >> simp[kept_def, owned_def]) >>
  ‘∀g. stdio_fd g ⇒ MEM g (l0_used w3)’
    by (qpat_x_assum ‘kept w3 ps3'’ mp_tac >> simp[kept_def]) >>
  drule_all l1_reap_kept >> strip_tac >>
  drule_all l1_reap_l0 >> strip_tac >>
  qpat_x_assum ‘_ = ps'’ (SUBST_ALL_TAC o SYM) >>
  conj_tac
  >- (qpat_assum ‘kept w3 ps3’ (irule o GEN_ALL o MATCH_MP kept_mono) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      simp[owned_def] >> rpt strip_tac >> fs[MEM_FILTER]) >>
  ‘EVERY ev_nostdio pevs’
    by (irule names_nostdio >> qexists_tac ‘«sys_poll»’ >> simp[] >>
        drule l1_polls_names >> simp[]) >>
  ‘EVERY ev_nostdio fevs’
    by (irule names_nostdio >> qexists_tac ‘«sys_send»’ >> simp[] >>
        drule l1_flush_names >> simp[]) >>
  ‘EVERY ev_nostdio gevs’
    by (drule pf_fetch_names >> rw[EVERY_MEM] >> res_tac >>
        irule ev_nostdio_name >> simp[]) >>
  gvs[EVERY_APPEND]
QED

Theorem pround_kept:
  pround lfd hw hs (w, ps) acts = SOME (sn, (w', ps'), log, evs) ∧
  wown lfd w ps ∧ own_ok lfd (k, opn) ps ∧ LENGTH ps.acq ≤ 1 ∧
  ps.b.nxt + naccepts acts < dimword (:64) ∧ kept w ps ⇒
  kept w' ps' ∧ EVERY ev_nostdio evs
Proof
  strip_tac >> qpat_x_assum ‘pround _ _ _ _ _ = _’ mp_tac >>
  simp[pround_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  rename1 ‘pacts _ _ _ = SOME (rs, evs1, ws1)’ >> PairCases_on ‘ws1’ >>
  ‘l0_rely w’ by gvs[wown_def] >>
  drule_all pacts_kept >> strip_tac >>
  drule_all pacts_wown >> strip_tac >>
  drule_all pacts_in >> strip_tac >>
  drule pacts_nxt >> strip_tac >>
  Cases_on ‘l0_ep_st (k, opn) evs1’ >> rename1 ‘l0_ep_st _ _ = (k1, opn1)’ >> gvs[] >>
  ‘LENGTH ws11.acq ≤ 1’ by (Cases_on ‘acts’ >> gvs[own_ok_def]) >>
  ‘ws11.b.nxt < dimword (:64)’ by (drule pacts_nxt_acc >> fs[]) >>
  drule_all pf_tail_kept >> simp[EVERY_APPEND]
QED

(* ------------------------------------------------------------------------
   The echo loop
   ------------------------------------------------------------------------ *)

Theorem run_kept:
  ri lfd (srelabel (server k)) ([], (w0, ps0), []) ∧ kept w0 ps0 ⇒
  ∀n h w ps evs logs.
    prounds_t lfd hw ifds (srelabel (server k)) (w0, ps0) n = SOME (h, (w, ps), evs, logs) ⇒
    kept w ps ∧ EVERY ev_nostdio evs
Proof
  strip_tac >> Induct >- (simp[prounds_t_def] >> rw[] >> gvs[]) >>
  rpt gen_tac >> simp[prounds_t_def] >>
  Cases_on ‘prounds_t lfd hw ifds (srelabel (server k)) (w0, ps0) n’ >> simp[] >>
  PairCases_on ‘x’ >> simp[] >>
  first_x_assum (qspecl_then [‘x0’, ‘x1’, ‘x2’, ‘x3’, ‘x4’] mp_tac) >> simp[] >> strip_tac >>
  ‘ri lfd (srelabel (server k)) (x0, (x1, x2), x3)’ by metis_tac[ri_echo] >>
  IF_CASES_TAC >> simp[] >- (
    simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >> gvs[] >>
    qabbrev_tac ‘acts = new_actions (log_of (srelabel (server k))) x0’ >>
    ‘x2.b.nxt + naccepts acts < dimword (:64)’ by gvs[hdl_room_def] >>
    qpat_x_assum ‘ri _ _ _’ (strip_assume_tac o REWRITE_RULE [ri_def]) >>
    Cases_on ‘l0_ep_st (0, []) x3’ >> gvs[] >>
    drule pround_kept >> disch_then (qspecl_then [‘r’, ‘q’] mp_tac) >>
    impl_tac >- fs[] >> simp[EVERY_APPEND]) >>
  rw[] >> gvs[]
QED
