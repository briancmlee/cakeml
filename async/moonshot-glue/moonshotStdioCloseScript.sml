(*
  E1 never closes its stdio fds: erounds' events have no sys_close on
  0, 1 or 2 (honestL0Outcome.no_close_stdio), given that the three are
  in use at the start.  Every close E1 issues is on an fd in its tables
  (tfds: a refused connect, an EOF'd PF handle, the closing list), and
  an fd in use at the start never enters them (fdg_ok, moonshotSentGlue's
  fd0_ok for any fd g).
*)
Theory moonshotStdioClose
Ancestors
  moonshotSentGlue honestL0Outcome
  honestL1EPRefine honestL1EPOut honestL1EPModel honestL1PFOut honestL1PFModel honestL1Model
  honestL1PFConnRun honestL1PFConn honestL1PFRound honestL1PFRefine honestL1Steps
  honestL0WorldProps honestL0Rely honestL0World honestL0 Marshalling
Libs
  preamble

(* fd g is in use and in none of E1's tables *)
Definition fdg_ok_def:
  fdg_ok g w es ⇔ MEM g (l0_used w) ∧ ¬MEM g (tfds es)
End

(* No close on fd g *)
Definition noclose_def:
  noclose (g : word64) evs ⇔
    ∀conf bs. MEM (IO_event (ExtCall «sys_close») conf bs) evs ⇒ bytes_fd conf ≠ g
End

Theorem noclose_append[simp]:
  noclose g (xs ++ ys) ⇔ noclose g xs ∧ noclose g ys
Proof
  simp[noclose_def] >> metis_tac[]
QED

Theorem noclose_nil[simp]:
  noclose g []
Proof
  simp[noclose_def]
QED

Theorem names_noclose:
  EVERY (λev. ev_name ev ≠ ExtCall «sys_close») evs ⇒ noclose g evs
Proof
  rw[noclose_def, EVERY_MEM] >> strip_tac >> res_tac >> fs[ev_name_def]
QED

(*---------------------------------------------------------------------------*)
(* Where the closes come from *)

Theorem l1_close_ev:
  l1_close f (w, b) = SOME ((w', b'), evs) ⇒
  ∃bs. evs = [IO_event (ExtCall «sys_close») (fd_bytes f) bs]
Proof
  rw[l1_close_def, AllCaseEqs(), sys_close_def] >> drule l0_do_cases >> rw[] >> simp[]
QED

Theorem l1_close_noclose:
  l1_close f (w, b) = SOME ((w', b'), evs) ∧ f ≠ g ⇒ noclose g evs
Proof
  strip_tac >> drule l1_close_ev >> strip_tac >> rw[noclose_def] >> gvs[]
QED

Theorem l1_reap_closes:
  ∀fs w st w' st' evs.
    l1_reap fs (w, st) = SOME ((w', st'), evs) ∧ ¬MEM g fs ⇒ noclose g evs
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  TRY (PairCases_on ‘ws’) >> gvs[] >>
  TRY (‘noclose g evs'’ by (irule l1_close_noclose >> metis_tac[])) >>
  first_x_assum drule >> simp[]
QED

Theorem l1do_write_names:
  l1do lfd (w, b) (Write h bs) = SOME (r, (w', b'), evs) ⇒
  EVERY (λev. ev_name ev ≠ ExtCall «sys_close») evs
Proof
  rw[l1do_def, AllCaseEqs()] >> gvs[sys_send_def] >>
  drule l0_do_cases >> rw[] >> simp[ev_name_def] >> EVAL_TAC
QED

Theorem edo_noclose:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ∧ ¬MEM g (tfds es) ⇒ noclose g evs
Proof
  strip_tac >> Cases_on ‘a’ >> gvs[edo_def, AllCaseEqs()]
  >~ [‘pdo _ _ (Accept _) = _’]
  >- (PairCases_on ‘z’ >> gvs[] >> drule pdo_accept_ostep >> simp[])
  >~ [‘pdo _ _ (Read _ _) = _’]
  >- (PairCases_on ‘z’ >> gvs[] >> qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >>
      simp[pdo_def, AllCaseEqs()] >> rw[] >> simp[] >>
      PairCases_on ‘z’ >> gvs[] >>
      rename1 ‘ALOOKUP es.p.b.tbl h = SOME f’ >>
      ‘MEM f (MAP SND es.p.b.tbl)’
        by (imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP] >> metis_tac[SND]) >>
      ‘f ≠ g’ by (strip_tac >> gvs[tfds_def]) >>
      drule_all l1_close_noclose >> simp[])
  >~ [‘pdo _ _ (Write _ _) = _’]
  >- (PairCases_on ‘z’ >> gvs[] >> irule names_noclose >>
      qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def] >> strip_tac >>
      pairarg_tac >> gvs[] >> drule l1do_write_names >> simp[])
  >~ [‘l1_close _ _ = _’]
  >- (PairCases_on ‘z’ >> gvs[] >>
      rename1 ‘ALOOKUP es.ctbl h = SOME f’ >>
      ‘MEM f (MAP SND es.ctbl)’
        by (imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP] >> metis_tac[SND]) >>
      ‘f ≠ g’ by (strip_tac >> gvs[tfds_def]) >>
      drule_all l1_close_noclose >> simp[]) >>
  gvs[sys_connect_def] >> drule l0_do_cases >> rw[] >> simp[noclose_def] >> EVAL_TAC
QED

Theorem etail_noclose:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, tevs) ∧ l0_rely w ∧
  ¬MEM g (tfds es) ⇒
  noclose g tevs
Proof
  simp[etail_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘_ = tevs’ (SUBST1_TAC o SYM) >> simp[] >>
  rpt conj_tac
  >- (irule names_noclose >> drule l1_polls_names >>
      simp[EVERY_MEM] >> rpt strip_tac >> res_tac >> fs[] >> EVAL_TAC)
  >- (irule names_noclose >> drule l1_flush_names >>
      simp[EVERY_MEM] >> rpt strip_tac >> res_tac >> fs[] >> EVAL_TAC)
  >- (irule names_noclose >> qpat_x_assum ‘pf_fetch _ _ _ _ = _’ assume_tac >>
      drule pf_fetch_names >> simp[EVERY_MEM] >> rpt strip_tac >> res_tac >> fs[] >> EVAL_TAC)
  >- (drule_all l1_polls_l0 >> strip_tac >>
      drule_all l1_flush_l0 >> strip_tac >>
      qpat_x_assum ‘pf_fetch _ _ _ _ = _’ assume_tac >>
      drule_all pf_fetch_quiet >> strip_tac >>
      ‘¬MEM g ps3'.b.closing’ by gvs[tfds_def] >>
      qpat_x_assum ‘l1_reap _ _ = _’ assume_tac >>
      drule_all l1_reap_closes >> simp[]) >>
  irule names_noclose >> drule settle_fds_names >>
  simp[EVERY_MEM] >> rpt strip_tac >> res_tac >> fs[] >> EVAL_TAC
QED

(*---------------------------------------------------------------------------*)
(* fdg_ok is invariant (as moonshotSentGlue's fd0_ok) *)

Theorem edo_fdg:
  edo lfd pol (wl, es) a = SOME (r, (wl', es'), evs) ∧ l0_rely wl ∧ fds_lt wl ∧
  fdg_ok g wl es ⇒
  fdg_ok g wl' es'
Proof
  strip_tac >> Cases_on ‘a’ >> gvs[edo_def, AllCaseEqs()]
  >~ [‘pdo _ _ (Accept _) = _’]
  >- (PairCases_on ‘z’ >> gvs[] >> drule pdo_accept_ostep >> strip_tac >>
      gvs[fdg_ok_def, tfds_def] >> Cases_on ‘es.p.acq’ >> gvs[])
  >~ [‘pdo _ _ (Read _ _) = _’]
  >- (PairCases_on ‘z’ >> gvs[] >> qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >>
      simp[pdo_def, AllCaseEqs()] >> rw[] >> gvs[fdg_ok_def, tfds_def, set_inb_def] >>
      TRY (PairCases_on ‘z’ >> gvs[] >> drule_all l1_close_l0 >> strip_tac) >>
      rename1 ‘ALOOKUP es.p.b.tbl h = SOME f’ >>
      ‘MEM f (MAP SND es.p.b.tbl)’
        by (imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP] >> metis_tac[SND]) >>
      ‘f ≠ g’ by (strip_tac >> gvs[]) >>
      gvs[MEM_FILTER] >>
      metis_tac[MEM_SND_ADELKEY_sub])
  >~ [‘pdo _ _ (Write _ _) = _’]
  >- (PairCases_on ‘z’ >> gvs[] >> drule pdo_write_held >> strip_tac >>
      qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def] >> strip_tac >>
      pairarg_tac >> gvs[] >> drule_all l1do_write_l0 >> strip_tac >>
      gvs[fdg_ok_def, tfds_def])
  >~ [‘l1_close _ _ = _’]
  >- (PairCases_on ‘z’ >> gvs[] >> drule_all l1_close_l0 >> strip_tac >>
      rename1 ‘ALOOKUP es.ctbl h = SOME f’ >>
      ‘MEM f (MAP SND es.ctbl)’
        by (imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP] >> metis_tac[SND]) >>
      ‘f ≠ g’ by (strip_tac >> gvs[fdg_ok_def, tfds_def]) >>
      gvs[fdg_ok_def, tfds_def, ec_del_def, MEM_FILTER] >>
      metis_tac[MEM_SND_ADELKEY_sub]) >>
  drule_all sys_connect_l0 >> strip_tac >> fs[fdg_ok_def, tfds_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem eacts_fdg:
  ∀acts wl es rs evs wl' es'.
    eacts lfd pol (wl, es) acts = SOME (rs, evs, (wl', es')) ∧ l0_rely wl ∧ fds_lt wl ∧
    fd0_ok wl es ∧ fdg_ok g wl es ⇒
    fdg_ok g wl' es' ∧ noclose g evs
Proof
  Induct >> simp[eacts_def] >> rpt gen_tac >> simp[AllCaseEqs(), PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >> PairCases_on ‘ws1’ >>
  ‘noclose g evs1’ by (drule edo_noclose >> fs[fdg_ok_def]) >>
  drule_all edo_fdg >> strip_tac >>
  drule_all edo_fd0 >> strip_tac >>
  first_x_assum (qspecl_then [‘ws10’, ‘ws11’, ‘rs'’, ‘evs'’, ‘wl'’, ‘es'’] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >> rveq >> simp[]
QED

Theorem etail_fdg:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, tevs) ∧
  l0_rely w ∧ fds_lt w ∧ fdg_ok g w es ⇒
  fdg_ok g w' es'
Proof
  simp[etail_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  ‘es'.p = (promote es5).p ∧ es'.ctbl = (promote es5).ctbl’
    by (qpat_x_assum ‘_ = es'’ (SUBST1_TAC o SYM) >> simp[]) >>
  qpat_x_assum ‘FILTER _ hs = rdy’ kall_tac >> qpat_x_assum ‘_ = es'’ kall_tac >>
  qabbrev_tac ‘ps3 = stall_step (pf_held ps3') (outbox_of es.p.b) log ps3'’ >>
  drule_all l1_polls_l0 >> strip_tac >>
  drule_all l1_flush_l0 >> strip_tac >>
  ‘fds_lt w2’ by gvs[honestL0WorldPropsTheory.fds_lt_def] >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ assume_tac >>
  drule_all fetch_acq >> strip_tac >> drule_all pf_fetch_quiet >> strip_tac >>
  ‘ps3.b.tbl = ps3'.b.tbl ∧ ps3.b.closing = ps3'.b.closing ∧ ps3.acq = ps3'.acq’
    by simp[Abbr ‘ps3’, stall_out] >>
  drule_all l1_reap_l0 >> strip_tac >>
  drule_all settle_fds_used >> strip_tac >>
  drule_all settle_fds_quiet >> simp[] >> strip_tac >>
  gvs[fdg_ok_def, tfds_def] >>
  ‘¬MEM g (fconns log)’ by (strip_tac >> res_tac >> gvs[]) >>
  mp_tac (Q.INST [‘es’ |-> ‘es5’] promote_fields) >> strip_tac >>
  ‘∀f. MEM f (MAP SND (promote es5).ctbl) ⇒ MEM f (MAP SND es5.ctbl)’
    by (simp[promote_def, MEM_MAP, MEM_FILTER] >> metis_tac[]) >>
  gvs[] >> rpt strip_tac >> res_tac >> gvs[MEM_FILTER]
QED

(*---------------------------------------------------------------------------*)
(* The run *)

Theorem einit_fdg:
  MEM g (l0_used w0) ⇒ fdg_ok g w0 einit
Proof
  simp[fdg_ok_def, tfds_def, einit_def, pinit_def, l1init_def]
QED

Theorem erounds_fdg:
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧ MEM 0w (l0_used w0) ∧
  MEM g (l0_used w0) ∧
  (∀n. SND (ecm lfd pol ifds m w0 n) + 1 < dimword (:64)) ⇒
  ∀n h ws evs logs.
    erounds lfd pol ifds m (w0, einit) n = SOME (h, ws, evs, logs) ⇒
    fdg_ok g (FST ws) (SND ws) ∧ noclose g evs
Proof
  strip_tac >> Induct
  >- (simp[erounds_def] >> metis_tac[einit_fdg]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum ‘erounds _ _ _ _ _ (SUC _) = _’
    (strip_assume_tac o SIMP_RULE (srw_ss()) [AllCaseEqs()] o
     ONCE_REWRITE_RULE [erounds_def]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum ‘eround _ _ _ _ _ = _’ mp_tac >> simp[eround_def, AllCaseEqs()] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rename1 ‘eacts _ _ ws' _ = SOME (rs, aevs, ws1)’ >>
  PairCases_on ‘ws'’ >> PairCases_on ‘ws1’ >> PairCases_on ‘ws’ >> fs[] >>
  (* l0_rely, fds_lt and fd0_ok at round n *)
  mp_tac (Q.INST [‘N’ |-> ‘n’] l1ep_refines_ehl_upto_sent) >> impl_tac >- fs[] >>
  disch_then (qspecl_then [‘n’, ‘h'’, ‘(ws'0, ws'1)’, ‘evs'’, ‘logs'’] mp_tac) >>
  simp[] >> strip_tac >>
  ‘fd0_ok ws'0 ws'1’
    by (mp_tac l0_ep_sent_run >> impl_tac >- fs[] >>
        disch_then (qspecl_then [‘n’, ‘h'’, ‘(ws'0, ws'1)’, ‘evs'’, ‘logs'’] mp_tac) >>
        simp[]) >>
  qpat_x_assum ‘eacts _ _ _ _ = _’ assume_tac >>
  drule_all eacts_fdg >> strip_tac >>
  drule_all eacts_fd0 >> strip_tac >>
  ‘noclose g tevs’ by (drule etail_noclose >> fs[fdg_ok_def]) >>
  drule_all etail_fdg >> simp[]
QED

Theorem erounds_no_close_stdio:
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
  MEM 0w (l0_used w0) ∧ MEM 1w (l0_used w0) ∧ MEM 2w (l0_used w0) ∧
  (∀n. SND (ecm lfd pol ifds m w0 n) + 1 < dimword (:64)) ⇒
  ∀n h ws evs logs.
    erounds lfd pol ifds m (w0, einit) n = SOME (h, ws, evs, logs) ⇒
    no_close_stdio evs
Proof
  rpt strip_tac >>
  ‘∀g. MEM g (l0_used w0) ⇒ noclose g evs’
    by (rpt strip_tac >> drule_at (Pos last) erounds_fdg >> simp[]) >>
  rw[no_close_stdio_def] >> strip_tac >>
  rpt (first_x_assum (qspec_then ‘bytes_fd conf’ mp_tac)) >>
  simp[noclose_def] >> metis_tac[]
QED
