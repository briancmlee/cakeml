(*
  Episodes of the PF run's trace (design/47 D, step i): the trace's
  accepted fds are exactly L1's new connections, in order, round by round
  (only the fetch accepts), so the trace's episode j is the version-2
  world's client j.
*)
Theory honestL1PFEpisode
Ancestors
  honestL1PFConnTrace honestL1PFObl honestL1BStmts honestL1BFaith honestL1BRuns
  honestL1PFConnRun honestL1PFClient honestL1PFLive honestL1PFRound honestL1PFRefine
  honestL1PFModel honestL1Model honestEchoL0Spec honestL0WorldProps honestL0Rely
  honestL0World honestL0
Libs
  preamble

Theorem l0_accepted_APPEND[simp]:
  l0_accepted (a ++ b) = l0_accepted a ++ l0_accepted b
Proof
  simp[l0_accepted_def]
QED

Theorem l0_accepted_CONS_none:
  l0_event_accepted ev = NONE ⇒ l0_accepted (ev :: evs) = l0_accepted evs
Proof
  simp[l0_accepted_def]
QED

(* ------------------------------------------------------------------------
   Only the fetch accepts
   ------------------------------------------------------------------------ *)

Theorem sys_noacc:
  (sys_recv f k w = SOME (out, w', ev) ⇒ l0_event_accepted ev = NONE) ∧
  (sys_send f bs w = SOME (out, w', ev) ⇒ l0_event_accepted ev = NONE) ∧
  (sys_close f w = SOME (out, w', ev) ⇒ l0_event_accepted ev = NONE) ∧
  (sys_poll fes w = SOME (out, w', ev) ⇒ l0_event_accepted ev = NONE)
Proof
  rw[sys_recv_def, sys_send_def, sys_close_def, sys_poll_def, l0_do_def,
     l0_do_buf_def, AllCaseEqs()] >>
  simp[l0_event_accepted_def]
QED

Theorem l1_close_noacc:
  l1_close f (w, st) = SOME ((w', st'), evs) ⇒ l0_accepted evs = []
Proof
  rw[l1_close_def, AllCaseEqs()] >> TRY (PairCases_on ‘v’) >> gvs[] >>
  imp_res_tac sys_noacc >> simp[l0_accepted_def]
QED

Theorem pdo_noacc:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ⇒ l0_accepted evs = []
Proof
  Cases_on ‘a’ >> rw[pdo_def, AllCaseEqs()] >> gvs[] >>
  TRY (PairCases_on ‘z’ >> gvs[]) >> TRY (imp_res_tac l1_close_noacc >> NO_TAC) >>
  gvs[l1do_def, AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac sys_noacc >> imp_res_tac l1_close_noacc >> gvs[l0_accepted_def]
QED

Theorem pacts_noacc:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ⇒ l0_accepted evs = []
Proof
  Induct >> rw[pacts_def, AllCaseEqs()] >> TRY (simp[l0_accepted_def] >> NO_TAC) >>
  PairCases_on ‘ws1’ >>
  res_tac >> imp_res_tac pdo_noacc >> simp[]
QED

Theorem polls_noacc:
  ∀chs w rv w' evs. l1_polls chs w = SOME (rv, w', evs) ⇒ l0_accepted evs = []
Proof
  Induct >> rw[l1_polls_def, AllCaseEqs()] >> TRY (simp[l0_accepted_def] >> NO_TAC) >>
  res_tac >> imp_res_tac sys_noacc >>
  simp[l0_accepted_CONS_none]
QED

Theorem flush_noacc:
  ∀fs w st w' st' evs. l1_flush fs (w, st) = SOME ((w', st'), evs) ⇒ l0_accepted evs = []
Proof
  Induct >> rw[l1_flush_def, AllCaseEqs()] >> TRY (simp[l0_accepted_def] >> NO_TAC) >>
  res_tac >> imp_res_tac sys_noacc >>
  simp[l0_accepted_CONS_none]
QED

Theorem reap_noacc:
  ∀fs w st w' st' evs. l1_reap fs (w, st) = SOME ((w', st'), evs) ⇒ l0_accepted evs = []
Proof
  Induct >> rw[l1_reap_def, AllCaseEqs()] >> TRY (simp[l0_accepted_def] >> NO_TAC) >>
  TRY (PairCases_on ‘ws’) >>
  res_tac >> imp_res_tac l1_close_noacc >> simp[]
QED

Theorem sys_accept_failed:
  sys_accept l w = SOME (out, w', ev) ∧ l0_rely w ∧ l0_res_of out = Fail e x ⇒
  l0_event_accepted ev = NONE
Proof
  rw[sys_accept_def, l0_do_def, AllCaseEqs()] >>
  drule_all l0_ffi_fn_length >> strip_tac >>
  gvs[l0_event_accepted_def, l0_ev_res_def, MAP_ZIP, l0_res_of_def, AllCaseEqs()] >>
  every_case_tac >> gvs[]
QED

(* The fetch's accepted fds are exactly its new connections, in order *)
Theorem pf_fetch_acc_eq:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ l0_rely w ⇒
    l0_accepted evs = log_conns log
Proof
  Induct >- simp[pf_fetch_def, log_conns_def, l0_accepted_def] >>
  simp[pf_fetch_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> rw[] >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >>
  imp_res_tac rplays_sys >> gvs[rplays_def] >>
  first_x_assum drule_all >> strip_tac >>
  imp_res_tac sys_noacc >> fs[log_conns_def, l0_accepted_def] >>
  TRY (drule_all sys_accept_accepted >> simp[] >> NO_TAC) >>
  drule_all sys_accept_failed >> simp[]
QED

(* A round's accepted fds are exactly its fetch log's new connections *)
Theorem pround_acc_eq:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧ l0_rely w ⇒
  l0_accepted evs = log_conns log
Proof
  rw[pround_def, AllCaseEqs()] >> PairCases_on ‘ws1’ >> gvs[pf_tail_def, AllCaseEqs()] >>
  imp_res_tac rplays_pacts >> imp_res_tac rplays_polls >> imp_res_tac rplays_flush >>
  gvs[rplays_def] >> drule_all pf_fetch_acc_eq >> strip_tac >>
  imp_res_tac pacts_noacc >> imp_res_tac polls_noacc >> imp_res_tac flush_noacc >>
  imp_res_tac reap_noacc >> simp[]
QED

(* ------------------------------------------------------------------------
   Along the run: the trace's accepted fds are the clients, in order
   ------------------------------------------------------------------------ *)

Theorem run_acc:
  run_ok lfd pol ifds m w0 ∧ winv w0 ⇒
  ∀n. l0_accepted (revs lfd pol ifds m w0 n) =
      FLAT (GENLIST (λk. log_conns (rlog lfd pol ifds m w0 k)) n)
Proof
  strip_tac >> drule_all winv_run >> strip_tac >>
  Induct >- simp[revs_def, prun_0, l0_accepted_def] >>
  drule_then (qspec_then ‘n’ strip_assume_tac) prun_round >>
  ‘rlog lfd pol ifds m w0 n = log’ by simp[rlog_def] >>
  ‘l0_rely (rworld lfd pol ifds m w0 n)’ by fs[winv_def] >>
  drule_all pround_acc_eq >> simp[GENLIST, SNOC_APPEND]
QED

Theorem log_conns_simps[simp]:
  log_conns [] = [] ∧
  log_conns (FConn c :: l) = c :: log_conns l ∧
  log_conns (FData f bs :: l) = log_conns l ∧
  log_conns (FEof f :: l) = log_conns l ∧
  log_conns (FReset f :: l) = log_conns l
Proof
  simp[log_conns_def]
QED

Theorem arrs_cm:
  ∀l cm k. FST (SND (arrs lfd (cm, k) l)) =
           REVERSE (ZIP (log_conns l, GENLIST (λi. k + i) (LENGTH (log_conns l)))) ++ cm
Proof
  Induct >- simp[arrs_def] >>
  Cases >> rpt gen_tac >> simp[arrs_def]
  >- (Cases_on ‘arrs lfd ((c, k) :: cm, k + 1) l’ >> simp[] >>
      first_x_assum (qspecl_then [‘(c, k) :: cm’, ‘k + 1’] mp_tac) >> simp[] >>
      ‘GENLIST (λi. i + k) (SUC (LENGTH (log_conns l))) =
       k :: GENLIST (λi. i + (k + 1)) (LENGTH (log_conns l))’
        by (REWRITE_TAC[GENLIST_CONS] >> simp[GENLIST_FUN_EQ]) >>
      simp[])
  >> (Cases_on ‘arrs lfd (cm, k) l’ >> simp[] >>
      first_x_assum (qspecl_then [‘cm’, ‘k’] mp_tac) >> simp[])
QED

Theorem pcm_count:
  run_ok lfd pol ifds m w0 ∧ winv w0 ⇒
  ∀n. SND (pcm lfd pol ifds m w0 n) = LENGTH (l0_accepted (revs lfd pol ifds m w0 n))
Proof
  strip_tac >> drule_all run_acc >> strip_tac >> Induct >- simp[pcm_def] >>
  ‘∀x l. SND (SND (arrs lfd x l)) = SND x + LENGTH (log_conns l)’
    by (rpt gen_tac >> PairCases_on ‘x’ >> metis_tac[arrs_nconns, SND]) >>
  simp[pcm_def, plog_rlog, GENLIST, SNOC_APPEND]
QED

Theorem pcm_cm:
  run_ok lfd pol ifds m w0 ∧ winv w0 ⇒
  ∀n. FST (pcm lfd pol ifds m w0 n) =
      REVERSE (ZIP (l0_accepted (revs lfd pol ifds m w0 n),
                    GENLIST I (LENGTH (l0_accepted (revs lfd pol ifds m w0 n)))))
Proof
  strip_tac >> drule_all pcm_count >> drule_all run_acc >> rpt strip_tac >>
  Induct_on ‘n’ >- simp[pcm_def] >>
  simp[pcm_def] >> Cases_on ‘pcm lfd pol ifds m w0 n’ >> simp[arrs_cm] >>
  fs[plog_rlog, GENLIST, SNOC_APPEND] >>
  qmatch_goalsub_abbrev_tac ‘ZIP (A ++ L, _)’ >>
  ‘GENLIST I (LENGTH A + LENGTH L) = GENLIST I (LENGTH A) ++ GENLIST (λi. LENGTH A + i) (LENGTH L)’
    by (ONCE_REWRITE_TAC[ADD_COMM] >> REWRITE_TAC[GENLIST_APPEND] >> simp[GENLIST_FUN_EQ]) >>
  ‘r = LENGTH A’
    by (qpat_x_assum ‘∀n. SND _ = _’ (qspec_then ‘n’ mp_tac) >> simp[Abbr ‘A’]) >>
  pop_assum SUBST_ALL_TAC >> asm_rewrite_tac[] >>
  ‘ZIP (A ++ L, GENLIST I (LENGTH A) ++ GENLIST (λi. i + LENGTH A) (LENGTH L)) =
   ZIP (A, GENLIST I (LENGTH A)) ++ ZIP (L, GENLIST (λi. i + LENGTH A) (LENGTH L))’
    by metis_tac[ZIP_APPEND, LENGTH_GENLIST] >>
  simp[REVERSE_APPEND]
QED

Theorem alookup_rev_zip:
  ∀A j f. j < LENGTH A ∧ EL j A = f ∧ ¬MEM f (DROP (SUC j) A) ⇒
          ALOOKUP (REVERSE (ZIP (A, GENLIST I (LENGTH A)))) f = SOME j
Proof
  ho_match_mp_tac SNOC_INDUCT >> simp[] >> rpt strip_tac >>
  ‘GENLIST I (SUC (LENGTH A)) = SNOC (LENGTH A) (GENLIST I (LENGTH A))’
    by simp[GENLIST] >>
  simp[ZIP_SNOC, REVERSE_SNOC] >>
  Cases_on ‘j = LENGTH A’ >- gvs[EL_LENGTH_SNOC] >>
  ‘j < LENGTH A’ by simp[] >>
  ‘DROP (SUC j) (SNOC x A) = SNOC x (DROP (SUC j) A)’ by simp[DROP_SNOC] >>
  gvs[EL_SNOC, MEM_SNOC]
QED

(* While episode j is open, its fd's client in psk is j *)
Theorem cl_episode:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ ep_open j (revs lfd pol ifds m w0 n) ⇒
  j < LENGTH (l0_accepted (revs lfd pol ifds m w0 n)) ∧
  cl (FST (pcm lfd pol ifds m w0 n)) (EL j (l0_accepted (revs lfd pol ifds m w0 n))) = j
Proof
  strip_tac >> drule_all pcm_cm >> disch_then (qspec_then ‘n’ assume_tac) >>
  qabbrev_tac ‘acc = l0_accepted (revs lfd pol ifds m w0 n)’ >>
  fs[ep_open_def] >>
  ‘¬MEM f (l0_accepted post)’
    by (CCONTR_TAC >> fs[l0_accepted_def, MEM_FLAT, MEM_MAP, EVERY_MEM, ep_ends_def] >>
        gvs[AllCaseEqs()] >> metis_tac[]) >>
  ‘acc = l0_accepted pre ++ [f] ++ l0_accepted post’
    by (simp[Abbr ‘acc’] >> fs[l0_accepted_def]) >>
  ‘j < LENGTH acc ∧ EL j acc = f’ by simp[EL_APPEND2, EL_APPEND1] >>
  ‘DROP (SUC j) acc = l0_accepted post’
    by (‘SUC j = LENGTH (l0_accepted pre ++ [f])’ by simp[] >> pop_assum SUBST1_TAC >>
        qpat_assum ‘acc = _’ (fn th => REWRITE_TAC[th]) >> REWRITE_TAC[DROP_LENGTH_APPEND]) >>
  ‘ALOOKUP (REVERSE (ZIP (acc, GENLIST I (LENGTH acc)))) f = SOME j’
    by (irule alookup_rev_zip >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum ‘EL j acc = f’ (fn th => REWRITE_TAC[th]) >>
  qpat_x_assum ‘ALOOKUP _ f = _’ (fn th => REWRITE_TAC[cl_def, th]) >> simp[]
QED
