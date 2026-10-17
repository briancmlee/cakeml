(*
  P4 (design/46), step C: the truncated version-2 world psk_upto N.

  psk (honestL1PFRefine) is the v2 world built from L1's run; its schedule
  is well formed (sched_wf2) only under a bound on the client count for
  EVERY round, which the L1 loop does not give once its handles run out
  (D25).  psk_upto N is psk with no arrivals after round N.

  - The handle layer reads the schedule only when it polls: round n reads
    arrival n.  So two worlds that differ only in their schedules, and
    agree on the arrivals before round n, run the same first n rounds
    (hrounds_future); in particular psk_upto N and psk agree on rounds up
    to SUC N (psk_upto_hst).
  - sched_wf2 (psk_upto N) needs the bound only for the rounds up to N
    (psk_upto_sched_wf2).
*)
Theory honestKvL0Trunc
Ancestors
  llist socketV2FFI socketV2Fair socketV2Events asyncHLModel honestL1PFModel honestL1PFRefine
Libs
  preamble

(* ------------------------------------------------------------------------
   The handle layer does not read the schedule, except when it polls
   ------------------------------------------------------------------------ *)

Theorem client_of_future[simp]:
  client_of (s with future := f) = client_of s
Proof
  simp[FUN_EQ_THM, client_of_def]
QED

Theorem used_fds_future[simp]:
  used_fds (s with future := f) = used_fds s
Proof
  simp[used_fds_def]
QED

Theorem hdo_future:
  hdo lfd (s with future := f, hs) a =
    OPTION_MAP (λ(r, (s', hs'), evs). (r, (s' with future := f, hs'), evs)) (hdo lfd (s, hs) a)
Proof
  Cases_on ‘a’ >>
  simp[hdo_def, sock_accept2_def, sock_read2_def, sock_write2_def, sock_close2_def,
       update_client_def] >>
  rpt CASE_TAC >> fs[client_of_def]
QED

Theorem hacts_future:
  ∀acts s hs.
    hacts lfd (s with future := f, hs) acts =
      OPTION_MAP (λ(rs, evs, (s', hs')). (rs, evs, (s' with future := f, hs')))
        (hacts lfd (s, hs) acts)
Proof
  Induct >> simp[hacts_def, hdo_future] >> rpt gen_tac >>
  Cases_on ‘hdo lfd (s, hs) h’ >> simp[] >>
  rename1 ‘hdo _ _ _ = SOME x’ >> PairCases_on ‘x’ >> simp[] >>
  Cases_on ‘hacts lfd (x1, x2) acts’ >> simp[] >>
  rename1 ‘hacts _ _ _ = SOME y’ >> PairCases_on ‘y’ >> simp[]
QED

Theorem hacts_tot_future:
  hacts_tot lfd (s with future := f, hs) acts =
    (λ(rs, evs, (s', hs')). (rs, evs, (s' with future := f, hs'))) (hacts_tot lfd (s, hs) acts)
Proof
  simp[hacts_tot_def, hacts_future] >>
  Cases_on ‘hacts lfd (s, hs) acts’ >> simp[] >>
  rename1 ‘hacts _ _ _ = SOME y’ >> PairCases_on ‘y’ >> simp[]
QED

Theorem deliver2_future:
  deliver2 (s with future := f) a = (deliver2 s a) with future := f
Proof
  Cases_on ‘a’ >> rw[deliver2_def, update_client_def]
QED

Theorem FOLDL_deliver2_future:
  ∀as s. FOLDL deliver2 (s with future := f) as = (FOLDL deliver2 s as) with future := f
Proof
  Induct >> simp[deliver2_future]
QED

Theorem tick2_LGENLIST:
  tick2 (s with future := LGENLIST f NONE) =
    (FOLDL deliver2 s (f 0)) with future := LGENLIST (λi. f (SUC i)) NONE
Proof
  simp[tick2_def, FOLDL_deliver2_future, combinTheory.o_DEF]
QED

Theorem is_ready2_future:
  is_ready2 (s with future := f) = is_ready2 s
Proof
  simp[FUN_EQ_THM, is_ready2_def, client_of_def]
QED

(* The state of the handle layer's run after n rounds, in a world with the
   schedule LGENLIST f: its own world with the rest of the schedule *)
Definition fstate_def:
  fstate f n (st : sockets2 # hstate) =
    ((FST st) with future := LGENLIST (λi. f (n + i)) NONE, SND st)
End

(* MAIN: two schedules that agree before round n give the same first n
   rounds *)
Theorem hrounds_future:
  ∀n. (∀i. i < n ⇒ f i = g i) ⇒
      hrounds lfd ifds m (s0 with future := LGENLIST g NONE) n =
        (FST (hrounds lfd ifds m (s0 with future := LGENLIST f NONE) n),
         fstate g n (SND (hrounds lfd ifds m (s0 with future := LGENLIST f NONE) n))) ∧
      (FST (SND (hrounds lfd ifds m (s0 with future := LGENLIST f NONE) n))).future =
        LGENLIST (λi. f (n + i)) NONE
Proof
  Induct
  >- (simp[hrounds_def, fstate_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  strip_tac >> fs[] >>
  qabbrev_tac ‘sf = s0 with future := LGENLIST f NONE’ >>
  qabbrev_tac ‘sg = s0 with future := LGENLIST g NONE’ >>
  Cases_on ‘hrounds lfd ifds m sf n’ >> rename1 ‘_ = (h, st)’ >>
  PairCases_on ‘st’ >> rename1 ‘_ = (h, (s, hs))’ >> fs[fstate_def] >>
  simp[hrounds_def] >>
  qabbrev_tac ‘sb = s with future := LNIL’ >>
  ‘s = sb with future := LGENLIST (λi. f (i + n)) NONE’
    by (qpat_x_assum ‘s.future = _’ mp_tac >>
        simp[Abbr ‘sb’, socketV2FFITheory.sockets2_component_equality]) >>
  ‘s with future := LGENLIST (λi. g (i + n)) NONE = sb with future := LGENLIST (λi. g (i + n)) NONE’
    by simp[Abbr ‘sb’] >>
  ntac 2 (pop_assum SUBST1_TAC) >>
  simp[hacts_tot_future] >>
  Cases_on ‘hacts_tot lfd (sb, hs) (new_actions (log_of m) h)’ >>
  rename1 ‘_ = (rs, r2)’ >> PairCases_on ‘r2’ >> simp[] >>
  simp[hpoll_def, sock_poll2_def, tick2_LGENLIST, is_ready2_future] >>
  simp[is_ready2_future] >> rpt conj_tac >>
  rpt (AP_THM_TAC ORELSE AP_TERM_TAC) >> simp[FUN_EQ_THM] >>
  rw[] >> AP_TERM_TAC >> decide_tac
QED

(* ------------------------------------------------------------------------
   The world left alone, under a changed schedule
   ------------------------------------------------------------------------ *)

Theorem ticks2_LGENLIST_future:
  ∀n s g. (ticks2 n (s with future := LGENLIST g NONE)).future = LGENLIST (λi. g (n + i)) NONE
Proof
  Induct >> simp[ticks2_def, tick2_LGENLIST]
  >- (CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  rpt gen_tac >> AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM, ADD_CLAUSES]
QED

Theorem ticks2_sched:
  ∀n s f g. (∀i. i < n ⇒ f i = g i) ⇒
    ticks2 n (s with future := LGENLIST g NONE) =
      (ticks2 n (s with future := LGENLIST f NONE)) with future := LGENLIST (λi. g (n + i)) NONE
Proof
  Induct
  >- (simp[ticks2_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  rpt strip_tac >> simp[ticks2_def, tick2_LGENLIST] >>
  ‘f 0 = g 0’ by simp[] >> simp[] >>
  first_x_assum (qspecl_then [‘FOLDL deliver2 s (g 0)’, ‘λi. f (SUC i)’, ‘λi. g (SUC i)’] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then SUBST1_TAC >>
  rpt (AP_THM_TAC ORELSE AP_TERM_TAC) >> simp[FUN_EQ_THM] >>
  rw[] >> AP_TERM_TAC >> decide_tac
QED

Theorem step_ok2_future:
  ∀as s. step_ok2 (s with future := x) as ⇔ step_ok2 s as
Proof
  Induct >> simp[step_ok2_def, deliver2_future] >> Cases >> simp[arrival_ok2_def]
QED

(* ------------------------------------------------------------------------
   Round n of psk's schedule is effective, given the bound up to SUC n
   (psk_sched_wf2's proof, with l1pf_refines_hl_upto)
   ------------------------------------------------------------------------ *)

Theorem psk_step_ok:
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n'. n' ≤ SUC n ⇒ SND (pcm lfd pol ifds m w0 n') + 1 < dimword (:64)) ⇒
  step_ok2 (ticks2 n (psk lfd pol ifds m w0)) (parr lfd pol ifds m w0 n)
Proof
  strip_tac >>
  qspecl_then [‘parr lfd pol ifds m w0 n’, ‘ticks2 n (psk lfd pol ifds m w0)’,
               ‘FST (hst lfd ifds m (psk lfd pol ifds m w0) n)’] mp_tac step_ok2_agree >>
  simp[agree_run] >> disch_then kall_tac >>
  Cases_on ‘prounds lfd pol ifds m (w0, pinit) (SUC n)’
  >- (simp[parr_def, plog_def] >> Cases_on ‘pcm lfd pol ifds m w0 n’ >>
      simp[arrs_def, step_ok2_def]) >>
  rename1 ‘_ = SOME x’ >> PairCases_on ‘x’ >>
  qpat_assum ‘prounds _ _ _ _ _ (SUC _) = _’
    (strip_assume_tac o SIMP_RULE (srw_ss()) [AllCaseEqs()] o
     ONCE_REWRITE_RULE [prounds_def]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rename1 ‘prounds _ _ _ _ _ n = SOME (h0, ws0, evs0, logs0)’ >>
  rename1 ‘pround _ _ _ _ _ = SOME (snap, ws1, log, revs)’ >>
  mp_tac (Q.INST [‘N’ |-> ‘SUC n’] l1pf_refines_hl_upto) >>
  impl_tac >- simp[] >>
  disch_then (qpat_assum ‘prounds _ _ _ _ _ n = _’ o mp_then Any mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  ‘hacts_of lfd ifds m (psk lfd pol ifds m w0) n = new_actions (log_of m) h0’
    by simp[hacts_of_def] >>
  PairCases_on ‘ws0’ >> rename1 ‘prounds _ _ _ _ _ n = SOME (h0, (w, ps), evs0, logs0)’ >>
  PairCases_on ‘ws1’ >> rename1 ‘pround _ _ _ _ _ = SOME (snap, (w', ps'), log, revs)’ >>
  gvs[] >>
  Cases_on ‘hst lfd ifds m (psk lfd pol ifds m w0) n’ >> rename1 ‘_ = (s, hs)’ >> gvs[] >>
  ‘plog lfd pol ifds m w0 n = log’
    by (drule prounds_logs >> strip_tac >>
        qpat_x_assum ‘prounds _ _ _ _ _ (SUC n) = _’ assume_tac >>
        drule plog_EL >> disch_then (qspec_then ‘n’ mp_tac) >>
        simp[EL_APPEND2]) >>
  Cases_on ‘pcm lfd pol ifds m w0 n’ >> rename1 ‘pcm _ _ _ _ _ n = (cm, k)’ >> gvs[] >>
  Cases_on ‘arrs lfd (cm, LENGTH s.clients) (plog lfd pol ifds m w0 n)’ >>
  rename1 ‘_ = (as, ck)’ >> PairCases_on ‘ck’ >>
  ‘pcm lfd pol ifds m w0 (SUC n) = (ck0, ck1) ∧ parr lfd pol ifds m w0 n = as’
    by simp[pcm_def, parr_def] >>
  ‘∀f j. MEM (f, j) ck0 ∧ LENGTH s.clients ≤ j ⇒
         ∀used. ¬MEM f used ⇒ s.alloc j used = f’
    by (rw[] >> irule run_alloc_eq >> simp[] >> qexists_tac ‘SUC n’ >> simp[]) >>
  ‘LHD s.future = SOME as’ by simp[] >>
  ‘ck1 + 1 < dimword (:64)’
    by (qpat_assum ‘∀n'. n' ≤ SUC n ⇒ SND (pcm _ _ _ _ _ n') + 1 < _’ (mp_tac o Q.SPEC ‘SUC n’) >>
        qpat_assum ‘pcm _ _ _ _ _ (SUC n) = _’ (fn th => REWRITE_TAC [th]) >>
        simp[]) >>
  drule_all round_rel >> strip_tac >>
  drule hacts_agree >> strip_tac >>
  qspecl_then [‘as’, ‘s1’, ‘s’] mp_tac step_ok2_agree >> simp[]
QED

(* ------------------------------------------------------------------------
   psk_upto N: psk with the arrivals of the first N rounds only
   ------------------------------------------------------------------------ *)

Definition psk_upto_def:
  psk_upto N lfd pol ifds m w0 =
    psk lfd pol ifds m w0 with
      future := LGENLIST (λi. if i < N then parr lfd pol ifds m w0 i else []) NONE
End

Theorem psk_upto_ticks2:
  n ≤ N ⇒
  ticks2 n (psk_upto N lfd pol ifds m w0) =
    ticks2 n (psk lfd pol ifds m w0) with
      future := LGENLIST (λi. if n + i < N then parr lfd pol ifds m w0 (n + i) else []) NONE
Proof
  strip_tac >> simp[psk_upto_def] >>
  qspecl_then [‘n’, ‘psk lfd pol ifds m w0’, ‘parr lfd pol ifds m w0’,
               ‘λi. if i < N then parr lfd pol ifds m w0 i else []’] mp_tac ticks2_sched >>
  impl_tac >- simp[] >>
  disch_then SUBST1_TAC >>
  ‘psk lfd pol ifds m w0 with future := LGENLIST (parr lfd pol ifds m w0) NONE =
   psk lfd pol ifds m w0’ by simp[psk_def] >>
  pop_assum SUBST1_TAC >> simp[]
QED

(* MAIN: the truncated world's schedule is well formed, given the bound on
   the client count for the rounds up to N only *)
Theorem psk_upto_sched_wf2:
  l0_rely w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n'. n' ≤ N ⇒ SND (pcm lfd pol ifds m w0 n') + 1 < dimword (:64)) ⇒
  sched_wf2 (psk_upto N lfd pol ifds m w0)
Proof
  strip_tac >> simp[sched_wf2_def, next_step2_def] >> gen_tac >>
  ‘(ticks2 n (psk_upto N lfd pol ifds m w0)).future =
   LGENLIST (λi. if n + i < N then parr lfd pol ifds m w0 (n + i) else []) NONE’
    by simp[psk_upto_def, ticks2_LGENLIST_future] >>
  simp[] >>
  Cases_on ‘n < N’ >> simp[step_ok2_def] >>
  simp[psk_upto_ticks2, step_ok2_future] >>
  irule psk_step_ok >> simp[]
QED

(* MAIN: psk_upto N runs as psk for the first N rounds *)
Theorem psk_upto_hst:
  n ≤ N ⇒
  hhist lfd ifds m (psk_upto N lfd pol ifds m w0) n = hhist lfd ifds m (psk lfd pol ifds m w0) n ∧
  hst lfd ifds m (psk_upto N lfd pol ifds m w0) n =
    ((FST (hst lfd ifds m (psk lfd pol ifds m w0) n)) with
       future := LGENLIST (λi. if n + i < N then parr lfd pol ifds m w0 (n + i) else []) NONE,
     SND (hst lfd ifds m (psk lfd pol ifds m w0) n))
Proof
  strip_tac >>
  qspecl_then [‘n’] mp_tac
    (Q.INST [‘f’ |-> ‘parr lfd pol ifds m w0’,
             ‘g’ |-> ‘λi. if i < N then parr lfd pol ifds m w0 i else []’,
             ‘s0’ |-> ‘psk lfd pol ifds m w0’] hrounds_future) >>
  impl_tac >- simp[] >>
  ‘psk lfd pol ifds m w0 with future := LGENLIST (parr lfd pol ifds m w0) NONE =
   psk lfd pol ifds m w0’ by simp[psk_def] >>
  pop_assum SUBST1_TAC >>
  simp[GSYM psk_upto_def, hhist_def, hst_def, fstate_def] >> strip_tac >>
  Cases_on ‘hrounds lfd ifds m (psk lfd pol ifds m w0) n’ >> simp[] >>
  Cases_on ‘r’ >> simp[]
QED
