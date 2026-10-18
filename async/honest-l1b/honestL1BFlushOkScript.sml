(*
  L3-09 (S3), D32 step 3b: flush_ok holds.  A PF prefix with episode j's
  channel flushed while the episode is open is matched by a blocking
  prefix with the same non-poll events and the channel flushed
  (honestL1BFlushXfer.p2b_fl, case A), unless it falls inside an idle round
  whose blocking poll never returns (case B).  Case B cannot happen while
  the blocking trace has episode j open on channel c: the run then sleeps
  after that round, so the episode's accept is in the round's events, its
  fd f is held (run_acc_owned) under a handle on the interest list (S1),
  f keeps channel c (replay_chan_keep, with no connect: bpre_nc), and a
  break on c wakes the idle poll (idle_break_wakes).

  MAIN: flush_ok_holds.
*)
Theory honestL1BFlushOk
Ancestors
  honestL1BNoConn honestL1BChanKeep honestL1BFlushXfer honestL1BFlush honestL1BLive
  honestL1BDrains honestL1BTransfer honestL1BCorr honestL1BObs honestL1BRuns honestL1BSim
  honestL1BRefine honestL1BPoll honestL1BModel honestL1BStmts honestL0Reindex
  honestL1PFOwn honestL1PFConnRun honestL1PFConn honestL1PFLive honestL1PFInv
  honestL1PFRound honestL1PFRefine honestL1PFModel honestL1Inv honestL1Model honestL0Part
  honestEchoL0Spec honestL0WorldInv
  honestL0WorldProps honestL0World honestL0
Libs
  preamble

(* ------------------------------------------------------------------------
   Trace facts
   ------------------------------------------------------------------------ *)

Theorem accepted_not_poll[local]:
  l0_event_accepted ev = SOME f ⇒ ¬is_poll ev
Proof
  metis_tac[poll_not_accepted, optionTheory.NOT_NONE_SOME]
QED

Theorem close_nopoll:
  ∀l. EXISTS (l0_close_call f) (nopoll l) ⇔ EXISTS (l0_close_call f) l
Proof
  Induct >> simp[nopoll_def] >> Cases >> rw[is_poll_def, l0_close_call_def] >>
  fs[nopoll_def]
QED

Theorem l0_accepted_append[local]:
  l0_accepted (a ++ b) = l0_accepted a ++ l0_accepted b
Proof
  simp[l0_accepted_def]
QED

(* The j-th accept sits at one place *)
Theorem acc_pos_unique:
  ∀x x' e e' y y'.
    x ++ [e] ++ y = x' ++ [e'] ++ y' ∧ l0_event_accepted e ≠ NONE ∧
    l0_event_accepted e' ≠ NONE ∧ LENGTH (l0_accepted x) = LENGTH (l0_accepted x') ⇒
    x = x' ∧ e = e' ∧ y = y'
Proof
  Induct >> Cases_on ‘x'’ >> simp[] >> rpt gen_tac >> strip_tac >> gvs[l0_accepted_def] >>
  every_case_tac >> gvs[] >> first_x_assum drule >> simp[]
QED

Theorem nopoll_mid[local]:
  l0_event_accepted ev = SOME f ⇒
  nopoll (pre ++ [ev] ++ post) = nopoll pre ++ [ev] ++ nopoll post
Proof
  strip_tac >> drule accepted_not_poll >> simp[nopoll_def]
QED

(* A blocking prefix with the PF prefix's non-poll events splits at the
   episode's accept, and an open blocking prefix of it ends before no close
   call on its fd *)
Theorem open_suffix:
  evs ≼ bp ∧ ep_open j evs ∧ nopoll bp = nopoll (pre ++ [ev] ++ post) ∧
  LENGTH (l0_accepted pre) = j ∧ l0_event_accepted ev = SOME f ∧
  ¬EXISTS (l0_close_call f) post ⇒
  EL j (l0_accepted evs) = f ∧ ∃s. bp = evs ++ s ∧ ¬EXISTS (l0_close_call f) s
Proof
  strip_tac >> drule nopoll_mid >> disch_then (qspecl_then [‘pre’, ‘post’] assume_tac) >>
  ‘nopoll bp = nopoll pre ++ [ev] ++ nopoll post’ by metis_tac[] >>
  drule nopoll_split >> strip_tac >>
  qpat_x_assum ‘ep_open _ _’ (strip_assume_tac o REWRITE_RULE[ep_open_def]) >>
  qpat_x_assum ‘evs ≼ bp’ (strip_assume_tac o REWRITE_RULE[IS_PREFIX_APPEND]) >>
  rename1 ‘bp = evs ++ s’ >>
  ‘LENGTH (l0_accepted a') = j’ by metis_tac[nopoll_accepted] >>
  ‘a' ++ [ev] ++ b' = pre' ++ [ev'] ++ (post' ++ s)’ by gvs[] >>
  drule acc_pos_unique >> simp[] >> strip_tac >> gvs[] >>
  ‘¬EXISTS (l0_close_call f) (post' ++ s)’
    by (ONCE_REWRITE_TAC[GSYM close_nopoll] >> REWRITE_TAC[nopoll_append] >>
        asm_rewrite_tac[] >> REWRITE_TAC[close_nopoll] >> fs[EVERY_MEM, EXISTS_MEM]) >>
  simp[l0_accepted_append] >>
  ‘l0_accepted [ev] = [f]’ by simp[l0_accepted_def] >> pop_assum SUBST1_TAC >>
  qpat_x_assum ‘LENGTH (l0_accepted a') = _’ (SUBST1_TAC o SYM) >>
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> simp[EL_APPEND2] >> fs[EVERY_MEM, EXISTS_MEM]
QED

(* ------------------------------------------------------------------------
   Case A: the PF flush shows on a blocking prefix
   ------------------------------------------------------------------------ *)

Theorem flush_case_a:
  btrace lfd hw ifds bz m w0 ps0 io_b ∧ bpre lfd hw ifds bz m (w0, ps0) bp ∧
  nopoll bp = nopoll (pre ++ [ev] ++ post) ∧ world_at w0 bp = SOME wb ∧ fl c wb ∧
  LENGTH (l0_accepted pre) = j ∧ l0_event_accepted ev = SOME f ∧
  ¬EXISTS (l0_close_call f) post ⇒
  flushed_open w0 io_b j c
Proof
  strip_tac >> drule nopoll_mid >> disch_then (qspecl_then [‘pre’, ‘post’] assume_tac) >>
  ‘nopoll bp = nopoll pre ++ [ev] ++ nopoll post’ by metis_tac[] >>
  drule nopoll_split >> strip_tac >>
  simp[flushed_open_def] >> qexistsl_tac [‘a'’, ‘ev’, ‘b'’, ‘f’, ‘wb’] >>
  ‘¬EXISTS (l0_close_call f) b'’
    by (ONCE_REWRITE_TAC[GSYM close_nopoll] >> asm_rewrite_tac[] >>
        REWRITE_TAC[close_nopoll] >> first_assum ACCEPT_TAC) >>
  rpt conj_tac
  >- metis_tac[btrace_def]
  >- metis_tac[nopoll_accepted]
  >- simp[]
  >- fs[EVERY_MEM, EXISTS_MEM]
  >- gvs[]
  >> fs[fl_def]
QED

(* ------------------------------------------------------------------------
   winv along blocking prefixes
   ------------------------------------------------------------------------ *)

Theorem FOLDL_step_NONE[local]:
  ∀cs. FOLDL l0_step NONE cs = NONE
Proof
  Induct >> simp[l0_step_def]
QED

Theorem winv_unreindex:
  l0_rely w ∧ winv (reindex tr w) ⇒ winv w
Proof
  strip_tac >> fs[winv_def, reindex_def, l0wf_def, noconn_def, fds_lt_def, errb_def, used_chans_def,
       l0_used_def] >> metis_tac[]
QED

Theorem step_winv[local]:
  l0_step (SOME w) (n, conf, bytes) = SOME w' ∧ winv w ∧ n ≠ «sys_connect» ⇒ winv w'
Proof
  rw[l0_step_def, AllCaseEqs()] >> rename1 ‘FFIreturn out1 w'’ >>
  ‘l0_do_buf n conf bytes w = SOME (out1, w', IO_event (ExtCall n) conf (ZIP (bytes, out1)))’
    by simp[l0_do_buf_def] >>
  drule_all winv_do_buf >> simp[]
QED

Theorem replay_winv:
  ∀B x y. FOLDL l0_step (SOME x) (MAP ev_lcall B) = SOME y ∧ winv x ∧ nc B ⇒ winv y
Proof
  Induct >- simp[] >> rpt gen_tac >> simp[] >>
  Cases_on ‘l0_step (SOME x) (ev_lcall h)’ >> simp[FOLDL_step_NONE] >> strip_tac >>
  first_x_assum irule >> simp[] >> qexists_tac ‘x'’ >> simp[] >>
  Cases_on ‘ev_lcall h’ >> PairCases_on ‘r’ >> gvs[] >> drule_all step_winv >> simp[]
QED

Theorem world_at_winv:
  winv w0 ∧ world_at w0 evs = SOME w ∧ nc evs ⇒ winv w
Proof
  rw[world_at_def, l0_replay_def] >> drule_all replay_winv >> simp[]
QED

(* ------------------------------------------------------------------------
   Case B: an idle round holds the open episode's fd on the interest list
   ------------------------------------------------------------------------ *)

Theorem acc_ev_accepted[local]:
  l0_event_accepted ev = SOME f ⇒ honestL1PFOwn$acc_ev f ev
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event nm cf bs’ >> Cases_on ‘nm’ >>
  rw[l0_event_accepted_def, acc_ev_def, l0_ev_res_def, AllCaseEqs()] >> simp[]
QED

Theorem close_ev_call[local]:
  close_ev f e ⇔ l0_close_call f e
Proof
  Cases_on ‘e’ >> simp[close_ev_def, l0_close_call_def]
QED

Theorem acq_idle[local]:
  pf_ready lfd ps hs = [] ∧ MEM lfd hs ∧ ALOOKUP ps.b.tbl lfd = NONE ⇒ ps.acq = []
Proof
  rw[pf_ready_def, FILTER_EQ_NIL, EVERY_MEM] >> first_x_assum drule >> simp[]
QED

Theorem idle_held:
  bquiet m ifds bz ∧
  run_ok lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ∧
  winv (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ∧
  MEM lfd (l0_used (reindex (btr lfd hw ifds bz m (w0, pinit)) w0)) ∧
  (∀n. SND (pcm lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) n) + 1 <
       dimword (:64)) ∧
  S1 lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ∧
  brounds lfd hw ifds bz m (w0, pinit) n = SOME (BRun h (wb, ps) bp logs) ∧
  bidle lfd hw ifds bz m h ps ∧
  nopoll bp = nopoll (pre ++ [ev] ++ post) ∧ l0_event_accepted ev = SOME f ∧
  ¬EXISTS (l0_close_call f) post ⇒
  ∃hh. ALOOKUP ps.b.tbl hh = SOME f ∧ MEM hh (ifds h) ∧ f ≠ lfd ∧ small f
Proof
  strip_tac >>
  ‘binv lfd hw ifds bz m w0 pinit h wb ps bp’
    by (qpat_assum ‘brounds _ _ _ _ _ _ n = _’ mp_tac >>
        qpat_assum ‘bquiet _ _ _’ (fn th => REWRITE_TAC[MATCH_MP l1b_refines_pf th])) >>
  pop_assum (strip_assume_tac o REWRITE_RULE[binv_def, binv_at_def]) >>
  qabbrev_tac ‘pw = reindex (btr lfd hw ifds bz m (w0, pinit)) w0’ >>
  ‘prun lfd hw ifds m pw N = (full, (lift (btr lfd hw ifds bz m (w0, pinit)) (w0.hist ++ xs) wb, ps),
                             pevs, plogs)’
    by (simp[prun_def] >> qpat_assum ‘prounds _ _ _ _ _ N = _’ (fn th => REWRITE_TAC[th]) >>
        simp[]) >>
  ‘rstate lfd hw ifds m pw N = ps ∧ rhist lfd hw ifds m pw N = full ∧
   revs lfd hw ifds m pw N = pevs’
    by (REWRITE_TAC[revs_def, rstate_def, rhist_def] >>
        qpat_assum ‘prun _ _ _ _ _ N = _’ (fn th => REWRITE_TAC[th]) >> simp[]) >>
  ‘ifds full = ifds h’
    by (qpat_x_assum ‘sfor _ _ _ _ _’ mp_tac >> simp[sfor_def] >>
        disch_then (qspec_then ‘[]’ mp_tac) >> simp[]) >>
  (* the episode's accept, with no close after it, in the PF events *)
  ‘nopoll pevs = nopoll pre ++ [ev] ++ nopoll post’
    by (drule_then (qspecl_then [‘pre’, ‘post’] assume_tac) nopoll_mid >>
        metis_tac[evrel_nopoll]) >>
  drule nopoll_split >> strip_tac >>
  ‘close_ev f = l0_close_call f’ by simp[FUN_EQ_THM, close_ev_call] >>
  ‘¬EXISTS (close_ev f) b'’
    by (asm_rewrite_tac[] >> ONCE_REWRITE_TAC[GSYM close_nopoll] >> asm_rewrite_tac[] >>
        REWRITE_TAC[close_nopoll] >> fs[EVERY_MEM, EXISTS_MEM]) >>
  ‘owned ps f’
    by (REWRITE_TAC[owned_def] >>
        qpat_x_assum ‘run_ok _ _ _ _ _’ assume_tac >>
        drule run_acc_owned >> disch_then (qspecl_then [‘N’, ‘f’, ‘a'’, ‘ev’, ‘b'’] mp_tac) >>
        impl_tac
        >- (rpt conj_tac
            >- asm_rewrite_tac[]
            >- metis_tac[acc_ev_accepted]
            >> first_assum ACCEPT_TAC) >>
        qpat_x_assum ‘rstate _ _ _ _ _ _ = ps’ (fn th => REWRITE_TAC[th])) >>
  qpat_x_assum ‘run_ok _ _ _ _ _’ assume_tac >>
  drule round_facts >> impl_tac >- simp[] >>
  disch_then (qspec_then ‘N’ strip_assume_tac) >>
  qpat_x_assum ‘rstate _ _ _ _ _ N = ps’
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE[th]) >> assume_tac th) >>
  ‘ALOOKUP ps.b.tbl lfd = NONE’
    by (irule tbl_lfd >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        qpat_assum ‘pown _ _’ (mp_tac o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
                               REWRITE_RULE [honestL1PFRefineTheory.pown_def]) >> simp[]) >>
  ‘pf_idle lfd hw ps (ifds h)’ by fs[bidle_def] >>
  ‘MEM lfd (ifds h)’
    by (qpat_x_assum ‘S1 _ _ _ _ _’ mp_tac >> REWRITE_TAC[S1_def] >>
        disch_then (qspec_then ‘N’ mp_tac o CONJUNCT2) >>
        qpat_x_assum ‘rhist _ _ _ _ _ N = full’ (fn th => REWRITE_TAC[th]) >>
        qpat_x_assum ‘ifds full = ifds h’ (fn th => REWRITE_TAC[th])) >>
  ‘ps.acq = [] ∧ ps.b.closing = []’ by (fs[pf_idle_def] >> drule_all acq_idle >> simp[]) >>
  ‘MEM f (MAP SND ps.b.tbl)’ by fs[owned_def] >>
  ‘∃hh. MEM (hh, f) ps.b.tbl’ by (fs[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  qexists_tac ‘hh’ >>
  ‘ALOOKUP ps.b.tbl hh = SOME f’
    by (irule ALOOKUP_ALL_DISTINCT_MEM >> fs[pown_def]) >>
  rpt conj_tac
  >- simp[]
  >- (qpat_x_assum ‘S1 _ _ _ _ _’ mp_tac >> simp[S1_def] >> strip_tac >>
      first_x_assum (qspecl_then [‘N’, ‘hh’, ‘f’] mp_tac) >> simp[])
  >- (strip_tac >> gvs[pown_def])
  >> fs[psmall_def, small_fds_def, EVERY_MEM]
QED

(* The round after an idle one whose poll never returns sleeps *)
Theorem idle_sleeps[local]:
  brounds lfd hw ifds bz m ws0 n = SOME (BRun h (wb, ps) bp logs) ∧
  bidle lfd hw ifds bz m h ps ∧
  pollb_wait (pf_poll_set lfd hw ps (ifds h)) wb = NONE ⇒
  ∃cb. brounds lfd hw ifds bz m ws0 (SUC n) = SOME (BSlept h bp cb)
Proof
  strip_tac >> fs[bidle_def] >>
  ‘sys_pollb (pf_poll_set lfd hw ps (ifds h)) wb =
     SOME (INR (pollb_conf, poll_buf (pf_poll_set lfd hw ps (ifds h))))’
    by simp[sys_pollb_wait] >>
  simp[brounds_def, bround_def, pacts_def]
QED

Theorem flush_case_b:
  bquiet m ifds bz ∧ l0_rely w0 ∧
  run_ok lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ∧
  winv (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ∧
  MEM lfd (l0_used (reindex (btr lfd hw ifds bz m (w0, pinit)) w0)) ∧
  (∀n. SND (pcm lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) n) + 1 <
       dimword (:64)) ∧
  S1 lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ∧
  (∀ps f. outbox_of ps.b f = [] ⇒ ¬hw ps f) ∧
  bpre lfd hw ifds bz m (w0, pinit) evs ∧ ep_open j evs ∧ world_at w0 evs = SOME w ∧
  l0_chan_of w (EL j (l0_accepted evs)) = SOME c ∧
  brounds lfd hw ifds bz m (w0, pinit) n = SOME (BRun h (wb, ps) bp logs) ∧
  bidle lfd hw ifds bz m h ps ∧ nopoll pp = nopoll bp ∧
  pp = pre ++ [ev] ++ post ∧ LENGTH (l0_accepted pre) = j ∧
  l0_event_accepted ev = SOME f ∧ ¬EXISTS (l0_close_call f) post ∧
  pollb_wait (pf_poll_set lfd hw ps (ifds h)) wb = NONE ∧
  fl c (l0_ticks «sys_poll» i wb) ⇒
  F
Proof
  strip_tac >>
  drule_all idle_sleeps >> strip_tac >>
  ‘evs ≼ bp’ by (irule asleep_prefixes >> metis_tac[]) >>
  ‘EL j (l0_accepted evs) = f ∧ ∃s. bp = evs ++ s ∧ ¬EXISTS (l0_close_call f) s’
    by (irule open_suffix >> metis_tac[]) >>
  qpat_x_assum ‘EL _ _ = f’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE[th])) >>
  ‘winv w0’ by metis_tac[winv_unreindex] >>
  ‘nc bp’ by (irule bpre_nc >> metis_tac[bpre_round, IS_PREFIX_REFL]) >>
  ‘nc evs ∧ nc s’ by (qpat_x_assum ‘nc bp’ mp_tac >> simp[]) >>
  ‘winv w’ by metis_tac[world_at_winv] >>
  ‘world_at w0 bp = SOME wb’ by metis_tac[bworld] >>
  ‘FOLDL l0_step (SOME w) (MAP ev_lcall s) = SOME wb’
    by (qpat_x_assum ‘world_at w0 bp = _’ mp_tac >> simp[world_at_append]) >>
  ‘winv wb ∧ l0_chan_of wb f = SOME c’
    by (irule replay_chan_keep >> qexistsl_tac [‘s’, ‘w’] >> simp[] >>
        fs[nc_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  ‘nopoll bp = nopoll (pre ++ [ev] ++ post)’ by metis_tac[] >>
  drule_all idle_held >> strip_tac >>
  ‘pf_idle lfd hw ps (ifds h)’ by fs[bidle_def] >>
  ‘pollb_wait (pf_poll_set lfd hw ps (ifds h)) wb ≠ NONE’
    by (irule idle_break_wakes >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        qexistsl_tac [‘c’, ‘f’, ‘hh’, ‘i’] >> rpt conj_tac >>
        FIRST [first_assum ACCEPT_TAC,
               irule noconn_ticks >> qpat_x_assum ‘winv wb’ mp_tac >> simp[winv_def] >> NO_TAC,
               irule chan_of_ticks >> first_assum ACCEPT_TAC,
               irule ticks_le_fl >> qexists_tac ‘i’ >> asm_rewrite_tac[] >> simp[]]) >>
  qpat_x_assum ‘pollb_wait _ _ = NONE’ mp_tac >> asm_rewrite_tac[]
QED

(* ------------------------------------------------------------------------
   The excuse
   ------------------------------------------------------------------------ *)

(* MAIN *)
Theorem flush_ok_holds:
  bquiet m ifds bz ∧ l0_rely w0 ∧ (∀n. brounds lfd hw ifds bz m (w0, pinit) n ≠ NONE) ∧
  run_ok lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ∧
  winv (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ∧
  MEM lfd (l0_used (reindex (btr lfd hw ifds bz m (w0, pinit)) w0)) ∧
  (∀n. SND (pcm lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) n) + 1 <
       dimword (:64)) ∧
  S1 lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ∧
  (∀ps f. outbox_of ps.b f = [] ⇒ ¬hw ps f) ⇒
  flush_ok lfd hw ifds bz m w0 pinit
Proof
  strip_tac >> REWRITE_TAC[flush_ok_def] >> rpt strip_tac >>
  qpat_x_assum ‘flushed_open _ io_p _ _’ (strip_assume_tac o REWRITE_RULE[flushed_open_def]) >>
  rename1 ‘world_at _ (pre ++ [ev] ++ post) = SOME w'’ >>
  ‘ppre lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0, pinit)
        (pre ++ [ev] ++ post)’ by metis_tac[ptrace_def] >>
  ‘fl c w'’ by simp[fl_def] >>
  ‘bpre lfd hw ifds bz m (w0, pinit) evs’ by metis_tac[btrace_def] >>
  drule_all p2b_fl >> strip_tac
  >- (mp_tac (Q.INST [‘ps0’ |-> ‘pinit’] (SPEC_ALL flush_case_a)) >>
      impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, metis_tac[]]) >>
      REWRITE_TAC[])
  >>
  mp_tac (Q.INST [‘pp’ |-> ‘pre ++ [ev] ++ post’] (SPEC_ALL flush_case_b)) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, REFL_TAC]) >>
  REWRITE_TAC[]
QED
