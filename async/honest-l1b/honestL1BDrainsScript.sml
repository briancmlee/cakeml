(*
  L3-09 (S3): D(c) (drains) transfers from the blocking trace to the PF
  trace.  A PF prefix inside an idle segment sees the world after i steps
  of time; bytes in flight there were in flight before (steps of time add
  none), and either the peer reads before the blocking poll returns (the
  prefix after it is the witness) or nothing was read, so the bytes are
  still in flight after it and the blocking trace's D(c) applies there.
  If the blocking run sleeps, its trace ends at the sleep, and its D(c)
  rules out bytes in flight there (drained counts only grow).

  MAIN: drains_transfer.
*)
Theory honestL1BDrains
Ancestors
  honestL1BTransfer honestL1BChan honestL1BCorr honestL1BObs honestL1BRuns
  honestL1BReplay honestL1BSim honestL1BRefine honestL1BPoll honestL1BModel
  honestL1BStmts honestL0Reindex honestL0Part honestL1PFRound honestL1Model
  honestL0World honestL0 llist
Libs
  preamble

Theorem sys_poll_chans:
  sys_poll fes x = SOME (out, x', ev) ⇒ x'.chans = (l0_tick «sys_poll» x).chans
Proof
  rw[sys_poll_def] >> drule l0_do_buf_cases >> rw[] >>
  gvs[l0_call_def, AllCaseEqs()]
QED

(* The blocking poll's world, as steps of time *)
Theorem pollb_chans:
  poll_ok fes ∧ pollb_wait fes w = SOME k ∧ sys_pollb fes w = SOME (INL (out, v, ev)) ⇒
  v.chans = (l0_ticks «sys_poll» (SUC k) w).chans
Proof
  strip_tac >> drule (cj 2 sys_pollb_wait) >> strip_tac >> gvs[] >>
  drule sys_poll_chans >> simp[tick_ticks]
QED

Theorem world_at_mono_dmono:
  world_at w0 a = SOME x ∧ world_at w0 (a ++ b) = SOME y ⇒ dmono c x y
Proof
  rw[world_at_def, l0_replay_def, FOLDL_APPEND] >> gvs[] >> metis_tac[replay_dmono]
QED

Theorem brounds_evs_mono:
  ∀m' m h ws e logs h' ws' e' logs'.
    brounds lfd hw ifds bz mm ws0 m = SOME (BRun h ws e logs) ∧
    brounds lfd hw ifds bz mm ws0 m' = SOME (BRun h' ws' e' logs') ∧ m ≤ m' ⇒ e ≼ e'
Proof
  Induct >> rw[] >- gvs[] >>
  Cases_on ‘m = SUC m'’ >> gvs[] >>
  drule brounds_SUC_BRun >> strip_tac >> gvs[] >>
  ‘e ≼ evs’ by (first_x_assum (qspecl_then [‘m’, ‘h’, ‘ws’, ‘e’, ‘logs’] mp_tac) >> simp[]) >>
  fs[IS_PREFIX_APPEND] >> qexists_tac ‘l ++ revs’ >> simp[]
QED

Theorem brounds_after_slept:
  ∀m'. brounds lfd hw ifds bz mm ws0 m = SOME (BSlept h evs cb) ∧ m ≤ m' ⇒
       brounds lfd hw ifds bz mm ws0 m' = SOME (BSlept h evs cb)
Proof
  Induct >> rw[] >> Cases_on ‘m = SUC m'’ >> gvs[] >> simp[brounds_def]
QED

(* When the blocking run falls asleep after the round with events bp, its
   prefixes are bp's *)
Theorem asleep_prefixes:
  brounds lfd hw ifds bz mm ws0 n0 = SOME (BRun h (wb, ps) bp logs) ∧
  brounds lfd hw ifds bz mm ws0 (SUC n0) = SOME (BSlept h' evs' cb) ∧
  bpre lfd hw ifds bz mm ws0 bevs ⇒ bevs ≼ bp
Proof
  strip_tac >>
  ‘evs' = bp’
    by (qpat_x_assum ‘brounds _ _ _ _ _ _ (SUC n0) = _’ mp_tac >>
        simp[brounds_def, AllCaseEqs()] >> rw[] >> drule bround_asleep >> rw[] >> simp[]) >>
  gvs[bpre_def]
  >- (Cases_on ‘n ≤ n0’
      >- (irule IS_PREFIX_TRANS >> qexists_tac ‘evs’ >> simp[] >>
          irule brounds_evs_mono >> metis_tac[])
      >> ‘brounds lfd hw ifds bz mm ws0 n = SOME (BSlept h' bp cb)’
           by (irule brounds_after_slept >> qexists_tac ‘SUC n0’ >> simp[]) >> gvs[])
  >> Cases_on ‘SUC n0 ≤ n’
  >- (‘brounds lfd hw ifds bz mm ws0 n = SOME (BSlept h' bp cb)’
        by (irule brounds_after_slept >> qexists_tac ‘SUC n0’ >> simp[]) >> gvs[])
  >> ‘brounds lfd hw ifds bz mm ws0 n0 = SOME (BSlept h'' evs cb')’
       by (irule brounds_after_slept >> qexists_tac ‘n’ >> simp[]) >> gvs[]
QED

Theorem pf_after_evs:
  pf_after lfd hw hs ps fes (rv, w1, pevs) = SOME (rdy, ws, log, tevs) ⇒ ∃r. tevs = pevs ++ r
Proof
  rw[pf_after_def, AllCaseEqs()] >> simp[]
QED

(* An idle round that does not fail polls a well-formed set *)
Theorem idle_poll_ok:
  brounds lfd hw ifds bz mm ws0 n = SOME (BRun h (wb, ps) bp logs) ∧
  brounds lfd hw ifds bz mm ws0 (SUC n) ≠ NONE ∧ bidle lfd hw ifds bz mm h ps ⇒
  poll_ok (pf_poll_set lfd hw ps (ifds h))
Proof
  simp[]
QED

(* The blocking prefix just after an idle round's poll returns *)
Theorem idle_wake_pre:
  l0_rely w0 ∧
  brounds lfd hw ifds bz mm (w0, ps0) n = SOME (BRun h (wb, ps) bp logs) ∧
  brounds lfd hw ifds bz mm (w0, ps0) (SUC n) ≠ NONE ∧ bidle lfd hw ifds bz mm h ps ∧
  pollb_wait (pf_poll_set lfd hw ps (ifds h)) wb = SOME k ⇒
  ∃ev v. bpre lfd hw ifds bz mm (w0, ps0) (bp ++ [ev]) ∧ world_at w0 (bp ++ [ev]) = SOME v ∧
         v.chans = (l0_ticks «sys_poll» (SUC k) wb).chans
Proof
  strip_tac >> drule_all idle_poll_ok >> strip_tac >>
  qabbrev_tac ‘fes = pf_poll_set lfd hw ps (ifds h)’ >>
  ‘world_at w0 bp = SOME wb ∧ l0_rely wb’ by metis_tac[bworld] >>
  drule (cj 2 sys_pollb_wait) >> strip_tac >>
  qmatch_asmsub_abbrev_tac ‘sys_pollb fes wb = SOME (INL (out, v, evb))’ >>
  qexistsl_tac [‘evb’, ‘v’] >> rpt conj_tac
  >- (Cases_on ‘pf_after lfd hw (ifds h) ps fes (poll_revents fes out, v, [evb])’
      >- (qpat_x_assum ‘brounds _ _ _ _ _ _ (SUC n) ≠ NONE’ mp_tac >>
          fs[bidle_def] >> simp[brounds_def, bround_def])
      >> rename1 ‘SOME r’ >> PairCases_on ‘r’ >>
      drule pf_after_evs >> strip_tac >>
      irule bpre_round >> qexistsl_tac [‘bp ++ evb :: r’, ‘h ++ [ssnap r0 []]’,
                                        ‘logs ++ [r3]’, ‘SUC n’, ‘(r1, r2)’] >>
      conj_tac
      >- (fs[bidle_def] >> qunabbrev_tac ‘evb’ >> qunabbrev_tac ‘fes’ >>
          simp[brounds_def, bround_def])
      >> REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >> simp[])
  >- (REWRITE_TAC[world_at_append] >> asm_rewrite_tac[optionTheory.OPTION_BIND_def] >>
      BETA_TAC >> drule rplays_pollb >> simp[rplays_def])
  >> irule pollb_chans >> metis_tac[]
QED

(* An idle round whose poll never returns: the run sleeps after it *)
Theorem idle_asleep:
  brounds lfd hw ifds bz mm ws0 n = SOME (BRun h (wb, ps) bp logs) ∧
  brounds lfd hw ifds bz mm ws0 (SUC n) ≠ NONE ∧ bidle lfd hw ifds bz mm h ps ∧
  pollb_wait (pf_poll_set lfd hw ps (ifds h)) wb = NONE ⇒
  ∃cb. brounds lfd hw ifds bz mm ws0 (SUC n) = SOME (BSlept h bp cb)
Proof
  strip_tac >> drule_all idle_poll_ok >> strip_tac >>
  ‘sys_pollb (pf_poll_set lfd hw ps (ifds h)) wb =
     SOME (INR (pollb_conf, poll_buf (pf_poll_set lfd hw ps (ifds h))))’
    by metis_tac[sys_pollb_wait] >>
  fs[bidle_def] >> simp[brounds_def, bround_def]
QED

(* A blocking prefix's channels are a PF prefix's *)
Theorem b_reach:
  bquiet m ifds bz ∧ l0_rely w0 ∧ ptrace lfd hw ifds bz m w0 ps0 io_p ∧
  bpre lfd hw ifds bz m (w0, ps0) bq ∧ world_at w0 bq = SOME wq ⇒
  ∃pp w. LPREFIX (fromList pp) io_p ∧
         world_at (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) pp = SOME w ∧
         w.chans = wq.chans
Proof
  strip_tac >> drule_all b2p >> strip_tac >> gvs[ptrace_def] >>
  qexistsl_tac [‘pp’, ‘lift (btr lfd hw ifds bz m (w0, ps0)) hp wb’] >> simp[]
QED

(* Bytes in flight at a blocking prefix: some PF prefix drains more *)
Theorem b_drains_p:
  bquiet m ifds bz ∧ l0_rely w0 ∧
  btrace lfd hw ifds bz m w0 ps0 io_b ∧ ptrace lfd hw ifds bz m w0 ps0 io_p ∧
  drains w0 io_b c ∧ bpre lfd hw ifds bz m (w0, ps0) bq ∧ world_at w0 bq = SOME wq ∧
  c < LENGTH wq.chans ∧ 0 < (EL c wq.chans).inflight ⇒
  ∃pp w. LPREFIX (fromList pp) io_p ∧
         world_at (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) pp = SOME w ∧
         c < LENGTH w.chans ∧ (EL c wq.chans).drained < (EL c w.chans).drained
Proof
  strip_tac >>
  ‘LPREFIX (fromList bq) io_b’ by metis_tac[btrace_def] >>
  qpat_x_assum ‘drains _ _ _’ (fn th => mp_tac (REWRITE_RULE[drains_def] th)) >>
  disch_then (qspecl_then [‘bq’, ‘wq’] mp_tac) >> simp[] >> strip_tac >>
  ‘bpre lfd hw ifds bz m (w0, ps0) evs'’ by metis_tac[btrace_def] >>
  drule_all b_reach >> strip_tac >> metis_tac[]
QED

(* MAIN: D(c) (blocking ⇒ PF) *)
Theorem drains_transfer:
  bquiet m ifds bz ∧ l0_rely w0 ∧ (∀n. brounds lfd hw ifds bz m (w0, ps0) n ≠ NONE) ∧
  btrace lfd hw ifds bz m w0 ps0 io_b ∧ ptrace lfd hw ifds bz m w0 ps0 io_p ∧
  drains w0 io_b c ⇒ drains (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) io_p c
Proof
  strip_tac >> REWRITE_TAC[drains_def] >> rpt strip_tac >>
  ‘ppre lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0, ps0) evs’
    by metis_tac[ptrace_def] >>
  drule_all p2b >> strip_tac
  >- (gvs[palign_def] >> irule b_drains_p >> simp[] >> metis_tac[])
  >> gvs[pmid_def] >>
  qabbrev_tac ‘u = l0_ticks «sys_poll» i wb’ >>
  ‘inflight_le c wb u’ by simp[Abbr ‘u’, ticks_inflight] >>
  ‘c < LENGTH wb.chans ∧ 0 < (EL c wb.chans).inflight’
    by (fs[inflight_le_def] >> Cases_on ‘c < LENGTH wb.chans’ >> fs[]) >>
  ‘bpre lfd hw ifds bz m (w0, ps0) bp’ by metis_tac[bpre_round, IS_PREFIX_REFL]
  >- ((* asleep: the blocking trace ends at bp, where c is never drained *)
      ‘∃cb. brounds lfd hw ifds bz m (w0, ps0) (SUC n) = SOME (BSlept h bp cb)’
        by (irule idle_asleep >> metis_tac[]) >>
      ‘LPREFIX (fromList bp) io_b’ by metis_tac[btrace_def] >>
      qpat_x_assum ‘drains _ _ _’ (fn th => mp_tac (REWRITE_RULE[drains_def] th)) >>
      disch_then (qspecl_then [‘bp’, ‘wb’] mp_tac) >> simp[] >> strip_tac >>
      ‘bpre lfd hw ifds bz m (w0, ps0) evs'’ by metis_tac[btrace_def] >>
      ‘evs' ≼ bp’ by metis_tac[asleep_prefixes] >>
      fs[IS_PREFIX_APPEND] >> rveq >>
      drule_all world_at_mono_dmono >> disch_then (qspec_then ‘c’ mp_tac) >>
      simp[dmono_def])
  >> (* the poll returns after k ≥ i steps of time *)
  drule_at (Pos (el 2)) idle_wake_pre >> simp[] >> strip_tac >>
  ‘chan_mono c u v’
    by (‘l0_ticks «sys_poll» (SUC k) wb = l0_ticks «sys_poll» (SUC k − i) u’
          by (qunabbrev_tac ‘u’ >> REWRITE_TAC[GSYM ticks_add] >>
              AP_THM_TAC >> AP_TERM_TAC >> decide_tac) >>
        simp[chan_mono_def] >> qspecl_then [‘SUC k − i’, ‘u’] mp_tac (Q.INST [‘nm’ |-> ‘«sys_poll»’] ticks_chan) >>
        simp[chan_mono_def]) >>
  qpat_x_assum ‘v.chans = _’ kall_tac >> fs[chan_mono_def] >>
  Cases_on ‘(EL c u.chans).drained < (EL c v.chans).drained’
  >- (drule_all b_reach >> strip_tac >> metis_tac[])
  >> ‘(EL c v.chans).drained = (EL c u.chans).drained’ by (fs[] >> decide_tac) >>
  ‘c < LENGTH v.chans ∧ 0 < (EL c v.chans).inflight’ by fs[] >>
  drule_all (Q.INST [‘bq’ |-> ‘bp ++ [ev]’, ‘wq’ |-> ‘v’] b_drains_p) >>
  strip_tac >> qexistsl_tac [‘pp’, ‘w’] >> fs[]
QED
