(*
  L3-09 (S1): the blocking run never fails.  A round is the PF round's
  actions, then either the PF tail (never fails: honestL1PFInv) or, when
  idle, a blocking poll and the PF tail's remainder (pf_after).  Under D20
  a blocking poll of any poll set is a well-formed call, so it returns or
  waits for ever; pf_after never fails for the same reasons as the PF tail.
  What the server must do (well-formed actions, no handle overflow) is the
  PF run's obligation pl2_ok, read at the matching PF round (the server's
  view and the L1 state are the same there: honestL1BSim.binv).

  MAIN: brounds_ok.
*)
Theory honestL1BNoFail
Ancestors
  honestL1BCorr honestL1BSim honestL1BRefine honestL1BPoll honestL1BModel
  honestL0Reindex honestL1PFLive honestL1PFInv honestL1Inv honestL1PFModel
  honestL1Model honestL0WorldProps honestL0World honestL0
Libs
  preamble

Theorem pf_after_ok:
  l0_rely w1 ∧ psmall lfd ps ∧ EVERY (small o FST) rv ⇒
  ∃rdy w' ps' log evs.
    pf_after lfd hw hs ps fes (rv, w1, pevs) = SOME (rdy, (w', ps'), log, evs) ∧
    l0_rely w' ∧ psmall lfd ps' ∧ ps'.b.nxt = ps.b.nxt
Proof
  strip_tac >> simp[pf_after_def] >>
  drule readable_small >> strip_tac >>
  ‘small_fds lfd ps.b’ by gvs[psmall_def] >>
  qspecl_then [‘writable_fds rv’, ‘w1’, ‘ps.b’] mp_tac l1_flush_ok >> simp[] >> strip_tac >>
  rename1 ‘l1_flush _ _ = SOME ((w2, b2), fevs)’ >> simp[] >>
  ‘psmall lfd (ps with b := b2)’ by gvs[psmall_def] >>
  ‘EVERY small (FILTER (λf. MEM f (in_fds fes)) (readable_fds rv))’
    by gvs[EVERY_MEM, MEM_FILTER] >>
  drule_all pf_fetch_ok >> disch_then (qspec_then ‘hw’ strip_assume_tac) >> simp[] >>
  rename1 ‘pf_fetch _ _ _ _ = SOME ((w3, ps3'), log, gevs)’ >>
  qabbrev_tac ‘ps3 = stall_step (pf_held ps3') (outbox_of ps.b) log ps3'’ >>
  ‘psmall lfd ps3 ∧ ps3.b.nxt = ps3'.b.nxt ∧ ps3'.b.closing = ps3.b.closing ∧
   ps3'.pause = ps3.pause’ by simp[Abbr ‘ps3’, psmall_stall] >>
  ntac 2 (pop_assum (fn th => REWRITE_TAC [th])) >>
  ‘small_fds lfd ps3.b ∧ EVERY small ps3.b.closing’ by gvs[psmall_def, small_fds_def] >>
  qspecl_then [‘ps3.b.closing’, ‘w3’, ‘ps3.b’] mp_tac l1_reap_ok >> simp[] >> strip_tac >>
  simp[] >> gvs[psmall_def]
QED

(* D20: a blocking poll is always a well-formed call *)
Theorem sys_pollb_some:
  l0_rely w ⇒
  ∃r. sys_pollb fes w = SOME r ∧
      ∀out w' ev. r = INL (out, w', ev) ⇒ l0_rely w' ∧ LENGTH out = LENGTH (poll_buf fes)
Proof
  strip_tac >> simp[sys_pollb_def] >>
  ‘∃x. l0_ffi_fn «sys_poll» pollb_conf (poll_buf fes) w = SOME x’
    by (simp[l0_ffi_fn_def, pollb_conf_def] >>
        simp[Once l0_call_def, poll_buf_ok] >> every_case_tac >> simp[]) >>
  Cases_on ‘x’ >> simp[] >>
  drule_all l0_ffi_fn_length >> simp[]
QED

Theorem bround_ok:
  l0_rely w ∧ psmall lfd ps ∧ EVERY (pact_ok lfd) acts ∧
  ps.b.nxt + naccepts acts < dimword (:64) ⇒
  bround lfd hw idle hs (w, ps) acts ≠ NONE
Proof
  strip_tac >> drule_all pacts_ok >> strip_tac >>
  simp[bround_def] >> IF_CASES_TAC
  >- (qspecl_then [‘pf_poll_set lfd hw ps' hs’] mp_tac
        (Q.GEN ‘fes’ (UNDISCH sys_pollb_some |> Q.INST [‘w’ |-> ‘w'’] |> DISCH_ALL)) >>
      simp[] >> strip_tac >> simp[] >>
      Cases_on ‘r’ >> simp[] >> PairCases_on ‘x’ >> fs[] >>
      ‘EVERY (small o FST) (poll_revents (pf_poll_set lfd hw ps' hs) x0)’
        by (irule poll_revents_small >> simp[LENGTH_poll_buf] >>
            drule pf_poll_set_small >> disch_then (qspecl_then [‘hw’, ‘hs’] mp_tac) >>
            simp[EVERY_MEM, FORALL_PROD] >> metis_tac[]) >>
      drule_all pf_after_ok >>
      disch_then (qspecl_then [‘[x2]’, ‘hw’, ‘hs’, ‘pf_poll_set lfd hw ps' hs’] strip_assume_tac) >>
      simp[])
  >> drule_all pf_tail_ok >> disch_then (qspecl_then [‘hw’, ‘hs’] strip_assume_tac) >> simp[]
QED

(* MAIN, (S1): the blocking run never fails, given the PF run's own
   standing facts in the reindexed world *)
Theorem brounds_ok:
  bquiet m ifds bz ∧ l0_rely w0 ∧
  run_ok lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ⇒
  ∀n. brounds lfd hw ifds bz m (w0, pinit) n ≠ NONE
Proof
  strip_tac >>
  ‘∀n h w ps evs logs. brounds lfd hw ifds bz m (w0, pinit) n = SOME (BRun h (w, ps) evs logs) ⇒
     bround lfd hw (¬bz h) (ifds h) (w, ps) (new_actions (log_of m) h) ≠ NONE’
    by (rpt gen_tac >> disch_tac >>
        ‘l0_rely w’ by metis_tac[bworld] >>
        ‘binv lfd hw ifds bz m w0 pinit h w ps evs’
          by (qpat_assum ‘brounds _ _ _ _ _ _ n = _’ mp_tac >>
              qpat_assum ‘bquiet _ _ _’ (fn th => REWRITE_TAC[MATCH_MP l1b_refines_pf th])) >>
        pop_assum (strip_assume_tac o REWRITE_RULE[binv_def, binv_at_def]) >>
        fs[run_ok_def] >>
        ‘psmall lfd ps’
          by (drule_all prounds_ok >> disch_then (qspec_then ‘N’ strip_assume_tac) >> gvs[]) >>
        qpat_x_assum ‘pl2_ok _ _ _ _ _’ (mp_tac o REWRITE_RULE[pl2_ok_def]) >>
        disch_then drule >> strip_tac >>
        ‘new_actions (log_of m) full = new_actions (log_of m) h’
          by (fs[sfor_def] >> first_x_assum (qspec_then ‘[]’ mp_tac) >> simp[]) >>
        irule bround_ok >> fs[]) >>
  Induct >- simp[brounds_def] >>
  simp[brounds_def] >>
  Cases_on ‘brounds lfd hw ifds bz m (w0, pinit) n’ >> gvs[] >>
  rename1 ‘SOME r’ >> Cases_on ‘r’ >> simp[] >>
  rename1 ‘BRun h ws evs logs’ >> PairCases_on ‘ws’ >>
  first_x_assum drule >> strip_tac >>
  Cases_on ‘bround lfd hw (¬bz h) (ifds h) (ws0, ws1) (new_actions (log_of m) h)’ >> gvs[] >>
  rename1 ‘SOME b’ >> Cases_on ‘b’ >> simp[]
QED
