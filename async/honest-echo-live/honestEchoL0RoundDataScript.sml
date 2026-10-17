(*
  The round-level data chain of echo_live_l0, by f's state in L1 (design/47
  D, trace assembly): in the table without EOF (conn_data_out), at EOF
  (eof_data_out), and released after EOF (the table is left only through
  the auto-close of a read at EOF: run_tbl_stay).

  MAIN: run_tbl_stay, run_closing_origin.
*)
Theory honestEchoL0RoundData
Ancestors
  honestEchoL0Acq honestEchoL0EofCase honestEchoL0DataIn honestEchoL0LiveOwn
  honestEchoL0Inv honestEchoL0Obl honestL1PFObl honestL1PFBroken honestL1PFStream
  honestL1PFLive honestL1PFRound honestL1PFOutLive honestL1PFOut honestL1PFRefine honestL1PFInv
  honestL1PFModel honestEchoL0Eof honestL1Model honestEchoL0Peer honestEchoL0Excuse
Libs
  preamble


(* An fd in L1's table without EOF stays in the table *)
Theorem run_tbl_stay:
  echo_run lfdn pol w0 ∧ qfresh w0 ∧
  MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 k).b.tbl) ∧
  ¬MEM f (rstate (n2w lfdn) pol EI ES w0 k).eof ⇒
  MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 (SUC k)).b.tbl)
Proof
  strip_tac >>
  ‘oassm (n2w lfdn) pol EI ES w0’ by fs[oassm_def, echo_run_def] >>
  ‘run_ok (n2w lfdn) pol EI ES w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0) ∧
   (∀n. SND (pcm (n2w lfdn) pol EI ES w0 n) + 1 < dimword (:64)) ∧ fds_lt w0’
    by fs[echo_run_def, winv_def] >>
  drule_all run_own >> strip_tac >>
  ‘pown (n2w lfdn) (rstate (n2w lfdn) pol EI ES w0 k)’ by metis_tac[run_pown, echo_run_hyp] >>
  ‘¬MEM f (rstate (n2w lfdn) pol EI ES w0 k).acq’
    by (gvs[pown_def, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  ‘keep f (rstate (n2w lfdn) pol EI ES w0 k)’ by simp[keep_def] >>
  ‘(rstate (n2w lfdn) pol EI ES w0 k).b.nxt +
   naccepts (new_actions (log_of ES) (rhist (n2w lfdn) pol EI ES w0 k)) < dimword (:64)’
    by (qpat_assum ‘run_ok _ _ _ _ _’ (fn th => assume_tac (MATCH_MP prun_some th)) >>
        first_x_assum (qspec_then ‘k’ assume_tac) >>
        Cases_on ‘prun (n2w lfdn) pol EI ES w0 k’ >> rename1 ‘_ = (hh, rr)’ >>
        PairCases_on ‘rr’ >>
        gvs[rstate_def, rhist_def, run_ok_def, pl2_ok_def] >>
        first_x_assum drule >> simp[]) >>
  qpat_assum ‘run_ok _ _ _ _ _’ (fn th => mp_tac (Q.SPEC ‘k’ (MATCH_MP prun_round' th))) >>
  strip_tac >>
  qpat_assum ‘∀n. wown _ _ _ ∧ _’ (qspec_then ‘k’ strip_assume_tac) >>
  Cases_on ‘l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 k)’ >> fs[] >>
  drule pround_keep >> disch_then drule >> disch_then drule >>
  disch_then (qspec_then ‘f’ mp_tac) >> simp[] >> strip_tac >>
  (* pending again would need a re-connect of f in round k *)
  ‘winv (rworld (n2w lfdn) pol EI ES w0 k)’ by metis_tac[winv_run] >>
  drule_all pround_acq >> strip_tac >>
  ‘∃h. ALOOKUP (rstate (n2w lfdn) pol EI ES w0 k).b.tbl h = SOME f’
    by (fs[pown_def, MEM_MAP, EXISTS_PROD] >> metis_tac[ALOOKUP_ALL_DISTINCT_MEM]) >>
  ‘fkeep (n2w lfdn) h f (rstate (n2w lfdn) pol EI ES w0 k)’
    by (irule fkeep_run >> fs[wordsTheory.dimword_64]) >>
  ‘∃c. l0_chan_of (rworld (n2w lfdn) pol EI ES w0 k) f = SOME c’
    by (irule run_held_chan >> simp[]) >>
  ‘fl (rworld (n2w lfdn) pol EI ES w0 k) f []’ by simp[fl_def, front_def] >>
  ‘¬MEM (FConn f) (rlog (n2w lfdn) pol EI ES w0 k)’
    by (irule fkeep_noconn >> simp[] >> metis_tac[]) >>
  gvs[]
QED

Theorem FOLDL_drop_out_closing2[local]:
  ∀fs b. (FOLDL drop_out b fs).closing = b.closing
Proof
  Induct >> simp[drop_out_def, set_outbox_def]
QED

(* L1 puts f in its closing list only by an auto-close at end-of-file *)
Theorem pround_closing_origin:
  pround lfd pol hs (w, ps) acts = SOME (sn, (w', ps'), log, evs) ∧ winv w ∧
  MEM f ps'.b.closing ∧ ¬MEM f ps.b.closing ⇒
  MEM f ps.eof
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >> gvs[] >>
  CCONTR_TAC >> drule_all pacts_eof_closing >> strip_tac >>
  ‘winv ws10’ by (drule_all pacts_winv >> simp[]) >>
  qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >>
  simp[pf_tail_def, AllCaseEqs(), PULL_EXISTS] >> rpt strip_tac >> gvs[] >>
  ‘winv w1’ by (drule_all l1_polls_winv >> simp[]) >>
  drule_all l1_flush_f >> strip_tac >> drule pf_fetch_b >> strip_tac >>
  drule l1_reap_closing >> disch_then drule >> strip_tac >>
  gvs[stall_step_def, FOLDL_drop_out_closing2]
QED

(* MAIN: the round that put f in L1's closing list had f at EOF in L1's
   table, and f has been closing since *)
Theorem run_closing_origin:
  echo_run lfdn pol w0 ⇒
  ∀n. MEM f (rstate (n2w lfdn) pol EI ES w0 n).b.closing ⇒
      ∃k. k < n ∧ ¬MEM f (rstate (n2w lfdn) pol EI ES w0 k).b.closing ∧
          MEM f (rstate (n2w lfdn) pol EI ES w0 k).eof ∧
          MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 k).b.tbl) ∧
          ∀i. k < i ∧ i ≤ n ⇒ MEM f (rstate (n2w lfdn) pol EI ES w0 i).b.closing
Proof
  strip_tac >>
  ‘run_ok (n2w lfdn) pol EI ES w0 ∧ winv w0’ by fs[echo_run_def] >>
  ‘∀i. pown (n2w lfdn) (rstate (n2w lfdn) pol EI ES w0 i)’
    by metis_tac[run_pown, echo_run_hyp] >>
  Induct >- simp[rstate_def, prun_0, pinit_def, l1init_def] >>
  strip_tac >>
  Cases_on ‘MEM f (rstate (n2w lfdn) pol EI ES w0 n).b.closing’
  >- (first_x_assum drule >> strip_tac >> qexists_tac ‘k’ >> simp[] >>
      rpt strip_tac >> Cases_on ‘i = SUC n’ >> gvs[]) >>
  qpat_assum ‘run_ok _ _ _ _ _’ (fn th => mp_tac (Q.SPEC ‘n’ (MATCH_MP prun_round' th))) >>
  strip_tac >>
  ‘winv (rworld (n2w lfdn) pol EI ES w0 n)’ by metis_tac[winv_run] >>
  drule_all pround_closing_origin >> strip_tac >>
  qexists_tac ‘n’ >> simp[] >> conj_tac
  >- (qpat_x_assum ‘∀i. pown _ _’ (qspec_then ‘n’ mp_tac) >> simp[pown_def] >>
      metis_tac[]) >>
  rpt strip_tac >> ‘i = SUC n’ by decide_tac >> gvs[]
QED

(* MAIN: the round-level data chain from a round at which L1 holds f *)
Theorem held_data_out:
  echo_run lfdn pol w0 ∧ qfresh w0 ∧ qinb w0 ∧ pol_ok hw pol ∧ F1 (n2w lfdn) pol EI ES w0 ∧
  honestL1PFFlush$F2 w0 ∧ honestL1PFFlush$drains (n2w lfdn) pol EI ES w0 c ∧ nshut w0 ∧
  pftrace (n2w lfdn) pol EI ES w0 io ∧
  (MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 n).b.tbl) ∨
   MEM f (rstate (n2w lfdn) pol EI ES w0 n).b.closing) ∧
  l0_chan_of (rworld (n2w lfdn) pol EI ES w0 n) f = SOME c ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 n))) f = SOME j0 ⇒
  (∃n'. (EL c (rworld (n2w lfdn) pol EI ES w0 n).chans).peer_sent ≼
        csent (rworld (n2w lfdn) pol EI ES w0 n') c) ∨
  (∃k. fl_at (n2w lfdn) pol EI ES w0 f j0 k) ∨
  ep_hard_err j0 io ∨ ep_timed_out pf_sendwait j0 io
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  ‘oassm (n2w lfdn) pol EI ES w0’ by fs[oassm_def, echo_run_def] >>
  ‘run_ok (n2w lfdn) pol EI ES w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0) ∧
   (∀n. SND (pcm (n2w lfdn) pol EI ES w0 n) + 1 < dimword (:64))’ by fs[echo_run_def] >>
  ‘∀i. pown (n2w lfdn) (rstate (n2w lfdn) pol EI ES w0 i)’
    by metis_tac[run_pown, echo_run_hyp] >>
  (* f's connect round, from any round at which L1 holds f *)
  ‘∀i. (MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 i).b.tbl) ∨
        MEM f (rstate (n2w lfdn) pol EI ES w0 i).b.closing) ⇒
       ∃a. a < i ∧ MEM (FConn f) (rlog (n2w lfdn) pol EI ES w0 a) ∧
           ∀k. a < k ∧ k < i ⇒ ¬MEM (FConn f) (rlog (n2w lfdn) pol EI ES w0 k)’
    by (rpt strip_tac >>
        qpat_assum ‘run_ok _ _ _ _ _’ (fn th => irule (MATCH_MP last_conn th)) >>
        drule run_rel >> disch_then (qspec_then ‘i’ strip_assume_tac) >>
        drule held_acct >> disch_then drule >> disch_then drule >>
        disch_then (qspec_then ‘f’ mp_tac) >> simp[]) >>
  Cases_on ‘MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 n).b.tbl)’
  >- (first_x_assum (qspec_then ‘n’ mp_tac) >> simp[] >> strip_tac >>
      Cases_on ‘MEM f (rstate (n2w lfdn) pol EI ES w0 n).eof’
      >- (‘n ≤ n’ by simp[] >>
          drule_all eof_data_out >> strip_tac >> simp[] >> metis_tac[]) >>
      ‘∃h. ALOOKUP (rstate (n2w lfdn) pol EI ES w0 n).b.tbl h = SOME f’
        by (qpat_x_assum ‘∀i. pown _ _’ (qspec_then ‘n’ mp_tac) >> rw[pown_def] >>
            qpat_x_assum ‘MEM f (MAP SND _)’ mp_tac >> rw[MEM_MAP] >>
            PairCases_on ‘y’ >> qexists_tac ‘y0’ >> irule ALOOKUP_ALL_DISTINCT_MEM >> fs[]) >>
      drule_all conn_data_out >> strip_tac >> simp[] >> metis_tac[]) >>
  (* closing: it was put there at a round k with f at EOF in the table *)
  fs[] >>
  drule run_closing_origin >> disch_then drule >> strip_tac >>
  ‘∀i. k ≤ i ∧ i ≤ n ⇒
       MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 i).b.tbl) ∨
       MEM f (rstate (n2w lfdn) pol EI ES w0 i).b.closing’
    by (rpt strip_tac >> Cases_on ‘i = k’ >> gvs[]) >>
  ‘∃c1. l0_chan_of (rworld (n2w lfdn) pol EI ES w0 k) f = SOME c1’
    by (irule run_held_chan >> simp[]) >>
  ‘c1 = c’
    by (drule held_chan_stretch >> disch_then drule >>
        disch_then (qspec_then ‘n − k’ mp_tac) >>
        impl_tac >- (rpt strip_tac >> first_x_assum irule >> simp[]) >>
        ‘k + (n − k) = n’ by simp[] >> simp[]) >>
  rveq >>
  ‘∃j1. ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 k))) f = SOME j1’
    by (irule run_known_ep >> simp[]) >>
  ‘ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 n))) f = SOME j1’
    by (irule keep_to_round >> simp[] >> qexists_tac ‘k’ >> simp[] >> rpt strip_tac >>
        first_x_assum irule >> simp[]) >>
  ‘j1 = j0’ by fs[] >> rveq >>
  qpat_x_assum ‘∀i. _ ⇒ ∃a. _’ (qspec_then ‘k’ mp_tac) >> impl_tac >- simp[] >> strip_tac >>
  ‘k ≤ n’ by simp[] >>
  drule_all eof_data_out >> strip_tac >> simp[] >> metis_tac[]
QED
