(*
  The round-level data chain of echo_live_l0, by f's state in L1 (design/47
  D, trace assembly): in the table without EOF (conn_data_out), at EOF
  (eof_data_out), and released after EOF (the table is left only through
  the auto-close of a read at EOF: run_tbl_stay).

  MAIN: run_tbl_stay.
*)
Theory honestEchoL0RoundData
Ancestors
  honestEchoL0Acq honestEchoL0EofCase honestEchoL0DataIn honestEchoL0LiveOwn
  honestEchoL0Inv honestEchoL0Obl honestL1PFObl honestL1PFBroken honestL1PFStream
  honestL1PFLive honestL1PFRound honestL1PFOutLive honestL1PFOut honestL1PFRefine honestL1PFInv
  honestL1PFModel
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
