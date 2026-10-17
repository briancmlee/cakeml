(*
  L3-09 (S3): the echo's guarantee transfers from the PF trace (in the
  reindexed world) to the blocking trace.  Safety goes PF ⇒ blocking; the
  liveness hypotheses go blocking ⇒ PF ([F1], [F2], accepts_below), and so
  do D(c) and D19 (episode hypotheses of echo_live); the liveness
  conclusions come back PF ⇒ blocking.

  D19's transfer (hup_drains, blocking ⇒ PF) is a premise here, to be
  discharged on the D20 base (the per-poll POLLHUP reading changes there).

  MAIN: echo2_guar_transfer; echo2_guar_transfer_ok, with (S1)
  (honestL1BNoFail.brounds_ok) discharging the never-fails premise.
*)
Theory honestL1BGuar
Ancestors
  honestL1BNoFail honestL1BConnLive honestL1BLive honestL1BDrains honestL1BTransfer honestL1BConn
  honestL1BStmts honestL1PFConn honestL1PFLive honestL1PFModel honestL0World
Libs
  preamble

Theorem echo2_guar_transfer:
  bquiet m ifds bz ∧ l0_rely w0 ∧ l0wf w0 ∧ lone lfd w0 ∧ ps0 = pinit ∧
  (∀n. brounds lfd hw ifds bz m (w0, ps0) n ≠ NONE) ∧
  btrace lfd hw ifds bz m w0 ps0 io_b ∧ ptrace lfd hw ifds bz m w0 ps0 io_p ∧
  run_ok lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) ∧
  winv (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) ∧
  linv lfd (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) ∧
  MEM lfd (l0_used (reindex (btr lfd hw ifds bz m (w0, ps0)) w0)) ∧
  (∀n. SND (pcm lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) n) + 1 <
       dimword (:64)) ∧
  S1 lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) ∧
  (∀j c. hup_drains KK w0 io_b j c ⇒
         hup_drains KK (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) io_p j c) ∧
  echo2_guar_l0 KK (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) io_p ⇒
  echo2_guar_l0 KK w0 io_b
Proof
  strip_tac >> qpat_x_assum ‘echo2_guar_l0 _ _ _’ mp_tac >>
  REWRITE_TAC[echo2_guar_l0_def] >> strip_tac >> conj_tac
  >- metis_tac[echo_safe_transfer]
  >> strip_tac >>
  ‘F1_io io_p’ by metis_tac[F1_transfer] >>
  ‘F2 (reindex (btr lfd hw ifds bz m (w0, ps0)) w0)’ by metis_tac[F2_transfer] >>
  ‘accepts_below io_p’ by metis_tac[accepts_below_transfer] >>
  ‘echo_live_l0 KK (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) io_p ∧
   conn_live_l0 (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) io_p’ by metis_tac[] >>
  conj_tac
  >- (irule echo_live_transfer >> metis_tac[])
  >> irule conn_live_transfer >> metis_tac[]
QED

(* MAIN: the transfer, with (S1) discharging the never-fails premise *)
Theorem echo2_guar_transfer_ok:
  bquiet m ifds bz ∧ l0_rely w0 ∧ l0wf w0 ∧ lone lfd w0 ∧
  btrace lfd hw ifds bz m w0 pinit io_b ∧ ptrace lfd hw ifds bz m w0 pinit io_p ∧
  run_ok lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ∧
  winv (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ∧
  linv lfd (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ∧
  MEM lfd (l0_used (reindex (btr lfd hw ifds bz m (w0, pinit)) w0)) ∧
  (∀n. SND (pcm lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) n) + 1 <
       dimword (:64)) ∧
  S1 lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ∧
  (∀j c. hup_drains KK w0 io_b j c ⇒
         hup_drains KK (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) io_p j c) ∧
  echo2_guar_l0 KK (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) io_p ⇒
  echo2_guar_l0 KK w0 io_b
Proof
  strip_tac >>
  ‘∀n. brounds lfd hw ifds bz m (w0, pinit) n ≠ NONE’ by (irule brounds_ok >> simp[]) >>
  mp_tac (GEN_ALL (REWRITE_RULE[] (Q.INST [‘ps0’ |-> ‘pinit’] echo2_guar_transfer))) >>
  disch_then drule_all >> simp[]
QED
