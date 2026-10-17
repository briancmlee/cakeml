(*
  L3-09, the model-level wiring: quiet_on_kernel's shape for the blocking
  L1's run.  Given the PF run's standing facts in the reindexed world,
  the server's SQ there, and the echo's guarantee on the PF trace:
   - (S1) the blocking run never fails;
   - (S3) the guarantee holds on the blocking trace;
   - (S4′) with finitely many arrivals the blocking run sleeps, unless
     [F1] fails or accepts fail infinitely often on its trace.
  (S5) instantiates this for the CakeML echo program.

  The only step that reads an episode's close is (S3)'s sent_transfer,
  through ep_closed_nopoll: a change of the close conjunct (a close call
  in place of a successful close) is local to that lemma.

  MAIN: l1b_quiet.
*)
Theory honestL1BQuiet
Ancestors
  honestL1BTimeout honestL1BSleep honestL1BStable honestL1BNoFail honestL1BGuar
  honestL1BTransfer honestL1BModel honestL1BStmts honestL1BQuietWorld
  honestL1PFOut honestL1PFConnRun honestL1PFLive honestL1PFModel honestL0World
Libs
  preamble

Theorem arrivals_quiet[local]:
  arrivals_finite_l0 w0 ⇔ ∃N. quiet_after N w0
Proof
  simp[arrivals_finite_l0_def, quiet_after_def]
QED

(* MAIN *)
Theorem l1b_quiet:
  bquiet m ifds bz ∧ l0_rely w0 ∧ l0wf w0 ∧ lone lfd w0 ∧
  btrace lfd hw ifds bz m w0 pinit io_b ∧ ptrace lfd hw ifds bz m w0 pinit io_p ∧
  run_ok lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ∧
  winv (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ∧
  linv lfd (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ∧
  qfresh (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ∧
  MEM lfd (l0_used (reindex (btr lfd hw ifds bz m (w0, pinit)) w0)) ∧
  (∀n. SND (pcm lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) n) + 1 <
       dimword (:64)) ∧
  S1 lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ∧
  S2 lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ∧
  SQ lfd hw ifds bz m (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) ∧
  flush_ok lfd hw ifds bz m w0 pinit ∧
  echo2_guar_l0 KK (reindex (btr lfd hw ifds bz m (w0, pinit)) w0) io_p ⇒
  (∀n. brounds lfd hw ifds bz m (w0, pinit) n ≠ NONE) ∧
  echo2_guar_l0 KK w0 io_b ∧
  (arrivals_finite_l0 w0 ⇒
   ¬F1_io io_b ∨ accepts_fail_io io_b ∨
   ∃n h evs cb. brounds lfd hw ifds bz m (w0, pinit) n = SOME (BSlept h evs cb))
Proof
  strip_tac >> rpt conj_tac
  >- (irule brounds_ok >> simp[])
  >- (drule_all echo2_guar_transfer_full >> simp[])
  >> rw[arrivals_quiet] >>
  Cases_on ‘F1_io io_b’ >> simp[] >> Cases_on ‘accepts_fail_io io_b’ >> simp[] >>
  drule_all l1b_sleeps >> simp[]
QED
