(*
  L3-09 (S3): the guarantee transfers from the PF run's trace (in the
  reindexed world) to the blocking run's, predicate by predicate, through
  the prefix correspondence (honestL1BCorr: b2p, p2b).

  btrace / ptrace: io is the blocking run's / the PF run's trace (its
  finite prefixes are exactly bpre's / ppre's).

  MAIN: echo_safe_transfer, accepts_below_transfer, F2_transfer.
*)
Theory honestL1BTransfer
Ancestors
  honestL1BCorr honestL1BObs honestL1BStmts honestL1BSim honestL1BRefine
  honestL0Reindex honestEchoL0Spec honestL0World llist
Libs
  preamble

Definition btrace_def:
  btrace lfd hw ifds bz m w0 ps0 (io : io_event llist) ⇔
    ∀evs. LPREFIX (fromList evs) io ⇔ bpre lfd hw ifds bz m (w0, ps0) evs
End

Definition ptrace_def:
  ptrace lfd hw ifds bz m w0 ps0 (io : io_event llist) ⇔
    ∀evs. LPREFIX (fromList evs) io ⇔
          ppre lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0, ps0) evs
End

(* MAIN: safety (PF ⇒ blocking) *)
Theorem echo_safe_transfer:
  bquiet m ifds bz ∧ l0_rely w0 ∧
  btrace lfd hw ifds bz m w0 ps0 io_b ∧ ptrace lfd hw ifds bz m w0 ps0 io_p ∧
  echo_safe_l0 io_p ⇒ echo_safe_l0 io_b
Proof
  rw[echo_safe_l0_def, btrace_def, ptrace_def] >>
  ‘bpre lfd hw ifds bz m (w0, ps0) evs’ by metis_tac[] >>
  drule_all b2p >> strip_tac >>
  first_x_assum (qspecl_then [‘pp’, ‘j’] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[nopoll_accepted]) >>
  metis_tac[nopoll_sent, nopoll_read]
QED

(* MAIN: fewer than 2^64 − 1 accepts (blocking ⇒ PF) *)
Theorem accepts_below_transfer:
  bquiet m ifds bz ∧ l0_rely w0 ∧ (∀n. brounds lfd hw ifds bz m (w0, ps0) n ≠ NONE) ∧
  btrace lfd hw ifds bz m w0 ps0 io_b ∧ ptrace lfd hw ifds bz m w0 ps0 io_p ∧
  accepts_below io_b ⇒ accepts_below io_p
Proof
  rw[accepts_below_def, btrace_def, ptrace_def] >>
  ‘ppre lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0, ps0) evs’ by metis_tac[] >>
  drule_all p2b >> rw[palign_def, pmid_def]
  >- (first_x_assum (qspec_then ‘bp’ mp_tac) >> simp[] >> metis_tac[nopoll_accepted])
  >> first_x_assum (qspec_then ‘bp’ mp_tac) >>
  ‘bpre lfd hw ifds bz m (w0, ps0) bp’ by (irule bpre_round >> metis_tac[IS_PREFIX_REFL]) >>
  simp[] >> metis_tac[nopoll_accepted]
QED

(* MAIN: F2 (blocking world ⇒ reindexed world) *)
Theorem F2_transfer:
  F2 w0 ⇒ F2 (reindex tr w0)
Proof
  simp[F2_def, reindex_def, reindex_ch_def]
QED
