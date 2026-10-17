(*
  L3-09 (S3): the echo's raw liveness transfers from the PF trace to the
  blocking trace.  The blocking trace's prefixes have PF images with the
  same non-poll events and the same channels (b2p), where the PF
  liveness applies; what it promises (a hard error, bytes sent, a close)
  is read off non-poll events, which some blocking prefix has too (p2b).
  D(c) goes the other way (drains_transfer).  D23's observed excuse
  ep_timed_out goes from the PF trace to the blocking one (taken here as a
  premise, to be proved: the blocking L1 does not block while an outbox
  is pending, so an output-poll stretch is the same in both).

  MAIN: echo_live_transfer.
*)
Theory honestL1BLive
Ancestors
  honestL1BDrains honestL1BTransfer honestL1BCorr honestL1BObs honestL1BSim
  honestL1BRefine honestL1BModel honestL1BStmts honestL0Reindex honestEchoL0Spec
  honestL0World honestL0 llist
Libs
  preamble

Theorem bpre_prefix:
  bpre lfd hw ifds bz m ws0 bp ∧ a ≼ bp ⇒ bpre lfd hw ifds bz m ws0 a
Proof
  rw[bpre_def] >> metis_tac[IS_PREFIX_TRANS]
QED

(* Every PF prefix's non-poll events are a blocking prefix's *)
Theorem p2b_nopoll:
  bquiet m ifds bz ∧ l0_rely w0 ∧ (∀n. brounds lfd hw ifds bz m (w0, ps0) n ≠ NONE) ∧
  ppre lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0, ps0) pp ⇒
  ∃bp. bpre lfd hw ifds bz m (w0, ps0) bp ∧ nopoll bp = nopoll pp
Proof
  strip_tac >> drule_all p2b >> rw[palign_def, pmid_def] >- metis_tac[] >>
  qexists_tac ‘bp’ >> simp[] >> metis_tac[bpre_round, IS_PREFIX_REFL]
QED

(* ... and so is a PF prefix that ends in a non-poll event *)
Theorem p2b_last:
  bquiet m ifds bz ∧ l0_rely w0 ∧ (∀n. brounds lfd hw ifds bz m (w0, ps0) n ≠ NONE) ∧
  ppre lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0, ps0) (pp ++ [ev]) ∧
  ¬is_poll ev ⇒
  ∃bp. bpre lfd hw ifds bz m (w0, ps0) (bp ++ [ev]) ∧ nopoll bp = nopoll pp
Proof
  strip_tac >> drule_all p2b_nopoll >> strip_tac >>
  ‘nopoll bp = nopoll pp ++ [ev] ++ []’ by simp[nopoll_def] >>
  drule nopoll_split >> strip_tac >> qexists_tac ‘a'’ >> simp[] >>
  irule bpre_prefix >> qexists_tac ‘bp’ >> simp[]
QED

Theorem hard_err_not_poll:
  hard_err_on f ev ⇒ ¬is_poll ev
Proof
  Cases_on ‘ev’ >> rw[hard_err_on_def, is_poll_def] >> simp[]
QED

Theorem ep_hard_err_transfer:
  bquiet m ifds bz ∧ l0_rely w0 ∧ (∀n. brounds lfd hw ifds bz m (w0, ps0) n ≠ NONE) ∧
  btrace lfd hw ifds bz m w0 ps0 io_b ∧ ptrace lfd hw ifds bz m w0 ps0 io_p ∧
  ep_hard_err j io_p ⇒ ep_hard_err j io_b
Proof
  rw[ep_hard_err_def] >>
  ‘ppre lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0, ps0) (evs ++ [ev])’
    by metis_tac[ptrace_def] >>
  ‘¬is_poll ev’ by metis_tac[hard_err_not_poll] >> drule_all p2b_last >> strip_tac >>
  qexistsl_tac [‘bp’, ‘ev’] >> rpt conj_tac
  >- metis_tac[btrace_def]
  >- metis_tac[ep_open_nopoll]
  >> metis_tac[nopoll_accepted]
QED

(* What a PF prefix shows about episode j's sends and closes, some blocking
   prefix shows *)
Theorem sent_transfer:
  bquiet m ifds bz ∧ l0_rely w0 ∧ (∀n. brounds lfd hw ifds bz m (w0, ps0) n ≠ NONE) ∧
  btrace lfd hw ifds bz m w0 ps0 io_b ∧ ptrace lfd hw ifds bz m w0 ps0 io_p ∧
  LPREFIX (fromList pp) io_p ⇒
  ∃bp. LPREFIX (fromList bp) io_b ∧ l0_sent j bp = l0_sent j pp ∧
       (ep_closed j pp ⇒ ep_closed j bp)
Proof
  strip_tac >>
  ‘ppre lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0, ps0) pp’
    by metis_tac[ptrace_def] >>
  drule_all p2b_nopoll >> strip_tac >> qexists_tac ‘bp’ >> rpt conj_tac
  >- metis_tac[btrace_def]
  >- metis_tac[nopoll_sent]
  >> metis_tac[ep_closed_nopoll]
QED

Theorem close_call_not_poll:
  l0_close_call f ev ⇒ ¬is_poll ev
Proof
  Cases_on ‘ev’ >> rw[l0_close_call_def, is_poll_def] >> simp[]
QED

(* D27: a close call on episode j's fd while it is open, from PF to blocking *)
Theorem close_call_transfer:
  bquiet m ifds bz ∧ l0_rely w0 ∧ (∀n. brounds lfd hw ifds bz m (w0, ps0) n ≠ NONE) ∧
  btrace lfd hw ifds bz m w0 ps0 io_b ∧ ptrace lfd hw ifds bz m w0 ps0 io_p ∧
  LPREFIX (fromList (pp ++ [ev])) io_p ∧ ep_open j pp ∧
  l0_close_call (EL j (l0_accepted pp)) ev ⇒
  ∃bp. LPREFIX (fromList (bp ++ [ev])) io_b ∧ ep_open j bp ∧
       l0_close_call (EL j (l0_accepted bp)) ev
Proof
  strip_tac >>
  ‘ppre lfd hw ifds m (reindex (btr lfd hw ifds bz m (w0, ps0)) w0, ps0) (pp ++ [ev])’
    by metis_tac[ptrace_def] >>
  ‘¬is_poll ev’ by metis_tac[close_call_not_poll] >> drule_all p2b_last >> strip_tac >>
  qexists_tac ‘bp’ >> rpt conj_tac
  >- metis_tac[btrace_def]
  >- metis_tac[ep_open_nopoll]
  >> metis_tac[nopoll_accepted]
QED

(* D32's excuse, PF ⇒ blocking, for an episode open on the blocking trace
   with channel c: an OPEN obligation (to be proved: while the episode is
   open its fd is polled for input, so a break wakes the blocking poll) *)
Definition flush_ok_def:
  flush_ok lfd hw ifds bz m w0 ps0 ⇔
    ∀io_b io_p evs j c w.
      btrace lfd hw ifds bz m w0 ps0 io_b ∧ ptrace lfd hw ifds bz m w0 ps0 io_p ∧
      LPREFIX (fromList evs) io_b ∧ ep_open j evs ∧ world_at w0 evs = SOME w ∧
      l0_chan_of w (EL j (l0_accepted evs)) = SOME c ∧
      flushed_open (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) io_p j c ⇒
      flushed_open w0 io_b j c
End

(* MAIN: the echo's raw liveness (PF ⇒ blocking), given D19's transfer.
   D23's ep_timed_out and D32's flushed_open excuses are taken across as
   premises (to be proved) *)
Theorem echo_live_transfer:
  bquiet m ifds bz ∧ l0_rely w0 ∧ (∀n. brounds lfd hw ifds bz m (w0, ps0) n ≠ NONE) ∧
  btrace lfd hw ifds bz m w0 ps0 io_b ∧ ptrace lfd hw ifds bz m w0 ps0 io_p ∧
  (∀j. ep_timed_out KK j io_p ⇒ ep_timed_out KK j io_b) ∧
  flush_ok lfd hw ifds bz m w0 ps0 ∧
  echo_live_l0 KK (reindex (btr lfd hw ifds bz m (w0, ps0)) w0) io_p ⇒
  echo_live_l0 KK w0 io_b
Proof
  rw[echo_live_l0_def, echo_live_unless_def] >>
  ‘bpre lfd hw ifds bz m (w0, ps0) evs’ by metis_tac[btrace_def] >>
  drule_all b2p >> strip_tac >> gvs[] >>
  ‘l0_accepted pp = l0_accepted evs’ by metis_tac[nopoll_accepted] >>
  first_x_assum (qspecl_then [‘pp’, ‘j’, ‘c’, ‘lift (btr lfd hw ifds bz m (w0, ps0)) hp w’]
                   mp_tac) >>
  impl_tac
  >- (rpt conj_tac
      >- metis_tac[ptrace_def]
      >- metis_tac[ep_open_nopoll]
      >- simp[]
      >- fs[l0_chan_of_def]
      >> metis_tac[drains_transfer]) >>
  strip_tac
  >- (disj1_tac >> disj1_tac >> irule ep_hard_err_transfer >> metis_tac[])
  >- (disj1_tac >> disj2_tac >> disj1_tac >> metis_tac[])
  >- (disj1_tac >> disj2_tac >> disj2_tac >> fs[flush_ok_def] >> metis_tac[])
  >> disj2_tac >> fs[] >> conj_tac
  >- (drule_all sent_transfer >> disch_then (qspec_then ‘j’ strip_assume_tac) >>
      metis_tac[])
  >> strip_tac >> fs[] >> metis_tac[close_call_transfer]
QED
