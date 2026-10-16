(*
  R1-live for the prefetching L1 (design/36 §6, D14/D15): L1 eventually
  fetches what the kernel delivers, so the version-2 world built from its
  run (psk) misses nothing a client sent.  WORK IN PROGRESS.

  The run: an infinite run of L1 in the L0 world w0 (total by
  honestL1PFInv's prun_total).  Its CALL SEQUENCE is the L0 world's
  history, which only grows; [F1] is stated on it as approved (D11): per
  call kind and per fd (a poll involves every fd it lists), calls made
  infinitely often do not fail transiently (the world's choice
  `transient`) infinitely often.
*)
Theory honestL1PFLive
Ancestors
  honestL1PFInv honestL1PFRefine honestL1PFModel honestL1Inv honestL1Model honestL0Rely honestL0World
  honestL0 asyncCore asyncLevel1 asyncM3World alist
Libs
  preamble

(* ------------------------------------------------------------------------
   The run
   ------------------------------------------------------------------------ *)

(* Round n of the run (total, given prun_total's hypotheses) *)
Definition prun_def:
  prun lfd hw ifds m w0 n = THE (prounds lfd hw ifds m (w0, pinit) n)
End

Definition rworld_def:
  rworld lfd hw ifds m w0 n = FST (FST (SND (prun lfd hw ifds m w0 n)))
End

Definition rstate_def:
  rstate lfd hw ifds m w0 n = SND (FST (SND (prun lfd hw ifds m w0 n)))
End

Definition rhist_def:
  rhist lfd hw ifds m w0 n = FST (prun lfd hw ifds m w0 n)
End

(* The calls made so far *)
Definition rcalls_def:
  rcalls lfd hw ifds m w0 n = (rworld lfd hw ifds m w0 n).hist
End

(* ------------------------------------------------------------------------
   [F1] (D11, weak fairness, trusted): on the run's call sequence
   ------------------------------------------------------------------------ *)

(* The fds a call involves: its fd, or every fd a poll lists *)
Definition call_fds_def:
  call_fds (nm : mlstring) (conf : word8 list) =
    if nm = «sys_poll» then MAP FST (poll_entries (DROP 1 conf))
    else [bytes_fd (TAKE 8 conf)]
End

(* Call i of the run is a call nm involving fd f *)
Definition call_at_def:
  call_at lfd hw ifds m w0 i nm f ⇔
    ∃n. i < LENGTH (rcalls lfd hw ifds m w0 n) ∧
        FST (EL i (rcalls lfd hw ifds m w0 n)) = nm ∧
        MEM f (call_fds nm (FST (SND (EL i (rcalls lfd hw ifds m w0 n)))))
End

(* Call i did not fail transiently: the world's choice on the calls before *)
Definition call_ok_at_def:
  call_ok_at lfd hw ifds m w0 i ⇔
    ∃n. i < LENGTH (rcalls lfd hw ifds m w0 n) ∧
        w0.ch.transient (TAKE i (rcalls lfd hw ifds m w0 n)) = NONE
End

(* [F1]: per call kind and per fd: made infinitely often, it does not fail
   transiently infinitely often *)
Definition F1_def:
  F1 lfd hw ifds m w0 ⇔
    ∀nm f.
      (∀i. ∃i'. i ≤ i' ∧ call_at lfd hw ifds m w0 i' nm f) ⇒
      (∀i. ∃i'. i ≤ i' ∧ call_at lfd hw ifds m w0 i' nm f ∧
                call_ok_at lfd hw ifds m w0 i')
End

(* ------------------------------------------------------------------------
   The server's obligations, at the run (S1, S3, S4; per server, not
   trusted)
   ------------------------------------------------------------------------ *)

(* S1: the interest covers every open handle and the listener *)
Definition S1_def:
  S1 lfd hw ifds m w0 ⇔
    ∀n h f. ALOOKUP (rstate lfd hw ifds m w0 n).b.tbl h = SOME f ⇒
            MEM h (ifds (rhist lfd hw ifds m w0 n)) ∧
            MEM lfd (ifds (rhist lfd hw ifds m w0 n))
End

(* S3: what the server is shown, it eventually reads: an fd's inbox is
   eventually empty again *)
Definition S3_def:
  S3 lfd hw ifds m w0 ⇔
    ∀n f. ∃n'. n ≤ n' ∧ inb_of (rstate lfd hw ifds m w0 n') f = []
End

(* S4 (for fd f): eventually, f's outbox stays within hw until f is next
   fetched (servers that write only in reply: nothing new is written while
   nothing new is read) *)
Definition S4_def:
  S4 lfd hw ifds m w0 f ⇔
    ∀n. ∃n'. n ≤ n' ∧
         ∀n''. n' ≤ n'' ∧
               (∀k. n' ≤ k ∧ k < n'' ⇒
                    ¬EXISTS (λx. x = FEof f ∨ x = FReset f ∨ ∃bs. x = FData f bs)
                       (EL k (SND (SND (SND (prun lfd hw ifds m w0 (SUC k))))))) ⇒
               LENGTH (outbox_of (rstate lfd hw ifds m w0 n'').b f) ≤ hw
End

(* ------------------------------------------------------------------------
   The run, step by step
   ------------------------------------------------------------------------ *)

(* The run's hypotheses (as prun_total) *)
Definition run_ok_def:
  run_ok lfd hw ifds m w0 ⇔
    l0_rely w0 ∧ psmall lfd pinit ∧ pl2_ok lfd hw ifds m (w0, pinit)
End

Theorem prun_some:
  run_ok lfd hw ifds m w0 ⇒
  ∀n. prounds lfd hw ifds m (w0, pinit) n = SOME (prun lfd hw ifds m w0 n)
Proof
  rw[run_ok_def] >> drule_all prounds_ok >>
  disch_then (qspec_then ‘n’ strip_assume_tac) >> simp[prun_def]
QED

(* Round n's step: the round from state n gives state SUC n *)
Theorem prun_step:
  run_ok lfd hw ifds m w0 ⇒
  ∀n. ∃snap log revs.
    pround lfd hw (ifds (rhist lfd hw ifds m w0 n))
      (rworld lfd hw ifds m w0 n, rstate lfd hw ifds m w0 n)
      (new_actions (log_of m) (rhist lfd hw ifds m w0 n)) =
      SOME (snap, (rworld lfd hw ifds m w0 (SUC n), rstate lfd hw ifds m w0 (SUC n)),
            log, revs) ∧
    rhist lfd hw ifds m w0 (SUC n) = rhist lfd hw ifds m w0 n ++ [snap] ∧
    EL n (SND (SND (SND (prun lfd hw ifds m w0 (SUC n))))) = log
Proof
  rpt strip_tac >> drule prun_some >> strip_tac >>
  first_assum (qspec_then ‘SUC n’ mp_tac) >> first_x_assum (qspec_then ‘n’ mp_tac) >>
  simp[prounds_def] >>
  Cases_on ‘prun lfd hw ifds m w0 n’ >> rename1 ‘_ = (h, r)’ >> PairCases_on ‘r’ >>
  rename1 ‘_ = (h, (w, ps), evs, logs)’ >> rpt strip_tac >> gvs[AllCaseEqs()] >>
  PairCases_on ‘ws'’ >>
  simp[rworld_def, rstate_def, rhist_def] >>
  drule prounds_logs >> strip_tac >>
  qpat_x_assum ‘_ = prun _ _ _ _ _ (SUC n)’ (SUBST1_TAC o SYM) >> simp[EL_APPEND2]
QED

(* ------------------------------------------------------------------------
   The core: L1 fetches on an fd whose kernel input is pending
   ------------------------------------------------------------------------ *)

(* Round k's fetch log mentions f *)
Definition fetched_at_def:
  fetched_at lfd hw ifds m w0 k f ⇔
    EXISTS (λx. x = FEof f ∨ x = FReset f ∨ ∃bs. x = FData f bs)
      (EL k (SND (SND (SND (prun lfd hw ifds m w0 (SUC k))))))
End

(* TO PROVE (the statement, kept as a comment until it is proved):

PROGRESS: if fd f is an open handle's fd at round n and its channel has
   input pending (data, EOF, or broken), then L1 eventually fetches on f,
   or f stops being an open handle's fd *-)
Theorem fetch_progress:
  l0_rely w0 ∧ psmall lfd pinit ∧ pl2_ok lfd hw ifds m (w0, pinit) ∧
  F1 lfd hw ifds m w0 ∧ S1 lfd hw ifds m w0 ∧ S3 lfd hw ifds m w0 ∧
  S4 lfd hw ifds m w0 f ⇒
  ∀n. MEM f (MAP SND (rstate lfd hw ifds m w0 n).b.tbl) ∧
      (∃j. l0_chan_of (rworld lfd hw ifds m w0 n) f = SOME j ∧
           let c = EL j (rworld lfd hw ifds m w0 n).chans in
             c.inbox ≠ [] ∨ c.peer_eof ∨ c.broken) ⇒
      ∃k. n ≤ k ∧
          (fetched_at lfd hw ifds m w0 k f ∨
           ¬MEM f (MAP SND (rstate lfd hw ifds m w0 (SUC k)).b.tbl))
(not yet proved)
*)
