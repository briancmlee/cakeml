(*
  R1-live for the prefetching L1 (design/36 §6, D14/D15): L1 eventually
  fetches what the kernel delivers, so the version-2 world built from its
  run (psk) misses nothing a client sent.  WORK IN PROGRESS.

  The run: an infinite run of L1 in the L0 world w0 (total by
  honestL1PFInv's prun_total).  Its IO-event trace, which only grows,
  records each call with its observed result; [F1] is stated on it as
  approved (D11′): per call kind and per fd (a poll involves every fd it
  lists), calls made infinitely often do not return a retried outcome
  (honestL1PFRound's `retried`) infinitely often.
*)
Theory honestL1PFLive
Ancestors
  honestL1PFRound honestL1PFInv honestL1PFRefine honestL1PFModel honestL1Inv honestL1Model honestL0Rely honestL0World
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

(* The IO events so far: each call with its observed result *)
Definition revs_def:
  revs lfd hw ifds m w0 n = FST (SND (SND (prun lfd hw ifds m w0 n)))
End

(* ------------------------------------------------------------------------
   [F1] (D11′, weak fairness on observed outcomes, trusted): on the run's
   IO-event trace
   ------------------------------------------------------------------------ *)

(* Event i of the run is a call nm involving fd f *)
Definition call_at_def:
  call_at lfd hw ifds m w0 i nm f ⇔
    ∃n. i < LENGTH (revs lfd hw ifds m w0 n) ∧ ev_on nm f (EL i (revs lfd hw ifds m w0 n))
End

(* Event i's result is not one L1 retries *)
Definition call_ok_at_def:
  call_ok_at lfd hw ifds m w0 i ⇔
    ∃n. i < LENGTH (revs lfd hw ifds m w0 n) ∧ ¬retried (EL i (revs lfd hw ifds m w0 n))
End

(* [F1]: per call kind and per fd: made infinitely often, it does not
   return a retried outcome infinitely often *)
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

(* S4 (for fd f; design/36 §6's formal shape): eventually, until f is next
   fetched, the server issues no Write on f's handle and f's outbox stays
   within hw (servers that write only in reply: nothing new is written
   while nothing new is read) *)
Definition S4_def:
  S4 lfd hw ifds m w0 f ⇔
    ∀n. ∃n'. n ≤ n' ∧
         ∀n''. n' ≤ n'' ∧
               (∀k. n' ≤ k ∧ k < n'' ⇒
                    ¬fetched f (EL k (SND (SND (SND (prun lfd hw ifds m w0 (SUC k))))))) ⇒
               LENGTH (outbox_of (rstate lfd hw ifds m w0 n'').b f) ≤ hw ∧
               ∀h bs. ALOOKUP (rstate lfd hw ifds m w0 n'').b.tbl h = SOME f ⇒
                      ¬MEM (Write h bs) (new_actions (log_of m) (rhist lfd hw ifds m w0 n''))
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
    fetched f (EL k (SND (SND (SND (prun lfd hw ifds m w0 (SUC k))))))
End

(* Round n, with its events *)
Theorem prun_round:
  run_ok lfd hw ifds m w0 ⇒
  ∀n. ∃snap log rev.
    pround lfd hw (ifds (rhist lfd hw ifds m w0 n))
      (rworld lfd hw ifds m w0 n, rstate lfd hw ifds m w0 n)
      (new_actions (log_of m) (rhist lfd hw ifds m w0 n)) =
      SOME (snap, (rworld lfd hw ifds m w0 (SUC n), rstate lfd hw ifds m w0 (SUC n)),
            log, rev) ∧
    revs lfd hw ifds m w0 (SUC n) = revs lfd hw ifds m w0 n ++ rev ∧
    fetched_at lfd hw ifds m w0 n f = fetched f log
Proof
  rpt strip_tac >> drule prun_some >> strip_tac >>
  first_assum (qspec_then ‘SUC n’ mp_tac) >> first_x_assum (qspec_then ‘n’ mp_tac) >>
  simp[prounds_def] >>
  Cases_on ‘prun lfd hw ifds m w0 n’ >> rename1 ‘_ = (h, r)’ >> PairCases_on ‘r’ >>
  rename1 ‘_ = (h, (w, ps), evs, logs)’ >> rpt strip_tac >> gvs[AllCaseEqs()] >>
  PairCases_on ‘ws'’ >>
  simp[rworld_def, rstate_def, revs_def, fetched_at_def] >>
  drule prounds_logs >> strip_tac >>
  qpat_x_assum ‘_ = prun _ _ _ _ _ (SUC n)’ (SUBST1_TAC o SYM) >>
  simp[rhist_def, EL_APPEND_EQN]
QED

Theorem prun_0:
  prun lfd hw ifds m w0 0 = ([], (w0, pinit), [], [])
Proof
  simp[prun_def, prounds_def]
QED

(* The world invariant holds along the run *)
Theorem winv_run:
  run_ok lfd hw ifds m w0 ∧ winv w0 ⇒ ∀n. winv (rworld lfd hw ifds m w0 n)
Proof
  strip_tac >> Induct >- simp[rworld_def, prun_0] >>
  drule prun_round >> disch_then (qspecl_then [‘ARB’, ‘n’] strip_assume_tac) >>
  drule_all pround_winv >> simp[]
QED

(* The event trace only grows *)
Theorem revs_prefix:
  run_ok lfd hw ifds m w0 ⇒
  ∀k n. revs lfd hw ifds m w0 n ≼ revs lfd hw ifds m w0 (n + k)
Proof
  strip_tac >> Induct >> simp[] >> gen_tac >>
  drule prun_round >> disch_then (qspecl_then [‘ARB’, ‘n + k’] strip_assume_tac) >>
  first_x_assum (qspec_then ‘n’ assume_tac) >> simp[ADD_CLAUSES] >>
  irule IS_PREFIX_TRANS >> first_assum (irule_at Any) >> simp[IS_PREFIX_APPEND] >>
  qexists_tac ‘rev’ >> ONCE_REWRITE_TAC [ADD_COMM] >> simp[]
QED

(* L1's view of an open fd with no EOF, at any round (from R1-safe's
   invariants) *)
Theorem fkeep_run:
  run_ok lfd hw ifds m w0 ∧ fds_lt w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd hw ifds m w0 n) + 1 < dimword (:64)) ⇒
  ∀n h f. ALOOKUP (rstate lfd hw ifds m w0 n).b.tbl h = SOME f ∧
          ¬MEM f (rstate lfd hw ifds m w0 n).eof ⇒
          fkeep lfd h f (rstate lfd hw ifds m w0 n)
Proof
  rpt strip_tac >> drule prun_some >> disch_then (qspec_then ‘n’ assume_tac) >>
  ‘l0_rely w0’ by gvs[run_ok_def] >>
  Cases_on ‘prun lfd hw ifds m w0 n’ >> rename1 ‘_ = (hh, r)’ >> PairCases_on ‘r’ >>
  gvs[rstate_def] >>
  mp_tac l1pf_refines_hl >> impl_tac >- simp[] >> disch_then drule >> strip_tac >>
  ‘l1hdln (w2n lfd) (r1.b.nxt + LENGTH (new_actions (log_of m) hh)) < dimword (:64)’
    by (gvs[run_ok_def, pl2_ok_def] >> first_x_assum drule >> simp[]) >>
  gvs[fkeep_def, pown_def] >>
  ‘MEM f (MAP SND r1.b.tbl)’
    by (imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  ‘ALL_DISTINCT (MAP SND r1.b.tbl) ∧ ¬MEM f r1.b.closing ∧ ¬MEM f r1.acq’
    by gvs[ALL_DISTINCT_APPEND] >>
  rpt conj_tac
  >- metis_tac[alookup_snd_inj]
  >- simp[]
  >- simp[]
  >- (strip_tac >> gvs[])
  >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
  qexists_tac ‘i’ >> simp[] >>
  qspecl_then [‘i’, ‘LENGTH (new_actions (log_of m) (hhist lfd ifds m (psk lfd hw ifds m w0) n)) +
                     r1.b.nxt’, ‘w2n lfd’] mp_tac (Q.GENL [‘j’, ‘k’, ‘n’] l1hdln_mono) >>
  simp[]
QED
