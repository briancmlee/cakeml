(*
  R1-live for the prefetching L1 (design/36 §6, D14/D15), the fetch half:
  L1 eventually fetches on an open handle's fd whose kernel channel has
  input pending (fetch_progress), given [F1] (D11′), S1, S3 and S4.  The
  stream invariant and live-data / live-conn build on it.

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
    (∀n h f. ALOOKUP (rstate lfd hw ifds m w0 n).b.tbl h = SOME f ⇒
             MEM h (ifds (rhist lfd hw ifds m w0 n))) ∧
    ∀n. MEM lfd (ifds (rhist lfd hw ifds m w0 n))
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
    EL n (SND (SND (SND (prun lfd hw ifds m w0 (SUC n))))) = log
Proof
  rpt strip_tac >> drule prun_some >> strip_tac >>
  first_assum (qspec_then ‘SUC n’ mp_tac) >> first_x_assum (qspec_then ‘n’ mp_tac) >>
  simp[prounds_def] >>
  Cases_on ‘prun lfd hw ifds m w0 n’ >> rename1 ‘_ = (h, r)’ >> PairCases_on ‘r’ >>
  rename1 ‘_ = (h, (w, ps), evs, logs)’ >> rpt strip_tac >> gvs[AllCaseEqs()] >>
  PairCases_on ‘ws'’ >>
  simp[rworld_def, rstate_def, revs_def] >>
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
  drule prun_round >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  drule_all pround_winv >> simp[]
QED

(* The event trace only grows *)
Theorem revs_prefix:
  run_ok lfd hw ifds m w0 ⇒
  ∀k n. revs lfd hw ifds m w0 n ≼ revs lfd hw ifds m w0 (n + k)
Proof
  strip_tac >> Induct >> simp[] >> gen_tac >>
  drule prun_round >> disch_then (qspec_then ‘n + k’ strip_assume_tac) >>
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

(* ------------------------------------------------------------------------
   Rounds and positions in the event trace
   ------------------------------------------------------------------------ *)

(* Round k's events and fetch log *)
Definition rrev_def:
  rrev lfd hw ifds m w0 k =
    DROP (LENGTH (revs lfd hw ifds m w0 k)) (revs lfd hw ifds m w0 (SUC k))
End

Definition rlog_def:
  rlog lfd hw ifds m w0 k = EL k (SND (SND (SND (prun lfd hw ifds m w0 (SUC k)))))
End

Theorem prun_round':
  run_ok lfd hw ifds m w0 ⇒
  ∀k. ∃snap.
    pround lfd hw (ifds (rhist lfd hw ifds m w0 k))
      (rworld lfd hw ifds m w0 k, rstate lfd hw ifds m w0 k)
      (new_actions (log_of m) (rhist lfd hw ifds m w0 k)) =
      SOME (snap, (rworld lfd hw ifds m w0 (SUC k), rstate lfd hw ifds m w0 (SUC k)),
            rlog lfd hw ifds m w0 k, rrev lfd hw ifds m w0 k) ∧
    revs lfd hw ifds m w0 (SUC k) = revs lfd hw ifds m w0 k ++ rrev lfd hw ifds m w0 k ∧
    (fetched_at lfd hw ifds m w0 k f ⇔ fetched f (rlog lfd hw ifds m w0 k))
Proof
  rpt strip_tac >> drule prun_round >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  ‘rrev lfd hw ifds m w0 k = rev’ by simp[rrev_def, DROP_LENGTH_APPEND] >>
  ‘rlog lfd hw ifds m w0 k = log’ by gvs[rlog_def] >>
  simp[fetched_at_def] >> gvs[rlog_def]
QED

Theorem revs_0[simp]:
  revs lfd hw ifds m w0 0 = []
Proof
  simp[revs_def, prun_0]
QED

Theorem revs_grow:
  run_ok lfd hw ifds m w0 ∧ a ≤ b ⇒
  ∃l. revs lfd hw ifds m w0 b = revs lfd hw ifds m w0 a ++ l
Proof
  strip_tac >> drule revs_prefix >>
  disch_then (qspecl_then [‘b - a’, ‘a’] mp_tac) >> simp[IS_PREFIX_APPEND]
QED

Theorem revs_len_mono:
  run_ok lfd hw ifds m w0 ∧ a ≤ b ⇒
  LENGTH (revs lfd hw ifds m w0 a) ≤ LENGTH (revs lfd hw ifds m w0 b)
Proof
  strip_tac >> drule_all revs_grow >> strip_tac >> simp[]
QED

(* An index means the same event in every long enough trace *)
Theorem revs_EL:
  run_ok lfd hw ifds m w0 ∧ i < LENGTH (revs lfd hw ifds m w0 a) ∧
  i < LENGTH (revs lfd hw ifds m w0 b) ⇒
  EL i (revs lfd hw ifds m w0 a) = EL i (revs lfd hw ifds m w0 b)
Proof
  strip_tac >> Cases_on ‘a ≤ b’
  >- (‘∃l. revs lfd hw ifds m w0 b = revs lfd hw ifds m w0 a ++ l’
        by (irule revs_grow >> simp[]) >> simp[EL_APPEND1])
  >> ‘∃l. revs lfd hw ifds m w0 a = revs lfd hw ifds m w0 b ++ l’
       by (irule revs_grow >> simp[]) >> simp[EL_APPEND1]
QED

(* Every event belongs to a round *)
Theorem event_round:
  run_ok lfd hw ifds m w0 ⇒
  ∀n i. i < LENGTH (revs lfd hw ifds m w0 n) ⇒
        ∃k. k < n ∧ LENGTH (revs lfd hw ifds m w0 k) ≤ i ∧
            i < LENGTH (revs lfd hw ifds m w0 (SUC k)) ∧
            MEM (EL i (revs lfd hw ifds m w0 n)) (rrev lfd hw ifds m w0 k)
Proof
  strip_tac >> Induct >> simp[] >> rpt strip_tac >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘n’] strip_assume_tac) >>
  Cases_on ‘i < LENGTH (revs lfd hw ifds m w0 n)’
  >- (first_x_assum drule >> strip_tac >> qexists_tac ‘k’ >> gvs[EL_APPEND1])
  >> qexists_tac ‘n’ >> gvs[EL_APPEND2] >> irule EL_MEM >> gvs[]
QED

(* ... and every event of a round has a position in it *)
Theorem round_event:
  run_ok lfd hw ifds m w0 ∧ MEM ev (rrev lfd hw ifds m w0 k) ⇒
  ∃i. LENGTH (revs lfd hw ifds m w0 k) ≤ i ∧ i < LENGTH (revs lfd hw ifds m w0 (SUC k)) ∧
      EL i (revs lfd hw ifds m w0 (SUC k)) = ev
Proof
  strip_tac >> drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
  gvs[MEM_EL] >> qexists_tac ‘LENGTH (revs lfd hw ifds m w0 k) + n’ >>
  simp[EL_APPEND2]
QED

(* ------------------------------------------------------------------------
   Progress
   ------------------------------------------------------------------------ *)

(* While nothing is fetched on f, its input stays pending and L1's view of
   f is kept, from round to round *)
Theorem keep_run:
  run_ok lfd hw ifds m w0 ∧ winv w0 ⇒
  ∀d n. pend (rworld lfd hw ifds m w0 n) f ∧ fkeep lfd h f (rstate lfd hw ifds m w0 n) ∧
        (∀k. n ≤ k ∧ k < n + d ⇒ ¬fetched_at lfd hw ifds m w0 k f) ⇒
        pend (rworld lfd hw ifds m w0 (n + d)) f ∧
        fkeep lfd h f (rstate lfd hw ifds m w0 (n + d)) ∧
        (inb_of (rstate lfd hw ifds m w0 n) f = [] ⇒
         inb_of (rstate lfd hw ifds m w0 (n + d)) f = [])
Proof
  strip_tac >> drule_all winv_run >> strip_tac >>
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  ‘¬fetched_at lfd hw ifds m w0 (n + d) f’
    by (qpat_assum ‘∀k. _ ≤ k ∧ _ ⇒ _’ (qspec_then ‘n + d’ mp_tac) >> simp[]) >>
  qpat_x_assum ‘∀n. pend _ _ ∧ _ ⇒ _’ (qspec_then ‘n’ mp_tac) >>
  impl_tac >- (simp[] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  strip_tac >>
  drule prun_round' >> disch_then (qspecl_then [‘f’, ‘n + d’] strip_assume_tac) >>
  ‘winv (rworld lfd hw ifds m w0 (n + d))’ by simp[] >>
  drule_all pround_f >> strip_tac >> gvs[ADD_CLAUSES]
QED

(* If nothing is ever fetched on f from round n on (f open, no EOF in L1,
   input pending), then from some round N on: every round polls f, a poll
   on f that is not retried leads to a recv on f in the same round, and
   every recv on f is retried *)
Theorem late_rounds:
  run_ok lfd hw ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd hw ifds m w0 n) + 1 < dimword (:64)) ∧
  S1 lfd hw ifds m w0 ∧ S3 lfd hw ifds m w0 ∧ S4 lfd hw ifds m w0 f ∧
  ALOOKUP (rstate lfd hw ifds m w0 n).b.tbl h = SOME f ∧
  ¬MEM f (rstate lfd hw ifds m w0 n).eof ∧ pend (rworld lfd hw ifds m w0 n) f ∧
  (∀k. n ≤ k ⇒ ¬fetched_at lfd hw ifds m w0 k f) ⇒
  ∃N. n ≤ N ∧
      ∀k. N ≤ k ⇒
          EXISTS (ev_on «sys_poll» f) (rrev lfd hw ifds m w0 k) ∧
          (∀ev. MEM ev (rrev lfd hw ifds m w0 k) ∧ ev_on «sys_poll» f ev ∧ ¬retried ev ⇒
                EXISTS (ev_on «sys_recv» f) (rrev lfd hw ifds m w0 k)) ∧
          (∀ev. MEM ev (rrev lfd hw ifds m w0 k) ∧ ev_on «sys_recv» f ev ⇒ retried ev)
Proof
  strip_tac >>
  ‘fds_lt w0’ by gvs[winv_def] >>
  drule_all fkeep_run >> strip_tac >>
  drule_all winv_run >> strip_tac >>
  drule keep_run >> disch_then drule >> strip_tac >>
  ‘∀d. pend (rworld lfd hw ifds m w0 (n + d)) f ∧
       fkeep lfd h f (rstate lfd hw ifds m w0 (n + d))’
    by (gen_tac >> first_assum (qspecl_then [‘h’, ‘f’, ‘d’, ‘n’] mp_tac) >> simp[]) >>
  (* S4 from n, then S3 from there *)
  qpat_x_assum ‘S4 _ _ _ _ _ _’ (mp_tac o REWRITE_RULE [S4_def]) >>
  disch_then (qspec_then ‘n’ strip_assume_tac) >> rename1 ‘n ≤ n1’ >>
  qpat_assum ‘S3 _ _ _ _ _’ (mp_tac o REWRITE_RULE [S3_def]) >>
  disch_then (qspecl_then [‘n1’, ‘f’] strip_assume_tac) >> rename1 ‘n1 ≤ N’ >>
  qexists_tac ‘N’ >> simp[] >> gen_tac >> strip_tac >>
  (* round k *)
  ‘∃d. k = n + d’ by (qexists_tac ‘k - n’ >> simp[]) >>
  ‘∃e. k = N + e’ by (qexists_tac ‘k - N’ >> simp[]) >>
  ‘inb_of (rstate lfd hw ifds m w0 k) f = []’
    by (‘∃d'. N = n + d'’ by (qexists_tac ‘N - n’ >> simp[]) >>
        qpat_assum ‘∀h f d n. _’ (qspecl_then [‘h’, ‘f’, ‘e’, ‘N’] mp_tac) >> impl_tac
        >- (rpt conj_tac
            >- (qpat_assum ‘∀d. pend _ _ ∧ _’ (qspec_then ‘d'’ mp_tac) >> fs[])
            >- (qpat_assum ‘∀d. pend _ _ ∧ _’ (qspec_then ‘d'’ mp_tac) >> fs[])
            >> rpt strip_tac >> qpat_assum ‘∀k. n ≤ k ⇒ _’ (qspec_then ‘k'’ mp_tac) >>
            fs[]) >>
        simp[]) >>
  ‘pend (rworld lfd hw ifds m w0 k) f ∧ fkeep lfd h f (rstate lfd hw ifds m w0 k)’
    by (qpat_assum ‘∀d. pend _ _ ∧ _’ (qspec_then ‘d’ mp_tac) >> fs[]) >>
  ‘ALOOKUP (rstate lfd hw ifds m w0 k).b.tbl h = SOME f’
    by (qpat_assum ‘fkeep _ _ _ (rstate _ _ _ _ _ k)’
          (strip_assume_tac o REWRITE_RULE [fkeep_def]) >> first_assum ACCEPT_TAC) >>
  ‘LENGTH (outbox_of (rstate lfd hw ifds m w0 k).b f) ≤ hw ∧
   ∀bs. ¬MEM (Write h bs) (new_actions (log_of m) (rhist lfd hw ifds m w0 k))’
    by (qpat_assum ‘∀n''. n1 ≤ n'' ∧ _ ⇒ _’ (qspec_then ‘k’ mp_tac) >> impl_tac
        >- (simp[] >> rpt strip_tac >>
            qpat_assum ‘∀k. n ≤ k ⇒ _’ (qspec_then ‘k'’ mp_tac) >> fs[fetched_at_def]) >>
        strip_tac >> conj_tac >- simp[] >> gen_tac >> first_x_assum irule >> simp[]) >>
  ‘MEM h (ifds (rhist lfd hw ifds m w0 k))’
    by (qpat_assum ‘S1 _ _ _ _ _’ (mp_tac o CONJUNCT1 o REWRITE_RULE [S1_def]) >>
        disch_then drule >> simp[]) >>
  ‘¬fetched_at lfd hw ifds m w0 k f’
    by (qpat_assum ‘∀k. n ≤ k ⇒ _’ (qspec_then ‘k’ mp_tac) >> simp[]) >>
  drule prun_round' >> disch_then (qspecl_then [‘f’, ‘k’] strip_assume_tac) >>
  ‘winv (rworld lfd hw ifds m w0 k)’ by simp[] >>
  drule_all pround_f >> strip_tac >>
  qpat_x_assum ‘inb_of _ _ = [] ∧ _ ⇒ _’ mp_tac >> impl_tac >- simp[] >> strip_tac >>
  ‘N + e = k’ by simp[] >> pop_assum SUBST_ALL_TAC >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (rpt strip_tac >> first_x_assum irule >> metis_tac[])
  >> rpt strip_tac >> CCONTR_TAC >>
  qpat_x_assum ‘∀ev. MEM ev _ ∧ ev_on «sys_recv» _ ev ∧ ¬retried ev ⇒ _’ drule_all >>
  gvs[]
QED

(* [F1]'s indices and the rounds *)
Theorem call_at_round:
  run_ok lfd hw ifds m w0 ∧ MEM ev (rrev lfd hw ifds m w0 k) ∧ ev_on nm f ev ⇒
  ∃i. LENGTH (revs lfd hw ifds m w0 k) ≤ i ∧ call_at lfd hw ifds m w0 i nm f
Proof
  strip_tac >> drule_all round_event >> strip_tac >>
  qexists_tac ‘i’ >> simp[call_at_def] >> qexists_tac ‘SUC k’ >> simp[]
QED

Theorem call_ok_round:
  run_ok lfd hw ifds m w0 ∧ call_at lfd hw ifds m w0 i nm f ∧
  call_ok_at lfd hw ifds m w0 i ∧ LENGTH (revs lfd hw ifds m w0 K0) ≤ i ⇒
  ∃k ev. K0 ≤ k ∧ LENGTH (revs lfd hw ifds m w0 k) ≤ i ∧ MEM ev (rrev lfd hw ifds m w0 k) ∧
         ev_on nm f ev ∧ ¬retried ev
Proof
  rw[call_at_def, call_ok_at_def] >>
  drule event_round >> disch_then drule >> strip_tac >>
  qexistsl_tac [‘k’, ‘EL i (revs lfd hw ifds m w0 n)’] >> simp[] >>
  conj_tac
  >- (CCONTR_TAC >> ‘SUC k ≤ K0’ by simp[] >>
      drule_all revs_len_mono >> simp[])
  >> ‘EL i (revs lfd hw ifds m w0 n') = EL i (revs lfd hw ifds m w0 n)’
       by (irule revs_EL >> simp[]) >> gvs[]
QED

(* From some round on, every round has an event: the trace grows *)
Theorem revs_long:
  run_ok lfd hw ifds m w0 ∧ (∀k. N ≤ k ⇒ rrev lfd hw ifds m w0 k ≠ []) ⇒
  ∀d. d ≤ LENGTH (revs lfd hw ifds m w0 (N + d))
Proof
  strip_tac >> Induct >> simp[] >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘N + d’] strip_assume_tac) >>
  first_x_assum (qspec_then ‘N + d’ mp_tac) >> simp[ADD_CLAUSES] >>
  Cases_on ‘rrev lfd hw ifds m w0 (N + d)’ >> simp[]
QED

(* ------------------------------------------------------------------------
   R1-live, the fetch half: L1 eventually fetches what the kernel holds for
   an open handle's fd (D14, with [F1] as D11′)
   ------------------------------------------------------------------------ *)

Theorem fetch_progress:
  run_ok lfd hw ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd hw ifds m w0 n) + 1 < dimword (:64)) ∧
  F1 lfd hw ifds m w0 ∧ S1 lfd hw ifds m w0 ∧ S3 lfd hw ifds m w0 ∧
  S4 lfd hw ifds m w0 f ⇒
  ∀n h. ALOOKUP (rstate lfd hw ifds m w0 n).b.tbl h = SOME f ∧
        ¬MEM f (rstate lfd hw ifds m w0 n).eof ∧ pend (rworld lfd hw ifds m w0 n) f ⇒
        ∃k. n ≤ k ∧ fetched_at lfd hw ifds m w0 k f
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> CCONTR_TAC >>
  ‘∀k. n ≤ k ⇒ ¬fetched_at lfd hw ifds m w0 k f’ by metis_tac[] >>
  qpat_x_assum ‘¬_’ kall_tac >>
  drule_all late_rounds >> strip_tac >>
  ‘∀k. N ≤ k ⇒ rrev lfd hw ifds m w0 k ≠ []’
    by (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  drule_all revs_long >> strip_tac >>
  (* polls on f, infinitely often *)
  ‘∀i. ∃i'. i ≤ i' ∧ call_at lfd hw ifds m w0 i' «sys_poll» f’
    by (gen_tac >> qpat_assum ‘∀k. N ≤ k ⇒ _ ∧ _’ (qspec_then ‘N + i’ mp_tac) >>
        impl_tac >- simp[] >>
        disch_then (strip_assume_tac o REWRITE_RULE [EXISTS_MEM]) >>
        drule_all call_at_round >> strip_tac >>
        qexists_tac ‘i'’ >> simp[] >>
        qpat_assum ‘∀d. d ≤ _’ (qspec_then ‘i’ assume_tac) >> simp[]) >>
  (* [F1] on polls: infinitely many polls on f are not retried *)
  ‘∀i. ∃i'. i ≤ i' ∧ call_at lfd hw ifds m w0 i' «sys_poll» f ∧
            call_ok_at lfd hw ifds m w0 i'’
    by (qpat_assum ‘F1 _ _ _ _ _’ (mp_tac o REWRITE_RULE [F1_def]) >>
        disch_then (qspecl_then [‘«sys_poll»’, ‘f’] mp_tac) >> metis_tac[]) >>
  (* each leads to a recv on f in its round: recvs on f, infinitely often *)
  ‘∀i. ∃j. i ≤ j ∧ call_at lfd hw ifds m w0 j «sys_recv» f’
    by (gen_tac >>
        qpat_assum ‘∀i. ∃i'. i ≤ i' ∧ _ ∧ call_ok_at _ _ _ _ _ _’
          (qspec_then ‘LENGTH (revs lfd hw ifds m w0 (N + i))’ strip_assume_tac) >>
        drule_all call_ok_round >> strip_tac >>
        qpat_assum ‘∀k. N ≤ k ⇒ _ ∧ _’ (qspec_then ‘k’ mp_tac) >>
        impl_tac >- simp[] >> strip_tac >>
        qpat_x_assum ‘∀ev. MEM ev _ ∧ ev_on «sys_poll» _ ev ∧ _ ⇒ _’ drule_all >>
        disch_then (strip_assume_tac o REWRITE_RULE [EXISTS_MEM]) >>
        drule_all call_at_round >> strip_tac >>
        qexists_tac ‘i''’ >> simp[] >>
        ‘LENGTH (revs lfd hw ifds m w0 (N + i)) ≤ LENGTH (revs lfd hw ifds m w0 k)’
          by (irule revs_len_mono >> simp[]) >>
        qpat_assum ‘∀d. d ≤ _’ (qspec_then ‘i’ assume_tac) >> simp[]) >>
  (* [F1] on recvs: one on f is not retried; but from round N on, every recv
     on f is retried *)
  qpat_assum ‘F1 _ _ _ _ _’ (mp_tac o REWRITE_RULE [F1_def]) >>
  disch_then (qspecl_then [‘«sys_recv»’, ‘f’] mp_tac) >> impl_tac >- metis_tac[] >>
  disch_then (qspec_then ‘LENGTH (revs lfd hw ifds m w0 N)’ strip_assume_tac) >>
  drule_all call_ok_round >> strip_tac >>
  qpat_assum ‘∀k. N ≤ k ⇒ _ ∧ _’ (qspec_then ‘k’ mp_tac) >> impl_tac >- simp[] >>
  strip_tac >> first_x_assum drule_all >> simp[]
QED
