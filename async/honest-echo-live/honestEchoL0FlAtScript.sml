(*
  Flush excuses at a held round (design/47, D after D32): the data chain's
  "f's channel broke and was flushed at round k" comes with f held by L1
  at k in the same episode, which (with honestEchoL0NoClose) places it
  before any close call on f: D32's flushed_open.

  TEMP COPY (remove at merge of spike/moonshot-s4g): live_data_hr2 below
  is honest-ffi's, verbatim from spike/moonshot-s4g 75ff12db2
  (honest-l1/honestL1PFBrokenScript.sml).

  MAIN: fl_at, keep_span.
*)
Theory honestEchoL0FlAt
Ancestors
  honestEchoL0Excuse honestEchoL0LiveOwn honestEchoL0Inv honestEchoL0Trace
  honestL1PFBroken honestL1PFD16 honestL1PFStream honestL1PFInput honestL1PFOutLive
  honestL1PFLive honestL1PFInv honestL1PFRound honestL1PFModel honestL1BStmts
Libs
  preamble

(* f's channel is flushed at round k, while L1 holds f there in episode j *)
Definition fl_at_def:
  fl_at lfd pol ifds m w0 f j k ⇔
    flushed (rworld lfd pol ifds m w0 k) f ∧ owned (rstate lfd pol ifds m w0 k) f ∧
    ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 k))) f = SOME j
End

(* L1 holding f without EOF at a round's start: the round ends no
   episode of f *)
Theorem run_keep_noend:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  keep f (rstate lfd pol ifds m w0 i) ⇒
  ¬EXISTS (ep_ends f) (rrev lfd pol ifds m w0 i) ∧
  (MEM f (rstate lfd pol ifds m w0 (SUC i)).acq ∨
   MEM f (MAP SND (rstate lfd pol ifds m w0 (SUC i)).b.tbl))
Proof
  strip_tac >>
  drule_all run_own >> strip_tac >>
  first_x_assum (qspec_then ‘i’ strip_assume_tac) >>
  drule prun_round' >> disch_then (qspecl_then [‘f’, ‘i’] strip_assume_tac) >>
  drule prun_some >> disch_then (qspec_then ‘i’ assume_tac) >>
  ‘(rstate lfd pol ifds m w0 i).b.nxt +
   naccepts (new_actions (log_of m) (rhist lfd pol ifds m w0 i)) < dimword (:64)’
    by (Cases_on ‘prun lfd pol ifds m w0 i’ >> rename1 ‘_ = (hh, r)’ >> PairCases_on ‘r’ >>
        gvs[rstate_def, rhist_def, run_ok_def, pl2_ok_def] >>
        first_x_assum drule >> simp[]) >>
  Cases_on ‘l0_ep_st (0, []) (revs lfd pol ifds m w0 i)’ >>
  ‘own_ok lfd (q, r) (rstate lfd pol ifds m w0 i)’ by metis_tac[] >>
  conj_tac
  >- (drule_all pround_noend >> REWRITE_TAC [EXISTS_ep_ends] >> simp[]) >>
  drule_all pround_keep >> simp[]
QED

(* Kept (in the table or pending, without EOF) at rounds n .. k: the
   episode index of f is the same at k + 1, and L1 still holds f *)
Theorem keep_round[local]:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  keep f (rstate lfd pol ifds m w0 i) ⇒
  ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 (SUC i)))) f =
  ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 i))) f ∧
  owned (rstate lfd pol ifds m w0 (SUC i)) f
Proof
  strip_tac >> drule_all run_keep_noend >> strip_tac >>
  drule prun_round' >> disch_then (qspecl_then [‘f’, ‘i’] strip_assume_tac) >>
  qpat_x_assum ‘¬EXISTS _ _’ mp_tac >> REWRITE_TAC [EXISTS_ep_ends] >> strip_tac >>
  (conj_tac >- (simp[] >> irule ep_st_no_end >> first_assum ACCEPT_TAC)) >>
  fs[owned_def]
QED

Theorem keep_span:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ⇒
  ∀d n. (∀i. n ≤ i ∧ i ≤ n + d ⇒ keep f (rstate lfd pol ifds m w0 i)) ⇒
        ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 (SUC (n + d))))) f =
        ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 n))) f ∧
        owned (rstate lfd pol ifds m w0 (SUC (n + d))) f
Proof
  strip_tac >> Induct >> rpt gen_tac >> strip_tac
  >- (‘keep f (rstate lfd pol ifds m w0 n)’ by (first_x_assum irule >> simp[]) >>
      drule_all keep_round >> simp[]) >>
  ‘ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 (SUC (n + d))))) f =
   ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 n))) f’
    by (qpat_x_assum ‘∀n. (∀i. _) ⇒ _’ (qspec_then ‘n’ mp_tac) >>
        impl_tac >- (rpt strip_tac >> first_x_assum irule >> simp[]) >> simp[]) >>
  ‘keep f (rstate lfd pol ifds m w0 (SUC (n + d)))’ by (first_x_assum irule >> simp[]) >>
  drule_all keep_round >> strip_tac >>
  REWRITE_TAC [ADD_CLAUSES] >> fs[]
QED

(* TEMP COPY from spike/moonshot-s4g 75ff12db2 (honest-ffi) *)
Theorem live_data_hr2:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ∧
  F1 lfd pol ifds m w0 ∧ S1 lfd pol ifds m w0 ∧ S3w lfd pol ifds m w0 ∧
  pol_ok hw pol ∧ S4w lfd pol hw ifds m w0 f ⇒
  ∀R n0 h. ALOOKUP (rstate lfd pol ifds m w0 n0).b.tbl h = SOME f ∧
           ¬MEM f (rstate lfd pol ifds m w0 n0).eof ∧ fl (rworld lfd pol ifds m w0 n0) f R ⇒
           (∃d. fopen lfd pol ifds m w0 h f n0 d ∧ R ≼ fdata f (rlogs lfd pol ifds m w0 n0 d)) ∨
           (∃k. n0 ≤ k ∧ fopen lfd pol ifds m w0 h f n0 (SUC (k − n0)) ∧
                flushed (rworld lfd pol ifds m w0 (SUC k)) f) ∨
           ∃k. n0 ≤ k ∧ fopen lfd pol ifds m w0 h f n0 (SUC (k − n0)) ∧
               MEM (FReset f) (rlog lfd pol ifds m w0 k) ∧
               hard_recv f (rrev lfd pol ifds m w0 k)
Proof
  rpt strip_tac >>
  drule_all stream_progress >> strip_tac
  >- (CCONTR_TAC >>
      pop_assum (strip_assume_tac o SIMP_RULE bool_ss [NOT_EXISTS_THM, DE_MORGAN_THM]) >>
      ‘fds_lt w0’ by fs[winv_def] >>
      drule_all fkeep_run >> strip_tac >>
      drule_all stream_upto >> disch_then (qspec_then ‘d’ strip_assume_tac) >> gvs[] >>
      TRY (metis_tac[] >> NO_TAC) >>
      ‘winv (rworld lfd pol ifds m w0 k)’ by (drule_all winv_run >> simp[]) >>
      drule prun_round' >> disch_then (qspecl_then [‘f’, ‘k’] strip_assume_tac) >>
      ‘fopen lfd pol ifds m w0 h f n0 (SUC (k − n0))’
        by (fs[fopen_def] >> rpt strip_tac >> ‘i < d’ by decide_tac >> metis_tac[]) >>
      Cases_on ‘MEM (FReset f) (rlog lfd pol ifds m w0 k)’
      >- (drule_all pround_freset >> strip_tac >> metis_tac[]) >>
      ‘MEM (FEof f) (rlog lfd pol ifds m w0 k)’
        by (gvs[fend_def, EXISTS_MEM] >> metis_tac[]) >>
      drule_all pround_feof >> strip_tac
      >- (‘n0 + (k − n0) = k’ by decide_tac >>
          ‘fdata f (rlogs lfd pol ifds m w0 n0 (k − n0)) ++ R' ≼
           fdata f (rlogs lfd pol ifds m w0 n0 (SUC (k − n0)))’
            by (REWRITE_TAC [rlogs_SUC] >> fs[]) >>
          metis_tac[])
      >> metis_tac[])
  >> disj1_tac >> qexists_tac ‘d’ >> simp[]
QED

(* live_data_hr2's flush: f kept in the table through rounds n0 .. k, so the
   flush at k + 1 is at a held round of the same episode *)
Theorem fopen_fl_at:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  fopen lfd pol ifds m w0 h f n0 (SUC (k − n0)) ∧ n0 ≤ k ∧
  flushed (rworld lfd pol ifds m w0 (SUC k)) f ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 n0))) f = SOME j ⇒
  fl_at lfd pol ifds m w0 f j (SUC k)
Proof
  strip_tac >> mp_tac keep_span >> impl_tac >- simp[] >>
  disch_then (qspecl_then [‘k − n0’, ‘n0’] mp_tac) >>
  impl_tac
  >- (rpt strip_tac >> fs[fopen_def] >>
      first_x_assum (qspec_then ‘i − n0’ mp_tac) >> simp[] >> strip_tac >>
      fs[fkeep_def, keep_def] >> metis_tac[ALOOKUP_MEM, MEM_MAP, pairTheory.SND]) >>
  ‘n0 + (k − n0) = k’ by decide_tac >> simp[fl_at_def]
QED
