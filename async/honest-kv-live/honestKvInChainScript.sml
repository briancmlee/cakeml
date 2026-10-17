(*
  The input chain (honestEchoL0Chain.in_chain) with S3w at one fd only.
  S3w for all fds is false for KV (after an invalid request its handler
  never reads that handle again), but the chain uses it at f only (in
  late_rounds).  Copied from honestL1PFLive (late_rounds, fetch_progress),
  honestL1PFStream (stream_progress), honestEchoL0FlAt (live_data_hr2) and
  honestEchoL0Chain (in_chain), with S3w replaced by S3f … f; the proofs
  are unchanged.  Unify with the originals at the merge (generalise them
  to S3f there).

  MAIN: S3f, in_chain_f.
*)
Theory honestKvInChain
Ancestors
  honestEchoL0Chain honestEchoL0FlAt
  honestEchoL0Drains honestL1PFConnTrace honestEchoL0Excuse honestEchoL0LiveOwn honestEchoL0Inv
  honestEchoL0Trace honestL1PFBroken honestL1PFD16 honestL1PFStream honestL1PFInput honestL1PFOutLive
  honestL1PFFlushLive honestL1PFFlush honestL1PFDead honestL1PFOut
  honestL1PFLive honestL1PFInv honestL1PFRound honestL1PFModel honestL1BStmts
Libs
  preamble

(* S3w at one fd f *)
Definition S3f_def:
  S3f lfd pol ifds m w0 f ⇔
    ∀n. (∀k. n ≤ k ⇒ ¬fetched f (EL k (SND (SND (SND (prun lfd pol ifds m w0 (SUC k))))))) ⇒
        ∃n'. n ≤ n' ∧ inb_of (rstate lfd pol ifds m w0 n') f = []
End

Theorem S3w_S3f:
  S3w lfd pol ifds m w0 ⇒ S3f lfd pol ifds m w0 f
Proof
  rw[S3w_def, S3f_def]
QED

Theorem late_rounds_f:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ∧
  S1 lfd pol ifds m w0 ∧ S3f lfd pol ifds m w0 f ∧ pol_ok hw pol ∧ S4w lfd pol hw ifds m w0 f ∧
  ALOOKUP (rstate lfd pol ifds m w0 n).b.tbl h = SOME f ∧
  ¬MEM f (rstate lfd pol ifds m w0 n).eof ∧ pend (rworld lfd pol ifds m w0 n) f ∧
  (∀k. n ≤ k ⇒ ¬fetched_at lfd pol ifds m w0 k f) ⇒
  ∃N. n ≤ N ∧
      ∀k. N ≤ k ⇒
          EXISTS (ev_on «sys_poll» f) (rrev lfd pol ifds m w0 k) ∧
          (∀ev. MEM ev (rrev lfd pol ifds m w0 k) ∧ ev_on «sys_poll» f ev ∧ ¬retried ev ⇒
                EXISTS (ev_on «sys_recv» f) (rrev lfd pol ifds m w0 k)) ∧
          (∀ev. MEM ev (rrev lfd pol ifds m w0 k) ∧ ev_on «sys_recv» f ev ⇒ retried ev)
Proof
  strip_tac >>
  ‘fds_lt w0’ by gvs[winv_def] >>
  drule_all fkeep_run >> strip_tac >>
  drule_all winv_run >> strip_tac >>
  drule keep_run >> disch_then drule >> strip_tac >>
  ‘∀d. pend (rworld lfd pol ifds m w0 (n + d)) f ∧
       fkeep lfd h f (rstate lfd pol ifds m w0 (n + d))’
    by (gen_tac >> first_assum (qspecl_then [‘h’, ‘f’, ‘d’, ‘n’] mp_tac) >> simp[]) >>
  (* S4 from n, then S3 from there *)
  qpat_x_assum ‘S4w _ _ _ _ _ _ _’ (mp_tac o REWRITE_RULE [S4w_def]) >>
  disch_then (qspec_then ‘n’ mp_tac) >>
  impl_tac >- (rpt strip_tac >> qpat_assum ‘∀k. n ≤ k ⇒ _’ (qspec_then ‘k’ mp_tac) >>
               fs[fetched_at_def]) >>
  strip_tac >> rename1 ‘n ≤ n1’ >>
  qpat_assum ‘S3f _ _ _ _ _ _’ (mp_tac o REWRITE_RULE [S3f_def]) >>
  disch_then (qspec_then ‘n1’ mp_tac) >>
  impl_tac >- (rpt strip_tac >> qpat_assum ‘∀k. n ≤ k ⇒ _’ (qspec_then ‘k’ mp_tac) >>
               fs[fetched_at_def]) >>
  strip_tac >> rename1 ‘n1 ≤ N’ >>
  qexists_tac ‘N’ >> simp[] >> gen_tac >> strip_tac >>
  (* round k *)
  ‘∃d. k = n + d’ by (qexists_tac ‘k - n’ >> simp[]) >>
  ‘∃e. k = N + e’ by (qexists_tac ‘k - N’ >> simp[]) >>
  ‘inb_of (rstate lfd pol ifds m w0 k) f = []’
    by (‘∃d'. N = n + d'’ by (qexists_tac ‘N - n’ >> simp[]) >>
        qpat_assum ‘∀h f d n. _’ (qspecl_then [‘h’, ‘f’, ‘e’, ‘N’] mp_tac) >> impl_tac
        >- (rpt conj_tac
            >- (qpat_assum ‘∀d. pend _ _ ∧ _’ (qspec_then ‘d'’ mp_tac) >> fs[])
            >- (qpat_assum ‘∀d. pend _ _ ∧ _’ (qspec_then ‘d'’ mp_tac) >> fs[])
            >> rpt strip_tac >> qpat_assum ‘∀k. n ≤ k ⇒ _’ (qspec_then ‘k'’ mp_tac) >>
            fs[]) >>
        simp[]) >>
  ‘pend (rworld lfd pol ifds m w0 k) f ∧ fkeep lfd h f (rstate lfd pol ifds m w0 k)’
    by (qpat_assum ‘∀d. pend _ _ ∧ _’ (qspec_then ‘d’ mp_tac) >> fs[]) >>
  ‘ALOOKUP (rstate lfd pol ifds m w0 k).b.tbl h = SOME f’
    by (qpat_assum ‘fkeep _ _ _ (rstate _ _ _ _ _ k)’
          (strip_assume_tac o REWRITE_RULE [fkeep_def]) >> first_assum ACCEPT_TAC) >>
  ‘LENGTH (outbox_of (rstate lfd pol ifds m w0 k).b f) ≤ hw ∧
   ∀bs. MEM (Write h bs) (new_actions (log_of m) (rhist lfd pol ifds m w0 k)) ⇒ bs = []’
    by (qpat_assum ‘∀n''. n1 ≤ n'' ⇒ _’ (qspec_then ‘k’ mp_tac) >> impl_tac
        >- decide_tac >>
        strip_tac >> conj_tac >- simp[] >> rpt strip_tac >>
        first_x_assum (qspecl_then [‘h’, ‘bs’] mp_tac) >> simp[]) >>
  ‘MEM h (ifds (rhist lfd pol ifds m w0 k))’
    by (qpat_assum ‘S1 _ _ _ _ _’ (mp_tac o CONJUNCT1 o REWRITE_RULE [S1_def]) >>
        disch_then drule >> simp[]) >>
  ‘¬fetched_at lfd pol ifds m w0 k f’
    by (qpat_assum ‘∀k. n ≤ k ⇒ _’ (qspec_then ‘k’ mp_tac) >> simp[]) >>
  drule prun_round' >> disch_then (qspecl_then [‘f’, ‘k’] strip_assume_tac) >>
  ‘winv (rworld lfd pol ifds m w0 k)’ by simp[] >>
  ‘psmall lfd (rstate lfd pol ifds m w0 k)’ by metis_tac[psmall_run] >>
  drule_all pround_f >> disch_then (qspec_then ‘hw’ strip_assume_tac) >>
  qpat_x_assum ‘inb_of _ _ = [] ∧ _ ⇒ _’ mp_tac >> impl_tac >- simp[] >> strip_tac >>
  ‘N + e = k’ by simp[] >> pop_assum SUBST_ALL_TAC >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (rpt strip_tac >> first_x_assum irule >> metis_tac[])
  >> rpt strip_tac >> CCONTR_TAC >>
  qpat_x_assum ‘∀ev. MEM ev _ ∧ ev_on «sys_recv» _ ev ∧ ¬retried ev ⇒ _’ drule_all >>
  gvs[]
QED

Theorem fetch_progress_f:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ∧
  F1 lfd pol ifds m w0 ∧ S1 lfd pol ifds m w0 ∧ S3f lfd pol ifds m w0 f ∧
  pol_ok hw pol ∧ S4w lfd pol hw ifds m w0 f ⇒
  ∀n h. ALOOKUP (rstate lfd pol ifds m w0 n).b.tbl h = SOME f ∧
        ¬MEM f (rstate lfd pol ifds m w0 n).eof ∧ pend (rworld lfd pol ifds m w0 n) f ⇒
        ∃k. n ≤ k ∧ fetched_at lfd pol ifds m w0 k f
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> CCONTR_TAC >>
  ‘∀k. n ≤ k ⇒ ¬fetched_at lfd pol ifds m w0 k f’ by metis_tac[] >>
  qpat_x_assum ‘¬_’ kall_tac >>
  drule_all late_rounds_f >> strip_tac >>
  ‘∀k. N ≤ k ⇒ rrev lfd pol ifds m w0 k ≠ []’
    by (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  drule_all revs_long >> strip_tac >>
  (* polls on f, infinitely often *)
  ‘∀i. ∃i'. i ≤ i' ∧ call_at lfd pol ifds m w0 i' «sys_poll» f’
    by (gen_tac >> qpat_assum ‘∀k. N ≤ k ⇒ _ ∧ _’ (qspec_then ‘N + i’ mp_tac) >>
        impl_tac >- simp[] >>
        disch_then (strip_assume_tac o REWRITE_RULE [EXISTS_MEM]) >>
        drule_all call_at_round >> strip_tac >>
        qexists_tac ‘i'’ >> simp[] >>
        qpat_assum ‘∀d. d ≤ _’ (qspec_then ‘i’ assume_tac) >> simp[]) >>
  (* [F1] on polls: infinitely many polls on f are not retried *)
  ‘∀i. ∃i'. i ≤ i' ∧ call_at lfd pol ifds m w0 i' «sys_poll» f ∧
            call_ok_at lfd pol ifds m w0 i'’
    by (qpat_assum ‘F1 _ _ _ _ _’ (mp_tac o REWRITE_RULE [F1_def]) >>
        disch_then (qspecl_then [‘«sys_poll»’, ‘f’] mp_tac) >> metis_tac[]) >>
  (* each leads to a recv on f in its round: recvs on f, infinitely often *)
  ‘∀i. ∃j. i ≤ j ∧ call_at lfd pol ifds m w0 j «sys_recv» f’
    by (gen_tac >>
        qpat_assum ‘∀i. ∃i'. i ≤ i' ∧ _ ∧ call_ok_at _ _ _ _ _ _’
          (qspec_then ‘LENGTH (revs lfd pol ifds m w0 (N + i))’ strip_assume_tac) >>
        drule_all call_ok_round >> strip_tac >>
        qpat_assum ‘∀k. N ≤ k ⇒ _ ∧ _’ (qspec_then ‘k’ mp_tac) >>
        impl_tac >- simp[] >> strip_tac >>
        qpat_x_assum ‘∀ev. MEM ev _ ∧ ev_on «sys_poll» _ ev ∧ _ ⇒ _’ drule_all >>
        disch_then (strip_assume_tac o REWRITE_RULE [EXISTS_MEM]) >>
        drule_all call_at_round >> strip_tac >>
        qexists_tac ‘i''’ >> simp[] >>
        ‘LENGTH (revs lfd pol ifds m w0 (N + i)) ≤ LENGTH (revs lfd pol ifds m w0 k)’
          by (irule revs_len_mono >> simp[]) >>
        qpat_assum ‘∀d. d ≤ _’ (qspec_then ‘i’ assume_tac) >> simp[]) >>
  (* [F1] on recvs: one on f is not retried; but from round N on, every recv
     on f is retried *)
  qpat_assum ‘F1 _ _ _ _ _’ (mp_tac o REWRITE_RULE [F1_def]) >>
  disch_then (qspecl_then [‘«sys_recv»’, ‘f’] mp_tac) >> impl_tac >- metis_tac[] >>
  disch_then (qspec_then ‘LENGTH (revs lfd pol ifds m w0 N)’ strip_assume_tac) >>
  drule_all call_ok_round >> strip_tac >>
  qpat_assum ‘∀k. N ≤ k ⇒ _ ∧ _’ (qspec_then ‘k’ mp_tac) >> impl_tac >- simp[] >>
  strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem stream_progress_f:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ∧
  F1 lfd pol ifds m w0 ∧ S1 lfd pol ifds m w0 ∧ S3f lfd pol ifds m w0 f ∧
  pol_ok hw pol ∧ S4w lfd pol hw ifds m w0 f ⇒
  ∀R n0 h. ALOOKUP (rstate lfd pol ifds m w0 n0).b.tbl h = SOME f ∧
           ¬MEM f (rstate lfd pol ifds m w0 n0).eof ∧ fl (rworld lfd pol ifds m w0 n0) f R ⇒
           ∃d. fopen lfd pol ifds m w0 h f n0 d ∧
               (fend f (rlogs lfd pol ifds m w0 n0 d) ∨ R ≼ fdata f (rlogs lfd pol ifds m w0 n0 d))
Proof
  strip_tac >> gen_tac >> completeInduct_on ‘LENGTH R’ >> rw[] >>
  Cases_on ‘R = []’ >- (qexists_tac ‘0’ >> simp[fopen_def]) >>
  ‘fds_lt w0’ by gvs[winv_def] >>
  ‘fkeep lfd h f (rstate lfd pol ifds m w0 n0)’ by (drule_all fkeep_run >> simp[]) >>
  ‘pend (rworld lfd pol ifds m w0 n0) f’ by metis_tac[fl_pend] >>
  ‘∃k. n0 ≤ k ∧ fetched_at lfd pol ifds m w0 k f’ by (drule_all fetch_progress_f >> metis_tac[]) >>
  (* the first fetch on f *)
  ‘∃k. (n0 ≤ k ∧ fetched_at lfd pol ifds m w0 k f) ∧
       ∀j. j < k ⇒ ¬(n0 ≤ j ∧ fetched_at lfd pol ifds m w0 j f)’
    by (ho_match_mp_tac WOP >> metis_tac[]) >>
  (* nothing changes up to round k' *)
  ‘fl (rworld lfd pol ifds m w0 k') f R ∧ fkeep lfd h f (rstate lfd pol ifds m w0 k') ∧
   fdata f (rlogs lfd pol ifds m w0 n0 (k' − n0)) = [] ∧
   ¬fend f (rlogs lfd pol ifds m w0 n0 (k' − n0))’
    by (mp_tac stay_rounds >> impl_tac >- simp[] >>
        disch_then (qspec_then ‘k' − n0’ mp_tac) >> impl_tac
        >- (simp[] >> rpt strip_tac >>
            qpat_x_assum ‘∀j. j < k' ⇒ _’ (qspec_then ‘j’ mp_tac) >> simp[]) >>
        simp[]) >>
  ‘rlogs lfd pol ifds m w0 n0 (k' − n0 + 1) =
   rlogs lfd pol ifds m w0 n0 (k' − n0) ++ rlog lfd pol ifds m w0 k'’
    by (simp[rlogs_add] >> simp[rlogs_def]) >>
  ‘fopen lfd pol ifds m w0 h f n0 (k' − n0 + 1)’
    by (rw[fopen_def] >> qexists_tac ‘R’ >>
        mp_tac stay_rounds >> impl_tac >- simp[] >>
        disch_then (qspec_then ‘i’ mp_tac) >> impl_tac
        >- (simp[] >> rpt strip_tac >>
            qpat_x_assum ‘∀j. j < k' ⇒ _’ (qspec_then ‘j’ mp_tac) >> simp[]) >>
        simp[]) >>
  drule_all stream_step >> strip_tac
  >- (qexists_tac ‘k' − n0 + 1’ >> simp[])
  >- (qexists_tac ‘k' − n0 + 1’ >> simp[]) >>
  Cases_on ‘fend f (rlog lfd pol ifds m w0 k')’
  >- (qexists_tac ‘k' − n0 + 1’ >> simp[]) >>
  (* data was fetched: R shrank *)
  drule prun_round' >> disch_then (qspecl_then [‘f’, ‘k'’] strip_assume_tac) >>
  ‘∃bs. MEM (FData f bs) (rlog lfd pol ifds m w0 k')’
    by (qpat_x_assum ‘fetched_at _ _ _ _ _ k' f ⇔ _’
          (fn th => qpat_x_assum ‘fetched_at _ _ _ _ _ k' f’ (assume_tac o EQ_MP th)) >>
        qpat_x_assum ‘fetched _ _’ mp_tac >> simp[fetched_fend]) >>
  ‘winv (rworld lfd pol ifds m w0 k')’ by (drule_all winv_run >> simp[]) >>
  drule_all pround_data >> strip_tac >>
  ‘bs ≠ []’ by (strip_tac >> gvs[]) >>
  ‘fdata f (rlog lfd pol ifds m w0 k') ≠ []’ by metis_tac[fdata_nonnil] >>
  ‘LENGTH R' < LENGTH R’ by (gvs[] >> Cases_on ‘fdata f (rlog lfd pol ifds m w0 k')’ >> gvs[]) >>
  ‘ALOOKUP (rstate lfd pol ifds m w0 (SUC k')).b.tbl h = SOME f ∧
   ¬MEM f (rstate lfd pol ifds m w0 (SUC k')).eof’
    by (qpat_x_assum ‘fkeep _ _ _ (rstate _ _ _ _ _ (SUC k'))’ mp_tac >> simp[fkeep_def]) >>
  qpat_x_assum ‘∀m'. m' < LENGTH R ⇒ _’ (qspec_then ‘LENGTH R'’ mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qspec_then ‘R'’ mp_tac) >> simp[] >>
  disch_then (qspecl_then [‘SUC k'’, ‘h’] mp_tac) >> simp[] >> strip_tac >>
  qexists_tac ‘k' − n0 + 1 + d’ >>
  ‘rlogs lfd pol ifds m w0 n0 (k' − n0 + 1 + d) =
   rlogs lfd pol ifds m w0 n0 (k' − n0 + 1) ++ rlogs lfd pol ifds m w0 (SUC k') d’
    by (simp[rlogs_add] >> simp[ADD1]) >>
  ‘fopen lfd pol ifds m w0 h f n0 (k' − n0 + 1 + d)’
    by (gvs[fopen_def] >> rw[] >> Cases_on ‘i < k' − n0 + 1’ >- simp[] >>
        qpat_x_assum ‘∀i. i < d ⇒ _’ (qspec_then ‘i − (k' − n0 + 1)’ mp_tac) >>
        simp[ADD1]) >>
  gvs[]
QED

Theorem live_data_hr2_f:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ∧
  F1 lfd pol ifds m w0 ∧ S1 lfd pol ifds m w0 ∧ S3f lfd pol ifds m w0 f ∧
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
  drule_all stream_progress_f >> strip_tac
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

Theorem in_chain_f:
  oassm lfd pol ifds m w0 ∧ qinb w0 ∧
  F1 lfd pol ifds m w0 ∧ S1 lfd pol ifds m w0 ∧ S3f lfd pol ifds m w0 f ∧
  pol_ok hw pol ∧ S4w lfd pol hw ifds m w0 f ∧
  MEM (FConn f) (rlog lfd pol ifds m w0 a) ∧
  (∀k. a < k ∧ k < n ⇒ ¬MEM (FConn f) (rlog lfd pol ifds m w0 k)) ∧ a < n ∧
  ALOOKUP (rstate lfd pol ifds m w0 n).b.tbl h = SOME f ∧
  ¬MEM f (rstate lfd pol ifds m w0 n).eof ∧
  l0_chan_of (rworld lfd pol ifds m w0 n) f = SOME c ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 n))) f = SOME j0 ⇒
  (∃d. fopen lfd pol ifds m w0 h f n d ∧
       (EL c (rworld lfd pol ifds m w0 n).chans).peer_sent ≼
       fdata f (rlogs lfd pol ifds m w0 a (n − a + d))) ∨
  (∃k. n ≤ k ∧ fl_at lfd pol ifds m w0 f j0 k) ∨
  ∃k. n ≤ k ∧ fopen lfd pol ifds m w0 h f n (SUC (k − n)) ∧
      hard_recv f (rrev lfd pol ifds m w0 k)
Proof
  strip_tac >>
  ‘run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
   ∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)’ by fs[oassm_def] >>
  drule_all run_peer_sent >> strip_tac
  >- (‘fl (rworld lfd pol ifds m w0 n) f (EL c (rworld lfd pol ifds m w0 n).chans).inbox’
        by simp[fl_def, front_def] >>
      drule_all live_data_hr2_f >> strip_tac
      >- (disj1_tac >> qexists_tac ‘d’ >> simp[] >>
          ‘rlogs lfd pol ifds m w0 a (d + n − a) =
           rlogs lfd pol ifds m w0 a (n − a) ++ rlogs lfd pol ifds m w0 n d’
            by (qspecl_then [‘d’, ‘n − a’] mp_tac (Q.INST [‘n0’ |-> ‘a’] rlogs_add) >>
                simp[]) >>
          ‘∀x y. fdata f (x ++ y) = fdata f x ++ fdata f y’ by simp[fdata_def] >>
          qpat_x_assum ‘_.peer_sent = _’ SUBST1_TAC >>
          qpat_x_assum ‘rlogs _ _ _ _ _ a _ = _’ SUBST1_TAC >>
          pop_assum (fn th => REWRITE_TAC [th]) >>
          fs[IS_PREFIX_APPEND])
      >- (disj2_tac >> disj1_tac >> qexists_tac ‘SUC k’ >> simp[] >>
          irule fopen_fl_at >> simp[] >> metis_tac[])
      >> disj2_tac >> disj2_tac >> metis_tac[]) >>
  disj2_tac >> disj1_tac >> qexists_tac ‘n’ >> simp[fl_at_def, owned_def] >>
  imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED
