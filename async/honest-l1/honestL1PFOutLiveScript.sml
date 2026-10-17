(*
  The output side of R1-live (moonshot step 8): flush_live.  Everything
  the server wrote to a client by round n eventually reaches the kernel
  (is in its channel's sent), unless the channel breaks or L1 dropped f's
  output: f was already gone at n, a send on f failed hard (D16/D19 (a)),
  or the write timeout dropped f (D23).
*)
Theory honestL1PFOutLive
Ancestors
  honestL1PFDead honestL1PFFlushLive honestL1PFFlush honestL1PFOut honestL0WorldProps
  honestL1PFConnRun honestL1PFConn honestL1PFLive honestL1PFRound honestL1PFRefine honestL1PFInv
  honestL1PFModel honestL1Steps honestL1Inv honestL1Props honestL1Model honestL0WorldInv
  honestL0Rely honestL0World honestL0 socketV2FFI asyncHLModel asyncCore Marshalling
Libs
  preamble

(* ------------------------------------------------------------------------
   The run's rounds, as the round lemmas need them
   ------------------------------------------------------------------------ *)

(* Round k's write-timeout drops *)
Definition rdrop_def:
  rdrop lfd pol ifds m w0 k f ⇔
    MEM f (round_drops lfd pol (ifds (rhist lfd pol ifds m w0 k))
             (rworld lfd pol ifds m w0 k, rstate lfd pol ifds m w0 k)
             (new_actions (log_of m) (rhist lfd pol ifds m w0 k)))
End

(* The run's hypotheses for the output side: R1-safe's, plus queued
   connections with nothing sent and sends that record their counts *)
Definition oassm_def:
  oassm lfd pol ifds m w0 ⇔
    run_ok lfd pol ifds m w0 ∧ winv w0 ∧ qfresh w0 ∧ MEM lfd (l0_used w0) ∧
    (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ∧
    ∀n. EVERY small_send (revs lfd pol ifds m w0 n)
End

Theorem prun_parts:
  run_ok lfd pol ifds m w0 ⇒
  ∀n. ∃logs. prounds lfd pol ifds m (w0, pinit) n =
             SOME (rhist lfd pol ifds m w0 n,
                   (rworld lfd pol ifds m w0 n, rstate lfd pol ifds m w0 n),
                   revs lfd pol ifds m w0 n, logs)
Proof
  rpt strip_tac >> drule prun_some >> disch_then (qspec_then ‘n’ assume_tac) >>
  Cases_on ‘prun lfd pol ifds m w0 n’ >> PairCases_on ‘r’ >>
  gvs[rhist_def, rworld_def, rstate_def, revs_def]
QED

(* R1-safe's relations at round k *)
Theorem run_rel:
  oassm lfd pol ifds m w0 ⇒
  ∀k. pv_rel lfd (FST (pcm lfd pol ifds m w0 k)) (rstate lfd pol ifds m w0 k)
               (FST (hst lfd ifds m (psk lfd pol ifds m w0) k)) ∧
      pown lfd (rstate lfd pol ifds m w0 k) ∧
      out_rel (FST (pcm lfd pol ifds m w0 k)) (rworld lfd pol ifds m w0 k)
              (rstate lfd pol ifds m w0 k) (FST (hst lfd ifds m (psk lfd pol ifds m w0) k))
Proof
  rw[oassm_def] >> drule prun_parts >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  ‘l0_rely w0 ∧ fds_lt w0’ by fs[winv_def]
  >- (mp_tac l1pf_refines_hl >> simp[] >> disch_then drule >> simp[])
  >- (mp_tac l1pf_refines_hl >> simp[] >> disch_then drule >> simp[])
  >> mp_tac l1pf_refines_hl_out >> simp[] >> disch_then drule >> simp[]
QED

(* l1pf_round_sent_x on the run *)
Theorem run_round_x:
  oassm lfd pol ifds m w0 ∧
  (MEM f (MAP SND (rstate lfd pol ifds m w0 k).b.tbl) ∨
   MEM f (rstate lfd pol ifds m w0 k).b.closing ∨ MEM f (rstate lfd pol ifds m w0 k).acq) ∧
  l0_chan_of (rworld lfd pol ifds m w0 k) f = SOME c ⇒
  ∃live. tkx live (MEM f (rstate lfd pol ifds m w0 k).b.gone ∨
                   hard_send f (rrev lfd pol ifds m w0 k) ∨ rdrop lfd pol ifds m w0 k f)
           (rworld lfd pol ifds m w0 (SUC k)) (rstate lfd pol ifds m w0 (SUC k)) f c
           (csent (rworld lfd pol ifds m w0 k) c ++ evs_sent f (rrev lfd pol ifds m w0 k))
           (EL (cl (FST (pcm lfd pol ifds m w0 k)) f)
               (FST (hst lfd ifds m (psk lfd pol ifds m w0) (SUC k))).clients).outgoing
Proof
  rw[oassm_def] >>
  drule prun_parts >> disch_then (fn th => strip_assume_tac (Q.SPEC ‘k’ th) >>
                                            strip_assume_tac (Q.SPEC ‘SUC k’ th)) >>
  mp_tac (Q.INST [‘N’ |-> ‘SUC k’] l1pf_round_sent_x) >> simp[] >>
  disch_then (qspecl_then [‘k’, ‘rhist lfd pol ifds m w0 k’,
                           ‘(rworld lfd pol ifds m w0 k, rstate lfd pol ifds m w0 k)’,
                           ‘revs lfd pol ifds m w0 k’, ‘logs’,
                           ‘rhist lfd pol ifds m w0 (SUC k)’,
                           ‘(rworld lfd pol ifds m w0 (SUC k), rstate lfd pol ifds m w0 (SUC k))’,
                           ‘revs lfd pol ifds m w0 (SUC k)’, ‘logs'’] mp_tac) >>
  simp[rdrop_def, rrev_def]
QED

(* An fd still on channel c after round k keeps its client *)
Theorem run_cl_stable:
  oassm lfd pol ifds m w0 ∧
  (MEM f (MAP SND (rstate lfd pol ifds m w0 k).b.tbl) ∨
   MEM f (rstate lfd pol ifds m w0 k).b.closing ∨ MEM f (rstate lfd pol ifds m w0 k).acq) ∧
  l0_chan_of (rworld lfd pol ifds m w0 k) f = SOME c ∧
  l0_chan_of (rworld lfd pol ifds m w0 (SUC k)) f = SOME c ⇒
  cl (FST (pcm lfd pol ifds m w0 (SUC k))) f = cl (FST (pcm lfd pol ifds m w0 k)) f
Proof
  rw[oassm_def] >>
  drule prun_parts >> disch_then (fn th => strip_assume_tac (Q.SPEC ‘k’ th) >>
                                            strip_assume_tac (Q.SPEC ‘SUC k’ th)) >>
  ‘¬MEM (FConn f) (plog lfd pol ifds m w0 k)’
    by (mp_tac (Q.INST [‘N’ |-> ‘SUC k’] l1pf_round_noconn) >> simp[] >>
        disch_then (qspecl_then [‘k’, ‘rhist lfd pol ifds m w0 k’,
                                 ‘(rworld lfd pol ifds m w0 k, rstate lfd pol ifds m w0 k)’,
                                 ‘revs lfd pol ifds m w0 k’, ‘logs’,
                                 ‘rhist lfd pol ifds m w0 (SUC k)’,
                                 ‘(rworld lfd pol ifds m w0 (SUC k),
                                   rstate lfd pol ifds m w0 (SUC k))’,
                                 ‘revs lfd pol ifds m w0 (SUC k)’, ‘logs'’] mp_tac) >>
        simp[]) >>
  simp[pcm_def] >>
  Cases_on ‘pcm lfd pol ifds m w0 k’ >> simp[] >>
  Cases_on ‘arrs lfd (q, r) (plog lfd pol ifds m w0 k)’ >> rename1 ‘_ = (as, ck)’ >>
  PairCases_on ‘ck’ >> simp[] >>
  drule arrs_fconn >> strip_tac >> gvs[] >>
  irule (cj 1 cl_append) >> simp[]
QED

(* ------------------------------------------------------------------------
   Following f's connection round by round
   ------------------------------------------------------------------------ *)

(* What the server has written to client j by round k *)
Definition oout_def:
  oout lfd pol ifds m w0 j k =
    (EL j (FST (hst lfd ifds m (psk lfd pol ifds m w0) k)).clients).outgoing
End

(* At round k, f is still the connection of client j on channel c, not
   gone, and the kernel's sent then f's outbox is what the server wrote *)
Definition good_def:
  good lfd pol ifds m w0 f c j k ⇔
    (MEM f (MAP SND (rstate lfd pol ifds m w0 k).b.tbl) ∨
     MEM f (rstate lfd pol ifds m w0 k).b.closing ∨ MEM f (rstate lfd pol ifds m w0 k).acq) ∧
    cl (FST (pcm lfd pol ifds m w0 k)) f = j ∧
    j < LENGTH (FST (hst lfd ifds m (psk lfd pol ifds m w0) k)).clients ∧
    ¬MEM f (rstate lfd pol ifds m w0 k).b.gone ∧
    l0_chan_of (rworld lfd pol ifds m w0 k) f = SOME c ∧
    csent (rworld lfd pol ifds m w0 k) c ++ outbox_of (rstate lfd pol ifds m w0 k).b f =
      oout lfd pol ifds m w0 j k
End

(* One round from a good one: L1 dropped f's output (a hard error or the
   write timeout), or closed f with everything written taken, or f is
   still good, with what the round's sends took on f added *)
Theorem good_step:
  oassm lfd pol ifds m w0 ∧ good lfd pol ifds m w0 f c j k ⇒
  hard_send f (rrev lfd pol ifds m w0 k) ∨ rdrop lfd pol ifds m w0 k f ∨
  csent (rworld lfd pol ifds m w0 (SUC k)) c = oout lfd pol ifds m w0 j (SUC k) ∨
  (good lfd pol ifds m w0 f c j (SUC k) ∧
   csent (rworld lfd pol ifds m w0 (SUC k)) c =
     csent (rworld lfd pol ifds m w0 k) c ++ evs_sent f (rrev lfd pol ifds m w0 k))
Proof
  strip_tac >> simp[oout_def] >>
  ‘(MEM f (MAP SND (rstate lfd pol ifds m w0 k).b.tbl) ∨
    MEM f (rstate lfd pol ifds m w0 k).b.closing ∨ MEM f (rstate lfd pol ifds m w0 k).acq) ∧
   cl (FST (pcm lfd pol ifds m w0 k)) f = j ∧
   j < LENGTH (FST (hst lfd ifds m (psk lfd pol ifds m w0) k)).clients ∧
   ¬MEM f (rstate lfd pol ifds m w0 k).b.gone ∧
   l0_chan_of (rworld lfd pol ifds m w0 k) f = SOME c’ by fs[good_def] >>
  mp_tac run_round_x >> (impl_tac >- fs[]) >> strip_tac >>
  qpat_x_assum ‘cl _ _ = j’ (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  Cases_on ‘live’ >> fs[tkx_def] >>
  TRY (fs[dinv_def, uchan_def] >> NO_TAC) >>
  qpat_x_assum ‘tk T _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [tk_def]) >>
  Cases_on ‘MEM f (rstate lfd pol ifds m w0 (SUC k)).b.gone’ >> fs[] >>
  ‘l0_chan_of (rworld lfd pol ifds m w0 (SUC k)) f = SOME c’ by fs[acct_def] >>
  disj2_tac >> disj2_tac >> disj2_tac >>
  simp[good_def, oout_def] >>
  ‘cl (FST (pcm lfd pol ifds m w0 (SUC k))) f = j’
    by (‘cl (FST (pcm lfd pol ifds m w0 k)) f = j’ by fs[good_def] >>
        pop_assum (SUBST1_TAC o SYM) >> irule run_cl_stable >> fs[] >> metis_tac[]) >>
  ‘j < LENGTH (FST (hst lfd ifds m (psk lfd pol ifds m w0) (SUC k))).clients’
    by (drule hst_out_step >> simp[]) >>
  fs[acct_def] >> metis_tac[APPEND_ASSOC]
QED

(* An open or closing fd that is not gone starts good *)
Theorem good_init:
  oassm lfd pol ifds m w0 ∧
  (MEM f (MAP SND (rstate lfd pol ifds m w0 n).b.tbl) ∨
   MEM f (rstate lfd pol ifds m w0 n).b.closing) ∧
  ¬MEM f (rstate lfd pol ifds m w0 n).b.gone ∧
  l0_chan_of (rworld lfd pol ifds m w0 n) f = SOME c ⇒
  good lfd pol ifds m w0 f c (cl (FST (pcm lfd pol ifds m w0 n)) f) n
Proof
  strip_tac >> drule run_rel >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  qpat_x_assum ‘out_rel _ _ _ _’ (strip_assume_tac o REWRITE_RULE [out_rel_def]) >>
  qpat_x_assum ‘∀f. MEM f (MAP SND _) ∨ _ ⇒ _’ (qspec_then ‘f’ mp_tac) >>
  (impl_tac >- fs[]) >> strip_tac >>
  ‘c' = c’ by fs[acct_def] >> gvs[] >>
  simp[good_def] >> gvs[acct_def, oout_def] >>
  drule cl_mem >> strip_tac >> gvs[pv_rel_def, EVERY_MEM]
QED

(* Following a good f: up to round k + d, either L1 closed f with all
   written taken or dropped its output in some round, or f is still good
   and its channel's sent only grew *)
Theorem good_iter:
  oassm lfd pol ifds m w0 ∧ good lfd pol ifds m w0 f c j k ⇒
  ∀d. (∃i. k ≤ i ∧ i < k + d ∧
           (hard_send f (rrev lfd pol ifds m w0 i) ∨ rdrop lfd pol ifds m w0 i f ∨
            csent (rworld lfd pol ifds m w0 (SUC i)) c = oout lfd pol ifds m w0 j (SUC i))) ∨
      (good lfd pol ifds m w0 f c j (k + d) ∧
       csent (rworld lfd pol ifds m w0 k) c ≼ csent (rworld lfd pol ifds m w0 (k + d)) c)
Proof
  strip_tac >> Induct >> simp[] >>
  pop_assum DISJ_CASES_TAC
  >- (disj1_tac >> pop_assum strip_assume_tac >> qexists_tac ‘i’ >> fs[]) >>
  pop_assum strip_assume_tac >>
  drule_all good_step >> strip_tac >>
  TRY (disj1_tac >> qexists_tac ‘k + d’ >> fs[ADD_CLAUSES] >> NO_TAC) >>
  disj2_tac >> fs[ADD_CLAUSES] >>
  irule IS_PREFIX_TRANS >> goal_assum (first_assum o mp_then Any mp_tac) >> simp[]
QED

(* ------------------------------------------------------------------------
   Progress
   ------------------------------------------------------------------------ *)

(* Finished, from round k, by round k': what was written (O) is in c's
   sent, or c broke, or L1 dropped f's output in a round in between *)
Definition ofin_def:
  ofin lfd pol ifds m w0 f c wr k k' ⇔
    wr ≼ csent (rworld lfd pol ifds m w0 k') c ∨
    (EL c (rworld lfd pol ifds m w0 k').chans).broken ∨
    ∃i. k ≤ i ∧ i < k' ∧
        (hard_send f (rrev lfd pol ifds m w0 i) ∨ rdrop lfd pol ifds m w0 i f)
End

Theorem good_owed:
  good lfd pol ifds m w0 f c j k ∧ wr ≼ oout lfd pol ifds m w0 j k ∧
  ¬(wr ≼ csent (rworld lfd pol ifds m w0 k) c) ⇒
  outbox_of (rstate lfd pol ifds m w0 k).b f ≠ []
Proof
  rw[good_def] >> strip_tac >> gvs[]
QED

Theorem good_oout_mono:
  good lfd pol ifds m w0 f c j k ∧ k ≤ k' ⇒
  oout lfd pol ifds m w0 j k ≼ oout lfd pol ifds m w0 j k'
Proof
  rw[good_def, oout_def] >>
  ‘k' = k + (k' − k)’ by simp[] >> pop_assum SUBST1_TAC >>
  drule hst_out_mono >> disch_then (qspec_then ‘k' − k’ strip_assume_tac) >> simp[]
QED

Theorem good_olive:
  oassm lfd pol ifds m w0 ∧ good lfd pol ifds m w0 f c j k ∧
  outbox_of (rstate lfd pol ifds m w0 k).b f ≠ [] ⇒
  olive lfd f (rstate lfd pol ifds m w0 k)
Proof
  strip_tac >> drule run_rel >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  gvs[olive_def, good_def, pown_def, ALL_DISTINCT_APPEND] >> rpt strip_tac >> gvs[]
QED

(* Round k's events are small sends *)
Theorem rrev_small:
  oassm lfd pol ifds m w0 ⇒ EVERY small_send (rrev lfd pol ifds m w0 k)
Proof
  rw[oassm_def] >> drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
  first_x_assum (qspec_then ‘SUC k’ mp_tac) >> simp[EVERY_APPEND]
QED

(* A non-retried send on f in a round from good f with output owed: it
   took bytes, or failed hard *)
Theorem good_send:
  oassm lfd pol ifds m w0 ∧ good lfd pol ifds m w0 f c j k ∧
  outbox_of (rstate lfd pol ifds m w0 k).b f ≠ [] ∧
  MEM ev (rrev lfd pol ifds m w0 k) ∧ ev_on «sys_send» f ev ∧ ¬retried ev ⇒
  evs_sent f (rrev lfd pol ifds m w0 k) ≠ [] ∨ hard_send f (rrev lfd pol ifds m w0 k)
Proof
  strip_tac >> drule_all good_olive >> strip_tac >>
  drule rrev_small >> disch_then (qspec_then ‘k’ assume_tac) >>
  ‘run_ok lfd pol ifds m w0 ∧ winv w0’ by fs[oassm_def] >>
  ‘winv (rworld lfd pol ifds m w0 k)’ by metis_tac[winv_run] >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
  irule pround_progress >> fs[good_def] >> metis_tac[]
QED

(* From a good round with output still owed, a later round finishes or
   is good with strictly more taken on c *)
Theorem good_progress:
  oassm lfd pol ifds m w0 ∧ F1 lfd pol ifds m w0 ∧ F2 w0 ∧
  drains lfd pol ifds m w0 c ∧ nshut w0 ∧
  good lfd pol ifds m w0 f c j k ∧ wr ≼ oout lfd pol ifds m w0 j k ∧
  ¬(wr ≼ csent (rworld lfd pol ifds m w0 k) c) ⇒
  ∃k'. k < k' ∧
       (ofin lfd pol ifds m w0 f c wr k k' ∨
        (good lfd pol ifds m w0 f c j k' ∧
         LENGTH (csent (rworld lfd pol ifds m w0 k) c) <
         LENGTH (csent (rworld lfd pol ifds m w0 k') c)))
Proof
  strip_tac >>
  drule_all good_owed >> strip_tac >>
  drule_all good_olive >> strip_tac >>
  ‘l0_chan_of (rworld lfd pol ifds m w0 k) f = SOME c’ by fs[good_def] >>
  mp_tac (Q.INST [‘n’ |-> ‘k’] flush_progress_nshut) >>
  (impl_tac >- fs[oassm_def]) >>
  disch_then (qx_choose_then ‘k1’ (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  drule_all good_iter >> disch_then (qspec_then ‘k1 − k’ mp_tac) >>
  ‘k + (k1 − k) = k1’ by simp[] >> pop_assum SUBST1_TAC >>
  disch_then DISJ_CASES_TAC
  >- ((* finished in a round before k1 *)
      pop_assum (qx_choose_then ‘i’ strip_assume_tac) >>
      qexists_tac ‘SUC i’ >> simp[] >> disj1_tac >> simp[ofin_def] >>
      TRY (disj2_tac >> disj2_tac >> qexists_tac ‘i’ >> simp[] >> NO_TAC) >>
      disj1_tac >> irule IS_PREFIX_TRANS >>
      qexists_tac ‘oout lfd pol ifds m w0 j k’ >> simp[] >>
      qpat_x_assum ‘csent _ c = _’ SUBST1_TAC >>
      irule good_oout_mono >> simp[] >> metis_tac[]) >>
  (* good at k1: its round *)
  pop_assum strip_assume_tac >>
  ‘wr ≼ oout lfd pol ifds m w0 j k1’
    by (irule IS_PREFIX_TRANS >> qexists_tac ‘oout lfd pol ifds m w0 j k’ >> simp[] >>
        irule good_oout_mono >> simp[] >> metis_tac[]) >>
  ‘wr ≼ oout lfd pol ifds m w0 j (SUC k1)’
    by (irule IS_PREFIX_TRANS >> qexists_tac ‘oout lfd pol ifds m w0 j k1’ >> simp[] >>
        irule good_oout_mono >> simp[] >> metis_tac[]) >>
  drule_all good_step >> disch_then (fn th => STRIP_ASSUME_TAC th) >>
  TRY (qexists_tac ‘SUC k1’ >> simp[] >> disj1_tac >> simp[ofin_def] >>
       disj2_tac >> disj2_tac >> qexists_tac ‘k1’ >> simp[] >> NO_TAC) >>
  TRY (qexists_tac ‘SUC k1’ >> simp[] >> disj1_tac >> simp[ofin_def] >> NO_TAC) >>
  qpat_x_assum ‘(∃ev. _) ∨ _’ strip_assume_tac
  >- ((* a send on f that L1 does not retry *)
      Cases_on ‘wr ≼ csent (rworld lfd pol ifds m w0 k1) c’
      >- (qexists_tac ‘k1’ >> Cases_on ‘k1 = k’ >> gvs[] >> simp[ofin_def])
      >> ‘outbox_of (rstate lfd pol ifds m w0 k1).b f ≠ []’ by metis_tac[good_owed] >>
      drule_all good_send >> strip_tac
      >- (qexists_tac ‘SUC k1’ >> simp[] >> disj2_tac >>
          imp_res_tac IS_PREFIX_LENGTH >>
          Cases_on ‘evs_sent f (rrev lfd pol ifds m w0 k1)’ >> gvs[])
      >> qexists_tac ‘SUC k1’ >> simp[] >> disj1_tac >> simp[ofin_def] >>
      disj2_tac >> disj2_tac >> qexists_tac ‘k1’ >> simp[])
  >- ((* f's outbox emptied: everything written is taken *)
      qexists_tac ‘SUC k1’ >> simp[] >> disj1_tac >> simp[ofin_def] >> disj1_tac >>
      qpat_x_assum ‘good _ _ _ _ _ _ _ _ (SUC k1)’ mp_tac >> simp[good_def] >>
      strip_tac >> gvs[])
  >> qexists_tac ‘SUC k1’ >> simp[] >> disj1_tac >> simp[ofin_def]
QED

Theorem ofin_mono:
  ofin lfd pol ifds m w0 f c wr k k' ∧ n ≤ k ⇒ ofin lfd pol ifds m w0 f c wr n k'
Proof
  rw[ofin_def] >> simp[] >> disj2_tac >> disj2_tac >> qexists_tac ‘i’ >> simp[]
QED

Theorem good_finish:
  oassm lfd pol ifds m w0 ∧ F1 lfd pol ifds m w0 ∧ F2 w0 ∧
  drains lfd pol ifds m w0 c ∧ nshut w0 ⇒
  ∀d k. good lfd pol ifds m w0 f c j k ∧ n ≤ k ∧ wr ≼ oout lfd pol ifds m w0 j k ∧
        LENGTH wr − LENGTH (csent (rworld lfd pol ifds m w0 k) c) = d ⇒
        ∃n'. k ≤ n' ∧ ofin lfd pol ifds m w0 f c wr n n'
Proof
  strip_tac >> completeInduct_on ‘d’ >> rpt strip_tac >>
  Cases_on ‘wr ≼ csent (rworld lfd pol ifds m w0 k) c’
  >- (qexists_tac ‘k’ >> simp[ofin_def]) >>
  drule_all good_progress >> strip_tac
  >- (qexists_tac ‘k'’ >> simp[] >> irule ofin_mono >> metis_tac[]) >>
  ‘wr ≼ oout lfd pol ifds m w0 j k'’
    by (irule IS_PREFIX_TRANS >> qexists_tac ‘oout lfd pol ifds m w0 j k’ >> simp[] >>
        irule good_oout_mono >> simp[] >> metis_tac[]) >>
  ‘csent (rworld lfd pol ifds m w0 k') c ≼ oout lfd pol ifds m w0 j k'’
    by (qpat_x_assum ‘good _ _ _ _ _ _ _ _ k'’ mp_tac >> simp[good_def] >> strip_tac >>
        qpat_x_assum ‘_ ++ _ = oout _ _ _ _ _ _ _’ (SUBST1_TAC o SYM) >> simp[]) >>
  Cases_on ‘wr ≼ csent (rworld lfd pol ifds m w0 k') c’
  >- (qexists_tac ‘k'’ >> simp[ofin_def]) >>
  ‘LENGTH (csent (rworld lfd pol ifds m w0 k') c) < LENGTH wr’
    by (CCONTR_TAC >>
        qspecl_then [‘oout lfd pol ifds m w0 j k'’, ‘wr’,
                     ‘csent (rworld lfd pol ifds m w0 k') c’] mp_tac prefixes_is_prefix_total >>
        simp[] >> strip_tac >> imp_res_tac IS_PREFIX_LENGTH >>
        ‘csent (rworld lfd pol ifds m w0 k') c = wr’
          by (irule (iffLR IS_PREFIX_LENGTH_ANTI) >> simp[]) >>
        gvs[]) >>
  first_x_assum (qspec_then ‘LENGTH wr − LENGTH (csent (rworld lfd pol ifds m w0 k') c)’ mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qspec_then ‘k'’ mp_tac) >> simp[] >> strip_tac >>
  qexists_tac ‘n'’ >> simp[]
QED

(* MAIN (output liveness): what the server has written to an open or
   closing fd's client by round n eventually reaches the kernel (is in its
   channel's sent), unless the channel breaks or L1 dropped f's output:
   f was already gone at n, or a send on f failed hard (D16, D19 (a)), or
   the write timeout dropped f (D23) in a round from n on *)
Theorem flush_live:
  oassm lfd pol ifds m w0 ∧ F1 lfd pol ifds m w0 ∧ F2 w0 ∧
  drains lfd pol ifds m w0 c ∧ nshut w0 ∧
  (MEM f (MAP SND (rstate lfd pol ifds m w0 n).b.tbl) ∨
   MEM f (rstate lfd pol ifds m w0 n).b.closing) ∧
  l0_chan_of (rworld lfd pol ifds m w0 n) f = SOME c ⇒
  ∃n'. n ≤ n' ∧
       ((EL (cl (FST (pcm lfd pol ifds m w0 n)) f)
            (FST (hst lfd ifds m (psk lfd pol ifds m w0) n)).clients).outgoing ≼
          csent (rworld lfd pol ifds m w0 n') c ∨
        (EL c (rworld lfd pol ifds m w0 n').chans).broken ∨
        MEM f (rstate lfd pol ifds m w0 n).b.gone ∨
        ∃k. n ≤ k ∧ k < n' ∧
            (hard_send f (rrev lfd pol ifds m w0 k) ∨ rdrop lfd pol ifds m w0 k f))
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  Cases_on ‘MEM f (rstate lfd pol ifds m w0 n).b.gone’
  >- (qexists_tac ‘n’ >> simp[]) >>
  ‘good lfd pol ifds m w0 f c (cl (FST (pcm lfd pol ifds m w0 n)) f) n’
    by (irule good_init >> fs[]) >>
  mp_tac (Q.INST [‘j’ |-> ‘cl (FST (pcm lfd pol ifds m w0 n)) f’,
                  ‘wr’ |-> ‘oout lfd pol ifds m w0 (cl (FST (pcm lfd pol ifds m w0 n)) f) n’]
                 good_finish) >>
  (impl_tac >- fs[]) >>
  disch_then (qspecl_then
    [‘LENGTH (oout lfd pol ifds m w0 (cl (FST (pcm lfd pol ifds m w0 n)) f) n) −
      LENGTH (csent (rworld lfd pol ifds m w0 n) c)’, ‘n’] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac ‘n'’ >> fs[ofin_def, oout_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The write timeout's drops (D23), by cause
   ------------------------------------------------------------------------ *)

Theorem pf_sendwait_pos[simp]:
  1 < pf_sendwait
Proof
  simp[pf_sendwait_def]
QED

(* A stall count after the stall step: 0, or one more than before (a new
   fd's "before" is 0) for an fd whose outbox is not empty and did not
   shrink, and with no FReset *)
Theorem stall_step_entry:
  MEM (f, m) (stall_step hfs ob log ps).stalls ⇒
  m < pf_sendwait ∧
  (m = 0 ∨
   ¬MEM (FReset f) log ∧ outbox_of ps.b f ≠ [] ∧
   ¬(LENGTH (outbox_of ps.b f) < LENGTH (ob f)) ∧
   (m = 1 ∨ MEM (f, m − 1) ps.stalls))
Proof
  simp[stall_step_def, MEM_FILTER, MEM_MAP, EXISTS_PROD, PULL_EXISTS] >>
  rw[] >> gvs[MEM_FILTER, MEM_MAP] >> every_case_tac >> gvs[]
QED

(* A dropped fd: an FReset, or a count that reached pf_sendwait *)
Theorem stall_drops_entry:
  MEM f (stall_drops hfs ob log ps) ⇒
  MEM (FReset f) log ∨
  (outbox_of ps.b f ≠ [] ∧ ¬(LENGTH (outbox_of ps.b f) < LENGTH (ob f)) ∧
   ∃n. pf_sendwait ≤ n + 1 ∧ MEM (f, n) ps.stalls)
Proof
  simp[stall_drops_def, MEM_FILTER, MEM_MAP, EXISTS_PROD, PULL_EXISTS] >>
  rw[] >> gvs[MEM_FILTER, MEM_MAP] >> every_case_tac >> gvs[pf_sendwait_def] >>
  metis_tac[]
QED

(* A stalled round (the stall count's condition): after the round's
   actions f's outbox is not empty, and the round's flush did not shrink
   it *)
Definition tail_stalled_def:
  tail_stalled lfd pol hs (w, ps) f ⇔
    ∃rv w1 pevs w2 b2 fevs.
      l1_polls [pf_poll_set lfd pol ps hs] w = SOME (rv, w1, pevs) ∧
      l1_flush (writable_fds rv) (w1, ps.b) = SOME ((w2, b2), fevs) ∧
      outbox_of b2 f ≠ [] ∧ ¬(LENGTH (outbox_of b2 f) < LENGTH (outbox_of ps.b f))
End

Definition round_stalled_def:
  round_stalled lfd pol hs ws acts f ⇔
    ∃rs evs ws1. pacts lfd ws acts = SOME (rs, evs, ws1) ∧ tail_stalled lfd pol hs ws1 f
End

Definition rstalled_def:
  rstalled lfd pol ifds m w0 k f ⇔
    round_stalled lfd pol (ifds (rhist lfd pol ifds m w0 k))
      (rworld lfd pol ifds m w0 k, rstate lfd pol ifds m w0 k)
      (new_actions (log_of m) (rhist lfd pol ifds m w0 k)) f
End

Theorem pdo_stalls:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ⇒ ps'.stalls = ps.stalls
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> rw[AllCaseEqs()] >> gvs[set_inb_def] >>
  TRY (PairCases_on ‘z’) >> gvs[]
QED

Theorem pacts_stalls:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ⇒ ps'.stalls = ps.stalls
Proof
  Induct >> simp[pacts_def] >> rw[AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  imp_res_tac pdo_stalls >> first_x_assum drule >> simp[]
QED

Theorem pf_fetch_stalls:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ⇒ ps'.stalls = ps.stalls
Proof
  Induct >> simp[pf_fetch_def] >> rw[AllCaseEqs()] >>
  TRY (pairarg_tac >> gvs[AllCaseEqs()]) >> first_x_assum drule >> rw[] >> gvs[set_inb_def]
QED

(* One round's stall counts and drops *)
Theorem pround_stalls:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ⇒
  (∀f m. MEM (f, m) ps'.stalls ⇒
         m < pf_sendwait ∧
         (m = 0 ∨ round_stalled lfd pol hs (w, ps) acts f ∧ (m = 1 ∨ MEM (f, m − 1) ps.stalls))) ∧
  (∀f. MEM f (round_drops lfd pol hs (w, ps) acts) ⇒
       MEM (FReset f) log ∨
       round_stalled lfd pol hs (w, ps) acts f ∧
       ∃n. pf_sendwait ≤ n + 1 ∧ MEM (f, n) ps.stalls)
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >>
  gvs[pf_tail_def, AllCaseEqs()] >>
  rename1 ‘pacts _ _ _ = SOME (rs, aevs, wa, pa)’ >>
  drule pacts_stalls >> strip_tac >>
  rename1 ‘pf_fetch _ _ _ (w2, pa with b := b2) = SOME ((w3, ps3'), log, gevs)’ >>
  drule pf_fetch_stalls >> drule pf_fetch_b >> rpt strip_tac >> gvs[]
  >- (drule stall_step_entry >> simp[])
  >- (drule stall_step_entry >> simp[] >> strip_tac >> simp[] >>
      simp[round_stalled_def, tail_stalled_def] >> metis_tac[])
  >> qpat_x_assum ‘MEM _ (round_drops _ _ _ _ _)’ mp_tac >>
  simp[round_drops_def, tail_drops_def] >> strip_tac >>
  drule stall_drops_entry >> strip_tac >> simp[] >>
  simp[round_stalled_def, tail_stalled_def] >> metis_tac[]
QED

(* Along the run, a stall count n for f means f's last n rounds stalled *)
Theorem run_stalls:
  run_ok lfd pol ifds m w0 ⇒
  ∀k f n. MEM (f, n) (rstate lfd pol ifds m w0 k).stalls ⇒
          n ≤ k ∧ ∀i. k − n ≤ i ∧ i < k ⇒ rstalled lfd pol ifds m w0 i f
Proof
  strip_tac >> Induct
  >- simp[rstate_def, prun_0, pinit_def] >>
  rpt gen_tac >> strip_tac >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
  drule pround_stalls >> strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >>
  ‘rstalled lfd pol ifds m w0 k f’ by simp[rstalled_def] >>
  TRY (rw[] >> ‘i = k’ by simp[] >> simp[] >> NO_TAC) >>
  first_x_assum drule >> strip_tac >> rw[] >>
  Cases_on ‘i = k’ >> simp[] >> first_x_assum irule >> simp[]
QED

(* A write-timeout drop of f in round k: an FReset of f in the round's
   fetch (a hard input error, D19 (a)), or rounds k + 1 − pf_sendwait to k
   all stalled (D23) *)
Theorem rdrop_cause:
  run_ok lfd pol ifds m w0 ∧ rdrop lfd pol ifds m w0 k f ⇒
  MEM (FReset f) (rlog lfd pol ifds m w0 k) ∨
  (pf_sendwait ≤ SUC k ∧
   ∀i. SUC k − pf_sendwait ≤ i ∧ i ≤ k ⇒ rstalled lfd pol ifds m w0 i f)
Proof
  strip_tac >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
  drule pround_stalls >> strip_tac >>
  qpat_x_assum ‘rdrop _ _ _ _ _ _ _’ mp_tac >> simp[rdrop_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >>
  drule_all run_stalls >> strip_tac >>
  disj2_tac >> conj_tac >- simp[] >>
  rpt strip_tac >> Cases_on ‘i = k’ >> gvs[rstalled_def] >>
  first_x_assum irule >> simp[]
QED

(* sys_send_res without the length hypothesis: D24 (the kernel's counts
   are below 2^64) makes the recorded count exact for any payload *)
Theorem sys_send_res_rely:
  sys_send g bs w = SOME (out, w', ev) ∧ winv w ∧ bs ≠ [] ⇒
  (∃k. l0_res_of out = Ok k ∧ 0 < k ∧ k ≤ LENGTH bs) ∨ (∃e x. l0_res_of out = Fail e x)
Proof
  rw[sys_send_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def] >> rw[AllCaseEqs()] >>
  pairarg_tac >> gvs[] >>
  ‘LENGTH (fd_bytes g) = 8’ by simp[] >>
  ‘TAKE 8 (fd_bytes g ++ bs) = fd_bytes g ∧ DROP 8 (fd_bytes g ++ bs) = bs’
    by metis_tac[TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND] >>
  gvs[] >>
  ‘l0_rely (l0_tick «sys_send» w)’
    by (gvs[winv_def] >> irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  ‘l0_res_ok r’
    by (qpat_x_assum ‘l0_send _ _ _ = _’ mp_tac >>
        simp[l0_send_def, not_chan_def] >> rw[AllCaseEqs()] >>
        TRY (irule fail_ok >> first_assum ACCEPT_TAC >> NO_TAC) >>
        simp[l0_res_ok_def, MIN_DEF] >> rw[] >> fs[l0_rely_def] >>
        irule LESS_EQ_LESS_TRANS >> goal_assum (first_assum o mp_then Any mp_tac) >>
        simp[]) >>
  simp[l0_res_of_enc] >>
  qpat_x_assum ‘l0_send _ _ _ = _’ mp_tac >>
  simp[l0_send_def, not_chan_def] >> rw[AllCaseEqs()] >> gvs[fail_def] >>
  simp[MIN_DEF] >> rw[] >> fs[] >> Cases_on ‘bs’ >> fs[]
QED

Theorem after_send_le:
  LENGTH (outbox_of (after_send g r b) f) ≤ LENGTH (outbox_of b f)
Proof
  rw[after_send_def] >> every_case_tac >>
  simp[outbox_of_set_outbox] >> rw[] >> simp[]
QED

Theorem l1_flush_le:
  ∀fs w b w' b' evs.
    l1_flush fs (w, b) = SOME ((w', b'), evs) ⇒
    LENGTH (outbox_of b' f) ≤ LENGTH (outbox_of b f)
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (first_x_assum drule >> simp[]) >>
  gvs[AllCaseEqs()] >> first_x_assum drule >> strip_tac >>
  irule LESS_EQ_TRANS >> goal_assum (first_assum o mp_then Any mp_tac) >>
  simp[after_send_le]
QED

(* A flush that leaves f's outbox not empty and no shorter: every send
   on f in it was retried (a non-retried one takes bytes or fails hard) *)
Theorem l1_flush_stalled:
  ∀fs w b w' b' evs.
    l1_flush fs (w, b) = SOME ((w', b'), evs) ∧ winv w ∧ outbox_of b' f ≠ [] ∧
    ¬(LENGTH (outbox_of b' f) < LENGTH (outbox_of b f)) ⇒
    ∀ev. MEM ev evs ∧ ev_on «sys_send» f ev ⇒ retried ev
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (first_x_assum (qspecl_then [‘w’, ‘b’, ‘w'’, ‘b'’, ‘evs’] mp_tac) >> simp[]) >>
  gvs[AllCaseEqs()] >>
  rename1 ‘sys_send h _ w = SOME (out, w1, ev1)’ >>
  ‘winv w1’ by metis_tac[sys_winv] >>
  drule l1_flush_le >> disch_then (qspec_then ‘f’ assume_tac) >>
  ‘LENGTH (outbox_of (after_send h (l0_res_of out) b) f) ≤ LENGTH (outbox_of b f)’
    by simp[after_send_le] >>
  ‘LENGTH (outbox_of (after_send h (l0_res_of out) b) f) = LENGTH (outbox_of b f)’
    by decide_tac >>
  rpt strip_tac >> gvs[]
  >- (‘h = f’ by (imp_res_tac ev_on_send >> fs[]) >> gvs[] >>
      drule_all retried_send >> strip_tac >> simp[] >>
      drule sys_send_res_rely >> simp[] >> strip_tac >> gvs[]
      >- (gvs[after_send_def, outbox_of_set_outbox] >>
          Cases_on ‘outbox_of b f’ >> gvs[])
      >> CCONTR_TAC >> gvs[after_send_def, outbox_of_set_outbox] >>
      Cases_on ‘outbox_of b f’ >> gvs[])
  >> first_x_assum irule >> simp[] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   A stalled round on the trace (for L3-00's ep_timed_out)
   ------------------------------------------------------------------------ *)

(* ev is a poll whose entries list f with output requested *)
Definition ev_polls_out_def:
  ev_polls_out f ev ⇔
    ∃conf bs e. ev = IO_event (ExtCall «sys_poll») conf bs ∧
                MEM (f, e) (MAP pe_fe (pollfd_entries (DROP 16 (MAP FST bs)))) ∧ 2 ≤ e
End

Theorem sys_poll_out_ev:
  sys_poll fes w = SOME (out, w', ev) ∧ winv w ∧ EVERY (λ(g, e). small g ∧ e < 4) fes ∧
  MEM (f, e) fes ∧ 2 ≤ e ⇒
  ev_polls_out f ev ∧ ev_name ev = ExtCall «sys_poll»
Proof
  simp[sys_poll_def] >> strip_tac >>
  ‘LENGTH out = LENGTH (poll_buf fes)’
    by (gvs[l0_do_buf_def, AllCaseEqs(), winv_def] >> drule_all l0_ffi_fn_length >> simp[]) >>
  drule l0_do_buf_cases >> strip_tac >> gvs[ev_name_def, ev_polls_out_def, MAP_ZIP] >>
  simp[poll_buf_def, DROP_APPEND, pollfd_entries_buf, MAP_MAP_o, MEM_MAP, PULL_EXISTS] >>
  qexists_tac ‘e’ >> qexists_tac ‘(f, e)’ >> simp[] >> gvs[EVERY_MEM] >>
  first_x_assum drule >> simp[pe_pfd_bytes]
QED

(* A stalled round's events: its one poll lists f for output; every send
   on f after it is retried; and if f had output pending at the round's
   start, no send on f comes before it either (a Write only queues) *)
Theorem round_stalled_events:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧ winv w ∧
  psmall lfd ps ∧ round_stalled lfd pol hs (w, ps) acts f ∧ f ≠ lfd ⇒
  ∃pre pev post.
    evs = pre ++ [pev] ++ post ∧ ev_polls_out f pev ∧
    EVERY (λe. ev_name e ≠ ExtCall «sys_poll») (pre ++ post) ∧
    (∀e. MEM e post ∧ ev_on «sys_send» f e ⇒ retried e) ∧
    (∀c. olive lfd f ps ∧ l0_chan_of w f = SOME c ⇒ ¬EXISTS (ev_on «sys_send» f) pre)
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >>
  gvs[pf_tail_def, AllCaseEqs(), round_stalled_def, tail_stalled_def] >>
  rename1 ‘pacts _ _ _ = SOME (rs, aevs, wa, pa)’ >>
  qpat_x_assum ‘l1_polls _ _ = SOME (rv, w1, pevs)’ mp_tac >>
  simp[l1_polls_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 ‘sys_poll _ wa = SOME (out, w1, pev)’ >>
  qexists_tac ‘aevs’ >> qexists_tac ‘pev’ >> qexists_tac ‘fevs ++ gevs ++ cevs’ >> simp[] >>
  ‘winv wa ∧ psmall lfd pa’ by metis_tac[pacts_winv, pacts_psmall] >>
  ‘winv w1’ by metis_tac[sys_winv] >>
  ‘outbox_of pa.b f ≠ []’
    by (strip_tac >> drule l1_flush_le >> disch_then (qspec_then ‘f’ mp_tac) >> gvs[]) >>
  drule_all pf_poll_set_out >> disch_then (qspecl_then [‘pol’, ‘hs’] strip_assume_tac) >>
  ‘EVERY (λ(g, e). small g ∧ e < 4) (pf_poll_set lfd pol pa hs)’
    by (irule pf_poll_set_small >> simp[]) >>
  drule_all sys_poll_out_ev >> strip_tac >> simp[] >>
  imp_res_tac pacts_names >> imp_res_tac l1_flush_names >> imp_res_tac pf_fetch_names >>
  imp_res_tac l1_reap_names >>
  conj_tac >- (gvs[EVERY_MEM] >> rw[] >> res_tac >> gvs[]) >>
  conj_tac
  >- (rw[] >> imp_res_tac ev_on_name >> gvs[EVERY_MEM] >> res_tac >> gvs[] >>
      drule_all l1_flush_stalled >> simp[]) >>
  rpt strip_tac >> drule_all pacts_live >> simp[EVERY_MEM, EXISTS_MEM] >> metis_tac[]
QED

(* A hard input error on the trace: the recv on f that failed *)
Definition hard_recv_def:
  hard_recv f evs ⇔ ∃ev. MEM ev evs ∧ ev_on «sys_recv» f ev ∧ ¬retried ev ∧ ev_failed ev
End

Theorem pf_fetch_freset:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ winv w ∧
    MEM (FReset f) log ⇒ hard_recv f evs
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[AllCaseEqs()] >>
  TRY (pairarg_tac >> gvs[AllCaseEqs()]) >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  ‘winv w1’ by (TRY (drule_all (cj 3 sys_winv) >> simp[] >> NO_TAC) >>
                drule_all (cj 4 sys_winv) >> simp[]) >>
  TRY (first_x_assum drule_all >> simp[hard_recv_def] >> metis_tac[MEM] >> NO_TAC) >>
  simp[hard_recv_def] >> qexists_tac ‘ev’ >> simp[] >>
  ‘l0_rely w’ by fs[winv_def] >>
  qpat_x_assum ‘sys_recv _ _ _ = _’ mp_tac >> simp[sys_recv_def] >> strip_tac >>
  drule_all ev_do >> strip_tac >> simp[] >>
  ‘LENGTH out = 13 + pf_chunk’
    by (gvs[l0_do_def, AllCaseEqs()] >> drule_all l0_ffi_fn_length >> simp[]) >>
  drule l0_do_cases >> strip_tac >> gvs[ev_failed_def, MAP_SND_ZIP_REPLICATE]
QED

Theorem pround_freset:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧ winv w ∧
  MEM (FReset f) log ⇒ hard_recv f evs
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >>
  gvs[pf_tail_def, AllCaseEqs()] >>
  ‘winv ws10’ by metis_tac[pacts_winv] >>
  ‘winv w1’ by metis_tac[l1_polls_winv] >>
  ‘winv w2’ by metis_tac[l1_flush_winv] >>
  drule_all pf_fetch_freset >> simp[hard_recv_def] >> metis_tac[]
QED

(* MAIN ((3a)/(3b) of flush_live, split by cause): a write-timeout drop
   of f in round k is a hard input error observed in round k (a recv on f
   that failed with an error L1 does not retry: the FReset of D19 (a)), or
   the D23 timeout: in each of the pf_sendwait rounds ending at k, the
   round's one poll lists f for output, every send on f after that poll
   is retried, and (when f had output pending at the round's start) no
   send on f comes before it *)
Theorem rdrop_split:
  oassm lfd pol ifds m w0 ∧ rdrop lfd pol ifds m w0 k f ∧ f ≠ lfd ⇒
  hard_recv f (rrev lfd pol ifds m w0 k) ∨
  (pf_sendwait ≤ SUC k ∧
   ∀i. SUC k − pf_sendwait ≤ i ∧ i ≤ k ⇒
       ∃pre pev post.
         rrev lfd pol ifds m w0 i = pre ++ [pev] ++ post ∧ ev_polls_out f pev ∧
         EVERY (λe. ev_name e ≠ ExtCall «sys_poll») (pre ++ post) ∧
         (∀e. MEM e post ∧ ev_on «sys_send» f e ⇒ retried e) ∧
         ∀c. olive lfd f (rstate lfd pol ifds m w0 i) ∧
             l0_chan_of (rworld lfd pol ifds m w0 i) f = SOME c ⇒
             ¬EXISTS (ev_on «sys_send» f) pre)
Proof
  strip_tac >> ‘run_ok lfd pol ifds m w0 ∧ winv w0’ by fs[oassm_def] >>
  drule_all rdrop_cause >> strip_tac
  >- (disj1_tac >>
      drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘k’] strip_assume_tac) >>
      ‘winv (rworld lfd pol ifds m w0 k)’ by metis_tac[winv_run] >>
      drule_all pround_freset >> simp[]) >>
  disj2_tac >> simp[] >> rpt strip_tac >>
  ‘rstalled lfd pol ifds m w0 i f’ by (first_x_assum irule >> simp[]) >>
  pop_assum (strip_assume_tac o REWRITE_RULE [rstalled_def]) >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘i’] strip_assume_tac) >>
  ‘winv (rworld lfd pol ifds m w0 i)’ by metis_tac[winv_run] >>
  ‘psmall lfd (rstate lfd pol ifds m w0 i)’ by metis_tac[psmall_run] >>
  drule_all round_stalled_events >> strip_tac >>
  qexistsl_tac [‘pre’, ‘pev’, ‘post’] >> fs[]
QED
