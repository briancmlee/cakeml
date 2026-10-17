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
  honestL1PFConnRun honestL1PFLive honestL1PFRound honestL1PFRefine honestL1PFInv
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
