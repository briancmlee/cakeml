(*
  Run-level flush progress for E1 on R3 (close-v2, shared E1 progress
  layer): over a run's rounds (each one eround), from a round n where f's
  output is live on its channel c (eflive, channel up and not connecting,
  not shut), with drains, F2 at round n and the trace's F1 fairness, a
  send on f goes through, or f's outbox empties, or c breaks.

  flush_lift_from: e1FlushLift's flush_lift with F2 asked of round n's
  world only (the per-round cflow keeps ch from there on while f is live),
  since a round need not keep ch once f's output is gone.

  MAIN: eround_lift.
*)
Theory e1RoundLift
Ancestors
  e1RoundFlush e1FairRounds e1FlushLift honestL1EPModel honestL1PFFlush
  honestL1PFOut honestL0World
Libs
  preamble

(* flush_lift, F2 at round n only *)
Theorem flush_lift_from:
  ∀(wn : num -> l0world) L P Pok Sd Sdok D c n.
    (∀k. n ≤ k ∧ L k ∧ ¬Sdok k ∧ ¬D k ∧ ¬(EL c (wn (SUC k)).chans).broken ⇒
         L (SUC k) ∧ cflow (wn k) (wn (SUC k)) c ∧ csent (wn (SUC k)) c = csent (wn k) c ∧
         P k ∧
         (Pok k ∧ ¬(EL c (wn k).chans).shut ∧ (EL c (wn k).chans).inflight = 0 ∧
          (∀hh. 0 < (wn k).ch.takes c hh 0 1) ⇒ Sd k)) ∧
    L n ∧ ¬(EL c (wn n).chans).shut ∧
    (∀m. (∀k. m ≤ k ⇒ csent (wn k) c = csent (wn m) c) ⇒
         ∃m'. m ≤ m' ∧ (EL c (wn m').chans).inflight = 0) ∧
    honestL1PFFlush$F2 (wn n) ∧
    rfair P Pok ∧ rfair Sd Sdok ⇒
    ∃k. n ≤ k ∧ (Sdok k ∨ D k ∨ (EL c (wn (SUC k)).chans).broken)
Proof
  rpt gen_tac >> strip_tac >> CCONTR_TAC >>
  qpat_x_assum ‘¬∃k. _’ (strip_assume_tac o SIMP_RULE bool_ss [NOT_EXISTS_THM, DE_MORGAN_THM]) >>
  ‘∀k. n ≤ k ⇒ ¬Sdok k ∧ ¬D k ∧ ¬(EL c (wn (SUC k)).chans).broken’
    by (gen_tac >> strip_tac >> first_x_assum (qspec_then ‘k’ mp_tac) >> simp[]) >>
  ‘∀d. L (n + d) ∧ (wn (n + d)).ch = (wn n).ch’
    by (Induct >- simp[] >>
        ‘n ≤ n + d’ by decide_tac >>
        qpat_x_assum ‘∀k. n ≤ k ⇒ ¬Sdok k ∧ _’ (drule_then strip_assume_tac) >>
        qpat_x_assum ‘∀k. n ≤ k ∧ L k ∧ _ ⇒ _’ (qspec_then ‘n + d’ mp_tac) >>
        impl_tac >- simp[] >> strip_tac >>
        gvs[ADD_CLAUSES, cflow_def]) >>
  qspecl_then [‘λk. wn (MAX n k)’, ‘L’, ‘P’, ‘Pok’, ‘Sd’, ‘Sdok’, ‘D’, ‘wn n’, ‘c’, ‘n’]
    mp_tac flush_lift >>
  impl_tac
  >- (rpt conj_tac
      >- (gen_tac >> strip_tac >>
          ‘MAX n k = k ∧ MAX n (SUC k) = SUC k’ by simp[MAX_DEF] >>
          qpat_x_assum ‘∀k. n ≤ k ∧ L k ∧ _ ⇒ _’ (qspec_then ‘k’ mp_tac) >> simp[])
      >- simp[]
      >- simp[]
      >- (gen_tac >> strip_tac >>
          qpat_x_assum ‘∀m. (∀k. m ≤ k ⇒ _) ⇒ _’ (qspec_then ‘MAX n m’ mp_tac) >>
          impl_tac
          >- (gen_tac >> strip_tac >>
              qpat_x_assum ‘∀k. m ≤ k ⇒ _’ (qspec_then ‘k’ mp_tac) >>
              ‘m ≤ k ∧ MAX n k = k’ by gvs[MAX_DEF] >> simp[]) >>
          strip_tac >> qexists_tac ‘m'’ >>
          ‘MAX n m' = m' ∧ m ≤ m'’ by gvs[MAX_DEF] >> simp[])
      >- first_assum ACCEPT_TAC
      >- (gen_tac >> simp[] >>
          ‘∃d. MAX n k = n + d’ by (qexists_tac ‘MAX n k − n’ >> simp[MAX_DEF]) >>
          pop_assum SUBST1_TAC >> simp[])
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC) >>
  strip_tac >>
  ‘MAX n (SUC k) = SUC k’ by simp[MAX_DEF] >>
  qpat_x_assum ‘∀k. n ≤ k ⇒ ¬Sdok k ∧ _’ (qspec_then ‘k’ mp_tac) >> gvs[]
QED

(* MAIN *)
Theorem eround_lift:
  ∀(ws : num -> l0world # l1e) r lfd f c n pre.
    (∀k. ∃pol hs acts snap log.
           eround lfd pol hs (ws k) acts = SOME (snap, ws (SUC k), log, r k)) ∧
    ewinv (FST (ws n)) ∧ nc c (FST (ws n)) ∧ esmall lfd (SND (ws n)) ∧
    eflive lfd f (SND (ws n)) ∧ l0_chan_of (FST (ws n)) f = SOME c ∧
    ¬(EL c (FST (ws n)).chans).shut ∧
    (∀m. (∀k. m ≤ k ⇒ csent (FST (ws k)) c = csent (FST (ws m)) c) ⇒
         ∃m'. m ≤ m' ∧ (EL c (FST (ws m')).chans).inflight = 0) ∧
    honestL1PFFlush$F2 (FST (ws n)) ∧ F1_io (rio pre r) ⇒
    ∃k. n ≤ k ∧
        ((∃ev. MEM ev (r k) ∧ ev_on «sys_send» f ev ∧ ¬retried ev) ∨
         outbox_of (SND (ws (SUC k))).p.b f = [] ∨
         (EL c (FST (ws (SUC k))).chans).broken)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [‘λk. FST (ws k)’,
               ‘λk. ewinv (FST (ws k)) ∧ nc c (FST (ws k)) ∧ esmall lfd (SND (ws k)) ∧
                    eflive lfd f (SND (ws k)) ∧ l0_chan_of (FST (ws k)) f = SOME c’,
               ‘λk. ∃ev. MEM ev (r k) ∧ ev_on «sys_poll» f ev’,
               ‘λk. ∃ev. MEM ev (r k) ∧ ev_on «sys_poll» f ev ∧ ¬retried ev’,
               ‘λk. ∃ev. MEM ev (r k) ∧ ev_on «sys_send» f ev’,
               ‘λk. ∃ev. MEM ev (r k) ∧ ev_on «sys_send» f ev ∧ ¬retried ev’,
               ‘λk. outbox_of (SND (ws (SUC k))).p.b f = []’, ‘c’, ‘n’]
    mp_tac flush_lift_from >>
  impl_tac
  >- (rpt conj_tac
      >- (gen_tac >> BETA_TAC >> strip_tac >>
          qpat_x_assum ‘∀k. ∃pol. _’ (qspec_then ‘k’ strip_assume_tac) >>
          Cases_on ‘ws k’ >> Cases_on ‘ws (SUC k)’ >> gvs[] >>
          drule_all eround_flush >> strip_tac >> gvs[]
          >> FIRST [
               qpat_x_assum ‘∀ev. ¬MEM ev (r k) ∨ _’ (qspec_then ‘ev’ mp_tac) >> simp[] >> NO_TAC,
               rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
               >- (qpat_x_assum ‘EXISTS _ (r k)’ mp_tac >> simp[EXISTS_MEM])
               >> strip_tac >>
               qpat_x_assum ‘∀ev. MEM ev _ ∧ _ ⇒ _’ (qspec_then ‘ev’ mp_tac) >>
               simp[EXISTS_MEM]])
      >- (BETA_TAC >> rpt conj_tac >> first_assum ACCEPT_TAC)
      >- simp[]
      >- simp[]
      >- simp[]
      >- (irule F1_io_rfair >> qexists_tac ‘pre’ >> first_assum ACCEPT_TAC)
      >- (irule F1_io_rfair >> qexists_tac ‘pre’ >> first_assum ACCEPT_TAC)) >>
  simp[]
QED
