(*
  The data chain when L1 has seen f's end-of-file (design/47 D, trace
  assembly, EOF case): the round k that put f at end-of-file fetched FEof
  f -- then the peer's data on f's channel is final and is what L1 fetched
  since f's connect (eof_final), which reaches the kernel (fetched_out) --
  or FReset f, a hard recv error of f's episode.

  The peer's data is final then, so the conclusion is about peer_sent at
  any later round N.

  MAIN: eof_data_out.
*)
Theory honestEchoL0EofCase
Ancestors
  honestEchoL0FlAt honestEchoL0EofOrigin honestEchoL0Eof honestEchoL0Peer honestEchoL0DataOut
  honestEchoL0DataIn honestEchoL0OutAny honestEchoL0Excuse honestEchoL0LiveOwn
  honestEchoL0Inv honestEchoL0Obl honestL1PFObl
  honestL1PFBroken honestL1PFInput honestL1PFStream honestL1PFClient honestL1PFFlush
  honestL1PFOutLive honestL1PFOut honestL1PFLive honestL1PFRefine honestL1PFConnTrace
Libs
  preamble


(* An fd L1 holds or has pending has a channel *)
Theorem run_held_chan:
  oassm lfd pol ifds m w0 ∧
  (MEM f (MAP SND (rstate lfd pol ifds m w0 k).b.tbl) ∨
   MEM f (rstate lfd pol ifds m w0 k).b.closing ∨ MEM f (rstate lfd pol ifds m w0 k).acq) ⇒
  ∃c. l0_chan_of (rworld lfd pol ifds m w0 k) f = SOME c
Proof
  strip_tac >> drule run_rel >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  drule held_acct >> disch_then drule >> disch_then drule >>
  disch_then (qspec_then ‘f’ mp_tac) >> impl_tac >- simp[] >>
  rw[acct_def] >> metis_tac[]
QED

(* An fd L1 holds in its table or has pending is in an open episode *)
Theorem run_known_ep:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  (MEM f (MAP SND (rstate lfd pol ifds m w0 k).b.tbl) ∨ MEM f (rstate lfd pol ifds m w0 k).acq) ⇒
  ∃j. ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 k))) f = SOME j
Proof
  strip_tac >> drule_all run_own >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  Cases_on ‘l0_ep_st (0, []) (revs lfd pol ifds m w0 k)’ >>
  fs[own_ok_def, MEM_MAP, EXISTS_PROD]
  >- (res_tac >> metis_tac[]) >>
  fs[MEM_EL] >> res_tac >> metis_tac[]
QED

Theorem run_psmono[local]:
  run_ok lfd pol ifds m w0 ∧ a ≤ b ⇒
  psmono c (rworld lfd pol ifds m w0 a) (rworld lfd pol ifds m w0 b)
Proof
  strip_tac >>
  ‘revs lfd pol ifds m w0 a ≼ revs lfd pol ifds m w0 (a + (b − a))’
    by (drule revs_prefix >> disch_then (qspecl_then [‘b − a’, ‘a’] ACCEPT_TAC)) >>
  ‘a + (b − a) = b’ by decide_tac >> fs[IS_PREFIX_APPEND] >>
  irule world_at_psmono >> qexistsl_tac [‘revs lfd pol ifds m w0 a’, ‘l’, ‘w0’] >>
  metis_tac[run_world_at]
QED

(* MAIN: the data chain from a round at which L1 has seen f's EOF *)
Theorem eof_data_out:
  echo_run lfdn pol w0 ∧ qfresh w0 ∧ qinb w0 ∧ F1 (n2w lfdn) pol EI ES w0 ∧
  honestL1PFFlush$F2 w0 ∧ honestL1PFFlush$drains (n2w lfdn) pol EI ES w0 c ∧ nshut w0 ∧
  pftrace (n2w lfdn) pol EI ES w0 io ∧
  MEM (FConn f) (rlog (n2w lfdn) pol EI ES w0 a) ∧
  (∀i. a < i ∧ i < n ⇒ ¬MEM (FConn f) (rlog (n2w lfdn) pol EI ES w0 i)) ∧ a < n ∧
  MEM f (rstate (n2w lfdn) pol EI ES w0 n).eof ∧
  l0_chan_of (rworld (n2w lfdn) pol EI ES w0 n) f = SOME c ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 n))) f = SOME j0 ∧ n ≤ N ⇒
  (∃n'. (EL c (rworld (n2w lfdn) pol EI ES w0 N).chans).peer_sent ≼
        csent (rworld (n2w lfdn) pol EI ES w0 n') c) ∨
  (∃k. k ≤ n ∧ fl_at (n2w lfdn) pol EI ES w0 f j0 k ∧
       l0_chan_of (rworld (n2w lfdn) pol EI ES w0 k) f = SOME c) ∨
  ep_hard_err j0 io ∨ ep_timed_out pf_sendwait j0 io
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  ‘oassm (n2w lfdn) pol EI ES w0’ by fs[oassm_def, echo_run_def] >>
  ‘run_ok (n2w lfdn) pol EI ES w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0) ∧
   (∀n. SND (pcm (n2w lfdn) pol EI ES w0 n) + 1 < dimword (:64))’ by fs[echo_run_def] >>
  ‘∀i. pown (n2w lfdn) (rstate (n2w lfdn) pol EI ES w0 i)’
    by metis_tac[run_pown, echo_run_hyp] >>
  qpat_assum ‘run_ok _ _ _ _ _’ (fn th => mp_tac (MATCH_MP run_eof_origin th)) >>
  disch_then (qspec_then ‘n’ mp_tac) >> impl_tac >- simp[] >>
  disch_then (qx_choose_then ‘k’ (fn th => MAP_EVERY assume_tac (CONJUNCTS th))) >>
  ‘∀i. k < i ∧ i ≤ n ⇒ MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 i).b.tbl)’
    by (rpt strip_tac >>
        ‘MEM f (rstate (n2w lfdn) pol EI ES w0 i).eof’ by fs[] >>
        qpat_x_assum ‘∀i. pown _ _’ (qspec_then ‘i’ mp_tac) >> simp[pown_def] >>
        strip_tac >> qpat_x_assum ‘∀f. inb_of _ f ≠ [] ∨ _ ⇒ _’ irule >> simp[]) >>
  ‘f ≠ n2w lfdn’
    by (‘MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 n).b.tbl)’
          by (qpat_x_assum ‘∀i. k < i ∧ i ≤ n ⇒ MEM f (MAP SND _)’ irule >> simp[]) >>
        qpat_x_assum ‘∀i. pown _ _’ (qspec_then ‘n’ mp_tac) >> simp[pown_def] >>
        rpt strip_tac >> gvs[]) >>
  ‘∃j1. ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 k))) f = SOME j1’
    by (irule run_known_ep >> simp[] >> irule run_fetched_known >> fs[]) >>
  ‘ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 n))) f = SOME j1’
    by (irule keep_to_round >> simp[] >> qexists_tac ‘k’ >> simp[] >> rpt strip_tac >>
        qpat_x_assum ‘∀i. k < i ∧ i ≤ n ⇒ MEM f (MAP SND _)’ (qspec_then ‘i’ mp_tac) >>
        simp[]) >>
  ‘j1 = j0’ by fs[] >> rveq >>
  qpat_x_assum ‘ALOOKUP (SND (l0_ep_st _ (revs _ _ _ _ _ n))) f = _’ kall_tac >>
  qpat_x_assum ‘MEM (FEof f) _ ∨ _’ strip_assume_tac
  >- ((* FEof f in round k *)
      ‘¬MEM f (rstate (n2w lfdn) pol EI ES w0 k).b.closing’
        by (irule run_feof_not_closing >> fs[]) >>
      ‘∃c1. l0_chan_of (rworld (n2w lfdn) pol EI ES w0 (SUC k)) f = SOME c1’
        by (irule run_held_chan >> simp[] >> disj1_tac >>
            qpat_x_assum ‘∀i. k < i ∧ i ≤ n ⇒ MEM f (MAP SND _)’ irule >> simp[]) >>
      ‘∀i. SUC k ≤ i ∧ i ≤ n ⇒ l0_chan_of (rworld (n2w lfdn) pol EI ES w0 i) f = SOME c1’
        by (rpt strip_tac >>
            qpat_assum ‘l0_chan_of (rworld _ _ _ _ _ (SUC k)) f = SOME c1’ assume_tac >>
            drule held_chan_stretch >> disch_then drule >>
            disch_then (qspec_then ‘i − SUC k’ mp_tac) >>
            impl_tac
            >- (rpt strip_tac >> disj1_tac >>
                qpat_x_assum ‘∀i. k < i ∧ i ≤ n ⇒ MEM f (MAP SND _)’ irule >> simp[]) >>
            ‘SUC k + (i − SUC k) = i’ by decide_tac >> simp[]) >>
      ‘c1 = c’ by (first_x_assum (qspec_then ‘n’ mp_tac) >> simp[]) >> rveq >>
      ‘a ≤ k’
        by (CCONTR_TAC >>
            ‘¬MEM (FConn f) (rlog (n2w lfdn) pol EI ES w0 a)’ suffices_by fs[] >>
            irule run_noconn >> rpt conj_tac
            >- (qexists_tac ‘c’ >> conj_tac >>
                qpat_x_assum ‘∀i. SUC k ≤ i ∧ i ≤ n ⇒ l0_chan_of _ _ = _’ irule >>
                decide_tac)
            >- (simp[] >> disj1_tac >>
                qpat_x_assum ‘∀i. k < i ∧ i ≤ n ⇒ MEM f (MAP SND _)’ irule >> decide_tac) >>
            first_assum ACCEPT_TAC) >>
      ‘∃j. l0_chan_of (rworld (n2w lfdn) pol EI ES w0 (SUC k)) f = SOME j ∧
           ((EL j (rworld (n2w lfdn) pol EI ES w0 (SUC k)).chans).peer_eof ∧
            (EL j (rworld (n2w lfdn) pol EI ES w0 (SUC k)).chans).peer_sent =
              fdata f (rlogs (n2w lfdn) pol EI ES w0 a (SUC k − a)) ∨
            flushed (rworld (n2w lfdn) pol EI ES w0 (SUC k)) f)’
        by (irule eof_final >> simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
            rpt strip_tac >> qpat_x_assum ‘∀i. a < i ∧ i < n ⇒ _’ irule >> simp[]) >>
      ‘j = c’ by fs[] >> rveq >>
      ‘ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 (SUC k)))) f = SOME j0’
        by (irule keep_to_round >> simp[] >> qexists_tac ‘k’ >> simp[] >> rpt strip_tac >>
            ‘i = SUC k’ by decide_tac >>
            qpat_x_assum ‘∀i. k < i ∧ i ≤ n ⇒ MEM f (MAP SND _)’ (qspec_then ‘i’ mp_tac) >>
            simp[]) >>
      ‘MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 (SUC k)).b.tbl)’
        by (qpat_x_assum ‘∀i. k < i ∧ i ≤ n ⇒ MEM f (MAP SND _)’ irule >> decide_tac) >>
      TRY (disj2_tac >> disj1_tac >> qexists_tac ‘SUC k’ >>
           simp[fl_at_def, owned_def] >> fs[] >> NO_TAC) >>
      ((* the peer's data is final at SUC k *)
          ‘(EL c (rworld (n2w lfdn) pol EI ES w0 N).chans).peer_sent =
           (EL c (rworld (n2w lfdn) pol EI ES w0 (SUC k)).chans).peer_sent’
            by (‘SUC k ≤ N’ by decide_tac >>
                drule_all run_psmono >> disch_then (qspec_then ‘c’ mp_tac) >>
                simp[psmono_def] >> impl_tac >- metis_tac[chan_lt] >> simp[]) >>
          ‘∃n'. (EL c (rworld (n2w lfdn) pol EI ES w0 N).chans).peer_sent ≼
                  csent (rworld (n2w lfdn) pol EI ES w0 n') c ∨
                ep_hard_err j0 io ∨ ep_timed_out pf_sendwait j0 io’
            by (irule fetched_out >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
                qexistsl_tac [‘SUC k − a’, ‘a’, ‘f’, ‘SUC k’] >>
                rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY decide_tac >>
                TRY (rpt strip_tac >> qpat_x_assum ‘∀i. a < i ∧ i < n ⇒ _’ irule >>
                     decide_tac) >>
                TRY (‘a + (SUC k − a) = SUC k’ by decide_tac >> fs[] >> NO_TAC) >>
                simp[] >> disj1_tac >>
                qpat_x_assum ‘∀i. k < i ∧ i ≤ n ⇒ MEM f (MAP SND _)’ irule >> decide_tac) >>
          TRY (disj1_tac >> qexists_tac ‘n'’ >> first_assum ACCEPT_TAC >> NO_TAC) >>
          fs[])) >>
  (* FReset f in round k: a hard recv error *)
  disj2_tac >> disj2_tac >> disj1_tac >>
  ‘hard_recv f (rrev (n2w lfdn) pol EI ES w0 k)’
    by (drule prun_round' >> disch_then (qspecl_then [‘f’, ‘k’] strip_assume_tac) >>
        drule pround_freset >> disch_then irule >> simp[] >>
        drule_all winv_run >> simp[]) >>
  drule recv_excuse_j0 >> disch_then drule >> disch_then drule >>
  disch_then (qspec_then ‘k’ mp_tac) >> simp[]
QED
