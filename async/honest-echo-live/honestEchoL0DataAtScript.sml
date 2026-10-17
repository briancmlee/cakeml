(*
  The round-level data chain of echo_live_l0 from any round at which f's
  episode j0 is open with f on channel c (design/47 D, trace assembly):
  L1 holds f (held_data_out); f is pending (handed to the server later,
  same episode and channel: run_acq_taken, acq_ep_keep, run_chan_same); or
  L1 has released f while the episode is open after an interrupted close
  (released_while_open) -- L1 releases only after EOF, so the data is final.

  MAIN: known_data_out.
*)
Theory honestEchoL0DataAt
Ancestors
  honestEchoL0ChanId honestEchoL0RoundData honestEchoL0Acq honestEchoL0EofCase
  honestEchoL0Peer honestEchoL0Excuse honestEchoL0DataIn honestEchoL0LiveOwn
  honestEchoL0Inv honestEchoL0Obl honestL1PFObl honestL1PFBroken honestL1PFInput
  honestL1PFStream honestL1PFLive honestL1PFRound honestL1PFOutLive honestL1PFOut
  honestL1PFRefine honestL1PFConnTrace honestL1PFFlush
Libs
  preamble


Theorem run_psmono2[local]:
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

Theorem pfx_trans[local]:
  x ≼ y ∧ y ≼ z ⇒ x ≼ z
Proof
  rw[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]
QED

(* At EOF in the table, or closing: the data chain for any later round *)
Theorem eof_held_data_out:
  echo_run lfdn pol w0 ∧ qfresh w0 ∧ qinb w0 ∧ F1 (n2w lfdn) pol EI ES w0 ∧
  honestL1PFFlush$F2 w0 ∧ honestL1PFFlush$drains (n2w lfdn) pol EI ES w0 c ∧ nshut w0 ∧
  pftrace (n2w lfdn) pol EI ES w0 io ∧
  (MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 k).b.tbl) ∧
   MEM f (rstate (n2w lfdn) pol EI ES w0 k).eof ∨
   MEM f (rstate (n2w lfdn) pol EI ES w0 k).b.closing) ∧
  l0_chan_of (rworld (n2w lfdn) pol EI ES w0 k) f = SOME c ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 k))) f = SOME j0 ∧ k ≤ N ⇒
  (∃n'. (EL c (rworld (n2w lfdn) pol EI ES w0 N).chans).peer_sent ≼
        csent (rworld (n2w lfdn) pol EI ES w0 n') c) ∨
  (∃k'. fl_at (n2w lfdn) pol EI ES w0 f j0 k') ∨
  ep_hard_err j0 io ∨ ep_timed_out pf_sendwait j0 io
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  ‘oassm (n2w lfdn) pol EI ES w0’ by fs[oassm_def, echo_run_def] >>
  ‘run_ok (n2w lfdn) pol EI ES w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0) ∧
   (∀n. SND (pcm (n2w lfdn) pol EI ES w0 n) + 1 < dimword (:64))’ by fs[echo_run_def] >>
  ‘∀i. (MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 i).b.tbl) ∨
        MEM f (rstate (n2w lfdn) pol EI ES w0 i).b.closing) ⇒
       ∃a. a < i ∧ MEM (FConn f) (rlog (n2w lfdn) pol EI ES w0 a) ∧
           ∀k. a < k ∧ k < i ⇒ ¬MEM (FConn f) (rlog (n2w lfdn) pol EI ES w0 k)’
    by (rpt strip_tac >>
        qpat_assum ‘run_ok _ _ _ _ _’ (fn th => irule (MATCH_MP last_conn th)) >>
        drule run_rel >> disch_then (qspec_then ‘i’ strip_assume_tac) >>
        drule held_acct >> disch_then drule >> disch_then drule >>
        disch_then (qspec_then ‘f’ mp_tac) >> simp[]) >>
  (* the round k0 ≤ k with f at EOF in the table, same channel and episode *)
  ‘∃k0. k0 ≤ k ∧ MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 k0).b.tbl) ∧
        MEM f (rstate (n2w lfdn) pol EI ES w0 k0).eof ∧
        l0_chan_of (rworld (n2w lfdn) pol EI ES w0 k0) f = SOME c ∧
        ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 k0))) f = SOME j0’
    by (qpat_x_assum ‘_ ∧ _ ∨ _’ strip_assume_tac
        >- (qexists_tac ‘k’ >> simp[]) >>
        drule run_closing_origin >> disch_then drule >> strip_tac >>
        rename1 ‘k0 < k’ >> qexists_tac ‘k0’ >> simp[] >>
        ‘∀i. k0 ≤ i ∧ i ≤ k ⇒
             MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 i).b.tbl) ∨
             MEM f (rstate (n2w lfdn) pol EI ES w0 i).b.closing’
          by (rpt strip_tac >> Cases_on ‘i = k0’ >> gvs[]) >>
        ‘∃c1. l0_chan_of (rworld (n2w lfdn) pol EI ES w0 k0) f = SOME c1’
          by (irule run_held_chan >> simp[]) >>
        ‘c1 = c’
          by (drule held_chan_stretch >> disch_then drule >>
              disch_then (qspec_then ‘k − k0’ mp_tac) >>
              impl_tac >- (rpt strip_tac >> first_x_assum irule >> simp[]) >>
              ‘k0 + (k − k0) = k’ by simp[] >> simp[]) >>
        rveq >> simp[] >>
        ‘∃j1. ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 k0))) f = SOME j1’
          by (irule run_known_ep >> simp[]) >>
        ‘ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 k))) f = SOME j1’
          by (irule keep_to_round >> simp[] >> qexists_tac ‘k0’ >> simp[] >>
              rpt strip_tac >> first_x_assum irule >> simp[]) >>
        fs[]) >>
  qpat_x_assum ‘∀i. _ ⇒ ∃a. _’ (qspec_then ‘k0’ mp_tac) >> impl_tac >- simp[] >>
  strip_tac >>
  ‘k0 ≤ N’ by simp[] >>
  drule_all eof_data_out >> strip_tac >> simp[] >> metis_tac[]
QED

(* MAIN: the data chain from any round at which f's episode j0 is open
   with f on channel c *)
Theorem known_data_out:
  echo_run lfdn pol w0 ∧ qfresh w0 ∧ qinb w0 ∧ pol_ok hw pol ∧ F1 (n2w lfdn) pol EI ES w0 ∧
  honestL1PFFlush$F2 w0 ∧ honestL1PFFlush$drains (n2w lfdn) pol EI ES w0 c ∧ nshut w0 ∧
  pftrace (n2w lfdn) pol EI ES w0 io ∧
  l0_chan_of (rworld (n2w lfdn) pol EI ES w0 n) f = SOME c ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 n))) f = SOME j0 ⇒
  (∃n'. (EL c (rworld (n2w lfdn) pol EI ES w0 n).chans).peer_sent ≼
        csent (rworld (n2w lfdn) pol EI ES w0 n') c) ∨
  (∃k. fl_at (n2w lfdn) pol EI ES w0 f j0 k) ∨
  ep_hard_err j0 io ∨ ep_timed_out pf_sendwait j0 io
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  ‘run_ok (n2w lfdn) pol EI ES w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0) ∧
   (∀n. SND (pcm (n2w lfdn) pol EI ES w0 n) + 1 < dimword (:64))’ by fs[echo_run_def] >>
  ‘oassm (n2w lfdn) pol EI ES w0’ by fs[oassm_def, echo_run_def] >>
  Cases_on ‘MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 n).b.tbl) ∨
            MEM f (rstate (n2w lfdn) pol EI ES w0 n).b.closing’
  >- (irule held_data_out >> simp[] >> metis_tac[]) >>
  fs[] >>
  Cases_on ‘MEM f (rstate (n2w lfdn) pol EI ES w0 n).acq’
  >- ((* pending: handed to the server at n', same episode and channel *)
      drule_all run_acq_taken >> strip_tac >>
      ‘ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 n'))) f = SOME j0’
        by (‘n' − n + n = n'’ by decide_tac >>
            qpat_assum ‘run_ok _ _ _ _ _’ assume_tac >> drule acq_ep_keep >> simp[] >>
            disch_then (qspecl_then [‘f’, ‘n' − n’, ‘n’] mp_tac) >> simp[]) >>
      ‘∃c1. l0_chan_of (rworld (n2w lfdn) pol EI ES w0 n') f = SOME c1’
        by (irule run_held_chan >> simp[]) >>
      ‘c1 = c’
        by (‘l0_chan_of (rworld (n2w lfdn) pol EI ES w0 n) f = SOME c1’
              by (irule run_chan_same >> simp[] >> qexists_tac ‘n'’ >> simp[]) >>
            fs[]) >>
      rveq >>
      ‘(∃n''. (EL c (rworld (n2w lfdn) pol EI ES w0 n').chans).peer_sent ≼
              csent (rworld (n2w lfdn) pol EI ES w0 n'') c) ∨
       (∃k. fl_at (n2w lfdn) pol EI ES w0 f j0 k) ∨
       ep_hard_err j0 io ∨ ep_timed_out pf_sendwait j0 io’
        by (irule held_data_out >> simp[] >> metis_tac[]) >>
      TRY (disj2_tac >> fs[] >> metis_tac[] >> NO_TAC) >>
      disj1_tac >> qexists_tac ‘n''’ >> irule pfx_trans >>
      qexists_tac ‘(EL c (rworld (n2w lfdn) pol EI ES w0 n').chans).peer_sent’ >> simp[] >>
      ‘n ≤ n'’ by simp[] >> drule_all run_psmono2 >>
      disch_then (qspec_then ‘c’ mp_tac) >> simp[psmono_def] >>
      impl_tac >- metis_tac[chan_lt] >> simp[]) >>
  (* released while open: L1 released f at round k, after EOF *)
  drule released_while_open >> simp[] >>
  disch_then (qspecl_then [‘n’, ‘f’, ‘j0’] mp_tac) >> simp[] >> strip_tac >>
  ‘l0_chan_of (rworld (n2w lfdn) pol EI ES w0 k) f = SOME c’
    by (irule run_chan_same >> simp[] >> qexists_tac ‘n’ >> simp[]) >>
  ‘k ≤ n’ by simp[] >>
  irule eof_held_data_out >> simp[] >> qexists_tac ‘k’ >> simp[] >>
  Cases_on ‘MEM f (rstate (n2w lfdn) pol EI ES w0 k).b.closing’ >> simp[] >>
  fs[] >> CCONTR_TAC >> fs[] >>
  ‘MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 (SUC k)).b.tbl)’
    by (irule run_tbl_stay >> simp[]) >>
  fs[]
QED
