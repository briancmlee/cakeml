(*
  The data chain of echo_live_l0 on the trace (design/47 D, trace
  assembly): for a prefix evs = revs r ++ pre inside round r, with f's
  episode j open and f on channel c in evs's world, everything the peer has
  sent on c by then reaches the kernel's sent on c, unless f's channel is
  flushed or episode j shows a hard error or a D23 timeout.

  Cases: episode j still open at round r + 1 (trace_open_data), or ended
  in the rest of round r (trace_end_data): then L1 cannot have held f
  without EOF at round r (pround_noend), so f was at EOF, closing, or
  released while open (zombie_data_out); and j started before round r,
  since an accept is the last end of its fd in its round (run_acc_after).

  MAIN: trace_data.
*)
Theory honestEchoL0TraceData
Ancestors
  honestEchoL0FlAt honestEchoL0AccOnce honestEchoL0DataAt honestEchoL0ChanId honestEchoL0RoundData honestEchoL0Acq
  honestEchoL0EofCase honestEchoL0Peer honestEchoL0Excuse honestEchoL0Chain
  honestEchoL0LiveOwn honestEchoL0Obl honestL1PFObl honestL1BFaith honestL1BStmts
  honestL1PFBroken honestL1PFLive honestL1PFOutLive honestL1PFOut honestL1PFRefine
  honestL1PFConnTrace honestL1PFFlush honestL0Part honestEchoL0KSent honestEchoL0Trace honestL1PFInv
Libs
  preamble


Theorem pfx_trans[local]:
  x ≼ y ∧ y ≼ z ⇒ x ≼ z
Proof
  rw[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]
QED

(* With no end of f's episode in b, a channel f has after a ++ b it had
   after a *)
Theorem world_chan_back:
  faithful w0 (a ++ b) ∧ winv w0 ∧ qfresh w0 ∧ world_at w0 (a ++ b) = SOME y ∧
  EVERY (λe. ¬ep_ends f e) b ∧ l0_chan_of y f = SOME c ⇒
  ∃x. world_at w0 a = SOME x ∧ l0_chan_of x f = SOME c
Proof
  strip_tac >> drule faithful_APPEND_inv >> simp[] >> strip_tac >>
  drule_all faithful_chan_back >> strip_tac >>
  qexists_tac ‘u’ >> fs[world_at_def, l0_replay_def, FOLDL_APPEND] >>
  first_x_assum irule >> gvs[]
QED

(* The last event of a list with P *)
Theorem last_occ:
  ∀l. EXISTS P l ⇒ ∃p1 e p2. l = p1 ++ [e] ++ p2 ∧ P e ∧ ¬EXISTS P p2
Proof
  ho_match_mp_tac SNOC_INDUCT >> simp[EXISTS_SNOC] >> rpt strip_tac
  >- (qexistsl_tac [‘l’, ‘x’, ‘[]’] >> simp[SNOC_APPEND]) >>
  Cases_on ‘P x’
  >- (qexistsl_tac [‘l’, ‘x’, ‘[]’] >> simp[SNOC_APPEND]) >>
  fs[] >> qexistsl_tac [‘p1’, ‘e’, ‘p2 ++ [x]’] >> simp[SNOC_APPEND]
QED

(* An episode open inside round r that ends later in the round started
   before the round *)
Theorem pre_no_end:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  rrev lfd pol ifds m w0 r = pre ++ post ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 r ++ pre))) f = SOME j ∧
  EXISTS (ep_ends f) post ⇒
  ¬EXISTS (ep_ends f) pre
Proof
  rpt strip_tac >>
  drule last_occ >> strip_tac >> gvs[] >>
  Cases_on ‘l0_event_accepted e = SOME f’
  >- ((* an accept: no end after it in the round *)
      ‘¬EXISTS (λe. l0_event_closed e = SOME f ∨ l0_event_accepted e = SOME f) (p2 ++ post)’
        by (irule run_acc_after >> simp[] >>
            qexistsl_tac [‘p1’, ‘e’, ‘r’, ‘ifds’, ‘lfd’, ‘m’, ‘pol’, ‘w0’] >> simp[]) >>
      RULE_ASSUM_TAC (REWRITE_RULE [EXISTS_ep_ends]) >>
      fs[EXISTS_MEM, EVERY_MEM] >> metis_tac[]) >>
  (* a close: f leaves the open map and does not come back in p2 *)
  ‘l0_event_closed e = SOME f ∧ l0_event_accepted e = NONE’
    by (fs[ep_ends_def] >> Cases_on ‘l0_event_accepted e’ >> fs[] >>
        imp_res_tac accepted_not_closed >> fs[]) >>
  qpat_x_assum ‘ALOOKUP _ _ = SOME j’ mp_tac >>
  REWRITE_TAC [GSYM APPEND_ASSOC, l0_ep_st_simps] >>
  ‘¬EXISTS (λe. l0_event_closed e = SOME f ∨ l0_event_accepted e = SOME f) p2’
    by (qpat_x_assum ‘EVERY _ p2’ mp_tac >> simp[EVERY_MEM, EXISTS_MEM, ep_ends_def]) >>
  drule ep_st_no_end >> simp[] >> disch_then kall_tac >>
  Cases_on ‘l0_ep_st (l0_ep_st (0, []) (revs lfd pol ifds m w0 r)) p1’ >>
  simp[l0_ep_step_def, ALOOKUP_ADELKEY]
QED

(* The round-level chain for an episode released while open: from the
   release round (before m + 1) on *)
Theorem zombie_data_out:
  echo_run lfdn pol w0 ∧ qfresh w0 ∧ qinb w0 ∧ pol_ok hw pol ∧ F1 (n2w lfdn) pol EI ES w0 ∧
  honestL1PFFlush$F2 w0 ∧ honestL1PFFlush$drains (n2w lfdn) pol EI ES w0 c ∧ nshut w0 ∧
  pftrace (n2w lfdn) pol EI ES w0 io ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 n))) f = SOME j ∧
  ¬MEM f (rstate (n2w lfdn) pol EI ES w0 n).acq ∧
  ¬MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 n).b.tbl) ∧
  ¬MEM f (rstate (n2w lfdn) pol EI ES w0 n).b.closing ∧
  n ≤ SUC m ∧ SUC m ≤ N ∧
  rrev (n2w lfdn) pol EI ES w0 m = pre ++ post ∧
  world_at w0 (revs (n2w lfdn) pol EI ES w0 m ++ pre) = SOME w ∧ l0_chan_of w f = SOME c ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 m ++ pre))) f = SOME j ⇒
  (∃n'. (EL c (rworld (n2w lfdn) pol EI ES w0 N).chans).peer_sent ≼
        csent (rworld (n2w lfdn) pol EI ES w0 n') c) ∨
  (∃k. fl_at (n2w lfdn) pol EI ES w0 f j k) ∨
  ep_hard_err j io ∨ ep_timed_out pf_sendwait j io
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  ‘run_ok (n2w lfdn) pol EI ES w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0) ∧
   (∀n. SND (pcm (n2w lfdn) pol EI ES w0 n) + 1 < dimword (:64))’ by fs[echo_run_def] >>
  ‘oassm (n2w lfdn) pol EI ES w0’ by fs[oassm_def, echo_run_def] >>
  ‘revs (n2w lfdn) pol EI ES w0 (SUC m) = revs (n2w lfdn) pol EI ES w0 m ++ pre ++ post’
    by (qpat_assum ‘run_ok _ _ _ _ _’ (fn th => mp_tac (Q.SPEC ‘m’ (MATCH_MP prun_round' th))) >>
        rpt strip_tac >> simp[]) >>
  ‘faithful w0 (revs (n2w lfdn) pol EI ES w0 m ++ pre ++ post)’
    by metis_tac[run_world_at] >>
  ‘faithful w0 (revs (n2w lfdn) pol EI ES w0 m ++ pre)’
    by metis_tac[faithful_prefix, APPEND_ASSOC] >>
  drule released_while_open >> simp[] >>
  disch_then (qspecl_then [‘n’, ‘f’, ‘j’] mp_tac) >> simp[] >> strip_tac >>
  ‘k ≤ m’ by simp[] >>
  ‘revs (n2w lfdn) pol EI ES w0 m =
   revs (n2w lfdn) pol EI ES w0 k ++ rrounds (n2w lfdn) pol EI ES w0 k (m − k)’
    by (drule revs_rrounds >> disch_then (qspecl_then [‘k’, ‘m − k’] mp_tac) >>
        ‘k + (m − k) = m’ by decide_tac >> simp[]) >>
  ‘¬EXISTS (ep_ends f) (rrounds (n2w lfdn) pol EI ES w0 k (m − k) ++ pre)’
    by (qspecl_then [‘revs (n2w lfdn) pol EI ES w0 k’, ‘f’, ‘j’,
                     ‘rrounds (n2w lfdn) pol EI ES w0 k (m − k) ++ pre’] mp_tac
          (Q.GENL [‘evs’, ‘f’, ‘j’, ‘mid’] idx_stable) >> gvs[]) >>
  ‘revs (n2w lfdn) pol EI ES w0 k ++ (rrounds (n2w lfdn) pol EI ES w0 k (m − k) ++ pre) =
   revs (n2w lfdn) pol EI ES w0 m ++ pre’ by fs[] >>
  ‘l0_chan_of (rworld (n2w lfdn) pol EI ES w0 k) f = SOME c’
    by (‘∃x. world_at w0 (revs (n2w lfdn) pol EI ES w0 k) = SOME x ∧ l0_chan_of x f = SOME c’
          by (irule world_chan_back >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
              qexistsl_tac [‘rrounds (n2w lfdn) pol EI ES w0 k (m − k) ++ pre’, ‘w’] >>
              asm_rewrite_tac [] >> fs[EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
        metis_tac[run_world_at, SOME_11]) >>
  irule eof_held_data_out >> simp[] >> qexists_tac ‘k’ >> simp[] >>
  Cases_on ‘MEM f (rstate (n2w lfdn) pol EI ES w0 k).b.closing’ >> simp[] >>
  fs[] >> CCONTR_TAC >> fs[] >>
  ‘MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 (SUC k)).b.tbl)’
    by (irule run_tbl_stay >> simp[]) >>
  fs[]
QED

(* MAIN (case): episode j is still open at round r + 1 *)
Theorem trace_open_data:
  echo_run lfdn pol w0 ∧ qfresh w0 ∧ qinb w0 ∧ pol_ok hw pol ∧ F1 (n2w lfdn) pol EI ES w0 ∧
  honestL1PFFlush$F2 w0 ∧ honestL1PFFlush$drains (n2w lfdn) pol EI ES w0 c ∧ nshut w0 ∧
  pftrace (n2w lfdn) pol EI ES w0 io ∧
  rrev (n2w lfdn) pol EI ES w0 r = pre ++ post ∧
  world_at w0 (revs (n2w lfdn) pol EI ES w0 r ++ pre) = SOME w ∧ l0_chan_of w f = SOME c ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 r ++ pre))) f = SOME j ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 (SUC r)))) f = SOME j ⇒
  (∃n'. (EL c w.chans).peer_sent ≼ csent (rworld (n2w lfdn) pol EI ES w0 n') c) ∨
  (∃k. fl_at (n2w lfdn) pol EI ES w0 f j k) ∨
  ep_hard_err j io ∨ ep_timed_out pf_sendwait j io
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  ‘run_ok (n2w lfdn) pol EI ES w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0) ∧
   (∀n. SND (pcm (n2w lfdn) pol EI ES w0 n) + 1 < dimword (:64))’ by fs[echo_run_def] >>
  ‘oassm (n2w lfdn) pol EI ES w0’ by fs[oassm_def, echo_run_def] >>
  ‘revs (n2w lfdn) pol EI ES w0 (SUC r) = revs (n2w lfdn) pol EI ES w0 r ++ pre ++ post’
    by (qpat_assum ‘run_ok _ _ _ _ _’ (fn th => mp_tac (Q.SPEC ‘r’ (MATCH_MP prun_round' th))) >>
        rpt strip_tac >> simp[]) >>
  ‘faithful w0 (revs (n2w lfdn) pol EI ES w0 r ++ pre ++ post) ∧
   world_at w0 (revs (n2w lfdn) pol EI ES w0 r ++ pre ++ post) =
     SOME (rworld (n2w lfdn) pol EI ES w0 (SUC r))’
    by metis_tac[run_world_at] >>
  ‘¬EXISTS (ep_ends f) post’
    by (qspecl_then [‘revs (n2w lfdn) pol EI ES w0 r ++ pre’, ‘f’, ‘j’, ‘post’] mp_tac
          (Q.GENL [‘evs’, ‘f’, ‘j’, ‘mid’] idx_stable) >> gvs[]) >>
  ‘c < LENGTH w.chans’ by metis_tac[chan_lt] >>
  ‘(EL c w.chans).peer_sent ≼
   (EL c (rworld (n2w lfdn) pol EI ES w0 (SUC r)).chans).peer_sent’
    by (‘psmono c w (rworld (n2w lfdn) pol EI ES w0 (SUC r))’
          by (irule world_at_psmono >>
              qexistsl_tac [‘revs (n2w lfdn) pol EI ES w0 r ++ pre’, ‘post’, ‘w0’] >> simp[]) >>
        fs[psmono_def]) >>
  (* the data chain from some round N ≥ r + 1, for peer_sent at r + 1 *)
  ‘(∃n'. (EL c (rworld (n2w lfdn) pol EI ES w0 (SUC r)).chans).peer_sent ≼
         csent (rworld (n2w lfdn) pol EI ES w0 n') c) ∨
   (∃k. fl_at (n2w lfdn) pol EI ES w0 f j k) ∨
   ep_hard_err j io ∨ ep_timed_out pf_sendwait j io’
    suffices_by (strip_tac >> TRY (metis_tac[] >> NO_TAC) >>
                 disj1_tac >> qexists_tac ‘n'’ >> irule pfx_trans >>
                 qexists_tac ‘(EL c (rworld (n2w lfdn) pol EI ES w0 (SUC r)).chans).peer_sent’ >>
                 fs[]) >>
  Cases_on ‘MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 (SUC r)).b.tbl) ∨
            MEM f (rstate (n2w lfdn) pol EI ES w0 (SUC r)).b.closing ∨
            MEM f (rstate (n2w lfdn) pol EI ES w0 (SUC r)).acq’
  >- ((* L1 knows f at r + 1: its channel there is c *)
      ‘∃c1. l0_chan_of (rworld (n2w lfdn) pol EI ES w0 (SUC r)) f = SOME c1’
        by (irule run_held_chan >> metis_tac[]) >>
      ‘c1 = c’
        by (‘∃x. world_at w0 (revs (n2w lfdn) pol EI ES w0 r ++ pre) = SOME x ∧
                 l0_chan_of x f = SOME c1’
              by (irule world_chan_back >> simp[] >>
                  qexistsl_tac [‘post’, ‘rworld (n2w lfdn) pol EI ES w0 (SUC r)’] >>
                  fs[EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
            gvs[]) >>
      rveq >> irule known_data_out >> simp[] >> metis_tac[]) >>
  (* released while open *)
  fs[] >> irule zombie_data_out >> simp[] >>
  conj_tac >- (qexistsl_tac [‘r’, ‘SUC r’, ‘post’, ‘pre’, ‘w’] >> simp[]) >>
  metis_tac[]
QED

(* The case: episode j ends in the rest of round r *)
Theorem trace_end_data:
  echo_run lfdn pol w0 ∧ qfresh w0 ∧ qinb w0 ∧ pol_ok hw pol ∧ F1 (n2w lfdn) pol EI ES w0 ∧
  honestL1PFFlush$F2 w0 ∧ honestL1PFFlush$drains (n2w lfdn) pol EI ES w0 c ∧ nshut w0 ∧
  pftrace (n2w lfdn) pol EI ES w0 io ∧
  rrev (n2w lfdn) pol EI ES w0 r = pre ++ post ∧
  world_at w0 (revs (n2w lfdn) pol EI ES w0 r ++ pre) = SOME w ∧ l0_chan_of w f = SOME c ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 r ++ pre))) f = SOME j ∧
  EXISTS (ep_ends f) post ⇒
  (∃n'. (EL c w.chans).peer_sent ≼ csent (rworld (n2w lfdn) pol EI ES w0 n') c) ∨
  (∃k. fl_at (n2w lfdn) pol EI ES w0 f j k) ∨
  ep_hard_err j io ∨ ep_timed_out pf_sendwait j io
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  ‘run_ok (n2w lfdn) pol EI ES w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0) ∧
   (∀n. SND (pcm (n2w lfdn) pol EI ES w0 n) + 1 < dimword (:64))’ by fs[echo_run_def] >>
  ‘revs (n2w lfdn) pol EI ES w0 (SUC r) = revs (n2w lfdn) pol EI ES w0 r ++ pre ++ post’
    by (qpat_assum ‘run_ok _ _ _ _ _’ (fn th => mp_tac (Q.SPEC ‘r’ (MATCH_MP prun_round' th))) >>
        rpt strip_tac >> simp[]) >>
  ‘faithful w0 (revs (n2w lfdn) pol EI ES w0 r ++ pre ++ post) ∧
   world_at w0 (revs (n2w lfdn) pol EI ES w0 r ++ pre ++ post) =
     SOME (rworld (n2w lfdn) pol EI ES w0 (SUC r))’
    by metis_tac[run_world_at] >>
  ‘faithful w0 (revs (n2w lfdn) pol EI ES w0 r ++ pre)’
    by metis_tac[faithful_prefix, APPEND_ASSOC] >>
  ‘c < LENGTH w.chans’ by metis_tac[chan_lt] >>
  ‘(EL c w.chans).peer_sent ≼
   (EL c (rworld (n2w lfdn) pol EI ES w0 (SUC r)).chans).peer_sent’
    by (‘psmono c w (rworld (n2w lfdn) pol EI ES w0 (SUC r))’
          by (irule world_at_psmono >>
              qexistsl_tac [‘revs (n2w lfdn) pol EI ES w0 r ++ pre’, ‘post’, ‘w0’] >> simp[]) >>
        fs[psmono_def]) >>
  ‘(∃n'. (EL c (rworld (n2w lfdn) pol EI ES w0 (SUC r)).chans).peer_sent ≼
         csent (rworld (n2w lfdn) pol EI ES w0 n') c) ∨
   (∃k. fl_at (n2w lfdn) pol EI ES w0 f j k) ∨
   ep_hard_err j io ∨ ep_timed_out pf_sendwait j io’
    suffices_by (strip_tac >> TRY (metis_tac[] >> NO_TAC) >>
                 disj1_tac >> qexists_tac ‘n'’ >> irule pfx_trans >>
                 qexists_tac ‘(EL c (rworld (n2w lfdn) pol EI ES w0 (SUC r)).chans).peer_sent’ >>
                 fs[]) >>
  (* j was open at round r's start, on channel c *)
  ‘¬EXISTS (ep_ends f) pre’
    by metis_tac[pre_no_end] >>
  ‘ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 r))) f = SOME j’
    by (qpat_x_assum ‘ALOOKUP (SND (l0_ep_st _ (_ ++ pre))) _ = _’ mp_tac >>
        REWRITE_TAC [l0_ep_st_simps] >>
        ‘¬EXISTS (λe. l0_event_closed e = SOME f ∨ l0_event_accepted e = SOME f) pre’
          by (qpat_x_assum ‘¬EXISTS _ pre’ mp_tac >> REWRITE_TAC [EXISTS_ep_ends]) >>
        drule ep_st_no_end >> simp[]) >>
  ‘l0_chan_of (rworld (n2w lfdn) pol EI ES w0 r) f = SOME c’
    by (‘∃x. world_at w0 (revs (n2w lfdn) pol EI ES w0 r) = SOME x ∧ l0_chan_of x f = SOME c’
          by (irule world_chan_back >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
              qexistsl_tac [‘pre’, ‘w’] >> asm_rewrite_tac [] >>
              fs[EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
        metis_tac[run_world_at, SOME_11]) >>
  (* L1 did not hold f without EOF at round r *)
  ‘¬keep f (rstate (n2w lfdn) pol EI ES w0 r)’
    by (strip_tac >> drule_all run_keep_noend >> strip_tac >> metis_tac[EXISTS_APPEND]) >>
  ‘pown (n2w lfdn) (rstate (n2w lfdn) pol EI ES w0 r)’
    by metis_tac[run_pown, echo_run_hyp] >>
  Cases_on ‘MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 r).b.tbl) ∧
            MEM f (rstate (n2w lfdn) pol EI ES w0 r).eof ∨
            MEM f (rstate (n2w lfdn) pol EI ES w0 r).b.closing’
  >- (irule eof_held_data_out >> simp[] >> qexists_tac ‘r’ >> simp[]) >>
  ‘¬MEM f (rstate (n2w lfdn) pol EI ES w0 r).acq ∧
   ¬MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 r).b.tbl)’
    by (gvs[keep_def, pown_def] >> metis_tac[]) >>
  fs[] >> irule zombie_data_out >> simp[] >>
  conj_tac >- (qexistsl_tac [‘r’, ‘r’, ‘post’, ‘pre’, ‘w’] >> simp[]) >>
  metis_tac[]
QED

(* MAIN: the data chain at any prefix inside a round with episode j open
   and f on channel c *)
Theorem trace_data:
  echo_run lfdn pol w0 ∧ qfresh w0 ∧ qinb w0 ∧ pol_ok hw pol ∧ F1 (n2w lfdn) pol EI ES w0 ∧
  honestL1PFFlush$F2 w0 ∧ honestL1PFFlush$drains (n2w lfdn) pol EI ES w0 c ∧ nshut w0 ∧
  pftrace (n2w lfdn) pol EI ES w0 io ∧
  rrev (n2w lfdn) pol EI ES w0 r = pre ++ post ∧
  world_at w0 (revs (n2w lfdn) pol EI ES w0 r ++ pre) = SOME w ∧ l0_chan_of w f = SOME c ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 r ++ pre))) f = SOME j ⇒
  (∃n'. (EL c w.chans).peer_sent ≼ csent (rworld (n2w lfdn) pol EI ES w0 n') c) ∨
  (∃k. fl_at (n2w lfdn) pol EI ES w0 f j k) ∨
  ep_hard_err j io ∨ ep_timed_out pf_sendwait j io
Proof
  strip_tac >>
  ‘run_ok (n2w lfdn) pol EI ES w0’ by fs[echo_run_def] >>
  ‘revs (n2w lfdn) pol EI ES w0 (SUC r) = revs (n2w lfdn) pol EI ES w0 r ++ pre ++ post’
    by (qpat_assum ‘run_ok _ _ _ _ _’ (fn th => mp_tac (Q.SPEC ‘r’ (MATCH_MP prun_round' th))) >>
        rpt strip_tac >> simp[]) >>
  Cases_on ‘EXISTS (ep_ends f) post’
  >- (irule trace_end_data >> simp[] >>
      conj_tac >- (qexistsl_tac [‘post’, ‘pre’, ‘r’] >> fs[]) >>
      metis_tac[]) >>
  irule trace_open_data >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  qexistsl_tac [‘post’, ‘pre’, ‘r’] >> simp[] >>
  ‘¬EXISTS (λe. l0_event_closed e = SOME f ∨ l0_event_accepted e = SOME f) post’
    by (qpat_x_assum ‘¬EXISTS _ post’ mp_tac >> REWRITE_TAC [EXISTS_ep_ends]) >>
  drule ep_st_no_end >> fs[]
QED
