(*
  The data chain of echo_live_l0 on the trace (design/47 D, trace
  assembly): for a prefix evs = revs r ++ pre inside round r, with f's
  episode j open and f on channel c in evs's world, everything the peer has
  sent on c by then reaches the kernel's sent on c, unless f's channel is
  flushed or episode j shows a hard error or a D23 timeout.

  This file: the case where episode j is still open at round r + 1
  (trace_open_data).
*)
Theory honestEchoL0TraceData
Ancestors
  honestEchoL0DataAt honestEchoL0ChanId honestEchoL0RoundData honestEchoL0Acq
  honestEchoL0EofCase honestEchoL0Peer honestEchoL0Excuse honestEchoL0Chain
  honestEchoL0LiveOwn honestEchoL0Obl honestL1PFObl honestL1BFaith honestL1BStmts
  honestL1PFBroken honestL1PFLive honestL1PFOutLive honestL1PFOut honestL1PFRefine
  honestL1PFConnTrace honestL1PFFlush honestL0Part honestEchoL0KSent
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
  (∃k. flushed (rworld (n2w lfdn) pol EI ES w0 k) f) ∨
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
   (∃k. flushed (rworld (n2w lfdn) pol EI ES w0 k) f) ∨
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
  (* released while open: the release round k ≤ r *)
  fs[] >>
  drule released_while_open >> simp[] >>
  disch_then (qspecl_then [‘SUC r’, ‘f’, ‘j’] mp_tac) >> simp[] >> strip_tac >>
  ‘k ≤ r’ by simp[] >>
  ‘revs (n2w lfdn) pol EI ES w0 r =
   revs (n2w lfdn) pol EI ES w0 k ++ rrounds (n2w lfdn) pol EI ES w0 k (r − k)’
    by (drule revs_rrounds >> disch_then (qspecl_then [‘k’, ‘r − k’] mp_tac) >>
        ‘k + (r − k) = r’ by decide_tac >> simp[]) >>
  ‘¬EXISTS (ep_ends f) (rrounds (n2w lfdn) pol EI ES w0 k (r − k) ++ pre)’
    by (qspecl_then [‘revs (n2w lfdn) pol EI ES w0 k’, ‘f’, ‘j’,
                     ‘rrounds (n2w lfdn) pol EI ES w0 k (r − k) ++ pre’] mp_tac
          (Q.GENL [‘evs’, ‘f’, ‘j’, ‘mid’] idx_stable) >> gvs[]) >>
  ‘revs (n2w lfdn) pol EI ES w0 k ++ (rrounds (n2w lfdn) pol EI ES w0 k (r − k) ++ pre) =
   revs (n2w lfdn) pol EI ES w0 r ++ pre’ by fs[] >>
  ‘faithful w0 (revs (n2w lfdn) pol EI ES w0 r ++ pre)’
    by metis_tac[faithful_prefix, APPEND_ASSOC] >>
  ‘l0_chan_of (rworld (n2w lfdn) pol EI ES w0 k) f = SOME c’
    by (‘∃x. world_at w0 (revs (n2w lfdn) pol EI ES w0 k) = SOME x ∧ l0_chan_of x f = SOME c’
          by (irule world_chan_back >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
              qexistsl_tac [‘rrounds (n2w lfdn) pol EI ES w0 k (r − k) ++ pre’, ‘w’] >>
              asm_rewrite_tac [] >> fs[EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
        metis_tac[run_world_at, SOME_11]) >>
  irule eof_held_data_out >> simp[] >> qexists_tac ‘k’ >> simp[] >>
  Cases_on ‘MEM f (rstate (n2w lfdn) pol EI ES w0 k).b.closing’ >> simp[] >>
  fs[] >> CCONTR_TAC >> fs[] >>
  ‘MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 (SUC k)).b.tbl)’
    by (irule run_tbl_stay >> simp[]) >>
  fs[]
QED
