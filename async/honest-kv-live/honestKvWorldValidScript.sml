(*
  From the trace hypothesis peer_valid (honestKvL0LiveStmts, decision 3 (a))
  to the validity of what L1 fetched on f, which honestKvPeerValid's
  kv_S3w_conn asks for.  While f keeps its episode j and channel c, and c
  never freezes, what L1 fetched on f since its accept is a prefix of what
  c's peer sent (run_peer_sent: the flushed case breaks c), and every round
  boundary is a prefix of the trace (pftrace_revs, run_world_at), where
  peer_valid applies.

  MAIN: kv_fdata_valid.
*)
Theory honestKvWorldValid
Ancestors
  honestKvPeerValid honestKvL0LiveStmts honestEchoL0TraceWrap
  honestEchoL0TraceData honestEchoL0Excuse honestEchoL0Drains
  honestL1PFConnTrace honestL1BFaith honestKvReadSoonPF honestKvL0Obl
  honestL1PFInput honestL1PFStream honestL1PFLive honestL1PFOutLive honestL0World honestL1PFObl honestL1PFRound honestL1PFModel
  HttpSpecBodies HttpSpec
Libs
  preamble

Theorem revs_le[local]:
  run_ok lfd pol ifds m w0 ∧ a ≤ b ⇒
  revs lfd pol ifds m w0 a ≼ revs lfd pol ifds m w0 b
Proof
  strip_tac >> drule revs_prefix >> disch_then (qspecl_then [‘b − a’, ‘a’] mp_tac) >>
  ‘a + (b − a) = b’ by decide_tac >> simp[]
QED

(* honestEchoL0TraceWrap's chan_same / run_chan_same (local there) *)
Theorem chan_same[local]:
  faithful w0 (a ++ b) ∧ winv w0 ∧ qfresh w0 ∧
  world_at w0 a = SOME x ∧ world_at w0 (a ++ b) = SOME y ∧
  ALOOKUP (SND (l0_ep_st (0, []) a)) f = SOME j ∧
  ALOOKUP (SND (l0_ep_st (0, []) (a ++ b))) f = SOME j ∧
  l0_chan_of x f = SOME c ∧ l0_chan_of y f = SOME c' ⇒ c = c'
Proof
  strip_tac >>
  ‘¬EXISTS (ep_ends f) b’ by metis_tac[idx_stable] >>
  ‘EVERY (λe. ¬ep_ends f e) b’ by fs[EVERY_MEM, EXISTS_MEM] >>
  drule_all world_chan_back >> strip_tac >> gvs[]
QED

Theorem run_chan_same[local]:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ qfresh w0 ∧
  pftrace lfd pol ifds m w0 io ∧ LPREFIX (fromList evs) io ∧ world_at w0 evs = SOME w ∧
  ALOOKUP (SND (l0_ep_st (0, []) evs)) f = SOME j ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 k))) f = SOME j ∧
  l0_chan_of w f = SOME c ∧ l0_chan_of (rworld lfd pol ifds m w0 k) f = SOME ck ⇒
  ck = c
Proof
  strip_tac >>
  drule_all pftrace_locate >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  ‘revs lfd pol ifds m w0 k ≼ revs lfd pol ifds m w0 M’ by metis_tac[revs_le] >>
  ‘∀n. world_at w0 (revs lfd pol ifds m w0 n) = SOME (rworld lfd pol ifds m w0 n) ∧
       faithful w0 (revs lfd pol ifds m w0 n)’ by metis_tac[run_world_at] >>
  ‘evs ≼ revs lfd pol ifds m w0 k ∨ revs lfd pol ifds m w0 k ≼ evs’
    by metis_tac[prefixes_is_prefix_total] >>
  fs[IS_PREFIX_APPEND] >> metis_tac[chan_same, faithful_prefix]
QED

Theorem rlogs_zero[local]:
  rlogs lfd pol ifds m w0 a 0 = []
Proof
  simp[rlogs_def]
QED

(* MAIN: while f keeps episode j on channel c, and c never freezes, what L1
   fetched on f since its accept in round a is always a prefix of printed
   valid requests *)
Theorem kv_fdata_valid:
  kv_run lfdn pol w0 ∧ qfresh w0 ∧ qinb w0 ∧
  pftrace (n2w lfdn) pol KI KS w0 io ∧ peer_valid w0 io c ∧ ¬ch_frozen w0 io c ∧
  LPREFIX (fromList evs) io ∧ world_at w0 evs = SOME w ∧
  ALOOKUP (SND (l0_ep_st (0, []) evs)) f = SOME j ∧ l0_chan_of w f = SOME c ∧
  MEM (FConn f) (rlog (n2w lfdn) pol KI KS w0 a) ∧
  (∀k. a < k ⇒ ¬MEM (FConn f) (rlog (n2w lfdn) pol KI KS w0 k)) ∧
  (∀n. a < n ⇒
       ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol KI KS w0 n))) f = SOME j ∧
       l0_chan_of (rworld (n2w lfdn) pol KI KS w0 n) f ≠ NONE) ⇒
  ∀M. ∃rqs. EVERY valid_brequest rqs ∧
            fdata f (rlogs (n2w lfdn) pol KI KS w0 a M) ≼
            HttpSpec$bytes (FLAT (MAP print_brequest rqs))
Proof
  strip_tac >> gen_tac >>
  Cases_on ‘M = 0’
  >- (qexists_tac ‘[]’ >> simp[rlogs_zero, fdata_def]) >>
  ‘run_ok (n2w lfdn) pol KI KS w0 ∧ winv w0’ by fs[kv_run_def] >>
  ‘oassm (n2w lfdn) pol KI KS w0’ by fs[oassm_def, kv_run_def] >>
  qabbrev_tac ‘n = a + M’ >>
  ‘a < n ∧ n − a = M’ by simp[Abbr ‘n’] >>
  qpat_x_assum ‘∀n. a < n ⇒ _’ (qspec_then ‘n’ mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  Cases_on ‘l0_chan_of (rworld (n2w lfdn) pol KI KS w0 n) f’ >- fs[] >>
  rename1 ‘l0_chan_of _ f = SOME ck’ >>
  ‘ck = c’
    by (qspecl_then [‘n2w lfdn’, ‘pol’, ‘KI’, ‘KS’, ‘w0’, ‘io’, ‘evs’, ‘w’, ‘f’, ‘j’, ‘n’, ‘c’, ‘ck’] mp_tac
          (Q.GENL [‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘io’, ‘evs’, ‘w’, ‘f’, ‘j’, ‘k’, ‘c’, ‘ck’] run_chan_same) >>
        impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  qpat_x_assum ‘ck = c’ SUBST_ALL_TAC >>
  ‘c < LENGTH (rworld (n2w lfdn) pol KI KS w0 n).chans’
    by (qpat_x_assum ‘l0_chan_of (rworld _ _ _ _ _ n) f = _’ mp_tac >>
        rw[l0_chan_of_def, AllCaseEqs()] >> simp[]) >>
  ‘LPREFIX (fromList (revs (n2w lfdn) pol KI KS w0 n)) io’ by metis_tac[pftrace_revs] >>
  ‘world_at w0 (revs (n2w lfdn) pol KI KS w0 n) = SOME (rworld (n2w lfdn) pol KI KS w0 n)’
    by metis_tac[run_world_at] >>
  qspecl_then [‘n2w lfdn’, ‘pol’, ‘KI’, ‘KS’, ‘w0’, ‘f’, ‘a’, ‘n’, ‘c’] mp_tac
    (Q.GENL [‘lfd’, ‘pol’, ‘ifds’, ‘m’, ‘w0’, ‘f’, ‘a’, ‘n’, ‘c’] run_peer_sent) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> rpt strip_tac >>
      qpat_x_assum ‘∀k. a < k ⇒ ¬_’ (qspec_then ‘k’ mp_tac) >> simp[]) >>
  strip_tac
  >- (qpat_x_assum ‘peer_valid _ _ _’ mp_tac >> rewrite_tac[peer_valid_def] >>
      disch_then (qspecl_then [‘revs (n2w lfdn) pol KI KS w0 n’,
                               ‘rworld (n2w lfdn) pol KI KS w0 n’] mp_tac) >>
      impl_tac >- simp[] >> strip_tac >>
      qexists_tac ‘rqs’ >> simp[] >>
      irule IS_PREFIX_TRANS >>
      qexists_tac ‘(EL c (rworld (n2w lfdn) pol KI KS w0 n).chans).peer_sent’ >>
      conj_tac >- fs[brequests_def] >>
      qpat_x_assum ‘(EL c _).peer_sent = _’ SUBST1_TAC >> simp[]) >>
  qpat_x_assum ‘¬ch_frozen _ _ _’ mp_tac >> simp[ch_frozen_def] >>
  disch_then (qspecl_then [‘revs (n2w lfdn) pol KI KS w0 n’, ‘rworld (n2w lfdn) pol KI KS w0 n’] mp_tac) >>
  qpat_x_assum ‘flushed _ _’ mp_tac >> rewrite_tac[flushed_def] >> strip_tac >>
  qpat_x_assum ‘l0_chan_of _ f = SOME j'’ mp_tac >>
  qpat_x_assum ‘l0_chan_of (rworld _ _ _ _ _ n) f = SOME c’ (fn th => rewrite_tac[th]) >>
  strip_tac >> qpat_x_assum ‘SOME c = SOME j'’ (SUBST_ALL_TAC o SYM o REWRITE_RULE [optionTheory.SOME_11]) >> simp[]
QED
