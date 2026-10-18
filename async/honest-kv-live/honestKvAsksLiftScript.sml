(*
  K-asks on the PF KV trace (kv_live_l0's K-asks clause, at the PF run):
  if episode j on f (channel c) is open on the trace, c's peer sends only
  valid requests, and neither c freezes, nor episode j ends, nor a hard
  error hits it, then KV asks on f infinitely often.

  Otherwise L1 keeps f from some round t on (kv_held_forever) and the
  rounds stop asking on f from some round M0 on (run_asks_tail), so f is
  quiet from MAX M0 t (its handle stays live by S1); what L1 fetched on f
  is a prefix of c's peer data (run_peer_sent), so of valid requests
  (peer_valid), so f's inbox empties (kv_S3f), which kv_asks_pf rules out.

  MAIN: kv_asks_trace.
*)
Theory honestKvAsksLift
Ancestors
  honestKvAsksEp honestKvAsksTrace honestKvAsksPF honestKvL0AsksRun honestKvL0LiveStmts
  honestKvL0Obl honestEchoL0EofCase honestEchoL0Excuse honestEchoL0Spec honestL1BStmts
  honestL1PFInput honestL1PFStream honestL1PFOut honestL1PFOutLive honestL1PFConnTrace
  honestL1PFLive honestL1PFRound honestL1PFModel HttpSpecBodies
Libs
  preamble

(* An fd L1 holds or has pending at a round where episode j (open on the
   trace, on f) is accepted, is in episode j there *)
Theorem kv_ep_at:
  kv_run lfdn pol w0 ∧ pftrace (n2w lfdn) pol KI KS w0 io ∧
  LPREFIX (fromList evs) io ∧ ep_open j evs ∧ ¬ep_ended j io ∧ EL j (l0_accepted evs) = f ∧
  (MEM f (MAP SND (rstate (n2w lfdn) pol KI KS w0 n).b.tbl) ∨
   MEM f (rstate (n2w lfdn) pol KI KS w0 n).acq) ∧
  j < LENGTH (l0_accepted (revs (n2w lfdn) pol KI KS w0 n)) ⇒
  ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol KI KS w0 n))) f = SOME j
Proof
  strip_tac >>
  ‘run_ok (n2w lfdn) pol KI KS w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0)’
    by fs[kv_run_def] >>
  ‘∃j1. ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol KI KS w0 n))) f = SOME j1’
    by (irule run_known_ep >> simp[]) >>
  ‘j1 = j’
    by (drule ep_state_open >> strip_tac >>
        ‘ep_open j (revs (n2w lfdn) pol KI KS w0 n) ∧
         EL j (l0_accepted (revs (n2w lfdn) pol KI KS w0 n)) = EL j (l0_accepted evs)’
          by (qspecl_then [‘evs’, ‘io’, ‘j’] mp_tac (Q.GENL [‘evs’, ‘io’, ‘j’] ep_open_all) >>
              impl_tac >- simp[] >>
              disch_then irule >> simp[] >> irule pftrace_revs >> simp[]) >>
        irule ep_open_unique >> qexists_tac ‘revs (n2w lfdn) pol KI KS w0 n’ >> simp[]) >>
  fs[]
QED

(* What L1 fetched on f since its connect is a prefix of valid requests,
   if c's peer sends only valid requests and c does not freeze *)
Theorem kv_fdata_valid:
  kv_run lfdn pol w0 ∧ qfresh w0 ∧ qinb w0 ∧ pftrace (n2w lfdn) pol KI KS w0 io ∧
  LPREFIX (fromList evs) io ∧ ep_open j evs ∧ ¬ep_ended j io ∧
  EL j (l0_accepted evs) = f ∧ world_at w0 evs = SOME w ∧ l0_chan_of w f = SOME c ∧
  ¬ch_frozen w0 io c ∧ peer_valid w0 io c ∧
  MEM (FConn f) (rlog (n2w lfdn) pol KI KS w0 a) ∧
  (∀k. a < k ⇒ ¬MEM (FConn f) (rlog (n2w lfdn) pol KI KS w0 k)) ∧
  (∀k. a < k ⇒ j < LENGTH (l0_accepted (revs (n2w lfdn) pol KI KS w0 k))) ∧
  (∀k. a < k ⇒ MEM f (MAP SND (rstate (n2w lfdn) pol KI KS w0 k).b.tbl) ∨
               MEM f (rstate (n2w lfdn) pol KI KS w0 k).acq) ⇒
  ∀M. ∃rqs. EVERY valid_brequest rqs ∧
            fdata f (rlogs (n2w lfdn) pol KI KS w0 a M) ≼
            HttpSpec$bytes (FLAT (MAP print_brequest rqs))
Proof
  strip_tac >> gen_tac >>
  ‘run_ok (n2w lfdn) pol KI KS w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0)’
    by fs[kv_run_def] >>
  ‘oassm (n2w lfdn) pol KI KS w0’ by fs[oassm_def, kv_run_def] >>
  Cases_on ‘M’ >- (qexists_tac ‘[]’ >> simp[rlogs_def, fdata_def]) >>
  rename1 ‘SUC d’ >> qabbrev_tac ‘n = a + SUC d’ >>
  ‘a < n ∧ n − a = SUC d’ by simp[Abbr ‘n’] >>
  ‘∃c1. l0_chan_of (rworld (n2w lfdn) pol KI KS w0 n) f = SOME c1’
    by (irule honestEchoL0EofCaseTheory.run_held_chan >>
        qpat_assum ‘∀k. a < k ⇒ MEM f _ ∨ _’ (qspec_then ‘n’ mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >> disch_then strip_assume_tac >> asm_rewrite_tac[]) >>
  ‘ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol KI KS w0 n))) f = SOME j’
    by (qspecl_then [‘evs’, ‘f’, ‘io’, ‘j’, ‘lfdn’, ‘n’, ‘pol’, ‘w0’] mp_tac
          (Q.GENL [‘evs’, ‘f’, ‘io’, ‘j’, ‘lfdn’, ‘n’, ‘pol’, ‘w0’] kv_ep_at) >>
        impl_tac
        >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
            FIRST [qpat_assum ‘∀k. a < k ⇒ MEM f _ ∨ _’ (qspec_then ‘n’ mp_tac) >>
                   impl_tac >- first_assum ACCEPT_TAC >> disch_then ACCEPT_TAC,
                   qpat_assum ‘∀k. a < k ⇒ j < _’ (qspec_then ‘n’ mp_tac) >>
                   impl_tac >- first_assum ACCEPT_TAC >> disch_then ACCEPT_TAC]) >>
        disch_then ACCEPT_TAC) >>
  ‘ALOOKUP (SND (l0_ep_st (0, []) evs)) f = SOME j’
    by (irule ep_open_state >> simp[]) >>
  ‘c1 = c’
    by (qspecl_then [‘c’, ‘c1’, ‘evs’, ‘f’, ‘KI’, ‘io’, ‘j’, ‘n’, ‘n2w lfdn’, ‘KS’,
                     ‘pol’, ‘w’, ‘w0’] mp_tac
          (Q.GENL [‘c’, ‘ck’, ‘evs’, ‘f’, ‘ifds’, ‘io’, ‘j’, ‘k’, ‘lfd’, ‘m’, ‘pol’, ‘w’,
                   ‘w0’] run_chan_same_ev) >>
        simp[]) >>
  qpat_x_assum ‘c1 = c’ SUBST_ALL_TAC >>
  ‘LPREFIX (fromList (revs (n2w lfdn) pol KI KS w0 n)) io’ by (irule pftrace_revs >> simp[]) >>
  ‘world_at w0 (revs (n2w lfdn) pol KI KS w0 n) = SOME (rworld (n2w lfdn) pol KI KS w0 n)’
    by (drule run_world_at >> simp[]) >>
  ‘c < LENGTH (rworld (n2w lfdn) pol KI KS w0 n).chans’ by metis_tac[chan_lt] >>
  qspecl_then [‘a’, ‘c’, ‘f’, ‘KI’, ‘n2w lfdn’, ‘KS’, ‘n’, ‘pol’, ‘w0’] mp_tac
    (Q.GENL [‘a’, ‘c’, ‘f’, ‘ifds’, ‘lfd’, ‘m’, ‘n’, ‘pol’, ‘w0’] run_peer_sent) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt strip_tac >> qpat_x_assum ‘∀k. a < k ⇒ ¬MEM (FConn f) _’ (qspec_then ‘k’ mp_tac) >>
      simp[]) >>
  strip_tac
  >- (qpat_x_assum ‘peer_valid _ _ _’ (mp_tac o REWRITE_RULE [peer_valid_def]) >>
      disch_then (qspecl_then [‘revs (n2w lfdn) pol KI KS w0 n’,
                               ‘rworld (n2w lfdn) pol KI KS w0 n’] mp_tac) >>
      simp[] >> strip_tac >> qexists_tac ‘rqs’ >> fs[brequests_def] >>
      irule IS_PREFIX_TRANS >>
      qexists_tac ‘(EL c (rworld (n2w lfdn) pol KI KS w0 n).chans).peer_sent’ >>
      simp[] >> qpat_x_assum ‘_ = _ ++ _’ SUBST1_TAC >> simp[]) >>
  (* c is broken: frozen *)
  ‘ch_frozen w0 io c’
    by (rewrite_tac[ch_frozen_def] >>
        qexistsl_tac [‘revs (n2w lfdn) pol KI KS w0 n’, ‘rworld (n2w lfdn) pol KI KS w0 n’] >>
        qpat_x_assum ‘flushed _ _’ mp_tac >> simp[flushed_def] >> strip_tac >> gvs[]) >>
  qpat_x_assum ‘¬ch_frozen _ _ _’ mp_tac >> simp[]
QED

(* MAIN: K-asks on the PF KV trace *)
Theorem kv_asks_trace:
  kv_run lfdn (pol_self hw) w0 ∧ qfresh w0 ∧ qinb w0 ∧
  pftrace (n2w lfdn) (pol_self hw) KI KS w0 io ∧
  LPREFIX (fromList evs) io ∧ ep_open j evs ∧ world_at w0 evs = SOME w ∧
  EL j (l0_accepted evs) = f ∧ l0_chan_of w f = SOME c ∧ peer_valid w0 io c ⇒
  ep_hard_err j io ∨ ch_frozen w0 io c ∨ ep_ended j io ∨ asks_io_on f io
Proof
  rpt strip_tac >> CCONTR_TAC >>
  qpat_x_assum ‘¬(_ ∨ _)’ (strip_assume_tac o REWRITE_RULE [DE_MORGAN_THM]) >>
  ‘run_ok (n2w lfdn) (pol_self hw) KI KS w0’ by fs[kv_run_def] >>
  ‘oassm (n2w lfdn) (pol_self hw) KI KS w0’ by fs[oassm_def, kv_run_def] >>
  qspecl_then [‘c’, ‘evs’, ‘f’, ‘io’, ‘j’, ‘lfdn’, ‘pol_self hw’, ‘w’, ‘w0’] mp_tac
    (Q.GENL [‘c’, ‘evs’, ‘f’, ‘io’, ‘j’, ‘lfdn’, ‘pol’, ‘w’, ‘w0’] kv_held_forever) >>
  impl_tac >- simp[] >> strip_tac >>
  (* the rounds stop asking on f *)
  qspecl_then [‘f’, ‘KI’, ‘io’, ‘n2w lfdn’, ‘KS’, ‘pol_self hw’, ‘w0’] mp_tac
    (Q.GENL [‘f’, ‘ifds’, ‘io’, ‘lfd’, ‘m’, ‘pol’, ‘w0’] run_asks_tail) >>
  impl_tac >- simp[] >> strip_tac >> rename1 ‘M0 ≤ _ ⇒ _’ >>
  ‘∀k. M0 ≤ k ⇒ ¬fetched_at (n2w lfdn) (pol_self hw) KI KS w0 k f ∧
                ¬asked_at (n2w lfdn) (pol_self hw) KI KS w0 k f’
    by (rpt strip_tac >>
        qpat_x_assum ‘∀k. M0 ≤ k ⇒ ¬EXISTS _ _’ (qspec_then ‘k’ mp_tac) >> simp[]
        >- (drule_all run_fetched_asks >> simp[]) >>
        drule run_asked_asks >> simp[]) >>
  (* f's inbox empties once f is no longer fetched *)
  ‘∀M. ∃rqs. EVERY valid_brequest rqs ∧
             fdata f (rlogs (n2w lfdn) (pol_self hw) KI KS w0 a M) ≼
             HttpSpec$bytes (FLAT (MAP print_brequest rqs))’
    by (irule kv_fdata_valid >> simp[] >>
        qexistsl_tac [‘c’, ‘evs’, ‘io’, ‘j’, ‘w’] >> simp[] >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qspecl_then [‘a’, ‘f’, ‘lfdn’, ‘pol_self hw’, ‘w0’] mp_tac
    (Q.GENL [‘a’, ‘f’, ‘lfdn’, ‘pol’, ‘w0’] kv_S3f) >>
  impl_tac >- simp[] >> strip_tac >>
  (* f is quiet from some N ≥ M0, t *)
  ‘∃N. M0 ≤ N ∧ t ≤ N’ by (qexists_tac ‘M0 + t’ >> simp[]) >>
  pop_assum strip_assume_tac >>
  qpat_assum ‘kv_run _ _ _’
    (strip_assume_tac o REWRITE_RULE [honestL1PFLiveTheory.S1_def] o MATCH_MP kv_S1) >>
  ‘quiet_from (n2w lfdn) (pol_self hw) KI KS w0 N h f’
    by (rewrite_tac[quiet_from_def] >>
        conj_tac >- first_assum ACCEPT_TAC >>
        conj_tac >- (qpat_assum ‘∀k. t ≤ k ⇒ fkeep _ _ _ _’ irule >> first_assum ACCEPT_TAC) >>
        gen_tac >> strip_tac >> conj_tac
        >- (‘ALOOKUP (rstate (n2w lfdn) (pol_self hw) KI KS w0 k).b.tbl h = SOME f’
              by (qpat_assum ‘∀k. t ≤ k ⇒ fkeep _ _ _ _’ (qspec_then ‘k’ mp_tac) >>
                  impl_tac >- decide_tac >> rewrite_tac[fkeep_def] >> strip_tac) >>
            qpat_x_assum ‘ALOOKUP _ h = SOME f’ assume_tac >>
            first_x_assum drule >> disch_then ACCEPT_TAC) >>
        qpat_assum ‘∀k. M0 ≤ k ⇒ ¬fetched_at _ _ _ _ _ _ _ ∧ _’ (qspec_then ‘k’ mp_tac) >>
        impl_tac >- decide_tac >> strip_tac) >>
  qspecl_then [‘N’, ‘f’, ‘h’, ‘hw’, ‘lfdn’, ‘w0’] mp_tac
    (Q.GENL [‘N’, ‘f’, ‘h’, ‘hw’, ‘lfdn’, ‘w0’] kv_asks_pf) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> rpt strip_tac >>
      qpat_x_assum ‘fetched_at _ _ _ _ _ _ _’ mp_tac >>
      qpat_assum ‘∀k. M0 ≤ k ⇒ ¬fetched_at _ _ _ _ _ _ _ ∧ _’ (qspec_then ‘k’ mp_tac) >>
      impl_tac >- decide_tac >> simp[]) >>
  simp[]
QED
