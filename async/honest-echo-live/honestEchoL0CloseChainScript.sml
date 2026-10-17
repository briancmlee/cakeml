(*
  The close step of echo_live_l0 (design/47 D, D27 form): for a prefix
  evs of the PF echo trace with episode j open, its fd f on channel c and
  the peer's end-of-file on c, a later prefix of the trace ends in a close
  call on f while episode j is still open.

  L1 releases f (f leaves its table and closing list) only by a close
  call, and the first close call after a release round's start is made
  while the episode is open (release_open).  So it is enough to find a
  round n at which L1 holds f, does not hold it at n + 1, and f's episode
  is j.  From a round at which L1 holds f in episode j on channel c
  (held_released, by contradiction: L1 holds f in every later round):
   - f is never in the closing list (closing_released);
   - f is never at EOF in the table (echo_eof_leave: f leaves the table,
     so it is in the closing list);
   - so L1 keeps f with no EOF from the start, while c has the peer's
     end-of-file: eof_reaches gives a round that stops keeping it, but
     the table entry stays (pround_fkeep_tbl) and has no EOF.
  The first release round after that has episode j (first_release,
  keep_to_round).  Cases on the prefix, as in TraceData: episode j still
  open at round r + 1 with f held (held_close), pending (run_acq_taken,
  then held), or released while open (released_while_open); or episode j
  ended in the rest of round r (close_end).

  MAIN: trace_close.
*)
Theory honestEchoL0CloseChain
Ancestors
  honestEchoL0TraceWrap honestEchoL0TraceData honestEchoL0EofLeave honestEchoL0EofReach
  honestEchoL0Reap honestEchoL0CloseStep honestEchoL0Acq honestEchoL0EofCase honestEchoL0Stop
  honestEchoL0Obl honestEchoL0FlAt honestEchoL0Excuse honestEchoL0Peer honestEchoL0LiveOwn
  honestEchoL0Trace honestL1BFaith honestL1PFObl honestL1PFConnTrace honestL1PFOutLive honestL1PFFlush
  honestL1PFOut honestL1PFLive honestL1PFRound honestL1PFRefine honestL1PFModel honestL0World
Libs
  preamble

(* A round keeps a kept fd's table entry *)
Theorem pround_fkeep_tbl:
  pround lfd pol hs (w, ps) acts = SOME (sn, (w', ps'), log, evs) ∧ winv w ∧
  fkeep lfd h f ps ⇒
  ALOOKUP ps'.b.tbl h = SOME f
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >> gvs[] >>
  drule_all pacts_f >> strip_tac >>
  ‘winv ws10’ by metis_tac[pacts_winv] >>
  drule_all pf_tail_tbl >> strip_tac >> gvs[fkeep_def]
QED

Theorem run_psmono_c[local]:
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

Theorem pown_alookup[local]:
  pown lfd ps ∧ MEM f (MAP SND ps.b.tbl) ⇒ ∃h. ALOOKUP ps.b.tbl h = SOME f
Proof
  rw[pown_def, MEM_MAP] >> PairCases_on ‘y’ >> fs[] >>
  qexists_tac ‘y0’ >> irule ALOOKUP_ALL_DISTINCT_MEM >> simp[]
QED

(* The first release after a held round of episode j is in episode j *)
Theorem first_release:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ⇒
  ∀d a. held f (rstate lfd pol ifds m w0 a) ∧
        ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 a))) f = SOME j ∧
        ¬held f (rstate lfd pol ifds m w0 (SUC (a + d))) ⇒
        ∃n. a ≤ n ∧ held f (rstate lfd pol ifds m w0 n) ∧
            ¬held f (rstate lfd pol ifds m w0 (SUC n)) ∧
            ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 n))) f = SOME j
Proof
  strip_tac >> Induct
  >- (rpt strip_tac >> qexists_tac ‘a’ >> fs[]) >>
  rpt gen_tac >> disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  Cases_on ‘held f (rstate lfd pol ifds m w0 (SUC a))’
  >- (‘ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 (SUC a)))) f = SOME j’
        by (irule keep_to_round >> simp[] >> qexists_tac ‘a’ >> simp[] >>
            rpt strip_tac >> ‘i = SUC a’ by decide_tac >> gvs[]) >>
      first_x_assum (qspec_then ‘SUC a’ mp_tac) >> fs[ADD_CLAUSES] >>
      strip_tac >> qexists_tac ‘n’ >> simp[]) >>
  qexists_tac ‘a’ >> fs[]
QED

(* While f's episode stays j, f's channel stays the same *)
Theorem chan_fwd:
  oassm lfd pol ifds m w0 ∧ a ≤ b ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 a))) f = SOME j ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 b))) f = SOME j ∧
  l0_chan_of (rworld lfd pol ifds m w0 a) f = SOME c ∧
  (MEM f (MAP SND (rstate lfd pol ifds m w0 b).b.tbl) ∨
   MEM f (rstate lfd pol ifds m w0 b).b.closing ∨ MEM f (rstate lfd pol ifds m w0 b).acq) ⇒
  l0_chan_of (rworld lfd pol ifds m w0 b) f = SOME c
Proof
  strip_tac >>
  ‘run_ok lfd pol ifds m w0 ∧ winv w0 ∧ qfresh w0’ by fs[oassm_def] >>
  ‘∃c1. l0_chan_of (rworld lfd pol ifds m w0 b) f = SOME c1’
    by (irule run_held_chan >> metis_tac[]) >>
  ‘revs lfd pol ifds m w0 b = revs lfd pol ifds m w0 a ++ rrounds lfd pol ifds m w0 a (b − a)’
    by (drule revs_rrounds >> disch_then (qspecl_then [‘a’, ‘b − a’] mp_tac) >>
        ‘a + (b − a) = b’ by decide_tac >> simp[]) >>
  ‘¬EXISTS (ep_ends f) (rrounds lfd pol ifds m w0 a (b − a))’
    by (qspecl_then [‘revs lfd pol ifds m w0 a’, ‘f’, ‘j’, ‘rrounds lfd pol ifds m w0 a (b − a)’]
          mp_tac (Q.GENL [‘evs’, ‘f’, ‘j’, ‘mid’] idx_stable) >>
        gvs[]) >>
  ‘faithful w0 (revs lfd pol ifds m w0 b) ∧
   world_at w0 (revs lfd pol ifds m w0 b) = SOME (rworld lfd pol ifds m w0 b) ∧
   world_at w0 (revs lfd pol ifds m w0 a) = SOME (rworld lfd pol ifds m w0 a)’
    by metis_tac[run_world_at] >>
  ‘∃x. world_at w0 (revs lfd pol ifds m w0 a) = SOME x ∧ l0_chan_of x f = SOME c1’
    by (irule world_chan_back >> simp[] >>
        qexistsl_tac [‘rrounds lfd pol ifds m w0 a (b − a)’, ‘rworld lfd pol ifds m w0 b’] >>
        qpat_x_assum ‘revs _ _ _ _ _ b = _’ (fn th => fs[th, EVERY_MEM, EXISTS_MEM]) >>
        metis_tac[]) >>
  gvs[]
QED

(* MAIN (round level): L1 releases an fd it holds in episode j on channel
   c, if it holds it without EOF in the table only once c has the peer's
   end-of-file *)
Theorem held_released:
  echo_run lfdn pol w0 ∧ qfresh w0 ∧ qinb w0 ∧ pol_ok hw pol ∧ F1 (n2w lfdn) pol EI ES w0 ∧
  honestL1PFFlush$F2 w0 ∧ honestL1PFFlush$drains (n2w lfdn) pol EI ES w0 c ∧ nshut w0 ∧
  held f (rstate (n2w lfdn) pol EI ES w0 n) ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 n))) f = SOME j ∧
  l0_chan_of (rworld (n2w lfdn) pol EI ES w0 n) f = SOME c ∧
  (MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 n).b.tbl) ∧
   ¬MEM f (rstate (n2w lfdn) pol EI ES w0 n).eof ⇒
   (EL c (rworld (n2w lfdn) pol EI ES w0 n).chans).peer_eof) ⇒
  ∃k. n ≤ k ∧ ¬held f (rstate (n2w lfdn) pol EI ES w0 (SUC k))
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  ‘run_ok (n2w lfdn) pol EI ES w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0) ∧
   (∀n. SND (pcm (n2w lfdn) pol EI ES w0 n) + 1 < dimword (:64)) ∧ fds_lt w0’
    by fs[echo_run_def, winv_def] >>
  ‘oassm (n2w lfdn) pol EI ES w0’ by fs[oassm_def, echo_run_def] >>
  (* Reap states F2 with honestL1BStmts's copy (the same definition) *)
  ‘honestL1BStmts$F2 w0’
    by (qpat_x_assum ‘honestL1PFFlush$F2 w0’ mp_tac >>
        simp[honestL1BStmtsTheory.F2_def, honestL1PFFlushTheory.F2_def]) >>
  spose_not_then assume_tac >>
  (* ∀k. n ≤ k ⇒ held f (rstate … (SUC k)) *)
  ‘∀i. n ≤ i ⇒ held f (rstate (n2w lfdn) pol EI ES w0 i)’
    by (rpt strip_tac >> Cases_on ‘i = n’ >- (pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC) >>
        ‘i = SUC (i − 1) ∧ n ≤ i − 1’ by decide_tac >>
        pop_assum (fn th1 => pop_assum (fn th2 => ONCE_REWRITE_TAC [th2] >> assume_tac th1)) >>
        qpat_x_assum ‘∀k. n ≤ k ⇒ held _ _’ irule >> first_assum ACCEPT_TAC) >>
  ‘∀i. n ≤ i ⇒ ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 i))) f = SOME j’
    by (rpt strip_tac >> irule keep_to_round >> simp[] >> qexists_tac ‘n’ >> simp[]) >>
  ‘∀i. n ≤ i ⇒ l0_chan_of (rworld (n2w lfdn) pol EI ES w0 i) f = SOME c’
    by (rpt strip_tac >> irule chan_fwd >> rpt conj_tac
        >- (qexistsl_tac [‘n’, ‘j’] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
            qpat_x_assum ‘∀i. n ≤ i ⇒ ALOOKUP _ _ = _’ irule >> first_assum ACCEPT_TAC)
        >- (qpat_x_assum ‘∀i. n ≤ i ⇒ held f (rstate _ _ _ _ _ i)’ (qspec_then ‘i’ mp_tac) >>
            simp[] >> rpt strip_tac >> simp[]) >>
        first_assum ACCEPT_TAC) >>
  (* never closing *)
  ‘∀i. n ≤ i ⇒ ¬MEM f (rstate (n2w lfdn) pol EI ES w0 i).b.closing’
    by (rpt strip_tac >>
        ‘∃k. i ≤ k ∧ held f (rstate (n2w lfdn) pol EI ES w0 k) ∧
             ¬held f (rstate (n2w lfdn) pol EI ES w0 (SUC k))’
          by (irule closing_released >> simp[]) >>
        ‘held f (rstate (n2w lfdn) pol EI ES w0 (SUC k))’
          by (qpat_x_assum ‘∀k. n ≤ k ⇒ held _ (_ (SUC k))’ irule >> decide_tac) >>
        fs[]) >>
  (* never at EOF in the table *)
  ‘∀i. n ≤ i ⇒ ¬(MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 i).b.tbl) ∧
                 MEM f (rstate (n2w lfdn) pol EI ES w0 i).eof)’
    by (rpt strip_tac >>
        ‘pown (n2w lfdn) (rstate (n2w lfdn) pol EI ES w0 i)’
          by metis_tac[run_pown, echo_run_hyp] >>
        ‘∃h. ALOOKUP (rstate (n2w lfdn) pol EI ES w0 i).b.tbl h = SOME f’
          by (drule_all pown_alookup >> simp[]) >>
        ‘∃k. i ≤ k ∧ ALOOKUP (rstate (n2w lfdn) pol EI ES w0 k).b.tbl h = SOME f ∧
             ¬MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 (SUC k)).b.tbl)’
          by (irule echo_eof_leave >> simp[]) >>
        ‘held f (rstate (n2w lfdn) pol EI ES w0 (SUC k)) ∧
         ¬MEM f (rstate (n2w lfdn) pol EI ES w0 (SUC k)).b.closing’
          by (conj_tac
              >- (qpat_x_assum ‘∀k. n ≤ k ⇒ held _ (_ (SUC k))’ irule >> decide_tac) >>
              qpat_x_assum ‘∀i. n ≤ i ⇒ ¬MEM f _.b.closing’ irule >> decide_tac) >>
        fs[]) >>
  (* so L1 keeps f from n on, with the peer's end-of-file on c *)
  ‘MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 n).b.tbl) ∧
   ¬MEM f (rstate (n2w lfdn) pol EI ES w0 n).eof’
    by (qpat_x_assum ‘∀i. n ≤ i ⇒ ¬MEM f _.b.closing’ (qspec_then ‘n’ mp_tac) >>
        qpat_x_assum ‘∀i. n ≤ i ⇒ ¬(_ ∧ _)’ (qspec_then ‘n’ mp_tac) >>
        qpat_x_assum ‘held f (rstate _ _ _ _ _ n)’ mp_tac >>
        REWRITE_TAC [LESS_EQ_REFL] >> tautLib.TAUT_TAC) >>
  ‘(EL c (rworld (n2w lfdn) pol EI ES w0 n).chans).peer_eof’
    by (qpat_x_assum ‘_ ∧ _ ⇒ (EL c _).peer_eof’ irule >> conj_tac >> first_assum ACCEPT_TAC) >>
  ‘pown (n2w lfdn) (rstate (n2w lfdn) pol EI ES w0 n)’
    by metis_tac[run_pown, echo_run_hyp] >>
  ‘∃h. ALOOKUP (rstate (n2w lfdn) pol EI ES w0 n).b.tbl h = SOME f’
    by (drule_all pown_alookup >> simp[]) >>
  ‘fkeep (n2w lfdn) h f (rstate (n2w lfdn) pol EI ES w0 n)’
    by (drule_all fkeep_run >> simp[]) >>
  ‘S1 (n2w lfdn) pol EI ES w0’ by (irule S1_interest >> simp[]) >>
  ‘S3w (n2w lfdn) pol EI ES w0’ by metis_tac[echo_S3w] >>
  ‘S4w (n2w lfdn) pol hw EI ES w0 f’ by metis_tac[echo_S4w] >>
  ‘∃k. n ≤ k ∧ (∀i. n ≤ i ∧ i < k ⇒ fkeep (n2w lfdn) h f (rstate (n2w lfdn) pol EI ES w0 i)) ∧
       ¬fkeep (n2w lfdn) h f (rstate (n2w lfdn) pol EI ES w0 k)’
    by (irule eof_reaches >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        TRY (qexists_tac ‘c’ >> conj_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
        qexists_tac ‘hw’ >> conj_tac >> first_assum ACCEPT_TAC) >>
  Cases_on ‘k = n’ >- gvs[] >>
  ‘k = SUC (k − 1) ∧ n ≤ k − 1’ by decide_tac >>
  qabbrev_tac ‘k1 = k − 1’ >>
  ‘fkeep (n2w lfdn) h f (rstate (n2w lfdn) pol EI ES w0 k1)’
    by (qpat_x_assum ‘∀i. n ≤ i ∧ i < k ⇒ _’ irule >> decide_tac) >>
  qpat_assum ‘run_ok _ _ _ _ _’ (fn th => mp_tac (Q.SPEC ‘k1’ (MATCH_MP prun_round' th))) >>
  strip_tac >>
  ‘winv (rworld (n2w lfdn) pol EI ES w0 k1)’ by metis_tac[winv_run] >>
  ‘ALOOKUP (rstate (n2w lfdn) pol EI ES w0 (SUC k1)).b.tbl h = SOME f’
    by (drule_all pround_fkeep_tbl >> simp[]) >>
  ‘MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 (SUC k1)).b.tbl)’
    by (imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  ‘¬MEM f (rstate (n2w lfdn) pol EI ES w0 (SUC k1)).eof’
    by (strip_tac >>
        qpat_x_assum ‘∀i. n ≤ i ⇒ ¬(_ ∧ _)’ (qspec_then ‘SUC k1’ mp_tac) >> simp[]) >>
  ‘fkeep (n2w lfdn) h f (rstate (n2w lfdn) pol EI ES w0 (SUC k1))’
    by (drule_all fkeep_run >> simp[]) >>
  qpat_x_assum ‘¬fkeep _ _ _ _’ mp_tac >> qpat_x_assum ‘k = _’ SUBST1_TAC >> simp[]
QED

(* ... and the release round is in episode j *)
Theorem held_close:
  echo_run lfdn pol w0 ∧ qfresh w0 ∧ qinb w0 ∧ pol_ok hw pol ∧ F1 (n2w lfdn) pol EI ES w0 ∧
  honestL1PFFlush$F2 w0 ∧ honestL1PFFlush$drains (n2w lfdn) pol EI ES w0 c ∧ nshut w0 ∧
  held f (rstate (n2w lfdn) pol EI ES w0 n) ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 n))) f = SOME j ∧
  l0_chan_of (rworld (n2w lfdn) pol EI ES w0 n) f = SOME c ∧
  (MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 n).b.tbl) ∧
   ¬MEM f (rstate (n2w lfdn) pol EI ES w0 n).eof ⇒
   (EL c (rworld (n2w lfdn) pol EI ES w0 n).chans).peer_eof) ⇒
  ∃k. n ≤ k ∧ held f (rstate (n2w lfdn) pol EI ES w0 k) ∧
      ¬held f (rstate (n2w lfdn) pol EI ES w0 (SUC k)) ∧
      ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 k))) f = SOME j
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  ‘run_ok (n2w lfdn) pol EI ES w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0)’
    by fs[echo_run_def] >>
  mp_tac held_released >> impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then ‘k’ strip_assume_tac) >>
  drule first_release >>
  disch_then (qspecl_then [‘j’, ‘f’, ‘k − n’, ‘n’] mp_tac) >>
  ‘n + (k − n) = k’ by decide_tac >> pop_assum (fn th => REWRITE_TAC [th]) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then ‘k2’ (fn th => MAP_EVERY assume_tac (CONJUNCTS th))) >>
  qexists_tac ‘k2’ >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem acq_keep[local]:
  pown lfd ps ∧ MEM f ps.acq ⇒ keep f ps
Proof
  rw[pown_def, keep_def, ALL_DISTINCT_APPEND] >> metis_tac[]
QED

(* Episode j ends in the rest of round r: L1 held f at EOF or closing at
   round r, or had released it while open *)
Theorem close_end:
  echo_run lfdn pol w0 ∧ qfresh w0 ∧ qinb w0 ∧ pol_ok hw pol ∧ F1 (n2w lfdn) pol EI ES w0 ∧
  honestL1PFFlush$F2 w0 ∧ honestL1PFFlush$drains (n2w lfdn) pol EI ES w0 c ∧ nshut w0 ∧
  rrev (n2w lfdn) pol EI ES w0 r = pre ++ post ∧
  world_at w0 (revs (n2w lfdn) pol EI ES w0 r ++ pre) = SOME w ∧ l0_chan_of w f = SOME c ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 r ++ pre))) f = SOME j ∧
  EXISTS (ep_ends f) post ⇒
  ∃n. held f (rstate (n2w lfdn) pol EI ES w0 n) ∧
      ¬held f (rstate (n2w lfdn) pol EI ES w0 (SUC n)) ∧
      ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 n))) f = SOME j
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  ‘run_ok (n2w lfdn) pol EI ES w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0) ∧
   (∀n. SND (pcm (n2w lfdn) pol EI ES w0 n) + 1 < dimword (:64))’ by fs[echo_run_def] >>
  ‘revs (n2w lfdn) pol EI ES w0 (SUC r) = revs (n2w lfdn) pol EI ES w0 r ++ pre ++ post’
    by (qpat_assum ‘run_ok _ _ _ _ _’ (fn th => mp_tac (Q.SPEC ‘r’ (MATCH_MP prun_round' th))) >>
        rpt strip_tac >> simp[]) >>
  ‘faithful w0 (revs (n2w lfdn) pol EI ES w0 r ++ pre ++ post)’
    by metis_tac[run_world_at] >>
  ‘faithful w0 (revs (n2w lfdn) pol EI ES w0 r ++ pre)’
    by metis_tac[faithful_prefix, APPEND_ASSOC] >>
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
  ‘¬keep f (rstate (n2w lfdn) pol EI ES w0 r)’
    by (strip_tac >> drule_all run_keep_noend >> strip_tac >> metis_tac[EXISTS_APPEND]) >>
  ‘pown (n2w lfdn) (rstate (n2w lfdn) pol EI ES w0 r)’
    by metis_tac[run_pown, echo_run_hyp] >>
  Cases_on ‘MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 r).b.tbl) ∧
            MEM f (rstate (n2w lfdn) pol EI ES w0 r).eof ∨
            MEM f (rstate (n2w lfdn) pol EI ES w0 r).b.closing’
  >- (mp_tac (Q.INST [‘n’ |-> ‘r’] held_close) >>
      impl_tac
      >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
          >- (qpat_x_assum ‘(_ ∧ _) ∨ _’ mp_tac >> tautLib.TAUT_TAC) >>
          strip_tac >> qpat_x_assum ‘¬keep _ _’ mp_tac >> simp[keep_def]) >>
      disch_then (qx_choose_then ‘k’ (fn th => MAP_EVERY assume_tac (CONJUNCTS th))) >>
      qexists_tac ‘k’ >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  ‘¬MEM f (rstate (n2w lfdn) pol EI ES w0 r).acq ∧
   ¬MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 r).b.tbl)’
    by (gvs[keep_def, pown_def] >> metis_tac[]) >>
  ‘¬MEM f (rstate (n2w lfdn) pol EI ES w0 r).b.closing’ by fs[] >>
  drule released_while_open >>
  disch_then (qspecl_then [‘r’, ‘f’, ‘j’] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then ‘k’ (fn th => MAP_EVERY assume_tac (CONJUNCTS th))) >>
  qexists_tac ‘k’ >> asm_rewrite_tac []
QED

(* Episode j is still open at round r + 1 *)
Theorem close_open:
  echo_run lfdn pol w0 ∧ qfresh w0 ∧ qinb w0 ∧ pol_ok hw pol ∧ F1 (n2w lfdn) pol EI ES w0 ∧
  honestL1PFFlush$F2 w0 ∧ honestL1PFFlush$drains (n2w lfdn) pol EI ES w0 c ∧ nshut w0 ∧
  rrev (n2w lfdn) pol EI ES w0 r = pre ++ post ∧
  world_at w0 (revs (n2w lfdn) pol EI ES w0 r ++ pre) = SOME w ∧ l0_chan_of w f = SOME c ∧
  (EL c w.chans).peer_eof ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 r ++ pre))) f = SOME j ∧
  ¬EXISTS (ep_ends f) post ⇒
  ∃n. held f (rstate (n2w lfdn) pol EI ES w0 n) ∧
      ¬held f (rstate (n2w lfdn) pol EI ES w0 (SUC n)) ∧
      ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 n))) f = SOME j
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  ‘run_ok (n2w lfdn) pol EI ES w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0) ∧
   (∀n. SND (pcm (n2w lfdn) pol EI ES w0 n) + 1 < dimword (:64))’ by fs[echo_run_def] >>
  ‘oassm (n2w lfdn) pol EI ES w0’ by fs[oassm_def, echo_run_def] >>
  ‘revs (n2w lfdn) pol EI ES w0 (SUC r) = (revs (n2w lfdn) pol EI ES w0 r ++ pre) ++ post’
    by (qpat_assum ‘run_ok _ _ _ _ _’ (fn th => mp_tac (Q.SPEC ‘r’ (MATCH_MP prun_round' th))) >>
        rpt strip_tac >> simp[]) >>
  ‘faithful w0 ((revs (n2w lfdn) pol EI ES w0 r ++ pre) ++ post) ∧
   world_at w0 ((revs (n2w lfdn) pol EI ES w0 r ++ pre) ++ post) =
     SOME (rworld (n2w lfdn) pol EI ES w0 (SUC r))’
    by metis_tac[run_world_at] >>
  ‘ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 (SUC r)))) f = SOME j’
    by (qpat_x_assum ‘revs _ _ _ _ _ (SUC r) = _’ SUBST1_TAC >>
        ONCE_REWRITE_TAC [CONJUNCT2 (CONJUNCT2 l0_ep_st_simps)] >>
        irule ep_st_keep >> conj_tac >> first_assum ACCEPT_TAC) >>
  ‘c < LENGTH w.chans’ by metis_tac[chan_lt] >>
  ‘(EL c (rworld (n2w lfdn) pol EI ES w0 (SUC r)).chans).peer_eof’
    by (‘psmono c w (rworld (n2w lfdn) pol EI ES w0 (SUC r))’
          by (irule world_at_psmono >>
              qexistsl_tac [‘revs (n2w lfdn) pol EI ES w0 r ++ pre’, ‘post’, ‘w0’] >>
              rpt conj_tac >> first_assum ACCEPT_TAC) >>
        fs[psmono_def]) >>
  ‘pown (n2w lfdn) (rstate (n2w lfdn) pol EI ES w0 (SUC r))’
    by metis_tac[run_pown, echo_run_hyp] >>
  Cases_on ‘MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 (SUC r)).b.tbl) ∨
            MEM f (rstate (n2w lfdn) pol EI ES w0 (SUC r)).b.closing ∨
            MEM f (rstate (n2w lfdn) pol EI ES w0 (SUC r)).acq’
  >- ((* L1 knows f at r + 1: its channel there is c *)
      ‘∃c1. l0_chan_of (rworld (n2w lfdn) pol EI ES w0 (SUC r)) f = SOME c1’
        by (irule run_held_chan >> metis_tac[]) >>
      ‘l0_chan_of (rworld (n2w lfdn) pol EI ES w0 (SUC r)) f = SOME c’
        by (‘∃x. world_at w0 (revs (n2w lfdn) pol EI ES w0 r ++ pre) = SOME x ∧
                 l0_chan_of x f = SOME c1’
              by (irule world_chan_back >> simp[] >>
                  qexistsl_tac [‘post’, ‘rworld (n2w lfdn) pol EI ES w0 (SUC r)’] >>
                  fs[EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
            gvs[]) >>
      Cases_on ‘MEM f (rstate (n2w lfdn) pol EI ES w0 (SUC r)).acq’
      >- ((* pending: handed to the server at some round n' *)
          drule_all run_acq_taken >>
          disch_then (qx_choose_then ‘n'’ strip_assume_tac) >>
          ‘∃d. n' = SUC (SUC r + d)’ by (qexists_tac ‘n' − SUC (SUC r)’ >> decide_tac) >>
          ‘∀i. SUC r ≤ i ∧ i ≤ SUC r + d ⇒ keep f (rstate (n2w lfdn) pol EI ES w0 i)’
            by (rpt strip_tac >> irule acq_keep >> conj_tac
                >- (qpat_x_assum ‘∀i. SUC r ≤ i ∧ i < n' ⇒ _’ irule >> decide_tac) >>
                qexists_tac ‘n2w lfdn’ >> metis_tac[run_pown, echo_run_hyp]) >>
          ‘ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 n'))) f = SOME j’
            by (drule keep_span >> disch_then (qspecl_then [‘f’, ‘d’, ‘SUC r’] mp_tac) >>
                impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
                strip_tac >> qpat_x_assum ‘n' = _’ SUBST1_TAC >>
                qpat_x_assum ‘ALOOKUP _ _ = ALOOKUP _ _’ SUBST1_TAC >> first_assum ACCEPT_TAC) >>
          ‘l0_chan_of (rworld (n2w lfdn) pol EI ES w0 n') f = SOME c’
            by (irule chan_fwd >> rpt conj_tac
                >- (qexistsl_tac [‘SUC r’, ‘j’] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
                    decide_tac)
                >- (disj1_tac >> first_assum ACCEPT_TAC) >>
                first_assum ACCEPT_TAC) >>
          ‘(EL c (rworld (n2w lfdn) pol EI ES w0 n').chans).peer_eof’
            by (‘c < LENGTH (rworld (n2w lfdn) pol EI ES w0 (SUC r)).chans’ by metis_tac[chan_lt] >>
                ‘psmono c (rworld (n2w lfdn) pol EI ES w0 (SUC r)) (rworld (n2w lfdn) pol EI ES w0 n')’
                  by (irule run_psmono_c >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
                      decide_tac) >>
                qpat_x_assum ‘psmono _ _ _’ mp_tac >> qpat_x_assum ‘c < LENGTH _’ mp_tac >>
                qpat_x_assum ‘(EL c (rworld _ _ _ _ _ (SUC r)).chans).peer_eof’ mp_tac >>
                simp[psmono_def]) >>
          mp_tac (Q.INST [‘n’ |-> ‘n'’] held_close) >>
          impl_tac
          >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
              TRY (strip_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
              disj1_tac >> first_assum ACCEPT_TAC) >>
          disch_then (qx_choose_then ‘k’ (fn th => MAP_EVERY assume_tac (CONJUNCTS th))) >>
          qexists_tac ‘k’ >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      (* held at r + 1 *)
      mp_tac (Q.INST [‘n’ |-> ‘SUC r’] held_close) >>
      impl_tac
      >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          TRY (strip_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
          qpat_x_assum ‘_ ∨ _ ∨ _’ mp_tac >>
          qpat_x_assum ‘¬MEM f _.acq’ mp_tac >> tautLib.TAUT_TAC) >>
      disch_then (qx_choose_then ‘k’ (fn th => MAP_EVERY assume_tac (CONJUNCTS th))) >>
      qexists_tac ‘k’ >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  (* released while open *)
  qpat_x_assum ‘¬(_ ∨ _)’ (strip_assume_tac o REWRITE_RULE [DE_MORGAN_THM]) >>
  drule released_while_open >>
  disch_then (qspecl_then [‘SUC r’, ‘f’, ‘j’] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then ‘k’ (fn th => MAP_EVERY assume_tac (CONJUNCTS th))) >>
  qexists_tac ‘k’ >> asm_rewrite_tac []
QED

Theorem close_mid:
  echo_run lfdn pol w0 ∧ qfresh w0 ∧ qinb w0 ∧ pol_ok hw pol ∧ F1 (n2w lfdn) pol EI ES w0 ∧
  honestL1PFFlush$F2 w0 ∧ honestL1PFFlush$drains (n2w lfdn) pol EI ES w0 c ∧ nshut w0 ∧
  rrev (n2w lfdn) pol EI ES w0 r = pre ++ post ∧
  world_at w0 (revs (n2w lfdn) pol EI ES w0 r ++ pre) = SOME w ∧ l0_chan_of w f = SOME c ∧
  (EL c w.chans).peer_eof ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 r ++ pre))) f = SOME j ⇒
  ∃n. held f (rstate (n2w lfdn) pol EI ES w0 n) ∧
      ¬held f (rstate (n2w lfdn) pol EI ES w0 (SUC n)) ∧
      ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 n))) f = SOME j
Proof
  strip_tac >> Cases_on ‘EXISTS (ep_ends f) post’
  >- (irule close_end >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (qexists_tac ‘hw’ >> first_assum ACCEPT_TAC >> NO_TAC) >>
      qexistsl_tac [‘c’, ‘post’, ‘pre’, ‘r’, ‘w’] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  irule close_open >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (qexists_tac ‘hw’ >> first_assum ACCEPT_TAC >> NO_TAC) >>
  qexistsl_tac [‘c’, ‘post’, ‘pre’, ‘r’, ‘w’] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* ------------------------------------------------------------------------
   MAIN
   ------------------------------------------------------------------------ *)

Theorem trace_close:
  echo_run lfdn pol w0 ∧ qfresh w0 ∧ qinb w0 ∧ pol_ok hw pol ∧ F1 (n2w lfdn) pol EI ES w0 ∧
  honestL1PFFlush$F2 w0 ∧ honestL1PFFlush$drains (n2w lfdn) pol EI ES w0 c ∧ nshut w0 ∧
  pftrace (n2w lfdn) pol EI ES w0 io ∧
  LPREFIX (fromList evs) io ∧ ep_open j evs ∧ world_at w0 evs = SOME w ∧
  l0_chan_of w (EL j (l0_accepted evs)) = SOME c ∧ (EL c w.chans).peer_eof ⇒
  ∃evs' ev. LPREFIX (fromList (evs' ++ [ev])) io ∧ ep_open j evs' ∧
            l0_close_call (EL j (l0_accepted evs')) ev
Proof
  strip_tac >>
  ‘run_ok (n2w lfdn) pol EI ES w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0)’
    by fs[echo_run_def] >>
  ‘ALOOKUP (SND (l0_ep_st (0, []) evs)) (EL j (l0_accepted evs)) = SOME j’
    by metis_tac[ep_open_state] >>
  drule_all trace_locate >> strip_tac >>
  Q.SUBGOAL_THEN ‘∃n. held (EL j (l0_accepted evs)) (rstate (n2w lfdn) pol EI ES w0 n) ∧
       ¬held (EL j (l0_accepted evs)) (rstate (n2w lfdn) pol EI ES w0 (SUC n)) ∧
       ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 n)))
         (EL j (l0_accepted evs)) = SOME j’
    (qx_choose_then ‘n’ (fn th => MAP_EVERY assume_tac (CONJUNCTS th)))
  >- (irule close_mid >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      TRY (qexists_tac ‘hw’ >> first_assum ACCEPT_TAC >> NO_TAC) >>
      qpat_x_assum ‘evs = _’ SUBST_ALL_TAC >>
      qexistsl_tac [‘c’, ‘post’, ‘pre’, ‘r’, ‘w’] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule release_open >>
  disch_then (qspecl_then [‘n’, ‘j’, ‘EL j (l0_accepted evs)’] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [‘p1’, ‘e’, ‘p2’]
                (fn th => MAP_EVERY assume_tac (CONJUNCTS th))) >>
  qexistsl_tac [‘revs (n2w lfdn) pol EI ES w0 n ++ p1’, ‘e’] >>
  qpat_x_assum ‘EL j (l0_accepted (_ ++ p1)) = _’ (fn th => REWRITE_TAC [th]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  drule pftrace_sub >> disch_then irule >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> qexists_tac ‘SUC n’ >>
  qpat_assum ‘run_ok _ _ _ _ _’ (fn th => mp_tac (Q.SPEC ‘n’ (MATCH_MP prun_round' th))) >>
  strip_tac >> qpat_x_assum ‘revs _ _ _ _ _ (SUC n) = _’ SUBST1_TAC >>
  qpat_x_assum ‘rrev _ _ _ _ _ n = _’ SUBST1_TAC >>
  REWRITE_TAC [APPEND_ASSOC, rich_listTheory.IS_PREFIX_APPEND3]
QED
