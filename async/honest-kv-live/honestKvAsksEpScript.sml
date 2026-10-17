(*
  K-asks on the trace, the episode side: while episode j on f stays open
  on the PF KV trace (¬ep_ended), and neither its channel freezes nor a
  hard error hits it, L1 keeps f in its table from some round on, under a
  handle h, without EOF.

  Episode j is open on every prefix of the trace that has its accept
  (ep_open_ext, ep_open_prefix), and an open episode is the only one on
  its fd (ep_open_unique); f entered L1's pre-accepted fds at the round
  of that accept, and L1 takes it (kv_acq_taken, from KV's S2); f is at
  EOF only after an FEof (its channel ended: ch_frozen) or an FReset (a
  hard recv error of episode j).

  MAIN: kv_S2, kv_acq_taken, kv_eof_excuse, kv_held_forever.
*)
Theory honestKvAsksEp
Ancestors
  honestKvAsksTrace honestKvL0LiveStmts asyncKvLiveL honestL0GenS2 honestKvReadSoonPF
  honestKvL0Obl honestEchoL0TraceWrap honestEchoL0EofCase honestEchoL0EofOrigin
  honestEchoL0Eof honestEchoL0Acq honestEchoL0Excuse honestEchoL0LiveOwn honestEchoL0Drains
  honestEchoL0Chain honestEchoL0TraceData honestL1PFEpisode honestL1PFBroken honestL1PFObl
  honestL1PFOutLive honestL1PFConnTrace honestL1PFConnRun honestL1BStmts honestL1BFaith
  honestEchoL0Inv honestEchoL0Spec honestL1PFInv honestL1PFRefine honestL1BTransfer honestL1PFClient
  honestL1PFLive honestL1PFRound honestL1PFModel
Libs
  preamble

(* ------------------------------------------------------------------------
   KV's S2 and the take of a pre-accepted fd
   ------------------------------------------------------------------------ *)

Theorem kv_S2:
  kv_run lfdn pol w0 ⇒ S2 (n2w lfdn) pol KI KS w0
Proof
  strip_tac >> drule kv_v1_world >> strip_tac >>
  drule kv_gen_run >> strip_tac >>
  drule gen_S2 >> disch_then irule >> rpt strip_tac >>
  qspecl_then [‘c’, ‘lfdn’, ‘v1of (n2w lfdn) (psk (n2w lfdn) pol KI KS w0)’] mp_tac
    (Q.GENL [‘c’, ‘lfdn’, ‘s0’] kv_queue_progress_l) >>
  impl_tac >- fs[kv_run_def] >>
  disch_then drule >> simp[]
QED

Theorem kv_acq_taken:
  kv_run lfdn pol w0 ∧ MEM f (rstate (n2w lfdn) pol KI KS w0 n).acq ⇒
  ∃n'. n < n' ∧ MEM f (MAP SND (rstate (n2w lfdn) pol KI KS w0 n').b.tbl) ∧
       ∀i. n ≤ i ∧ i < n' ⇒ MEM f (rstate (n2w lfdn) pol KI KS w0 i).acq
Proof
  strip_tac >>
  ‘run_ok (n2w lfdn) pol KI KS w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0) ∧
   (∀n. SND (pcm (n2w lfdn) pol KI KS w0 n) + 1 < dimword (:64))’ by fs[kv_run_def] >>
  drule_all run_own >> strip_tac >>
  ‘∀i. pown (n2w lfdn) (rstate (n2w lfdn) pol KI KS w0 i)’
    by metis_tac[run_pown, kv_run_hyp] >>
  ‘∀i. (rstate (n2w lfdn) pol KI KS w0 i).b.nxt +
       naccepts (new_actions (log_of KS) (rhist (n2w lfdn) pol KI KS w0 i)) < dimword (:64)’
    by (gen_tac >>
        qpat_assum ‘run_ok _ _ _ _ _’ (fn th => assume_tac (MATCH_MP prun_some th)) >>
        first_x_assum (qspec_then ‘i’ assume_tac) >>
        Cases_on ‘prun (n2w lfdn) pol KI KS w0 i’ >> rename1 ‘_ = (hh, rr)’ >>
        PairCases_on ‘rr’ >>
        gvs[rstate_def, rhist_def, run_ok_def, pl2_ok_def] >>
        first_x_assum drule >> simp[]) >>
  ‘∀i. MEM f (rstate (n2w lfdn) pol KI KS w0 i).acq ⇒
       keep f (rstate (n2w lfdn) pol KI KS w0 i) ∧
       ¬MEM f (MAP SND (rstate (n2w lfdn) pol KI KS w0 i).b.tbl)’
    by (rpt gen_tac >> strip_tac >>
        qpat_x_assum ‘∀i. pown _ _’ (qspec_then ‘i’ mp_tac) >>
        simp[pown_def, keep_def, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  ‘(rstate (n2w lfdn) pol KI KS w0 n).acq ≠ []’ by (strip_tac >> fs[]) >>
  drule kv_S2 >> simp[S2_def] >> disch_then drule >> strip_tac >>
  ‘∃m. (n ≤ m ∧ ∃l. MEM (Accept l)
          (new_actions (log_of KS) (rhist (n2w lfdn) pol KI KS w0 m))) ∧
       ∀m'. m' < m ⇒ ¬(n ≤ m' ∧ ∃l. MEM (Accept l)
          (new_actions (log_of KS) (rhist (n2w lfdn) pol KI KS w0 m')))’
    by (ho_match_mp_tac WOP >> metis_tac[]) >>
  ‘∀d. n + d ≤ m ⇒ MEM f (rstate (n2w lfdn) pol KI KS w0 (n + d)).acq’
    by (Induct >> simp[] >> strip_tac >>
        ‘MEM f (rstate (n2w lfdn) pol KI KS w0 (n + d)).acq’
          by (qpat_x_assum ‘n + d ≤ m ⇒ _’ irule >> simp[]) >>
        ‘keep f (rstate (n2w lfdn) pol KI KS w0 (n + d)) ∧
         ¬MEM f (MAP SND (rstate (n2w lfdn) pol KI KS w0 (n + d)).b.tbl)’
          by (qpat_x_assum ‘∀i. MEM f _ ⇒ keep f _ ∧ _’ irule >> simp[]) >>
        ‘n + SUC d = SUC (n + d)’ by simp[] >> pop_assum SUBST1_TAC >>
        qpat_assum ‘run_ok _ _ _ _ _’
          (fn th => mp_tac (Q.SPEC ‘n + d’ (MATCH_MP prun_round' th))) >>
        strip_tac >>
        qpat_assum ‘∀n. wown _ _ _ ∧ _’ (qspec_then ‘n + d’ strip_assume_tac) >>
        ‘∀l. ¬MEM (Accept l) (new_actions (log_of KS) (rhist (n2w lfdn) pol KI KS w0 (n + d)))’
          by (qpat_x_assum ‘∀m'. m' < m ⇒ _’ (qspec_then ‘n + d’ mp_tac) >> simp[]) >>
        ‘winv (rworld (n2w lfdn) pol KI KS w0 (n + d))’ by metis_tac[winv_run] >>
        ‘¬MEM f (MAP SND (rstate (n2w lfdn) pol KI KS w0 (SUC (n + d))).b.tbl)’
          by (drule pround_noacc >> disch_then (qspec_then ‘f’ mp_tac) >> simp[]) >>
        Cases_on ‘l0_ep_st (0, []) (revs (n2w lfdn) pol KI KS w0 (n + d))’ >> fs[] >>
        drule pround_keep >> disch_then drule >> disch_then drule >>
        disch_then (qspec_then ‘f’ mp_tac) >> simp[]) >>
  ‘MEM f (rstate (n2w lfdn) pol KI KS w0 m).acq’
    by (first_x_assum (qspec_then ‘m − n’ mp_tac) >> simp[]) >>
  ‘(rstate (n2w lfdn) pol KI KS w0 m).acq = [f]’
    by (qpat_assum ‘∀n. wown _ _ _ ∧ _’ (qspec_then ‘m’ strip_assume_tac) >>
        Cases_on ‘(rstate (n2w lfdn) pol KI KS w0 m).acq’ >> gvs[] >>
        Cases_on ‘t’ >> gvs[]) >>
  qexists_tac ‘SUC m’ >> simp[] >> conj_tac
  >- (qpat_assum ‘run_ok _ _ _ _ _’
        (fn th => mp_tac (Q.SPEC ‘m’ (MATCH_MP prun_round' th))) >>
      strip_tac >>
      qpat_assum ‘∀n. wown _ _ _ ∧ _’ (qspec_then ‘m’ strip_assume_tac) >>
      Cases_on ‘l0_ep_st (0, []) (revs (n2w lfdn) pol KI KS w0 m)’ >> fs[] >>
      ‘winv (rworld (n2w lfdn) pol KI KS w0 m)’ by metis_tac[winv_run] >>
      drule pround_take >> disch_then irule >> fs[wown_def] >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum (qspec_then ‘i − n’ mp_tac) >> simp[]
QED

(* A round that accepts f leaves f pre-accepted *)
Theorem pf_fetch_conn_acq[local]:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ⇒
    ∀g. MEM g ps.acq ∨ MEM (FConn g) log ⇒ MEM g ps'.acq
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[AllCaseEqs()] >>
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> gvs[set_inb_def]
QED

Theorem pround_conn_acq:
  pround lfd pol hs (w, ps) acts = SOME (sn, (w', ps'), log, evs) ∧ MEM (FConn g) log ⇒
  MEM g ps'.acq
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >> gvs[] >>
  qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >> simp[pf_tail_def, AllCaseEqs()] >>
  strip_tac >> gvs[stall_step_fields] >>
  drule pf_fetch_conn_acq >> disch_then (qspec_then ‘g’ mp_tac) >> simp[]
QED

(* ------------------------------------------------------------------------
   Open episodes on the trace
   ------------------------------------------------------------------------ *)

Theorem ep_open_ext:
  ep_open j evs ∧ ¬EXISTS (ep_ends (EL j (l0_accepted evs))) mid ⇒
  ep_open j (evs ++ mid) ∧ j < LENGTH (l0_accepted evs) ∧
  EL j (l0_accepted (evs ++ mid)) = EL j (l0_accepted evs)
Proof
  strip_tac >> drule ep_open_split >> strip_tac >>
  ‘j < LENGTH (l0_accepted evs)’
    by (qpat_x_assum ‘evs = _’ SUBST1_TAC >> simp[l0_accepted_def] >>
        gvs[l0_accepted_def]) >>
  rpt conj_tac
  >- (simp[ep_open_def] >>
      qexistsl_tac [‘pre’, ‘ev’, ‘post ++ mid’, ‘EL j (l0_accepted evs)’] >>
      gvs[EVERY_MEM, EXISTS_MEM] >> metis_tac[])
  >- first_assum ACCEPT_TAC >>
  qpat_x_assum ‘j < _’ mp_tac >> rewrite_tac[l0_accepted_APPEND] >> simp[EL_APPEND1]
QED

Theorem ep_open_closed:
  ep_open j evs ∧ EXISTS (ep_ends (EL j (l0_accepted evs))) mid ⇒ ep_closed j (evs ++ mid)
Proof
  strip_tac >> drule ep_open_split >> strip_tac >> simp[ep_closed_def] >>
  qexistsl_tac [‘pre’, ‘ev’, ‘post ++ mid’, ‘EL j (l0_accepted evs)’] >>
  gvs[EXISTS_APPEND]
QED

Theorem ep_open_prefix:
  ep_open j (p ++ q) ∧ j < LENGTH (l0_accepted p) ⇒
  ep_open j p ∧ EL j (l0_accepted p) = EL j (l0_accepted (p ++ q))
Proof
  strip_tac >> simp[EL_APPEND1] >>
  qpat_x_assum ‘ep_open _ _’ mp_tac >> simp[ep_open_def] >> strip_tac >>
  qpat_x_assum ‘p ++ q = _’ mp_tac >>
  ‘pre ++ [ev] ++ post = (pre ++ [ev]) ++ post’ by simp[] >> pop_assum SUBST1_TAC >>
  simp[APPEND_EQ_APPEND] >> strip_tac
  >- (qexistsl_tac [‘pre’, ‘ev’, ‘l’, ‘f’] >> gvs[EVERY_APPEND]) >>
  Cases_on ‘l’ using SNOC_CASES >> gvs[]
  >- (qexistsl_tac [‘pre’, ‘ev’, ‘[]’, ‘f’] >> simp[]) >>
  gvs[SNOC_APPEND] >>
  qpat_x_assum ‘j < _’ mp_tac >> simp[] >> fs[l0_accepted_def]
QED

Theorem MEM_l0_accepted[local]:
  MEM f (l0_accepted l) ⇒ EXISTS (ep_ends f) l
Proof
  simp[l0_accepted_def, MEM_FLAT, MEM_MAP, EXISTS_MEM, PULL_EXISTS] >>
  rw[] >> first_assum (irule_at Any) >> simp[ep_ends_def] >>
  every_case_tac >> gvs[]
QED

Theorem ep_open_lt_unique[local]:
  ep_open i p ∧ i < i' ∧ i' < LENGTH (l0_accepted p) ⇒
  EL i' (l0_accepted p) ≠ EL i (l0_accepted p)
Proof
  strip_tac >> drule ep_open_split >> strip_tac >>
  qabbrev_tac ‘f = EL i (l0_accepted p)’ >>
  ‘l0_accepted p = l0_accepted pre ++ [f] ++ l0_accepted post’
    by (qpat_x_assum ‘p = _’ SUBST1_TAC >> simp[l0_accepted_def]) >>
  strip_tac >>
  ‘MEM f (l0_accepted post)’
    by (qpat_x_assum ‘EL i' _ = f’ mp_tac >>
        qpat_assum ‘l0_accepted p = _’ SUBST1_TAC >>
        qpat_x_assum ‘i' < _’ mp_tac >>
        qpat_x_assum ‘l0_accepted p = _’ SUBST1_TAC >>
        simp[EL_APPEND_EQN] >> rw[] >> simp[MEM_EL] >>
        qexists_tac ‘i' − (LENGTH (l0_accepted pre) + 1)’ >> simp[]) >>
  drule MEM_l0_accepted >> qpat_x_assum ‘¬EXISTS _ post’ mp_tac >> simp[]
QED

Theorem ep_open_unique:
  ep_open i p ∧ ep_open i' p ∧ i < LENGTH (l0_accepted p) ∧ i' < LENGTH (l0_accepted p) ∧
  EL i (l0_accepted p) = EL i' (l0_accepted p) ⇒ i = i'
Proof
  strip_tac >> CCONTR_TAC >>
  Cases_on ‘i < i'’
  >- (qspecl_then [‘i’, ‘i'’, ‘p’] mp_tac (Q.GENL [‘i’, ‘i'’, ‘p’] ep_open_lt_unique) >>
      simp[]) >>
  qspecl_then [‘i'’, ‘i’, ‘p’] mp_tac (Q.GENL [‘i’, ‘i'’, ‘p’] ep_open_lt_unique) >>
  simp[]
QED

(* The channel f holds at a prefix of the trace and at a round boundary,
   in the same episode, is the same (honestEchoL0TraceWrap's, local there) *)
Theorem run_chan_same_ev:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ qfresh w0 ∧
  pftrace lfd pol ifds m w0 io ∧ LPREFIX (fromList evs) io ∧ world_at w0 evs = SOME w ∧
  ALOOKUP (SND (l0_ep_st (0, []) evs)) f = SOME j ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 k))) f = SOME j ∧
  l0_chan_of w f = SOME c ∧ l0_chan_of (rworld lfd pol ifds m w0 k) f = SOME ck ⇒
  ck = c
Proof
  strip_tac >>
  drule_all pftrace_locate >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  ‘revs lfd pol ifds m w0 k ≼ revs lfd pol ifds m w0 M’
    by (drule revs_prefix >> disch_then (qspecl_then [‘M − k’, ‘k’] mp_tac) >>
        ‘k + (M − k) = M’ by decide_tac >> simp[]) >>
  ‘∀n. world_at w0 (revs lfd pol ifds m w0 n) = SOME (rworld lfd pol ifds m w0 n) ∧
       faithful w0 (revs lfd pol ifds m w0 n)’ by metis_tac[run_world_at] >>
  ‘evs ≼ revs lfd pol ifds m w0 k ∨ revs lfd pol ifds m w0 k ≼ evs’
    by metis_tac[prefixes_is_prefix_total] >>
  fs[IS_PREFIX_APPEND]
  >- (‘¬EXISTS (ep_ends f) l''’ by metis_tac[idx_stable] >>
      ‘EVERY (λe. ¬ep_ends f e) l''’ by fs[EVERY_MEM, EXISTS_MEM] >>
      ‘faithful w0 (evs ++ l'')’ by metis_tac[] >>
      ‘world_at w0 (evs ++ l'') = SOME (rworld lfd pol ifds m w0 k)’ by metis_tac[] >>
      drule_all world_chan_back >> strip_tac >> gvs[]) >>
  ‘¬EXISTS (ep_ends f) l''’ by metis_tac[idx_stable] >>
  ‘EVERY (λe. ¬ep_ends f e) l''’ by fs[EVERY_MEM, EXISTS_MEM] >>
  ‘faithful w0 (revs lfd pol ifds m w0 k ++ l'')’ by metis_tac[faithful_prefix] >>
  ‘world_at w0 (revs lfd pol ifds m w0 k ++ l'') = SOME w’ by metis_tac[] >>
  drule_all world_chan_back >> strip_tac >> gvs[]
QED

(* ------------------------------------------------------------------------
   Episode j on the trace: open on every prefix that has its accept
   ------------------------------------------------------------------------ *)

Theorem lprefix_total:
  LPREFIX (fromList a) io ∧ LPREFIX (fromList b) io ⇒ a ≼ b ∨ b ≼ a
Proof
  rw[LPREFIX_fromList_LNTH] >>
  ‘∀i. i < LENGTH a ∧ i < LENGTH b ⇒ EL i a = EL i b’
    by (rpt strip_tac >>
        qpat_x_assum ‘∀i. i < LENGTH a ⇒ _’ (qspec_then ‘i’ mp_tac) >>
        qpat_x_assum ‘∀i. i < LENGTH b ⇒ _’ (qspec_then ‘i’ mp_tac) >> simp[]) >>
  Cases_on ‘LENGTH a ≤ LENGTH b’
  >- (disj1_tac >> simp[IS_PREFIX_EQ_TAKE] >> qexists_tac ‘LENGTH a’ >>
      simp[LIST_EQ_REWRITE, EL_TAKE]) >>
  disj2_tac >> simp[IS_PREFIX_EQ_TAKE] >> qexists_tac ‘LENGTH b’ >>
  simp[LIST_EQ_REWRITE, EL_TAKE]
QED

Theorem ep_open_lt:
  ep_open j evs ⇒ j < LENGTH (l0_accepted evs)
Proof
  strip_tac >> drule ep_open_ext >> disch_then (qspec_then ‘[]’ mp_tac) >> simp[]
QED

Theorem ep_open_all:
  LPREFIX (fromList evs) io ∧ ep_open j evs ∧ ¬ep_ended j io ⇒
  ∀q. LPREFIX (fromList q) io ∧ j < LENGTH (l0_accepted q) ⇒
      ep_open j q ∧ EL j (l0_accepted q) = EL j (l0_accepted evs)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  ‘evs ≼ q ∨ q ≼ evs’ by metis_tac[lprefix_total] >> fs[IS_PREFIX_APPEND]
  >- (Cases_on ‘EXISTS (ep_ends (EL j (l0_accepted evs))) l’
      >- (‘ep_closed j (evs ++ l)’ by (irule ep_open_closed >> simp[]) >>
          qpat_x_assum ‘¬ep_ended _ _’ mp_tac >> rewrite_tac[ep_ended_def] >>
          metis_tac[]) >>
      qpat_x_assum ‘q = _’ SUBST_ALL_TAC >>
      drule_all ep_open_ext >> simp[]) >>
  qpat_x_assum ‘evs = _’ SUBST_ALL_TAC >>
  drule ep_open_prefix >> disch_then drule >> simp[]
QED

Theorem MEM_FConn_log_conns[local]:
  ∀l. MEM (FConn f) l ⇔ MEM f (log_conns l)
Proof
  Induct >> simp[log_conns_def] >> Cases >> simp[]
QED

(* The round a of episode j's accept: FConn f there and never after *)
Theorem run_acc_round:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ pftrace lfd pol ifds m w0 io ∧
  LPREFIX (fromList evs) io ∧ ep_open j evs ∧ ¬ep_ended j io ∧ EL j (l0_accepted evs) = f ⇒
  ∃a. MEM (FConn f) (rlog lfd pol ifds m w0 a) ∧
      (∀k. a < k ⇒ ¬MEM (FConn f) (rlog lfd pol ifds m w0 k)) ∧
      ∀n. a < n ⇒ j < LENGTH (l0_accepted (revs lfd pol ifds m w0 n))
Proof
  strip_tac >>
  ‘∀n. l0_accepted (revs lfd pol ifds m w0 (SUC n)) =
       l0_accepted (revs lfd pol ifds m w0 n) ++ log_conns (rlog lfd pol ifds m w0 n)’
    by (drule_all run_acc >> strip_tac >> simp[GENLIST, FLAT_SNOC]) >>
  ‘l0_accepted (revs lfd pol ifds m w0 0) = []’
    by (drule_all run_acc >> strip_tac >> simp[]) >>
  ‘∀d n. LENGTH (l0_accepted (revs lfd pol ifds m w0 n)) ≤
         LENGTH (l0_accepted (revs lfd pol ifds m w0 (n + d)))’
    by (Induct >> simp[] >> rpt strip_tac >>
        first_x_assum (qspec_then ‘n’ mp_tac) >> simp[ADD_CLAUSES]) >>
  ‘∀a b. a ≤ b ⇒ LENGTH (l0_accepted (revs lfd pol ifds m w0 a)) ≤
                 LENGTH (l0_accepted (revs lfd pol ifds m w0 b))’
    by (rpt strip_tac >> first_x_assum (qspecl_then [‘b − a’, ‘a’] mp_tac) >> simp[]) >>
  ‘∀q. LPREFIX (fromList q) io ∧ j < LENGTH (l0_accepted q) ⇒
       ep_open j q ∧ EL j (l0_accepted q) = f’
    by (qpat_x_assum ‘EL j _ = f’ (SUBST1_TAC o SYM) >>
        metis_tac[ep_open_all]) >>
  drule_all pftrace_locate >> disch_then (qspec_then ‘0’ strip_assume_tac) >>
  ‘j < LENGTH (l0_accepted (revs lfd pol ifds m w0 M))’
    by (drule ep_open_lt >> fs[IS_PREFIX_APPEND]) >>
  ‘∃n. j < LENGTH (l0_accepted (revs lfd pol ifds m w0 n)) ∧
       ∀n'. n' < n ⇒ ¬(j < LENGTH (l0_accepted (revs lfd pol ifds m w0 n')))’
    by (ho_match_mp_tac WOP >> qexists_tac ‘M’ >> first_assum ACCEPT_TAC) >>
  Cases_on ‘n’ >- gvs[] >> rename1 ‘SUC a’ >>
  ‘LENGTH (l0_accepted (revs lfd pol ifds m w0 a)) ≤ j’
    by (qpat_x_assum ‘∀n'. n' < SUC a ⇒ _’ (qspec_then ‘a’ mp_tac) >> simp[]) >>
  qexists_tac ‘a’ >> rpt conj_tac
  >- (‘EL j (l0_accepted (revs lfd pol ifds m w0 (SUC a))) = f’
        by (qpat_x_assum ‘∀q. _ ⇒ ep_open j q ∧ _’ (qspec_then ‘revs lfd pol ifds m w0 (SUC a)’ mp_tac) >>
            impl_tac >- (conj_tac >- (irule pftrace_revs >> conj_tac >> first_assum ACCEPT_TAC) >>
                         first_assum ACCEPT_TAC) >>
            simp[]) >>
      simp[MEM_FConn_log_conns] >>
      qpat_x_assum ‘EL j _ = f’ mp_tac >> qpat_x_assum ‘j < LENGTH _’ mp_tac >>
      qpat_assum ‘∀n. l0_accepted (revs _ _ _ _ _ (SUC n)) = _’ (fn th => rewrite_tac[th]) >>
      simp[EL_APPEND2, MEM_EL] >> rpt strip_tac >>
      qexists_tac ‘j − LENGTH (l0_accepted (revs lfd pol ifds m w0 a))’ >> simp[])
  >- (rpt strip_tac >>
      qpat_x_assum ‘MEM (FConn f) _’ mp_tac >> simp[MEM_FConn_log_conns, MEM_EL] >>
      rpt strip_tac >> rename1 ‘p < LENGTH (log_conns _)’ >>
      qabbrev_tac ‘i' = LENGTH (l0_accepted (revs lfd pol ifds m w0 k)) + p’ >>
      ‘j < LENGTH (l0_accepted (revs lfd pol ifds m w0 k))’
        by (qpat_assum ‘∀a b. a ≤ b ⇒ _’ (qspecl_then [‘SUC a’, ‘k’] mp_tac) >>
            impl_tac >- simp[] >>
            qpat_assum ‘j < LENGTH (l0_accepted (revs _ _ _ _ _ (SUC a)))’ mp_tac >>
            decide_tac) >>
      ‘i' < LENGTH (l0_accepted (revs lfd pol ifds m w0 (SUC k))) ∧
       EL i' (l0_accepted (revs lfd pol ifds m w0 (SUC k))) = f’
        by (qpat_assum ‘∀n. l0_accepted (revs _ _ _ _ _ (SUC n)) = _’ (fn th => rewrite_tac[th]) >>
            simp[Abbr ‘i'’, EL_APPEND2]) >>
      ‘ep_open j (revs lfd pol ifds m w0 (SUC k)) ∧
       EL j (l0_accepted (revs lfd pol ifds m w0 (SUC k))) = f’
        by (qpat_x_assum ‘∀q. _ ⇒ ep_open j q ∧ _’
              (qspec_then ‘revs lfd pol ifds m w0 (SUC k)’ mp_tac) >>
            impl_tac
            >- (conj_tac >- (irule pftrace_revs >> conj_tac >> first_assum ACCEPT_TAC) >>
                qpat_assum ‘∀n. l0_accepted (revs _ _ _ _ _ (SUC n)) = _’ (fn th => rewrite_tac[th]) >>
                simp[]) >>
            simp[]) >>
      ‘j < i'’ by simp[Abbr ‘i'’] >>
      drule_all ep_open_lt_unique >> simp[]) >>
  rpt strip_tac >>
  qpat_assum ‘∀a b. a ≤ b ⇒ _’ (qspecl_then [‘SUC a’, ‘n’] mp_tac) >>
  impl_tac >- simp[] >>
  qpat_assum ‘j < LENGTH (l0_accepted (revs _ _ _ _ _ (SUC a)))’ mp_tac >>
  decide_tac
QED

(* ------------------------------------------------------------------------
   EOF on episode j's fd: its channel ended, or a hard recv error
   ------------------------------------------------------------------------ *)

(* MAIN: L1 has f at EOF at round n while episode j on f is open there:
   the round that put f at EOF fetched FEof f (f's channel is then at
   peer EOF or broken, with an empty inbox: ch_frozen) or FReset f (a hard
   recv error of episode j) *)
Theorem kv_eof_excuse:
  kv_run lfdn pol w0 ∧ qfresh w0 ∧ pftrace (n2w lfdn) pol KI KS w0 io ∧
  LPREFIX (fromList evs) io ∧ ep_open j evs ∧ ¬ep_ended j io ∧
  EL j (l0_accepted evs) = f ∧ world_at w0 evs = SOME w ∧ l0_chan_of w f = SOME c ∧
  MEM f (rstate (n2w lfdn) pol KI KS w0 n).eof ∧
  j < LENGTH (l0_accepted (revs (n2w lfdn) pol KI KS w0 n)) ⇒
  ch_frozen w0 io c ∨ ep_hard_err j io
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  ‘run_ok (n2w lfdn) pol KI KS w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0) ∧
   (∀n. SND (pcm (n2w lfdn) pol KI KS w0 n) + 1 < dimword (:64))’ by fs[kv_run_def] >>
  ‘oassm (n2w lfdn) pol KI KS w0’ by fs[oassm_def] >>
  ‘∀i. pown (n2w lfdn) (rstate (n2w lfdn) pol KI KS w0 i)’
    by metis_tac[run_pown, kv_run_hyp] >>
  qpat_assum ‘run_ok _ _ _ _ _’ (fn th => mp_tac (MATCH_MP run_eof_origin th)) >>
  disch_then (qspec_then ‘n’ mp_tac) >> impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (qx_choose_then ‘k’ (fn th => MAP_EVERY assume_tac (CONJUNCTS th))) >>
  ‘∀i. k < i ∧ i ≤ n ⇒ MEM f (MAP SND (rstate (n2w lfdn) pol KI KS w0 i).b.tbl)’
    by (rpt strip_tac >>
        ‘MEM f (rstate (n2w lfdn) pol KI KS w0 i).eof’
          by (qpat_x_assum ‘∀i. k < i ∧ i ≤ n ⇒ MEM f _’ irule >> simp[]) >>
        qpat_x_assum ‘∀i. pown _ _’ (qspec_then ‘i’ mp_tac) >> simp[pown_def] >>
        strip_tac >> qpat_x_assum ‘∀f. inb_of _ f ≠ [] ∨ _ ⇒ _’ irule >> simp[]) >>
  ‘∃j1. ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol KI KS w0 k))) f = SOME j1’
    by (irule run_known_ep >> simp[] >> irule run_fetched_known >> simp[]) >>
  ‘ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol KI KS w0 n))) f = SOME j1’
    by (irule keep_to_round >> simp[] >> qexists_tac ‘k’ >> simp[] >> rpt strip_tac >>
        qpat_x_assum ‘∀i. k < i ∧ i ≤ n ⇒ MEM f (MAP SND _)’ (qspec_then ‘i’ mp_tac) >>
        simp[]) >>
  ‘j1 = j’
    by (drule ep_state_open >> strip_tac >>
        ‘ep_open j (revs (n2w lfdn) pol KI KS w0 n) ∧
         EL j (l0_accepted (revs (n2w lfdn) pol KI KS w0 n)) = EL j (l0_accepted evs)’
          by (qspecl_then [‘evs’, ‘io’, ‘j’] mp_tac (Q.GENL [‘evs’, ‘io’, ‘j’] ep_open_all) >>
              impl_tac >- simp[] >>
              disch_then irule >> simp[] >> irule pftrace_revs >> simp[]) >>
        irule ep_open_unique >> qexists_tac ‘revs (n2w lfdn) pol KI KS w0 n’ >> simp[]) >>
  qpat_x_assum ‘j1 = j’ SUBST_ALL_TAC >>
  qpat_x_assum ‘ALOOKUP (SND (l0_ep_st _ (revs _ _ _ _ _ n))) f = _’ kall_tac >>
  qpat_x_assum ‘MEM (FEof f) _ ∨ _’ strip_assume_tac
  >- ((* FEof f in round k: f's channel is at peer EOF or broken at SUC k *)
      disj1_tac >>
      ‘¬MEM f (rstate (n2w lfdn) pol KI KS w0 k).b.closing’
        by (irule run_feof_not_closing >> simp[]) >>
      ‘∃c1. l0_chan_of (rworld (n2w lfdn) pol KI KS w0 (SUC k)) f = SOME c1 ∧
            deof c1 (rworld (n2w lfdn) pol KI KS w0 (SUC k))’
        by (irule run_deof >> simp[]) >>
      ‘ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol KI KS w0 (SUC k)))) f = SOME j’
        by (irule keep_to_round >> simp[] >> qexists_tac ‘k’ >> simp[] >> rpt strip_tac >>
            qpat_x_assum ‘∀i. k < i ∧ i ≤ n ⇒ MEM f (MAP SND _)’ (qspec_then ‘i’ mp_tac) >>
            simp[]) >>
      ‘ALOOKUP (SND (l0_ep_st (0, []) evs)) f = SOME j’
        by (irule ep_open_state >> simp[]) >>
      ‘c1 = c’
        by (qspecl_then [‘c’, ‘c1’, ‘evs’, ‘f’, ‘KI’, ‘io’, ‘j’, ‘SUC k’, ‘n2w lfdn’, ‘KS’,
                         ‘pol’, ‘w’, ‘w0’] mp_tac
              (Q.GENL [‘c’, ‘ck’, ‘evs’, ‘f’, ‘ifds’, ‘io’, ‘j’, ‘k’, ‘lfd’, ‘m’, ‘pol’, ‘w’,
                       ‘w0’] run_chan_same_ev) >>
            simp[]) >>
      qpat_x_assum ‘c1 = c’ SUBST_ALL_TAC >>
      simp[ch_frozen_def] >>
      qexistsl_tac [‘revs (n2w lfdn) pol KI KS w0 (SUC k)’, ‘rworld (n2w lfdn) pol KI KS w0 (SUC k)’] >>
      conj_tac >- (irule pftrace_revs >> simp[]) >>
      conj_tac >- (drule run_world_at >> simp[]) >>
      qpat_x_assum ‘deof _ _’ mp_tac >> simp[deof_def] >> strip_tac >> simp[]) >>
  (* FReset f in round k: a hard recv error *)
  disj2_tac >>
  ‘hard_recv f (rrev (n2w lfdn) pol KI KS w0 k)’
    by (qpat_assum ‘run_ok _ _ _ _ _’ (fn th => strip_assume_tac (Q.SPEC ‘k’ (MATCH_MP prun_round' th))) >>
        drule pround_freset >> disch_then irule >> simp[] >>
        drule_all winv_run >> simp[]) >>
  qpat_x_assum ‘pftrace _ _ _ _ _ _’ assume_tac >>
  qpat_x_assum ‘oassm _ _ _ _ _’ assume_tac >>
  drule recv_excuse_j0 >> disch_then drule >> disch_then drule >>
  disch_then (qspec_then ‘k’ mp_tac) >> simp[]
QED

(* ------------------------------------------------------------------------
   f stays in L1's table, under one handle, without EOF
   ------------------------------------------------------------------------ *)

Theorem pround_tbl_keep[local]:
  pround lfd pol hs (w, ps) acts = SOME (sn, (w', ps'), log, evs) ∧ winv w ∧
  fkeep lfd h f ps ⇒
  ALOOKUP ps'.b.tbl h = SOME f
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >> gvs[] >>
  drule_all pacts_f >> strip_tac >>
  drule honestL1PFOblTheory.pf_tail_tbl >> strip_tac >> fs[fkeep_def]
QED

(* MAIN: while episode j on f stays open on the trace and neither its
   channel freezes nor a hard error hits it, L1 connected f in round a
   (and never again), and from some round t on keeps f under a handle h *)
Theorem kv_held_forever:
  kv_run lfdn pol w0 ∧ qfresh w0 ∧ pftrace (n2w lfdn) pol KI KS w0 io ∧
  LPREFIX (fromList evs) io ∧ ep_open j evs ∧ ¬ep_ended j io ∧
  EL j (l0_accepted evs) = f ∧ world_at w0 evs = SOME w ∧ l0_chan_of w f = SOME c ∧
  ¬ch_frozen w0 io c ∧ ¬ep_hard_err j io ⇒
  ∃a t h. a < t ∧ MEM (FConn f) (rlog (n2w lfdn) pol KI KS w0 a) ∧
          (∀k. a < k ⇒ ¬MEM (FConn f) (rlog (n2w lfdn) pol KI KS w0 k)) ∧
          (∀k. a < k ⇒ j < LENGTH (l0_accepted (revs (n2w lfdn) pol KI KS w0 k))) ∧
          (∀k. a < k ⇒ MEM f (MAP SND (rstate (n2w lfdn) pol KI KS w0 k).b.tbl) ∨
                       MEM f (rstate (n2w lfdn) pol KI KS w0 k).acq) ∧
          ∀k. t ≤ k ⇒ fkeep (n2w lfdn) h f (rstate (n2w lfdn) pol KI KS w0 k)
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  ‘run_ok (n2w lfdn) pol KI KS w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0) ∧
   (∀n. SND (pcm (n2w lfdn) pol KI KS w0 n) + 1 < dimword (:64))’ by fs[kv_run_def] >>
  ‘fds_lt w0’ by fs[winv_def] >>
  ‘∀n h f. ALOOKUP (rstate (n2w lfdn) pol KI KS w0 n).b.tbl h = SOME f ∧
           ¬MEM f (rstate (n2w lfdn) pol KI KS w0 n).eof ⇒
           fkeep (n2w lfdn) h f (rstate (n2w lfdn) pol KI KS w0 n)’
    by (match_mp_tac fkeep_run >> simp[]) >>
  ‘∀i. pown (n2w lfdn) (rstate (n2w lfdn) pol KI KS w0 i)’
    by metis_tac[run_pown, kv_run_hyp] >>
  ‘∃a. MEM (FConn f) (rlog (n2w lfdn) pol KI KS w0 a) ∧
       (∀k. a < k ⇒ ¬MEM (FConn f) (rlog (n2w lfdn) pol KI KS w0 k)) ∧
       ∀n. a < n ⇒ j < LENGTH (l0_accepted (revs (n2w lfdn) pol KI KS w0 n))’
    by (irule run_acc_round >> simp[] >>
        qexistsl_tac [‘evs’, ‘io’] >> simp[]) >>
  (* f is never at EOF after round a *)
  ‘∀k. a < k ⇒ ¬MEM f (rstate (n2w lfdn) pol KI KS w0 k).eof’
    by (rpt strip_tac >>
        qspecl_then [‘c’, ‘evs’, ‘f’, ‘io’, ‘j’, ‘lfdn’, ‘k’, ‘pol’, ‘w’, ‘w0’] mp_tac
          (Q.GENL [‘c’, ‘evs’, ‘f’, ‘io’, ‘j’, ‘lfdn’, ‘n’, ‘pol’, ‘w’, ‘w0’] kv_eof_excuse) >>
        simp[]) >>
  (* f is pre-accepted at SUC a, and L1 takes it at t *)
  ‘MEM f (rstate (n2w lfdn) pol KI KS w0 (SUC a)).acq’
    by (qpat_assum ‘run_ok _ _ _ _ _’
          (fn th => strip_assume_tac (Q.SPEC ‘a’ (MATCH_MP prun_round' th))) >>
        drule pround_conn_acq >> disch_then irule >> first_assum ACCEPT_TAC) >>
  drule_all kv_acq_taken >> strip_tac >> rename1 ‘SUC a < t’ >>
  ‘∃h. ALOOKUP (rstate (n2w lfdn) pol KI KS w0 t).b.tbl h = SOME f’
    by (qpat_x_assum ‘MEM f (MAP SND _)’ mp_tac >> simp[MEM_MAP, EXISTS_PROD] >>
        strip_tac >> qexists_tac ‘p_1’ >> irule ALOOKUP_ALL_DISTINCT_MEM >> simp[] >>
        qpat_x_assum ‘∀i. pown _ _’ (qspec_then ‘t’ mp_tac) >> simp[pown_def]) >>
  ‘∀d. ALOOKUP (rstate (n2w lfdn) pol KI KS w0 (t + d)).b.tbl h = SOME f’
    by (Induct >- simp[] >>
        ‘fkeep (n2w lfdn) h f (rstate (n2w lfdn) pol KI KS w0 (t + d))’
          by (qpat_assum ‘∀n h f. _ ⇒ fkeep _ _ _ _’ irule >> simp[]) >>
        qpat_assum ‘run_ok _ _ _ _ _’
          (fn th => strip_assume_tac (Q.SPEC ‘t + d’ (MATCH_MP prun_round' th))) >>
        drule pround_tbl_keep >> disch_then (qspecl_then [‘h’, ‘f’] mp_tac) >>
        impl_tac >- (simp[] >> drule_all winv_run >> simp[]) >>
        simp[ADD_CLAUSES]) >>
  ‘∀k. t ≤ k ⇒ fkeep (n2w lfdn) h f (rstate (n2w lfdn) pol KI KS w0 k)’
    by (rpt strip_tac >>
        qpat_assum ‘∀n h f. _ ⇒ fkeep _ _ _ _’ irule >> simp[] >>
        qpat_x_assum ‘∀d. ALOOKUP _ h = SOME f’ (qspec_then ‘k − t’ mp_tac) >>
        ‘t + (k − t) = k’ by decide_tac >> simp[]) >>
  qexistsl_tac [‘a’, ‘t’, ‘h’] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- decide_tac >>
  rpt strip_tac >> Cases_on ‘t ≤ k’
  >- (disj1_tac >>
      qpat_x_assum ‘∀k. t ≤ k ⇒ fkeep _ _ _ _’ (qspec_then ‘k’ mp_tac) >>
      simp[fkeep_def] >> strip_tac >> simp[MEM_MAP, EXISTS_PROD] >>
      qexists_tac ‘h’ >> irule ALOOKUP_MEM >> first_assum ACCEPT_TAC) >>
  disj2_tac >> qpat_x_assum ‘∀i. SUC a ≤ i ∧ i < t ⇒ _’ irule >> decide_tac
QED
