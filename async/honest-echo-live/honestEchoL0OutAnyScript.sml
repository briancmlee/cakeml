(*
  The output chain for client j's outgoing stream at ANY later round
  (design/47 D, assembly): from a round n at which L1 holds f (channel c,
  client j, episode j0), for every N ≥ n, client j's outgoing stream at N
  eventually reaches the kernel on c, or episode j0 shows a hard error or
  a D23 timeout on the trace.

  If f stays held to N: out_chain_all (no re-connect of f while held:
  held_window).  Else at the first release (round k): release_chain (the
  kernel has taken everything written by round k + 1, or an excuse), and
  client j's stream is final from k + 1 on (released_frozen) -- this
  covers an fd number released and re-connected in one round.

  MAIN: out_chain_any.
*)
Theory honestEchoL0OutAny
Ancestors
  honestEchoL0OutAll honestEchoL0Frozen honestEchoL0Chain honestEchoL0Excuse
  honestEchoL0SrvOut honestEchoL0Stop
  asyncHLSimWorld asyncHLModel
  honestEchoL0Obl honestL1PFObl honestL1PFBroken honestL1PFClient honestL1PFDead
  honestL1PFFlushLive honestL1PFFlush honestL1PFOutLive honestL1PFOut honestL1PFLive
  honestL1PFRefine
Libs
  preamble


(* A round in which L1 holds f on the same channel throughout does not
   re-connect f (from run_cl_stable's proof) *)
Theorem run_noconn:
  oassm lfd pol ifds m w0 ∧
  (MEM f (MAP SND (rstate lfd pol ifds m w0 k).b.tbl) ∨
   MEM f (rstate lfd pol ifds m w0 k).b.closing) ∧
  l0_chan_of (rworld lfd pol ifds m w0 k) f = SOME c ∧
  l0_chan_of (rworld lfd pol ifds m w0 (SUC k)) f = SOME c ⇒
  ¬MEM (FConn f) (rlog lfd pol ifds m w0 k)
Proof
  rw[oassm_def] >>
  ‘plog lfd pol ifds m w0 k = rlog lfd pol ifds m w0 k’ by (irule plog_rlog >> simp[]) >>
  pop_assum (SUBST1_TAC o SYM) >>
  drule prun_parts >> disch_then (fn th => strip_assume_tac (Q.SPEC ‘k’ th) >>
                                            strip_assume_tac (Q.SPEC ‘SUC k’ th)) >>
  mp_tac (Q.INST [‘N’ |-> ‘SUC k’] l1pf_round_noconn) >> simp[] >>
  disch_then (qspecl_then [‘k’, ‘rhist lfd pol ifds m w0 k’,
                           ‘(rworld lfd pol ifds m w0 k, rstate lfd pol ifds m w0 k)’,
                           ‘revs lfd pol ifds m w0 k’, ‘logs’,
                           ‘rhist lfd pol ifds m w0 (SUC k)’,
                           ‘(rworld lfd pol ifds m w0 (SUC k),
                             rstate lfd pol ifds m w0 (SUC k))’,
                           ‘revs lfd pol ifds m w0 (SUC k)’, ‘logs'’] mp_tac) >>
  simp[]
QED

(* Without a re-connect of f in round k, f keeps its client *)
Theorem pcm_keep:
  run_ok lfd pol ifds m w0 ∧ ¬MEM (FConn f) (rlog lfd pol ifds m w0 k) ∧
  ALOOKUP (FST (pcm lfd pol ifds m w0 k)) f = SOME j ⇒
  ALOOKUP (FST (pcm lfd pol ifds m w0 (SUC k))) f = SOME j
Proof
  strip_tac >>
  ‘plog lfd pol ifds m w0 k = rlog lfd pol ifds m w0 k’ by (irule plog_rlog >> simp[]) >>
  simp[pcm_def] >> Cases_on ‘pcm lfd pol ifds m w0 k’ >> fs[] >>
  Cases_on ‘arrs lfd (q, r) (rlog lfd pol ifds m w0 k)’ >> rename1 ‘_ = (as, ck)’ >>
  PairCases_on ‘ck’ >> simp[] >>
  drule arrs_fconn >> strip_tac >> gvs[ALOOKUP_APPEND] >>
  ‘ALOOKUP new f = NONE’ by (simp[ALOOKUP_NONE] >> metis_tac[]) >>
  simp[]
QED

(* While L1 holds f, f is not re-connected and keeps its client *)
Theorem held_window:
  oassm lfd pol ifds m w0 ∧ l0_chan_of (rworld lfd pol ifds m w0 n) f = SOME c ∧
  ALOOKUP (FST (pcm lfd pol ifds m w0 n)) f = SOME j ⇒
  ∀Kn. (∀i. n ≤ i ∧ i ≤ Kn ⇒
           MEM f (MAP SND (rstate lfd pol ifds m w0 i).b.tbl) ∨
           MEM f (rstate lfd pol ifds m w0 i).b.closing) ⇒
      (∀i. n ≤ i ∧ i < Kn ⇒ ¬MEM (FConn f) (rlog lfd pol ifds m w0 i)) ∧
      (∀i. n ≤ i ∧ i ≤ Kn ⇒ ALOOKUP (FST (pcm lfd pol ifds m w0 i)) f = SOME j)
Proof
  rpt gen_tac >> strip_tac >> qx_gen_tac ‘Kn’ >> strip_tac >>
  ‘∀i. n ≤ i ∧ i ≤ Kn ⇒ l0_chan_of (rworld lfd pol ifds m w0 i) f = SOME c’
    by (rpt strip_tac >>
        qpat_assum ‘l0_chan_of (rworld _ _ _ _ _ n) f = SOME c’ assume_tac >>
        drule held_chan_stretch >> disch_then drule >>
        disch_then (qspec_then ‘i − n’ mp_tac) >>
        impl_tac
        >- (rpt strip_tac >> qpat_x_assum ‘∀i. n ≤ i ∧ i ≤ Kn ⇒ _’ irule >> fs[]) >>
        ‘n + (i − n) = i’ by fs[] >> simp[]) >>
  ‘∀i. n ≤ i ∧ i < Kn ⇒ ¬MEM (FConn f) (rlog lfd pol ifds m w0 i)’
    by (rpt gen_tac >> strip_tac >>
        ‘MEM f (MAP SND (rstate lfd pol ifds m w0 i).b.tbl) ∨
         MEM f (rstate lfd pol ifds m w0 i).b.closing’
          by (qpat_x_assum ‘∀i. n ≤ i ∧ i ≤ Kn ⇒ MEM _ _ ∨ _’ irule >> fs[]) >>
        ‘l0_chan_of (rworld lfd pol ifds m w0 i) f = SOME c ∧
         l0_chan_of (rworld lfd pol ifds m w0 (SUC i)) f = SOME c’
          by (conj_tac >> qpat_x_assum ‘∀i. n ≤ i ∧ i ≤ Kn ⇒ l0_chan_of _ _ = _’ irule >>
              fs[]) >>
        irule run_noconn >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        TRY (qexists_tac ‘c’ >> fs[] >> NO_TAC) >> fs[]) >>
  simp[] >>
  ‘∀d. n + d ≤ Kn ⇒ ALOOKUP (FST (pcm lfd pol ifds m w0 (n + d))) f = SOME j’
    by (Induct >> simp[] >> strip_tac >>
        ‘n + SUC d = SUC (n + d)’ by simp[] >> pop_assum SUBST1_TAC >>
        irule pcm_keep >> rpt conj_tac >>
        TRY (fs[oassm_def] >> NO_TAC) >>
        TRY (qpat_x_assum ‘∀i. n ≤ i ∧ i < Kn ⇒ _’ irule >> simp[] >> NO_TAC) >>
        qpat_x_assum ‘n + d ≤ Kn ⇒ _’ irule >> simp[]) >>
  rpt strip_tac >> first_x_assum (qspec_then ‘i − n’ mp_tac) >> simp[]
QED

(* A held fd's client has a client record in the server's state *)
Theorem held_client_lt:
  echo_run lfdn pol w0 ∧
  (MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 n).b.tbl) ∨
   MEM f (rstate (n2w lfdn) pol EI ES w0 n).b.closing) ∧
  ALOOKUP (FST (pcm (n2w lfdn) pol EI ES w0 n)) f = SOME j ⇒
  j < LENGTH (FST (hst (n2w lfdn) EI ES PSK n)).clients
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  ‘pown (n2w lfdn) (rstate (n2w lfdn) pol EI ES w0 n)’
    by metis_tac[run_pown, echo_run_hyp] >>
  ‘¬MEM f (rstate (n2w lfdn) pol EI ES w0 n).acq’
    by (gvs[pown_def, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  drule_then (qspec_then ‘n’ strip_assume_tac) echo_sim >>
  Cases_on ‘hst (n2w lfdn) EI ES PSK n’ >> rename1 ‘_ = (s2, hs)’ >>
  ‘hsim0 (n2w lfdn) (gstate EI ES V1 n)
     (s2, hs_of (rstate (n2w lfdn) pol EI ES w0 n))’ by fs[hsim_def] >>
  ‘pv_rel (n2w lfdn) (FST (pcm (n2w lfdn) pol EI ES w0 n))
     (rstate (n2w lfdn) pol EI ES w0 n) s2’ by fs[] >>
  ‘j < (rstate (n2w lfdn) pol EI ES w0 n).b.nxt’
    by (irule client_taken >> metis_tac[]) >>
  fs[hsim0_def, hs_of_def] >> gvs[]
QED

(* The release step: L1 holds f from n to k and releases it in round k;
   the kernel has then taken all the server wrote to f's client by round
   k + 1, or episode j0 shows an output excuse *)
Theorem release_chain:
  oassm lfd pol ifds m w0 ∧ pftrace lfd pol ifds m w0 io ∧ f ≠ lfd ∧ n ≤ k ∧
  (∀i. n ≤ i ∧ i ≤ k ⇒
       MEM f (MAP SND (rstate lfd pol ifds m w0 i).b.tbl) ∨
       MEM f (rstate lfd pol ifds m w0 i).b.closing) ∧
  ¬MEM f (MAP SND (rstate lfd pol ifds m w0 (SUC k)).b.tbl) ∧
  ¬MEM f (rstate lfd pol ifds m w0 (SUC k)).b.closing ∧
  l0_chan_of (rworld lfd pol ifds m w0 n) f = SOME c ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 n))) f = SOME j0 ⇒
  csent (rworld lfd pol ifds m w0 (SUC k)) c =
    oout lfd pol ifds m w0 (cl (FST (pcm lfd pol ifds m w0 k)) f) (SUC k) ∨
  ep_hard_err j0 io ∨ ep_timed_out pf_sendwait j0 io
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  ‘run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0)’ by fs[oassm_def] >>
  ‘l0_chan_of (rworld lfd pol ifds m w0 k) f = SOME c’
    by (qpat_assum ‘l0_chan_of (rworld _ _ _ _ _ n) f = SOME c’ assume_tac >>
        drule held_chan_stretch >> disch_then drule >> disch_then (qspec_then ‘k − n’ mp_tac) >>
        impl_tac
        >- (rpt strip_tac >> qpat_x_assum ‘∀i. n ≤ i ∧ i ≤ k ⇒ _’ irule >> fs[]) >>
        ‘n + (k − n) = k’ by fs[] >> simp[]) >>
  ‘MEM f (MAP SND (rstate lfd pol ifds m w0 k).b.tbl) ∨
   MEM f (rstate lfd pol ifds m w0 k).b.closing’
    by (qpat_x_assum ‘∀i. n ≤ i ∧ i ≤ k ⇒ _’ (qspec_then ‘k’ mp_tac) >> simp[]) >>
  ‘csent (rworld lfd pol ifds m w0 (SUC k)) c =
     oout lfd pol ifds m w0 (cl (FST (pcm lfd pol ifds m w0 k)) f) (SUC k) ∨
   MEM f (rstate lfd pol ifds m w0 k).b.gone ∨
   hard_send f (rrev lfd pol ifds m w0 k) ∨ rdrop lfd pol ifds m w0 k f’
    by (irule close_flushed >> fs[]) >>
  TRY (disj1_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
  disj2_tac >>
  TRY (qpat_x_assum ‘MEM f (rstate _ _ _ _ _ k).b.gone’ assume_tac >>
       drule run_gone_cause >> disch_then drule >>
       disch_then (qx_choose_then ‘k1’ (fn th => MAP_EVERY assume_tac (CONJUNCTS th))) >>
       Cases_on ‘n ≤ k1’
       >- (drule excuse_j0 >> disch_then drule >> disch_then drule >> disch_then drule >>
           disch_then (qspec_then ‘k1’ mp_tac) >> impl_tac >> simp[] >> rpt conj_tac >>
           TRY (first_assum ACCEPT_TAC) >> TRY decide_tac >>
           rpt strip_tac >> qpat_x_assum ‘∀i. n ≤ i ∧ i ≤ k ⇒ _’ (qspec_then ‘i’ mp_tac) >>
           fs[]) >>
       drule excuse_back >> disch_then drule >> disch_then drule >> disch_then drule >>
       disch_then (qspec_then ‘k1’ mp_tac) >> impl_tac >> simp[] >> rpt conj_tac >>
       TRY (first_assum ACCEPT_TAC) >> TRY decide_tac >>
       rpt strip_tac >> irule run_okeys_held >> fs[] >> NO_TAC) >>
  drule excuse_j0 >> disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (qspec_then ‘k’ mp_tac) >> impl_tac >> simp[] >> rpt conj_tac >>
  TRY (asm_rewrite_tac [] >> NO_TAC) >>
  rpt strip_tac >> qpat_x_assum ‘∀i. n ≤ i ∧ i ≤ k ⇒ _’ (qspec_then ‘i’ mp_tac) >> fs[]
QED

(* MAIN: the output chain, for client j's outgoing stream at any N ≥ n *)
Theorem out_chain_any:
  echo_run lfdn pol w0 ∧ qfresh w0 ∧ F1 (n2w lfdn) pol EI ES w0 ∧
  honestL1PFFlush$F2 w0 ∧ honestL1PFFlush$drains (n2w lfdn) pol EI ES w0 c ∧ nshut w0 ∧
  pftrace (n2w lfdn) pol EI ES w0 io ∧ f ≠ n2w lfdn ∧
  held f (rstate (n2w lfdn) pol EI ES w0 n) ∧
  l0_chan_of (rworld (n2w lfdn) pol EI ES w0 n) f = SOME c ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs (n2w lfdn) pol EI ES w0 n))) f = SOME j0 ∧
  ALOOKUP (FST (pcm (n2w lfdn) pol EI ES w0 n)) f = SOME j ∧ n ≤ N ⇒
  ∃n'. (EL j (FST (hst (n2w lfdn) EI ES PSK N)).clients).outgoing ≼
         csent (rworld (n2w lfdn) pol EI ES w0 n') c ∨
       ep_hard_err j0 io ∨ ep_timed_out pf_sendwait j0 io
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS (BETA_RULE th))) >>
  ‘oassm (n2w lfdn) pol EI ES w0’ by fs[oassm_def, echo_run_def] >>
  ‘j < LENGTH (FST (hst (n2w lfdn) EI ES PSK n)).clients’
    by (irule held_client_lt >> conj_tac >- (qexists_tac ‘f’ >> fs[]) >> fs[]) >>
  Cases_on ‘∀i. n ≤ i ∧ i ≤ N ⇒ held f (rstate (n2w lfdn) pol EI ES w0 i)’
  >- ((* held to N *)
      ‘(∀i. n ≤ i ∧ i < N ⇒ ¬MEM (FConn f) (rlog (n2w lfdn) pol EI ES w0 i)) ∧
       (∀i. n ≤ i ∧ i ≤ N ⇒ ALOOKUP (FST (pcm (n2w lfdn) pol EI ES w0 i)) f = SOME j)’
        by (drule held_window >> disch_then drule >> disch_then drule >>
            disch_then (qspec_then ‘N’ mp_tac) >>
            impl_tac
            >- (rpt strip_tac >>
                qpat_x_assum ‘∀i. n ≤ i ∧ i ≤ N ⇒ _’ (qspec_then ‘i’ mp_tac) >> simp[]) >>
            simp[]) >>
      irule out_chain_all >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (qexistsl_tac [‘f’, ‘n’]) >> fs[]) >>
  (* the first release *)
  fs[] >> rename1 ‘¬MEM f (MAP SND (rstate _ _ _ _ _ kc).b.tbl)’ >>
  ‘∃t. (n ≤ t ∧ t ≤ N ∧ ¬held f (rstate (n2w lfdn) pol EI ES w0 t)) ∧
       ∀t'. t' < t ⇒ ¬(n ≤ t' ∧ t' ≤ N ∧ ¬held f (rstate (n2w lfdn) pol EI ES w0 t'))’
    by (ho_match_mp_tac WOP >> metis_tac[]) >>
  ‘n < t’ by (CCONTR_TAC >> ‘t = n’ by simp[] >> fs[]) >>
  ‘∃k. t = SUC k’ by (qexists_tac ‘t − 1’ >> simp[]) >> rveq >>
  ‘∀i. n ≤ i ∧ i ≤ k ⇒
       MEM f (MAP SND (rstate (n2w lfdn) pol EI ES w0 i).b.tbl) ∨
       MEM f (rstate (n2w lfdn) pol EI ES w0 i).b.closing’
    by (rpt strip_tac >> qpat_x_assum ‘∀t'. t' < SUC k ⇒ _’ (qspec_then ‘i’ mp_tac) >>
        simp[]) >>
  ‘∀i. n ≤ i ∧ i ≤ k ⇒ ALOOKUP (FST (pcm (n2w lfdn) pol EI ES w0 i)) f = SOME j’
    by (qpat_assum ‘oassm _ _ _ _ _’ assume_tac >>
        drule held_window >> disch_then drule >> disch_then drule >>
        disch_then (qspec_then ‘k’ mp_tac) >> simp[]) >>
  ‘cl (FST (pcm (n2w lfdn) pol EI ES w0 k)) f = j’
    by (qpat_x_assum ‘∀i. n ≤ i ∧ i ≤ k ⇒ ALOOKUP _ _ = _’ (qspec_then ‘k’ mp_tac) >>
        simp[cl_def]) >>
  ‘csent (rworld (n2w lfdn) pol EI ES w0 (SUC k)) c =
     oout (n2w lfdn) pol EI ES w0 (cl (FST (pcm (n2w lfdn) pol EI ES w0 k)) f) (SUC k) ∨
   ep_hard_err j0 io ∨ ep_timed_out pf_sendwait j0 io’
    by (irule release_chain >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        TRY (qexists_tac ‘n’) >> fs[]) >>
  ‘(EL j (FST (hst (n2w lfdn) EI ES PSK N)).clients).outgoing =
   (EL j (FST (hst (n2w lfdn) EI ES PSK (SUC k))).clients).outgoing’
    by (irule released_frozen >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        TRY (qexists_tac ‘f’) >> fs[] >>
        qpat_x_assum ‘∀i. n ≤ i ∧ i ≤ k ⇒ MEM _ _ ∨ _’ (qspec_then ‘k’ mp_tac) >> simp[]) >>
  qexists_tac ‘SUC k’ >>
  TRY (disj1_tac >> fs[oout_def] >> NO_TAC) >>
  fs[]
QED
