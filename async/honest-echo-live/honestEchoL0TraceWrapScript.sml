(*
  The data half of echo_live_l0 at the statement's level (design/47 D,
  trace wrapper): for any prefix evs of the PF echo trace with episode j
  open and its fd on channel c, everything the peer has sent on c by evs
  is a prefix of what episode j has sent on some later prefix of the
  trace, unless c was flushed while episode j was open and before any
  close call on its fd (D32's flushed_open), or episode j shows a hard
  error or a D23 timeout.

  evs lies inside some round r (pftrace_locate, locate); trace_data gives
  the four cases.  Kernel sent bytes on c at round n' reach l0_sent j at
  round MAX n' (SUC r) (smono, episode_csent_le); a flush at a held round
  k is before any close call on f (held_noclose), on the same channel c
  (idx_stable, world_chan_back).

  TEMP COPY (remove when honestL1BStmts is resynced to final/L3-00):
  flushed_open below is verbatim from final/L3-00-statements 907c32fdc
  (kernel/statements/kernelStatementsScript.sml).

  MAIN: trace_wrap.
*)
Theory honestEchoL0TraceWrap
Ancestors
  honestEchoL0TraceData honestEchoL0CSentFree honestEchoL0NoClose
  honestEchoL0FlAt honestEchoL0AccOnce honestEchoL0Drains honestEchoL0Chain honestEchoL0Excuse
  honestEchoL0LiveOwn honestEchoL0Obl honestL1PFObl honestL1BFaith honestL1BStmts
  honestL1PFStream honestL1PFOutLive honestL1PFOut honestL1PFLive
  honestL1PFConnTrace honestL1PFFlush honestL0Part honestEchoL0KSent honestEchoL0Trace honestL1PFInv
  honestEchoL0Spec honestL0World
Libs
  preamble

(* D32 (user decision, amending D28): channel c broke and its unread input
   was discarded while episode j was open, before any close call on the
   episode's fd *)
Definition flushed_open_def:
  flushed_open w0 io j c ⇔
    ∃pre ev post f w.
      LPREFIX (fromList (pre ++ [ev] ++ post)) io ∧ LENGTH (l0_accepted pre) = j ∧
      l0_event_accepted ev = SOME f ∧ ¬EXISTS (l0_close_call f) post ∧
      world_at w0 (pre ++ [ev] ++ post) = SOME w ∧
      c < LENGTH w.chans ∧ (EL c w.chans).broken ∧ (EL c w.chans).inbox = []
End

(* ------------------------------------------------------------------------
   Small facts
   ------------------------------------------------------------------------ *)

Theorem close_call_closes[local]:
  l0_close_call f ev ⇒ closes_call f ev
Proof
  Cases_on ‘ev’ >> rw[l0_close_call_def, closes_call_def]
QED

Theorem no_close_call[local]:
  ¬EXISTS (closes_call f) l ⇒ ¬EXISTS (l0_close_call f) l
Proof
  rw[EVERY_MEM] >> metis_tac[close_call_closes]
QED

(* An open episode's accept, with its fd named by l0_accepted *)
Theorem ep_open_split:
  ep_open j evs ⇒
  ∃pre ev post.
    evs = pre ++ [ev] ++ post ∧ LENGTH (l0_accepted pre) = j ∧
    l0_event_accepted ev = SOME (EL j (l0_accepted evs)) ∧
    ¬EXISTS (ep_ends (EL j (l0_accepted evs))) post
Proof
  simp[ep_open_def] >> strip_tac >> rename1 ‘l0_event_accepted ev = SOME g’ >>
  qpat_x_assum ‘evs = _’ SUBST_ALL_TAC >>
  ‘l0_accepted (pre ++ [ev] ++ post) = l0_accepted pre ++ [g] ++ l0_accepted post’
    by fs[l0_accepted_def, FLAT_APPEND] >>
  ‘EL j (l0_accepted (pre ++ [ev] ++ post)) = g’
    by (qpat_x_assum ‘l0_accepted (pre ++ _ ++ _) = _’ SUBST1_TAC >>
        rw[] >> simp[EL_APPEND1, EL_APPEND2]) >>
  pop_assum SUBST1_TAC >>
  qexistsl_tac [‘pre’, ‘ev’, ‘post’] >> fs[EVERY_MEM, EXISTS_MEM]
QED

(* A prefix of the trace lies inside some round *)
Theorem trace_locate:
  run_ok lfd pol ifds m w0 ∧ pftrace lfd pol ifds m w0 io ∧ LPREFIX (fromList evs) io ⇒
  ∃r pre post. evs = revs lfd pol ifds m w0 r ++ pre ∧
               rrev lfd pol ifds m w0 r = pre ++ post
Proof
  strip_tac >>
  drule_all pftrace_locate >> disch_then (qspec_then ‘0’ strip_assume_tac) >>
  drule locate >> disch_then drule >> strip_tac >> metis_tac[]
QED

Theorem revs_le[local]:
  run_ok lfd pol ifds m w0 ∧ a ≤ b ⇒
  revs lfd pol ifds m w0 a ≼ revs lfd pol ifds m w0 b
Proof
  strip_tac >> drule revs_prefix >> disch_then (qspecl_then [‘b − a’, ‘a’] mp_tac) >>
  ‘a + (b − a) = b’ by decide_tac >> simp[]
QED

(* ------------------------------------------------------------------------
   The csent case
   ------------------------------------------------------------------------ *)

Theorem cs_ok_sent:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ qfresh w0 ∧
  evs = revs lfd pol ifds m w0 r ++ pre ∧ rrev lfd pol ifds m w0 r = pre ++ post ∧
  ep_open j evs ∧ world_at w0 evs = SOME w ∧ l0_chan_of w (EL j (l0_accepted evs)) = SOME c ∧
  cs_ok lfd pol ifds m w0 c X n' ⇒
  ∃N. X ≼ l0_sent j (revs lfd pol ifds m w0 N)
Proof
  strip_tac >> qabbrev_tac ‘N = MAX n' (SUC r)’ >> qexists_tac ‘N’ >>
  ‘revs lfd pol ifds m w0 (SUC r) = revs lfd pol ifds m w0 r ++ rrev lfd pol ifds m w0 r’
    by metis_tac[prun_round'] >>
  ‘evs ≼ revs lfd pol ifds m w0 N’
    by (irule IS_PREFIX_TRANS >> qexists_tac ‘revs lfd pol ifds m w0 (SUC r)’ >>
        conj_tac >- (irule revs_le >> simp[Abbr ‘N’]) >>
        simp[IS_PREFIX_APPEND]) >>
  ‘revs lfd pol ifds m w0 n' ≼ revs lfd pol ifds m w0 N’
    by (irule revs_le >> simp[Abbr ‘N’]) >>
  ‘X ≼ csent (rworld lfd pol ifds m w0 N) c’
    by (qpat_x_assum ‘cs_ok _ _ _ _ _ _ _ _’ mp_tac >> rw[cs_ok_def] >>
        ‘smono c (rworld lfd pol ifds m w0 n') (rworld lfd pol ifds m w0 N)’
          by (irule world_at_smono >>
              qpat_x_assum ‘revs _ _ _ _ _ n' ≼ _’ mp_tac >> rw[IS_PREFIX_APPEND] >>
              qexistsl_tac [‘revs lfd pol ifds m w0 n'’, ‘l’, ‘w0’] >>
              metis_tac[run_world_at]) >>
        fs[smono_def, csent_def] >> metis_tac[IS_PREFIX_TRANS]) >>
  drule ep_open_split >> strip_tac >>
  qabbrev_tac ‘f = EL j (l0_accepted evs)’ >>
  qpat_x_assum ‘evs ≼ _’ (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
  rename1 ‘revs lfd pol ifds m w0 N = evs ++ rest’ >>
  ‘faithful w0 (revs lfd pol ifds m w0 N) ∧
   world_at w0 (revs lfd pol ifds m w0 N) = SOME (rworld lfd pol ifds m w0 N)’
    by (drule run_world_at >> simp[]) >>
  ‘faithful w0 (pre' ++ [ev] ++ (post' ++ rest))’
    by (qpat_x_assum ‘faithful _ (revs _ _ _ _ _ N)’ mp_tac >>
        qpat_x_assum ‘revs _ _ _ _ _ N = _’ SUBST1_TAC >>
        qpat_x_assum ‘evs = pre' ++ _ ++ _’ SUBST1_TAC >> simp[]) >>
  drule_all episode_csent_le >> strip_tac >>
  rename1 ‘l0_chan_of w1 f = SOME c1’ >>
  ‘w' = rworld lfd pol ifds m w0 N’
    by (qpat_x_assum ‘world_at w0 (revs _ _ _ _ _ N) = _’ mp_tac >>
        qpat_x_assum ‘revs _ _ _ _ _ N = _’ SUBST1_TAC >>
        qpat_x_assum ‘evs = pre' ++ _ ++ _’ SUBST1_TAC >>
        qpat_x_assum ‘world_at w0 (pre' ++ [ev] ++ (post' ++ rest)) = _’ mp_tac >>
        simp[]) >>
  ‘faithful w0 evs’
    by (qspecl_then [‘evs’, ‘rest’, ‘w0’] mp_tac faithful_prefix >>
        qpat_x_assum ‘revs _ _ _ _ _ N = _’ (fn th => REWRITE_TAC [GSYM th]) >>
        qpat_x_assum ‘faithful w0 (revs _ _ _ _ _ N)’ (fn th => REWRITE_TAC [th])) >>
  ‘EVERY (λe. ¬ep_ends f e) post'’
    by (qpat_x_assum ‘¬EXISTS _ post'’ mp_tac >> simp[EVERY_MEM, EXISTS_MEM]) >>
  ‘c1 = c’
    by (qpat_x_assum ‘faithful w0 evs’ mp_tac >>
        qpat_x_assum ‘world_at w0 evs = _’ mp_tac >>
        qpat_x_assum ‘evs = pre' ++ _ ++ _’ (fn th => REWRITE_TAC [th]) >>
        rpt strip_tac >> drule world_chan_back >>
        disch_then (qspecl_then [‘w’, ‘f’, ‘c’] mp_tac) >>
        impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
        ‘x = w1’
          by (qpat_x_assum ‘world_at w0 (pre' ++ [ev]) = SOME x’ mp_tac >>
              qpat_x_assum ‘world_at w0 (pre' ++ [ev]) = SOME w1’ (fn th => REWRITE_TAC [th]) >>
              simp[]) >>
        qpat_x_assum ‘x = w1’ SUBST_ALL_TAC >>
        qpat_x_assum ‘l0_chan_of w1 f = SOME c’ mp_tac >>
        qpat_x_assum ‘l0_chan_of w1 f = SOME c1’ (fn th => REWRITE_TAC [th]) >> simp[]) >>
  qpat_x_assum ‘c1 = c’ SUBST_ALL_TAC >>
  qpat_x_assum ‘w' = _’ SUBST_ALL_TAC >>
  ‘pre' ++ [ev] ++ post' ++ rest = revs lfd pol ifds m w0 N’
    by (qpat_x_assum ‘revs _ _ _ _ _ N = _’ SUBST1_TAC >>
        qpat_x_assum ‘evs = pre' ++ _ ++ _’ SUBST1_TAC >> simp[]) >>
  pop_assum (assume_tac o REWRITE_RULE [GSYM APPEND_ASSOC]) >>
  qpat_x_assum ‘csent _ c ≼ _’ (assume_tac o REWRITE_RULE [GSYM APPEND_ASSOC]) >>
  pop_assum mp_tac >> pop_assum (fn th => REWRITE_TAC [th]) >> strip_tac >>
  irule IS_PREFIX_TRANS >> qexists_tac ‘csent (rworld lfd pol ifds m w0 N) c’ >>
  conj_tac >> first_assum ACCEPT_TAC
QED

(* ------------------------------------------------------------------------
   The flush case
   ------------------------------------------------------------------------ *)

(* f keeps its channel while its episode stays open *)
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

(* The channel f holds at a prefix of the trace and at a round boundary,
   in the same episode, is the same *)
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

Theorem fl_at_open:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ qfresh w0 ∧ MEM lfd (l0_used w0) ∧
  pftrace lfd pol ifds m w0 io ∧ LPREFIX (fromList evs) io ∧
  ep_open j evs ∧ world_at w0 evs = SOME w ∧ l0_chan_of w (EL j (l0_accepted evs)) = SOME c ∧
  fl_at lfd pol ifds m w0 (EL j (l0_accepted evs)) j k ⇒
  flushed_open w0 io j c
Proof
  strip_tac >> qabbrev_tac ‘f = EL j (l0_accepted evs)’ >>
  ‘ALOOKUP (SND (l0_ep_st (0, []) evs)) f = SOME j’ by metis_tac[ep_open_state] >>
  qpat_x_assum ‘fl_at _ _ _ _ _ _ _ _’ mp_tac >> rw[fl_at_def] >>
  ‘∃ck. l0_chan_of (rworld lfd pol ifds m w0 k) f = SOME ck ∧
        (EL ck (rworld lfd pol ifds m w0 k).chans).broken ∧
        (EL ck (rworld lfd pol ifds m w0 k).chans).inbox = []’
    by (qpat_x_assum ‘flushed _ _’ mp_tac >> simp[flushed_def]) >>
  ‘ck = c’ by (irule run_chan_same >> metis_tac[]) >>
  qpat_x_assum ‘ck = c’ SUBST_ALL_TAC >>
  ‘c < LENGTH (rworld lfd pol ifds m w0 k).chans’
    by (qpat_x_assum ‘l0_chan_of (rworld _ _ _ _ _ k) f = _’ mp_tac >>
        rw[l0_chan_of_def, AllCaseEqs()] >> simp[]) >>
  ‘LPREFIX (fromList (revs lfd pol ifds m w0 k)) io’ by metis_tac[pftrace_revs] >>
  ‘world_at w0 (revs lfd pol ifds m w0 k) = SOME (rworld lfd pol ifds m w0 k)’
    by metis_tac[run_world_at] >>
  drule_all held_noclose >> strip_tac >>
  simp[flushed_open_def] >>
  qexistsl_tac [‘pre’, ‘ev’, ‘post’, ‘f’, ‘rworld lfd pol ifds m w0 k’] >>
  qpat_x_assum ‘revs _ _ _ _ _ k = _’ (SUBST_ALL_TAC o SYM) >> simp[] >>
  qpat_x_assum ‘¬EXISTS (closes_call f) post’ (mp_tac o MATCH_MP no_close_call) >> simp[]
QED

(* ------------------------------------------------------------------------
   MAIN
   ------------------------------------------------------------------------ *)

Theorem trace_wrap:
  echo_run lfdn pol w0 ∧ qfresh w0 ∧ qinb w0 ∧ pol_ok hw pol ∧ F1 (n2w lfdn) pol EI ES w0 ∧
  honestL1PFFlush$F2 w0 ∧ honestL1PFFlush$drains (n2w lfdn) pol EI ES w0 c ∧ nshut w0 ∧
  pftrace (n2w lfdn) pol EI ES w0 io ∧
  LPREFIX (fromList evs) io ∧ ep_open j evs ∧ world_at w0 evs = SOME w ∧
  l0_chan_of w (EL j (l0_accepted evs)) = SOME c ⇒
  (∃evs'. LPREFIX (fromList evs') io ∧ (EL c w.chans).peer_sent ≼ l0_sent j evs') ∨
  flushed_open w0 io j c ∨ ep_hard_err j io ∨ ep_timed_out pf_sendwait j io
Proof
  strip_tac >>
  ‘run_ok (n2w lfdn) pol EI ES w0 ∧ winv w0 ∧ MEM (n2w lfdn) (l0_used w0)’
    by fs[echo_run_def] >>
  ‘ALOOKUP (SND (l0_ep_st (0, []) evs)) (EL j (l0_accepted evs)) = SOME j’
    by metis_tac[ep_open_state] >>
  drule_all trace_locate >> strip_tac >>
  ‘(∃n'. cs_ok (n2w lfdn) pol EI ES w0 c (EL c w.chans).peer_sent n') ∨
   (∃k. fl_at (n2w lfdn) pol EI ES w0 (EL j (l0_accepted evs)) j k) ∨
   ep_hard_err j io ∨ ep_timed_out pf_sendwait j io’
    by (irule trace_data >> qpat_x_assum ‘evs = _’ (SUBST_ALL_TAC) >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        TRY (qexists_tac ‘hw’ >> first_assum ACCEPT_TAC) >>
        qexistsl_tac [‘post’, ‘pre’, ‘r’] >> simp[]) >>
  pop_assum strip_assume_tac
  >- (disj1_tac >> drule_all cs_ok_sent >> strip_tac >>
      qexists_tac ‘revs (n2w lfdn) pol EI ES w0 N’ >> simp[] >>
      irule pftrace_revs >> conj_tac >> first_assum ACCEPT_TAC)
  >- (disj2_tac >> disj1_tac >> drule_all fl_at_open >> simp[]) >>
  simp[]
QED
