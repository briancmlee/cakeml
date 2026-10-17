(*
  D(c) from the trace to the rounds (design/47 D, assembly): L3's
  drains w0 io c (if nothing more is sent on c after a prefix, c's bytes
  in flight eventually reach 0) gives honest-ffi's round-level drains on
  the PF run (the same, at round boundaries).

  Along a replay a channel's sent only grows, and while it does not grow
  its bytes in flight do not either (smono: sends are the only steps that
  add bytes in flight, and they add them to sent).  So a 0 in flight in
  the middle of a round shows at the next round boundary, and the run's
  "no more sends" gives the trace's.

  MAIN: drains_round.
*)
Theory honestEchoL0Drains
Ancestors
  honestL1BChan honestL1BStmts honestL1BCorr honestL0Part honestL0World
  honestL1PFConnTrace honestL1PFFlush honestL1PFOutLive honestL1PFOut honestL1PFLive
Libs
  preamble


Definition smono_def:
  smono c (w : l0world) (w' : l0world) ⇔
    c < LENGTH w.chans ⇒
    c < LENGTH w'.chans ∧ (EL c w.chans).sent ≼ (EL c w'.chans).sent ∧
    ((EL c w'.chans).sent = (EL c w.chans).sent ⇒
     (EL c w'.chans).inflight ≤ (EL c w.chans).inflight)
End

Theorem pfx_antisym[local]:
  x ≼ y ∧ y ≼ x ⇒ x = y
Proof
  rw[IS_PREFIX_APPEND] >> gvs[]
QED

Theorem pfx_trans[local]:
  x ≼ y ∧ y ≼ z ⇒ x ≼ z
Proof
  rw[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]
QED

Theorem smono_refl[simp]:
  smono c w w
Proof
  simp[smono_def]
QED

Theorem smono_trans:
  smono c w1 w2 ∧ smono c w2 w3 ⇒ smono c w1 w3
Proof
  rw[smono_def] >> fs[] >- metis_tac[pfx_trans] >>
  ‘(EL c w2.chans).sent = (EL c w1.chans).sent’
    by metis_tac[pfx_antisym, pfx_trans] >>
  fs[]
QED

Theorem deliver_smono[local]:
  smono c w (l0_deliver w a)
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def, smono_def, upd_lchan_def, EL_LUPDATE] >>
  every_case_tac >> gvs[EL_APPEND1, EL_LUPDATE] >> rw[] >> gvs[break_lchan_def] >> rw[]
QED

Theorem FOLDL_deliver_smono[local]:
  ∀as w. smono c w (FOLDL l0_deliver w as)
Proof
  Induct >> simp[] >> metis_tac[smono_trans, deliver_smono]
QED

Theorem tick_smono:
  smono c w (l0_tick nm w)
Proof
  simp[l0_tick_def] >>
  irule smono_trans >> qexists_tac ‘w with clock := w.clock + 1’ >>
  simp[FOLDL_deliver_smono] >> simp[smono_def]
QED

Theorem ticks_smono:
  ∀k w. smono c w (l0_ticks nm k w)
Proof
  Induct >> simp[l0_ticks_def] >> metis_tac[smono_trans, tick_smono]
QED

Theorem FOLDL_smono[local]:
  ∀q w1. (∀w' j. smono c w' (f w' j)) ∧ smono c w w1 ⇒ smono c w (FOLDL f w1 q)
Proof
  Induct >> rw[] >> first_x_assum irule >> simp[] >> metis_tac[smono_trans]
QED

Theorem l0_call_smono:
  l0_call n conf bytes w = SOME (FFIreturn out w') ⇒ smono c w w'
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  TRY (simp[ticks_smono] >> NO_TAC) >>
  TRY (simp[smono_def] >> NO_TAC) >>
  gvs[l0_listen_def, l0_accept_def, l0_recv_def, l0_send_def, l0_shutdown_def,
      l0_connect_def, l0_connerr_def, l0_close_def, close_fd_def, l0_alloc_def,
      AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[AllCaseEqs()]) >>
  TRY (irule FOLDL_smono >> conj_tac >> rpt gen_tac >>
       rw[smono_def, EL_LUPDATE, upd_lchan_def, break_lchan_def] >> rw[] >> NO_TAC) >>
  rw[smono_def, upd_lchan_def, EL_LUPDATE, break_lchan_def, EL_APPEND1] >> rw[] >>
  gvs[MIN_DEF] >> rw[] >> gvs[]
QED

Theorem step_smono:
  l0_step (SOME w) lc = SOME w' ⇒ smono c w w'
Proof
  PairCases_on ‘lc’ >> rw[l0_step_def, l0_ffi_fn_def, AllCaseEqs()] >>
  irule smono_trans >> qexists_tac ‘l0_tick lc0 w’ >>
  conj_tac >- simp[tick_smono] >>
  drule l0_call_smono >> simp[smono_def]
QED

Theorem FOLDL_step_NONE[local]:
  ∀cs. FOLDL l0_step NONE cs = NONE
Proof
  Induct >> simp[l0_step_def]
QED

Theorem replay_smono:
  ∀cs w w'. FOLDL l0_step (SOME w) cs = SOME w' ⇒ smono c w w'
Proof
  Induct >- simp[] >> rpt gen_tac >> simp[] >>
  Cases_on ‘l0_step (SOME w) h’ >> simp[FOLDL_step_NONE] >> strip_tac >>
  irule smono_trans >> qexists_tac ‘x’ >>
  conj_tac >- (irule step_smono >> qexists_tac ‘h’ >> first_assum ACCEPT_TAC) >>
  first_x_assum irule >> first_assum ACCEPT_TAC
QED

Theorem world_at_smono:
  world_at w0 a = SOME x ∧ world_at w0 (a ++ b) = SOME y ⇒ smono c x y
Proof
  rw[world_at_def, l0_replay_def, FOLDL_APPEND] >> gvs[] >> metis_tac[replay_smono]
QED

(* A prefix of the PF trace lies within the run's events by some round,
   as late as wanted *)
Theorem pftrace_locate:
  run_ok lfd pol ifds m w0 ∧ pftrace lfd pol ifds m w0 io ∧ LPREFIX (fromList evs) io ⇒
  ∀Kb. ∃M. Kb ≤ M ∧ evs ≼ revs lfd pol ifds m w0 M
Proof
  strip_tac >> gen_tac >>
  ‘ppre lfd pol ifds m (w0, pinit) evs’ by metis_tac[pftrace_def] >>
  fs[ppre_def] >>
  drule prun_parts >> disch_then (qspec_then ‘N’ strip_assume_tac) >> gvs[] >>
  qexists_tac ‘N + Kb’ >> simp[] >>
  irule pfx_trans >> qexists_tac ‘revs lfd pol ifds m w0 N’ >> simp[] >>
  drule revs_prefix >> disch_then (qspecl_then [‘Kb’, ‘N’] mp_tac) >> simp[]
QED

Theorem run_smono[local]:
  run_ok lfd pol ifds m w0 ∧ a ≤ b ⇒
  smono c (rworld lfd pol ifds m w0 a) (rworld lfd pol ifds m w0 b)
Proof
  strip_tac >>
  ‘revs lfd pol ifds m w0 a ≼ revs lfd pol ifds m w0 (a + (b − a))’
    by (drule revs_prefix >> disch_then (qspecl_then [‘b − a’, ‘a’] ACCEPT_TAC)) >>
  ‘a + (b − a) = b’ by decide_tac >> fs[IS_PREFIX_APPEND] >>
  irule world_at_smono >> qexistsl_tac [‘revs lfd pol ifds m w0 a’, ‘l’, ‘w0’] >>
  metis_tac[run_world_at]
QED

(* MAIN: L3's D(c) gives the round-level one *)
Theorem drains_round:
  run_ok lfd pol ifds m w0 ∧ pftrace lfd pol ifds m w0 io ∧ honestL1BStmts$drains w0 io c ∧
  c < LENGTH (rworld lfd pol ifds m w0 n0).chans ⇒
  honestL1PFFlush$drains lfd pol ifds m w0 c
Proof
  rw[honestL1PFFlushTheory.drains_def] >>
  qabbrev_tac ‘N = n + n0’ >>
  ‘c < LENGTH (rworld lfd pol ifds m w0 N).chans’
    by (‘n0 ≤ N’ by simp[Abbr ‘N’] >> drule_all run_smono >>
        disch_then (qspec_then ‘c’ mp_tac) >> simp[smono_def]) >>
  ‘csent (rworld lfd pol ifds m w0 N) c = csent (rworld lfd pol ifds m w0 n) c’
    by (first_x_assum irule >> simp[Abbr ‘N’]) >>
  (* the sent of any world past round N's boundary is round N's *)
  ‘∀evs' w'. LPREFIX (fromList (revs lfd pol ifds m w0 N ++ evs')) io ∧
             world_at w0 (revs lfd pol ifds m w0 N ++ evs') = SOME w' ⇒
             c < LENGTH w'.chans ∧
             (EL c w'.chans).sent = (EL c (rworld lfd pol ifds m w0 N).chans).sent ∧
             ∃M. N ≤ M ∧ smono c w' (rworld lfd pol ifds m w0 M)’
    by (rpt gen_tac >> strip_tac >>
        drule_all pftrace_locate >> disch_then (qspec_then ‘N’ strip_assume_tac) >>
        fs[IS_PREFIX_APPEND] >>
        ‘smono c (rworld lfd pol ifds m w0 N) w'’
          by (irule world_at_smono >> metis_tac[run_world_at]) >>
        ‘smono c w' (rworld lfd pol ifds m w0 M)’
          by (irule world_at_smono >> qexistsl_tac [‘revs lfd pol ifds m w0 N ++ evs'’, ‘l’, ‘w0’] >>
              metis_tac[run_world_at, APPEND_ASSOC]) >>
        ‘csent (rworld lfd pol ifds m w0 M) c = csent (rworld lfd pol ifds m w0 n) c’
          by (first_x_assum irule >> fs[Abbr ‘N’]) >>
        fs[smono_def, csent_def] >> rfs[] >>
        conj_tac >- metis_tac[pfx_antisym] >>
        qexists_tac ‘M’ >> simp[]) >>
  qpat_x_assum ‘honestL1BStmts$drains _ _ _’
    (qspecl_then [‘revs lfd pol ifds m w0 N’, ‘rworld lfd pol ifds m w0 N’] mp_tac o
     REWRITE_RULE [honestL1BStmtsTheory.drains_def]) >>
  impl_tac
  >- (rpt conj_tac >- metis_tac[pftrace_revs] >- metis_tac[run_world_at] >- simp[] >>
      rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac ‘M’ >> fs[Abbr ‘N’] >>
  qpat_x_assum ‘smono _ w' _’ mp_tac >> simp[smono_def] >>
  ‘(EL c (rworld lfd pol ifds m w0 M).chans).sent = (EL c w'.chans).sent’
    suffices_by (strip_tac >> fs[]) >>
  ‘csent (rworld lfd pol ifds m w0 M) c = csent (rworld lfd pol ifds m w0 n) c’
    by (first_x_assum irule >> decide_tac) >>
  fs[csent_def]
QED
