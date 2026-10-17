(*
  The L0 world along an E1 run's trace (close-v2; for client_live_claim's
  trace lift): an E1 round's events, replayed call by call in the L0 world
  (clientLiveCopy's world_at), lead from the round's start world to its end
  world.  So world_at w0 (erounds' events) is the run's world at that round.

  The per-call lemmas follow honest-l1b's honestL1BRuns / honestL1BFaith
  (rplays / fplays, spike/echo-live-pol), which are not on this line;
  eplays is fplays without `faithful` (E1 reads results from its events
  directly).

  MAIN: eplays_erounds, erounds_world_at.
*)
Theory e1TraceWorld
Ancestors
  clientLiveCopy honestL1EPModel honestL1PFRound honestL1PFModel honestL1Model
  honestL0WorldProps honestL0Rely honestL0World honestL0
Libs
  preamble

(* evs, replayed call by call from w, ends in w' (and keeps the rely) *)
Definition eplays_def:
  eplays w w' (evs : io_event list) ⇔
    l0_rely w ⇒ FOLDL l0_step (SOME w) (MAP ev_lcall evs) = SOME w' ∧ l0_rely w'
End

Theorem eplays_nil[simp]:
  eplays w w []
Proof
  simp[eplays_def]
QED

Theorem eplays_trans:
  eplays w1 w2 a ∧ eplays w2 w3 b ⇒ eplays w1 w3 (a ++ b)
Proof
  rw[eplays_def] >> fs[FOLDL_APPEND]
QED

Theorem eplays_cons:
  eplays w1 w2 [e] ∧ eplays w2 w3 b ⇒ eplays w1 w3 (e :: b)
Proof
  metis_tac[eplays_trans, APPEND]
QED

Theorem eplays_do:
  l0_do n conf alen w = SOME (out, w', ev) ⇒ eplays w w' [ev]
Proof
  rw[eplays_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  ‘l0_ffi_fn n conf (REPLICATE alen 0w) w =
     SOME (FFIreturn out (w1 with hist := w.hist ++ [(n, conf, REPLICATE alen 0w)]))’
    by simp[l0_ffi_fn_def] >>
  drule_all l0_ffi_fn_length >> strip_tac >>
  simp[ev_lcall_def, l0_step_def, MAP_ZIP]
QED

Theorem eplays_do_buf:
  l0_do_buf n conf bs w = SOME (out, w', ev) ⇒ eplays w w' [ev]
Proof
  rw[eplays_def] >> drule l0_do_buf_cases >> strip_tac >> gvs[] >>
  ‘l0_ffi_fn n conf bs w = SOME (FFIreturn out (w1 with hist := w.hist ++ [(n, conf, bs)]))’
    by simp[l0_ffi_fn_def] >>
  drule_all l0_ffi_fn_length >> strip_tac >>
  simp[ev_lcall_def, l0_step_def, MAP_ZIP]
QED

Theorem eplays_sys:
  (sys_accept l w = SOME (out, w', ev) ⇒ eplays w w' [ev]) ∧
  (sys_recv f k w = SOME (out, w', ev) ⇒ eplays w w' [ev]) ∧
  (sys_send f bs w = SOME (out, w', ev) ⇒ eplays w w' [ev]) ∧
  (sys_close f w = SOME (out, w', ev) ⇒ eplays w w' [ev]) ∧
  (sys_poll fes w = SOME (out, w', ev) ⇒ eplays w w' [ev]) ∧
  (sys_connect p w = SOME (out, w', ev) ⇒ eplays w w' [ev]) ∧
  (sys_connerr f w = SOME (out, w', ev) ⇒ eplays w w' [ev])
Proof
  rw[sys_accept_def, sys_recv_def, sys_send_def, sys_close_def, sys_poll_def,
     sys_connect_def, sys_connerr_def] >>
  TRY (irule eplays_do_buf >> metis_tac[] >> NO_TAC) >>
  irule eplays_do >> metis_tac[]
QED

Theorem eplays_close:
  l1_close f (w, st) = SOME ((w', st'), evs) ⇒ eplays w w' evs
Proof
  rw[l1_close_def, AllCaseEqs()] >> TRY (PairCases_on ‘v’) >> gvs[] >>
  metis_tac[eplays_sys]
QED

Theorem eplays_l1do:
  l1do lfd (w, st) a = SOME (r, (w', st'), evs) ⇒ eplays w w' evs
Proof
  Cases_on ‘a’ >> rw[l1do_def, AllCaseEqs()] >> gvs[] >>
  TRY (PairCases_on ‘v’) >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac eplays_sys >> imp_res_tac eplays_close >> gvs[] >>
  TRY (irule eplays_cons >> goal_assum drule >> first_assum ACCEPT_TAC)
QED

Theorem eplays_pdo:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ⇒ eplays w w' evs
Proof
  Cases_on ‘a’ >> rw[pdo_def, AllCaseEqs()] >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac eplays_close >> imp_res_tac eplays_l1do >> gvs[]
QED

Theorem eplays_polls:
  ∀fess w rv w' evs. l1_polls fess w = SOME (rv, w', evs) ⇒ eplays w w' evs
Proof
  Induct >> rw[l1_polls_def, AllCaseEqs()] >>
  res_tac >> imp_res_tac eplays_sys >> irule eplays_cons >> metis_tac[]
QED

Theorem eplays_flush:
  ∀fs w st w' st' evs. l1_flush fs (w, st) = SOME ((w', st'), evs) ⇒ eplays w w' evs
Proof
  Induct >> rw[l1_flush_def, AllCaseEqs()] >> res_tac >> imp_res_tac eplays_sys >>
  TRY (irule eplays_cons >> metis_tac[]) >> metis_tac[]
QED

Theorem eplays_fetch:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ⇒ eplays w w' evs
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> pairarg_tac >> gvs[] >>
  qpat_x_assum ‘_ = (ps1, _)’ (fn th => fs[th]) >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> imp_res_tac eplays_sys >> strip_tac >>
  irule eplays_cons >> goal_assum drule >> first_assum ACCEPT_TAC
QED

Theorem eplays_reap:
  ∀fs w st w' st' evs. l1_reap fs (w, st) = SOME ((w', st'), evs) ⇒ eplays w w' evs
Proof
  Induct >> rw[l1_reap_def, AllCaseEqs()] >> TRY (PairCases_on ‘ws’) >>
  res_tac >> imp_res_tac eplays_close >> gvs[] >>
  irule eplays_trans >> metis_tac[]
QED

Theorem eplays_settle:
  ∀fs w es w' es' evs. settle_fds fs (w, es) = SOME ((w', es'), evs) ⇒ eplays w w' evs
Proof
  Induct >> rw[settle_fds_def, AllCaseEqs()] >>
  imp_res_tac eplays_sys >> first_x_assum drule >> strip_tac >>
  irule eplays_cons >> goal_assum drule >> first_assum ACCEPT_TAC
QED

Theorem eplays_edo:
  edo lfd pol (w, es) a = SOME (r, (w', es'), evs) ⇒ eplays w w' evs
Proof
  Cases_on ‘a’ >> rw[edo_def, AllCaseEqs()] >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac eplays_sys >> imp_res_tac eplays_close >> imp_res_tac eplays_pdo >> gvs[]
QED

Theorem eplays_eacts:
  ∀acts w es rs evs w' es'.
    eacts lfd pol (w, es) acts = SOME (rs, evs, (w', es')) ⇒ eplays w w' evs
Proof
  Induct >> rw[eacts_def, AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  imp_res_tac eplays_edo >> first_x_assum drule >> strip_tac >>
  irule eplays_trans >> metis_tac[]
QED

Theorem eplays_etail:
  etail lfd pol hs (w, es) = SOME (rdy, (w', es'), log, evs) ⇒ eplays w w' evs
Proof
  rw[etail_def, AllCaseEqs()] >> gvs[] >>
  imp_res_tac eplays_polls >> imp_res_tac eplays_flush >> imp_res_tac eplays_fetch >>
  imp_res_tac eplays_reap >> imp_res_tac eplays_settle >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >> metis_tac[eplays_trans]
QED

Theorem eplays_eround:
  eround lfd pol hs (w, es) acts = SOME (snap, (w', es'), log, evs) ⇒ eplays w w' evs
Proof
  rw[eround_def, AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  imp_res_tac eplays_eacts >> imp_res_tac eplays_etail >>
  irule eplays_trans >> metis_tac[]
QED

(* MAIN: an E1 run's events replay from its start world to its world *)
Theorem eplays_erounds:
  ∀n h w es evs logs.
    erounds lfd pol ifds m (w0, es0) n = SOME (h, (w, es), evs, logs) ⇒
    eplays w0 w evs
Proof
  Induct >- rw[erounds_def] >>
  rw[erounds_def, AllCaseEqs()] >> PairCases_on ‘ws’ >>
  first_x_assum drule >> strip_tac >> imp_res_tac eplays_eround >>
  irule eplays_trans >> metis_tac[]
QED

(* world_at, after a start pre with world w0' *)
Theorem eplays_world_at:
  world_at w0 pre = SOME w1 ∧ eplays w1 w evs ∧ l0_rely w1 ⇒
  world_at w0 (pre ++ evs) = SOME w ∧ l0_rely w
Proof
  rw[eplays_def, world_at_def, l0_replay_def, FOLDL_APPEND]
QED

Theorem erounds_world_at:
  erounds lfd pol ifds m (w1, es0) n = SOME (h, (w, es), evs, logs) ∧
  world_at w0 pre = SOME w1 ∧ l0_rely w1 ⇒
  world_at w0 (pre ++ evs) = SOME w ∧ l0_rely w
Proof
  strip_tac >> drule eplays_erounds >> strip_tac >>
  irule eplays_world_at >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   A channel's sent only grows along a replay, and while it does not, its
   bytes in flight do not grow either.  COPY of honest-echo-live's
   honestEchoL0Drains smono .. world_at_smono (spike/echo-live-pol @
   b58968e19), not on this line; remove at the merge
   ------------------------------------------------------------------------ *)


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

Theorem FOLDL_step_NONE[local,simp]:
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


(* ------------------------------------------------------------------------
   world_at on prefixes
   ------------------------------------------------------------------------ *)

Theorem world_at_prefix:
  world_at w0 (a ++ b) = SOME w ⇒ ∃w'. world_at w0 a = SOME w'
Proof
  rw[world_at_def, l0_replay_def, FOLDL_APPEND] >>
  Cases_on ‘FOLDL l0_step (SOME w0) (MAP ev_lcall a)’ >> gvs[]
QED

Theorem replay_rely:
  ∀cs w w'. FOLDL l0_step (SOME w) cs = SOME w' ∧ l0_rely w ⇒ l0_rely w'
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on ‘h’ >> simp[l0_step_def] >>
  Cases_on ‘l0_ffi_fn h0 h1 h2 w’ >> simp[] >> Cases_on ‘x’ >> simp[] >> strip_tac >>
  drule_all l0_ffi_fn_length >> metis_tac[]
QED

Theorem world_at_rely:
  world_at w0 evs = SOME w ∧ l0_rely w0 ⇒ l0_rely w
Proof
  rw[world_at_def, l0_replay_def] >> metis_tac[replay_rely]
QED
