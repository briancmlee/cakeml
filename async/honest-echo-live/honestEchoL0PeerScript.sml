(*
  What the peer has sent, along the trace and the run (design/47 D, trace
  assembly): a channel's peer_sent only grows, and once the peer's
  end-of-file has arrived it stays and peer_sent is final (psmono; LData
  is dropped after peer_eof).  An fd L1 knows the client of was connected
  in a last round a (last_conn).

  MAIN: world_at_psmono, last_conn.
*)
Theory honestEchoL0Peer
Ancestors
  honestEchoL0Drains honestL1BStmts honestL0Part honestL0World
  honestL1PFConnTrace honestL1PFOut honestL1PFLive honestL1PFRefine honestL1PFClient
Libs
  preamble


Definition psmono_def:
  psmono c (w : l0world) (w' : l0world) ⇔
    c < LENGTH w.chans ⇒
    c < LENGTH w'.chans ∧ (EL c w.chans).peer_sent ≼ (EL c w'.chans).peer_sent ∧
    ((EL c w.chans).peer_eof ⇒
     (EL c w'.chans).peer_eof ∧ (EL c w'.chans).peer_sent = (EL c w.chans).peer_sent)
End

Theorem pfx_trans[local]:
  x ≼ y ∧ y ≼ z ⇒ x ≼ z
Proof
  rw[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]
QED

Theorem psmono_trans:
  psmono c w1 w2 ∧ psmono c w2 w3 ⇒ psmono c w1 w3
Proof
  rw[psmono_def] >> fs[] >> metis_tac[pfx_trans]
QED

Theorem deliver_psmono[local]:
  psmono c w (l0_deliver w a)
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def, psmono_def, upd_lchan_def, EL_LUPDATE] >>
  every_case_tac >> gvs[EL_APPEND1, EL_LUPDATE] >> rw[] >> gvs[break_lchan_def] >> rw[]
QED

Theorem FOLDL_deliver_psmono[local]:
  ∀as w. psmono c w (FOLDL l0_deliver w as)
Proof
  Induct >- simp[psmono_def] >> simp[] >> metis_tac[psmono_trans, deliver_psmono]
QED

Theorem tick_psmono:
  psmono c w (l0_tick nm w)
Proof
  simp[l0_tick_def] >>
  irule psmono_trans >> qexists_tac ‘w with clock := w.clock + 1’ >>
  simp[FOLDL_deliver_psmono] >> simp[psmono_def]
QED

Theorem ticks_psmono:
  ∀k w. psmono c w (l0_ticks nm k w)
Proof
  Induct >- simp[l0_ticks_def, psmono_def] >>
  simp[l0_ticks_def] >> metis_tac[psmono_trans, tick_psmono]
QED

Theorem FOLDL_psmono[local]:
  ∀q w1. (∀w' j. psmono c w' (f w' j)) ∧ psmono c w w1 ⇒ psmono c w (FOLDL f w1 q)
Proof
  Induct >> rw[] >> first_x_assum irule >> simp[] >> metis_tac[psmono_trans]
QED

Theorem l0_call_psmono:
  l0_call n conf bytes w = SOME (FFIreturn out w') ⇒ psmono c w w'
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  TRY (simp[ticks_psmono] >> NO_TAC) >>
  TRY (simp[psmono_def] >> NO_TAC) >>
  gvs[l0_listen_def, l0_accept_def, l0_recv_def, l0_send_def, l0_shutdown_def,
      l0_connect_def, l0_connerr_def, l0_close_def, close_fd_def, l0_alloc_def,
      AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[AllCaseEqs()]) >>
  TRY (irule FOLDL_psmono >> conj_tac >> rpt gen_tac >>
       rw[psmono_def, EL_LUPDATE, upd_lchan_def, break_lchan_def] >> rw[] >> NO_TAC) >>
  rw[psmono_def, upd_lchan_def, EL_LUPDATE, break_lchan_def, EL_APPEND1] >> rw[] >> gvs[]
QED

Theorem step_psmono:
  l0_step (SOME w) lc = SOME w' ⇒ psmono c w w'
Proof
  PairCases_on ‘lc’ >> rw[l0_step_def, l0_ffi_fn_def, AllCaseEqs()] >>
  irule psmono_trans >> qexists_tac ‘l0_tick lc0 w’ >>
  conj_tac >- simp[tick_psmono] >>
  drule l0_call_psmono >> simp[psmono_def]
QED

Theorem FOLDL_step_NONE[local]:
  ∀cs. FOLDL l0_step NONE cs = NONE
Proof
  Induct >> simp[l0_step_def]
QED

Theorem replay_psmono:
  ∀cs w w'. FOLDL l0_step (SOME w) cs = SOME w' ⇒ psmono c w w'
Proof
  Induct >- simp[psmono_def] >> rpt gen_tac >> simp[] >>
  Cases_on ‘l0_step (SOME w) h’ >> simp[FOLDL_step_NONE] >> strip_tac >>
  irule psmono_trans >> qexists_tac ‘x’ >>
  conj_tac >- (irule step_psmono >> qexists_tac ‘h’ >> first_assum ACCEPT_TAC) >>
  first_x_assum irule >> first_assum ACCEPT_TAC
QED

(* MAIN *)
Theorem world_at_psmono:
  world_at w0 a = SOME x ∧ world_at w0 (a ++ b) = SOME y ⇒ psmono c x y
Proof
  rw[world_at_def, l0_replay_def, FOLDL_APPEND] >> gvs[] >> metis_tac[replay_psmono]
QED

(* MAIN: an fd with a client was connected in a last round before n *)
Theorem last_conn:
  run_ok lfd pol ifds m w0 ⇒
  ∀n. MEM f (MAP FST (FST (pcm lfd pol ifds m w0 n))) ⇒
      ∃a. a < n ∧ MEM (FConn f) (rlog lfd pol ifds m w0 a) ∧
          ∀k. a < k ∧ k < n ⇒ ¬MEM (FConn f) (rlog lfd pol ifds m w0 k)
Proof
  strip_tac >> Induct >- simp[pcm_def] >> strip_tac >>
  Cases_on ‘MEM (FConn f) (rlog lfd pol ifds m w0 n)’
  >- (qexists_tac ‘n’ >> simp[]) >>
  ‘MEM f (MAP FST (FST (pcm lfd pol ifds m w0 n)))’
    by (qpat_x_assum ‘MEM f _’ mp_tac >>
        ‘plog lfd pol ifds m w0 n = rlog lfd pol ifds m w0 n’ by (irule plog_rlog >> simp[]) >>
        simp[pcm_def] >> Cases_on ‘pcm lfd pol ifds m w0 n’ >> simp[] >>
        Cases_on ‘arrs lfd (q, r) (plog lfd pol ifds m w0 n)’ >> rename1 ‘_ = (as, ck)’ >>
        PairCases_on ‘ck’ >> simp[] >>
        drule arrs_fconn >> strip_tac >> gvs[]) >>
  first_x_assum drule >> strip_tac >>
  qexists_tac ‘a’ >> simp[] >> rpt strip_tac >>
  Cases_on ‘k = n’ >> gvs[] >> first_x_assum irule >> simp[]
QED
