(*
  kv_live_l0 for the PF KV on its trace: the K-asks half from
  honestKvAsksLift.kv_asks_trace, the K-answers half (kv_answers_l0, the
  first clause of kv_live_l0 on its own) as a premise, proved separately
  (the K-answers chain: honestKvSrvOut's M4 middle, then the DataOut /
  TraceData / TraceWrap analogues).

  MAIN: kv_live_l0_split, kv_live_l0_pf.
*)
Theory honestKvLiveL0
Ancestors
  honestKvAsksLift honestKvL0LiveStmts honestKvL0Obl honestL1BStmts honestL1PFLive
Libs
  preamble

(* The K-answers clause of kv_live_l0 on its own *)
Definition kv_answers_l0_def:
  kv_answers_l0 Kt w0 io ⇔
    ∀evs j c w.
      LPREFIX (fromList evs) io ∧ ep_open j evs ∧ world_at w0 evs = SOME w ∧
      l0_chan_of w (EL j (l0_accepted evs)) = SOME c ∧ honestL1BStmts$drains w0 io c ⇒
      ∀rqs. EVERY valid_brequest rqs ∧ brequests rqs ≼ (EL c w.chans).peer_sent ⇒
            ep_hard_err j io ∨ ep_timed_out Kt j io ∨ honestL1BStmts$flushed_open w0 io j c ∨
            ∃evs' ans. LPREFIX (fromList evs') io ∧ LENGTH ans = LENGTH rqs ∧
                       reply_bytes ans ≼ l0_sent j evs'
End

(* The K-asks clause of kv_live_l0 on its own *)
Definition kv_asks_l0_def:
  kv_asks_l0 Kt w0 io ⇔
    ∀evs j c w.
      LPREFIX (fromList evs) io ∧ ep_open j evs ∧ world_at w0 evs = SOME w ∧
      l0_chan_of w (EL j (l0_accepted evs)) = SOME c ∧ honestL1BStmts$drains w0 io c ⇒
      peer_valid w0 io c ⇒
      ep_hard_err j io ∨ ep_timed_out Kt j io ∨ ch_frozen w0 io c ∨ ep_ended j io ∨
      asks_io_on (EL j (l0_accepted evs)) io
End

(* MAIN: kv_live_l0 is its two halves *)
Theorem kv_live_l0_split:
  kv_live_l0 Kt w0 io ⇔ kv_answers_l0 Kt w0 io ∧ kv_asks_l0 Kt w0 io
Proof
  rewrite_tac[kv_live_l0_def, kv_answers_l0_def, kv_asks_l0_def] >>
  eq_tac >> rpt strip_tac >>
  rpt (first_x_assum (qspecl_then [‘evs’, ‘j’, ‘c’, ‘w’] mp_tac)) >>
  asm_rewrite_tac[] >> rpt strip_tac >> TRY (asm_rewrite_tac[] >> NO_TAC) >>
  (qpat_x_assum ‘∀rqs. _’ (qspec_then ‘rqs’ mp_tac) >>
   impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC)
QED

(* The K-asks half, for the PF KV with pol_self *)
Theorem kv_asks_l0_pf:
  kv_run lfdn (pol_self hw) w0 ∧ qfresh w0 ∧ qinb w0 ∧
  pftrace (n2w lfdn) (pol_self hw) KI KS w0 io ⇒
  kv_asks_l0 Kt w0 io
Proof
  strip_tac >> rewrite_tac[kv_asks_l0_def] >> rpt gen_tac >> rpt strip_tac >>
  ‘ep_hard_err j io ∨ ch_frozen w0 io c ∨ ep_ended j io ∨
   asks_io_on (EL j (l0_accepted evs)) io’
    by (irule kv_asks_trace >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        TRY (qexistsl_tac [‘hw’, ‘lfdn’] >> conj_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
        qexistsl_tac [‘evs’, ‘w’] >> asm_rewrite_tac[]) >>
  asm_rewrite_tac[]
QED

(* MAIN: kv_live_l0 for the PF KV, given its K-answers half *)
Theorem kv_live_l0_pf:
  kv_run lfdn (pol_self hw) w0 ∧ qfresh w0 ∧ qinb w0 ∧
  pftrace (n2w lfdn) (pol_self hw) KI KS w0 io ∧ kv_answers_l0 Kt w0 io ⇒
  kv_live_l0 Kt w0 io
Proof
  strip_tac >> rewrite_tac[kv_live_l0_split] >> conj_tac >- first_assum ACCEPT_TAC >>
  irule kv_asks_l0_pf >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl_tac [‘hw’, ‘lfdn’] >> conj_tac >> first_assum ACCEPT_TAC
QED

(* The two copies of D32's flushed_open (honest-l1b's, used by the
   statement, and honest-echo-live's TraceWrap copy, used by echo's chain)
   agree *)
Theorem flushed_open_copies:
  honestL1BStmts$flushed_open = honestEchoL0TraceWrap$flushed_open
Proof
  simp[FUN_EQ_THM, honestL1BStmtsTheory.flushed_open_def,
       honestEchoL0TraceWrapTheory.flushed_open_def]
QED
