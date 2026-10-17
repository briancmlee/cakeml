(*
  echo_live_l0 for the PF echo on its trace (design/47 D): raw liveness of
  the echo per episode, unless the episode hit a hard error, timed out on
  output (K = pf_sendwait), or its channel was flushed while it was open.

  The data half is TraceWrap.trace_wrap, the close half (D27 form: a close
  call on the episode's fd while the episode is open) CloseChain.trace_close.
  Both take honest-ffi's round-level drains; Drains.drains_round gives it
  from the statement's trace-level drains, at a round where c exists.

  TEMP COPY: l3_echo_live_unless and l3_echo_live_l0 are L3-00's
  echo_live_unless and echo_live_l0 (final/L3-00-statements 001babe7e,
  kernel/statements/kernelStatementsScript.sml), renamed so as not to clash
  with this branch's older honestL1BStmts forms (ep_closed close half, no
  flushed_open), which honestL1BLive and honestL1BGuar still use.  Every
  definition they mention is the same here as in L3-00.  Remove at the
  merge onto L3.

  MAIN: echo_live_l0_pf.
*)
Theory honestEchoL0LiveL0
Ancestors
  honestEchoL0CloseChain honestEchoL0TraceWrap honestEchoL0Drains honestEchoL0TraceData
  honestEchoL0Obl honestL1BStmts honestL1PFConnTrace honestL1PFFlush honestL1PFOut honestL0World
Libs
  preamble

(* TEMP COPY of L3-00 kernelStatements echo_live_unless (D27) *)
Definition l3_echo_live_unless_def:
  l3_echo_live_unless D X w0 io ⇔
    ∀evs j c w.
      LPREFIX (fromList evs) io ∧ ep_open j evs ∧ world_at w0 evs = SOME w ∧
      l0_chan_of w (EL j (l0_accepted evs)) = SOME c ∧ drains w0 io c ∧ D j c ⇒
      X j c ∨
      ((∃evs'. LPREFIX (fromList evs') io ∧ (EL c w.chans).peer_sent ≼ l0_sent j evs') ∧
       ((EL c w.chans).peer_eof ⇒
        ∃evs' ev. LPREFIX (fromList (evs' ++ [ev])) io ∧ ep_open j evs' ∧
                  l0_close_call (EL j (l0_accepted evs')) ev))
End

(* TEMP COPY of L3-00 kernelStatements echo_live_l0 (D28, D32) *)
Definition l3_echo_live_l0_def:
  l3_echo_live_l0 K w0 io ⇔
    l3_echo_live_unless (λj c. T)
      (λj c. ep_hard_err j io ∨ ep_timed_out K j io ∨ flushed_open w0 io j c) w0 io
End

(* MAIN: echo_live_l0 for the PF echo, K = L1's write timeout *)
Theorem echo_live_l0_pf:
  echo_run lfdn pol w0 ∧ qfresh w0 ∧ qinb w0 ∧ pol_ok hw pol ∧ F1 (n2w lfdn) pol EI ES w0 ∧
  honestL1PFFlush$F2 w0 ∧ nshut w0 ∧ pftrace (n2w lfdn) pol EI ES w0 io ⇒
  l3_echo_live_l0 pf_sendwait w0 io
Proof
  strip_tac >> rewrite_tac [l3_echo_live_l0_def, l3_echo_live_unless_def] >>
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  ‘run_ok (n2w lfdn) pol EI ES w0’ by fs[echo_run_def] >>
  ‘c < LENGTH w.chans’ by metis_tac[chan_lt] >>
  ‘∃M. evs ≼ revs (n2w lfdn) pol EI ES w0 M’
    by (drule_all pftrace_locate >> disch_then (qspec_then ‘0’ strip_assume_tac) >>
        qexists_tac ‘M’ >> first_assum ACCEPT_TAC) >>
  ‘c < LENGTH (rworld (n2w lfdn) pol EI ES w0 M).chans’
    by (qpat_x_assum ‘evs ≼ _’ (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
        ‘world_at w0 (evs ++ l) = SOME (rworld (n2w lfdn) pol EI ES w0 M)’
          by metis_tac[run_world_at] >>
        ‘smono c w (rworld (n2w lfdn) pol EI ES w0 M)’ by metis_tac[world_at_smono] >>
        qpat_x_assum ‘smono _ _ _’ mp_tac >> qpat_x_assum ‘c < LENGTH w.chans’ mp_tac >>
        simp[smono_def]) >>
  ‘honestL1PFFlush$drains (n2w lfdn) pol EI ES w0 c’
    by (drule_all drains_round >> disch_then ACCEPT_TAC) >>
  ‘(∃evs'. LPREFIX (fromList evs') io ∧ (EL c w.chans).peer_sent ≼ l0_sent j evs') ∨
   flushed_open w0 io j c ∨ ep_hard_err j io ∨ ep_timed_out pf_sendwait j io’
    by (irule trace_wrap >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        TRY (qexistsl_tac [‘hw’, ‘lfdn’, ‘pol’] >> rpt conj_tac >> first_assum ACCEPT_TAC >>
             NO_TAC) >>
        qexists_tac ‘evs’ >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  TRY (asm_rewrite_tac [] >> NO_TAC) >>
  disj2_tac >> conj_tac >- (qexists_tac ‘evs'’ >> conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> irule trace_close >>
  qexistsl_tac [‘c’, ‘evs’, ‘hw’, ‘lfdn’, ‘pol’, ‘w’, ‘w0’] >> rpt conj_tac >>
  first_assum ACCEPT_TAC
QED
