(*
  Facts about the traces of diverging runs, for relating specs over
  different worlds.

  - Every finite prefix of a diverging run's trace is a prefix of the
    trace at some clock (diverge_prefix).
  - Every event of a run is a call the oracle answered (run_events_ok):
    so in a version-2 world no event is a connect or a send.
  - Without connects and sends, the endpoint world's per-episode views of
    a trace are EchoSpec2's (ch_events = ep_events, ch_read = ep_read,
    ch_sent = ep_written).
*)
Theory endpointTrace
Ancestors
  llist ffi semantics evaluateProps ml_prog ffiSpikeSocketFFI
  EchoSpec EchoSpec2 endpointWorld endpointSpecForms
Libs
  preamble

(* ------------------------------------------------------------------------
   Prefixes of a diverging run
   ------------------------------------------------------------------------ *)

Theorem prefix_FRONT[local]:
  a ≼ b ∧ a ≠ b ⇒ a ≼ FRONT b
Proof
  rw[IS_PREFIX_APPEND] >> gvs[] >> Cases_on ‘l’ using SNOC_CASES >> gvs[] >>
  qexists_tac ‘l'’ >> REWRITE_TAC[APPEND_ASSOC, GSYM SNOC_APPEND, FRONT_SNOC]
QED

Theorem diverge_prefix:
  semantics_prog st env prog (Diverge io) ∧ LPREFIX (fromList evs) io ⇒
  ∃k. evs ≼ (FST (evaluate_prog_with_clock st env k prog)).io_events
Proof
  rw[semanticsTheory.semantics_prog_def] >> CCONTR_TAC >> fs[] >>
  ‘evs ≠ []’ by (strip_tac >> fs[]) >>
  qmatch_asmsub_abbrev_tac ‘lprefix_lub (IMAGE g UNIV) io’ >>
  ‘∀k. LPREFIX (g k) (fromList (FRONT evs))’
    by (gen_tac >>
        ‘LPREFIX (g k) io’ by (fs[lprefix_lub_def] >> metis_tac[IN_IMAGE, IN_UNIV]) >>
        first_x_assum (qspec_then ‘k’ mp_tac) >> fs[Abbr ‘g’] >>
        qmatch_goalsub_abbrev_tac ‘evs ≼ ek’ >> rpt strip_tac >>
        ‘LPREFIX (fromList ek) (fromList evs) ∨ LPREFIX (fromList evs) (fromList ek)’
          by metis_tac[prefixes_lprefix_total] >>
        fs[LPREFIX_fromList, from_toList] >>
        irule prefix_FRONT >> rw[] >> strip_tac >> fs[]) >>
  ‘LPREFIX io (fromList (FRONT evs))’
    by (fs[lprefix_lub_def] >> first_x_assum irule >> rw[] >> simp[]) >>
  ‘LPREFIX (fromList evs) (fromList (FRONT evs))’ by metis_tac[LPREFIX_TRANS] >>
  fs[LPREFIX_fromList, from_toList] >>
  imp_res_tac IS_PREFIX_LENGTH >>
  Cases_on ‘evs’ using SNOC_CASES >> fs[FRONT_SNOC]
QED

(* ------------------------------------------------------------------------
   Every event is an answered call
   ------------------------------------------------------------------------ *)

(* Every call the oracle answers satisfies P *)
Definition oracle_ok_def:
  oracle_ok P (orc : 'a oracle) ⇔
    ∀n st conf bytes st' out. orc n st conf bytes = Oracle_return st' out ⇒ P n conf
End

Definition event_ok_def:
  event_ok P (IO_event n conf bs) ⇔ P n conf
End

Theorem call_FFI_rel_events_ok[local]:
  ∀f1 f2. RTC call_FFI_rel f1 f2 ⇒ oracle_ok P f1.oracle ⇒
          ∃new. f2.io_events = f1.io_events ++ new ∧ EVERY (event_ok P) new
Proof
  ho_match_mp_tac RTC_INDUCT >> conj_tac >- (rw[] >> qexists_tac ‘[]’ >> simp[]) >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  imp_res_tac call_FFI_rel_consts >> fs[] >>
  ‘∃e. f1'.io_events = f1.io_events ++ e ∧ EVERY (event_ok P) e’
    by (qpat_x_assum ‘oracle_ok _ _’ mp_tac >> qpat_x_assum ‘call_FFI_rel _ _’ mp_tac >>
        rw[call_FFI_rel_def, call_FFI_def] >> every_case_tac >> gvs[] >>
        TRY (qexists_tac ‘[]’ >> simp[] >> NO_TAC) >>
        fs[oracle_ok_def] >> res_tac >> simp[event_ok_def]) >>
  qexists_tac ‘e ++ new’ >> simp[]
QED

Theorem run_events_ok:
  semantics_prog (init_state f) init_env prog (Diverge io) ∧ f.io_events = [] ∧
  oracle_ok P f.oracle ∧ LPREFIX (fromList evs) io ⇒
  EVERY (event_ok P) evs
Proof
  strip_tac >> drule_all diverge_prefix >> strip_tac >>
  fs[evaluate_prog_with_clock_def] >> pairarg_tac >> fs[] >>
  imp_res_tac evaluate_call_FFI_rel_imp >>
  ‘(init_state f with clock := k).ffi = f’ by simp[ml_progTheory.init_state_def] >>
  fs[] >> drule call_FFI_rel_events_ok >> simp[] >>
  strip_tac >> gvs[] >> fs[IS_PREFIX_APPEND] >> gvs[EVERY_APPEND]
QED

(* ------------------------------------------------------------------------
   Without connects and sends, the endpoint views are EchoSpec2's
   ------------------------------------------------------------------------ *)

Definition no_conn_send_def:
  no_conn_send (n : ffiname) (conf : word8 list) ⇔
    n ≠ ExtCall «sock_connect» ∧ n ≠ ExtCall «sock_send»
End

Theorem event_opened_accepted[local]:
  event_ok no_conn_send ev ⇒ event_opened ev = event_accepted ev
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event n _ _’ >> Cases_on ‘n’ >>
  rw[event_ok_def, no_conn_send_def, event_opened_def, event_accepted_def] >>
  every_case_tac >> fs[]
QED

Theorem event_sent_nil[local]:
  event_ok no_conn_send ev ⇒ event_sent f ev = []
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event n _ _’ >> Cases_on ‘n’ >>
  rw[event_ok_def, no_conn_send_def, event_sent_def]
QED

Theorem opened_accepted_fds:
  EVERY (event_ok no_conn_send) evs ⇒ opened_fds evs = accepted_fds evs
Proof
  Induct_on ‘evs’ >> rw[opened_fds_def, accepted_fds_def] >>
  fs[opened_fds_def, accepted_fds_def, event_opened_accepted]
QED

Theorem ch_ep_events:
  ∀j k opn evs. EVERY (event_ok no_conn_send) evs ⇒ ch_events j k opn evs = ep_events j k opn evs
Proof
  Induct_on ‘evs’ >> rw[ch_events_def, ep_events_def, event_opened_accepted]
QED

Theorem ch_read_ep_read:
  EVERY (event_ok no_conn_send) evs ⇒ ch_read j evs = ep_read j evs
Proof
  rw[ch_read_def, EchoSpec2Theory.ep_read_def, opened_accepted_fds, ch_ep_events]
QED

Theorem MEM_ep_events[local]:
  ∀evs j k opn. MEM x (ep_events j k opn evs) ⇒ MEM x evs
Proof
  Induct >> rw[ep_events_def] >> every_case_tac >> fs[] >> metis_tac[]
QED

Theorem ch_sent_ep_written:
  EVERY (event_ok no_conn_send) evs ⇒ ch_sent j evs = ep_written j evs
Proof
  rw[ch_sent_def, ep_written_def, opened_accepted_fds, ch_ep_events, bytes_written_to_def] >>
  AP_TERM_TAC >> irule MAP_CONG >> rw[] >>
  ‘EVERY (event_ok no_conn_send) (ep_events j 0 [] evs)’ suffices_by
    (rw[EVERY_MEM] >> res_tac >> simp[event_sent_nil]) >>
  fs[EVERY_MEM] >> metis_tac[MEM_ep_events]
QED
