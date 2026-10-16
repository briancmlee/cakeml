(*
  EchoSpec to its endpoint form, for fd-disciplined programs: the ⇒
  direction of the disciplined echo_sym_equiv (endpointV1Echo has ⇐).

  An endpoint server world w with version 1's calls, no backpressure and a
  fixed schedule, that does not fill the fd space (nonsat1), answers as its
  version-2 world sk0 = v2of lfd a w.  The version-1 world v1of2 lfd sk0
  (endpointV1Conv) is a bounded version-1 server world, so EchoSpec gives
  a run there; the program is disciplined, so the run is its run in sk0
  (v12_diverge) and in w (v1_ep_diverge).  Along it:
   - client j's bytes in sk0 are fd F2 j's in v1of2 lfd sk0, and episode j's
     written bytes are fd F2 j's (v1of2_sent, v1of2_written), so EchoSpec's
     liveness is EchoSpec2's per episode (live2_of_v1);
   - endpointEcho2Conv's endpoint_of_live2 then gives the endpoint
     liveness and ticks_forever, for the class of programs making only
     version 1's calls (rclass_v1);
   - safety per renamed fd is safety per fd (v1_sym_safe).
  The ticks argument adds a client to a world connecting M: hence one more
  free fd than nonsat asks for (nonsat1).
*)
Theory endpointV1EchoConv
Ancestors
  llist ffi semantics ffiSpikeSocketFFI ffiSpikeSocketFair EchoSpec socketV2FFI
  socketV2Fair EchoSpec2 endpointWorld endpointFair endpointSpecForms
  endpointSemantics endpointInstances endpointServers endpointV2Sim endpointEcho2
  endpointV2Prefix endpointEcho2Conv endpointV1Sim endpointV1Run endpointV1Inst
  endpointV1Proj endpointV1Conv endpointV1Echo
Libs
  preamble

(* ------------------------------------------------------------------------
   The statement's pieces
   ------------------------------------------------------------------------ *)

(* EchoSpec, over the version-1 server worlds connecting at most M clients
   (endpointV1Echo's echo_spec_of_endpoint_disc concludes this) *)
Definition echo_spec_le_def:
  echo_spec_le lfd prog ⇔
    ∀sk M. server_world lfd sk ∧ sched_connects_le M sk.sched ∧ M + 3 < dimword (:64) ⇒
           ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog (Diverge io) ∧
                echo_safe io ∧ echo_live sk io
End

(* HYPOTHESIS (user decision 2026-10-16, design/35): nonsat, with room for
   one more client.  With plain nonsat the converse is false at reserved =
   [], M = 2^64 - 4: a program that stops polling once it has accepted
   2^64 - 4 clients and seen all their EOFs meets echo_spec_le but not
   ticks_forever *)
Definition nonsat1_def:
  nonsat1 lfd a (w:eworld) ⇔
    ∃M. LENGTH w.reserved + M + 4 < dimword (:64) ∧ ∀n. nconn (v2of lfd a w) n ≤ M
End

(* ------------------------------------------------------------------------
   The rely, with version 1's calls
   ------------------------------------------------------------------------ *)

Theorem ep_after_v1_rev:
  ∀cs w w'. w.calls = v2_calls ∧ EVERY (λ(n, conf, bys). MEM n v1_calls) cs ∧
            ep_after w cs = SOME w' ⇒
            ep_after (w with calls := v1_calls) cs = SOME (w' with calls := v1_calls)
Proof
  Induct >> simp[ep_after_def, FORALL_PROD] >> rpt gen_tac >> strip_tac >>
  rename1 ‘ep_ffi_fn n conf bys w’ >>
  ‘MEM n w.calls’ by simp[MEM_v1_v2] >>
  drule_all ep_ffi_fn_calls >> disch_then (qspecl_then [‘conf’, ‘bys’] SUBST1_TAC) >>
  Cases_on ‘ep_ffi_fn n conf bys w’ >> gvs[] >>
  rename1 ‘ep_ffi_fn n conf bys w = SOME q’ >> PairCases_on ‘q’ >>
  gvs[] >> first_x_assum irule >> simp[] >> metis_tac[ep_ffi_fn_calls_same]
QED

(* With version 2's calls, the world is in the class of programs making
   only version 1's calls *)
Theorem rclass_v1:
  ep_server_world v1_calls lfd a w ∧ no_backpressure w ∧ open_loop w ∧ ep_rely w ⇒
  rclass (λn. MEM n v1_calls) lfd a (w with calls := v2_calls)
Proof
  strip_tac >>
  ‘w with calls := v1_calls = w’ by fs[ep_server_world_def, eworld_component_equality] >>
  simp[rclass_def] >> rpt conj_tac
  >- fs[ep_server_world_def]
  >- fs[no_backpressure_def]
  >- fs[open_loop_def]
  >- (simp[rely_on_def] >> conj_tac >- fs[ep_rely_def] >> rpt strip_tac >>
      ‘ep_after (w with calls := v1_calls) cs = SOME (w' with calls := v1_calls)’
        by (mp_tac (Q.SPECL [‘cs’, ‘w with calls := v2_calls’, ‘w'’] ep_after_v1_rev) >>
            simp[]) >>
      gvs[] >>
      fs[ep_rely_def, ep_sched_ok_def] >> first_x_assum drule >>
      ‘(w' with calls := v1_calls) with clock := w'.clock + 1 =
       (w' with clock := w'.clock + 1) with calls := v1_calls’
        by simp[eworld_component_equality] >>
      simp[ep_step_ok_calls]) >>
  simp[v1_calls_def]
QED

(* ------------------------------------------------------------------------
   Clients not yet connected have sent nothing
   ------------------------------------------------------------------------ *)

Theorem step_ok2_data[local]:
  ∀xs s. step_ok2 s xs ∧ data_of j xs ≠ [] ⇒
         j < LENGTH s.clients + LENGTH (FILTER is_conn2 xs)
Proof
  Induct >- simp[data_of_def] >> Cases >> rpt gen_tac >> strip_tac >>
  fs[step_ok2_def, arrival_ok2_def, is_conn2_def] >>
  first_x_assum drule >>
  fs[data_of_def, deliver2_def, update_client_def] >> rw[] >> fs[] >>
  Cases_on ‘n = j’ >> fs[]
QED

Theorem sent2_unconn:
  server_world2 lfd sk ∧ nconn sk n ≤ j ⇒ sent2_upto j n sk = []
Proof
  strip_tac >>
  ‘∀m. m ≤ n ⇒ sent2_upto j m sk = []’ suffices_by simp[] >>
  Induct >- simp[sent2_upto_def, arrivals2_upto_def] >> strip_tac >>
  ‘sent2_upto j m sk = []’ by fs[] >> simp[sent2_upto_SUC] >>
  CCONTR_TAC >>
  ‘step_ok2 (ticks2 m sk) (fut_step sk.future m)’
    by (fs[server_world2_def, sched_wf2_def] >>
        first_x_assum (qspec_then ‘m’ mp_tac) >> simp[next_step2_fut, ticks2_future]) >>
  drule_all step_ok2_data >>
  ‘LENGTH (ticks2 m sk).clients = nconn sk m’
    by (fs[server_world2_def] >> drule ticks2_clients >> simp[]) >>
  ‘nconn sk (SUC m) = nconn sk m + LENGTH (FILTER is_conn2 (fut_step sk.future m))’
    by simp[nconn_def, arrivals2_upto_SUC, FILTER_APPEND] >>
  ‘nconn sk (SUC m) ≤ nconn sk n’ by simp[nconn_mono] >>
  decide_tac
QED

(* ------------------------------------------------------------------------
   The run in the version-1 world of a version-2 world
   ------------------------------------------------------------------------ *)

Theorem v1of2_run:
  v1_disciplined lfd prog ∧ server_world2 lfd sk2 ∧ (∀n. nconn sk2 n ≤ M) ∧
  LENGTH sk2.reserved + M + 3 < dimword (:64) ∧
  semantics_prog (init_state (socket_ffi (v1of2 lfd sk2))) init_env prog (Diverge io) ⇒
  fd_disciplined lfd io ∧
  semantics_prog (init_state (socket2_ffi sk2)) init_env prog (Diverge io)
Proof
  strip_tac >> drule_all v1of2_props >> strip_tac >>
  ‘fd_disciplined lfd io’
    by (fs[v1_disciplined_def] >> first_x_assum drule >> strip_tac >>
        metis_tac[diverge_unique]) >>
  simp[] >> irule v12_diverge >> fs[server_world_def, server_world2_def] >>
  metis_tac[]
QED

(* Client j's bytes in the version-2 world are fd F2 j's *)
Theorem v1of2_sent:
  server_world2 lfd sk2 ∧ (∀n. nconn sk2 n ≤ M) ∧
  LENGTH sk2.reserved + M + 3 < dimword (:64) ∧ j < nconn sk2 n ⇒
  sent2_upto j n sk2 = sent_upto (F2 lfd sk2 j) n (v1of2 lfd sk2)
Proof
  strip_tac >> drule_all v1of2_props >> strip_tac >>
  drule_all v1of2_sched >> strip_tac >>
  ‘(∀i i'. i < M + 1 ∧ i' < M + 1 ∧ F2 lfd sk2 i = F2 lfd sk2 i' ⇒ i = i')’
    by (mp_tac F2_fresh >> impl_tac >- fs[server_world2_def] >> simp[]) >>
  ‘findi (F2 lfd sk2 j) (GENLIST (F2 lfd sk2) (nconn sk2 n)) = j’
    by (irule findi_GENLIST >> simp[] >> qexists_tac ‘M + 1’ >> simp[] >>
        qpat_x_assum ‘∀n. nconn sk2 n ≤ M’ (qspec_then ‘n’ mp_tac) >> decide_tac) >>
  mp_tac (Q.INST [‘sk’ |-> ‘v1of2 lfd sk2’, ‘c’ |-> ‘F2 (lfd:word64) (sk2:sockets2) (j:num)’] sent_v2of1) >>
  impl_tac >- first_assum ACCEPT_TAC >> disch_then SUBST1_TAC >>
  simp[v1of2_conns, MEM_GENLIST] >>
  reverse IF_CASES_TAC >- metis_tac[] >>
  simp[sent2_upto_def, v2of1_def]
QED

(* Episode j's written bytes are fd F2 j's *)
Theorem v1of2_written:
  v1_disciplined lfd prog ∧ server_world2 lfd sk2 ∧ (∀n. nconn sk2 n ≤ M) ∧
  LENGTH sk2.reserved + M + 3 < dimword (:64) ∧
  semantics_prog (init_state (socket_ffi (v1of2 lfd sk2))) init_env prog (Diverge io) ∧
  LPREFIX (fromList evs) io ∧ j < nconn sk2 n ⇒
  ep_written j evs = bytes_written_to (F2 lfd sk2 j) evs
Proof
  strip_tac >> drule_all v1of2_run >> strip_tac >>
  drule_all v1of2_props >> strip_tac >>
  qabbrev_tac ‘s1 = v1of2 lfd sk2’ >>
  ‘sched_wf s1 ∧ sk2.open_fds = []’ by fs[server_world_def, server_world2_def] >>
  drule_all (Q.INST [‘ll0’ |-> ‘s1.sched’, ‘s2’ |-> ‘sk2’] v1_trace) >> strip_tac >>
  ‘accepted_fds evs = opened_fds evs ∧ ep_events j 0 [] evs = ch_events j 0 [] evs’
    by metis_tac[ep_events_v1] >>
  ‘∀i. i < nconn sk2 n ⇒ conn_fd s1.sched i = F2 lfd sk2 i’
    by (rpt strip_tac >>
        ‘i < LENGTH (sched_conns n s1.sched)’ by simp[Abbr ‘s1’, v1of2_conns] >>
        drule conn_fd_sched >> simp[Abbr ‘s1’, v1of2_conns]) >>
  ‘ALL_DISTINCT (opened_fds evs) ∧ LENGTH (opened_fds evs) ≤ dimword (:64)’
    by gvs[ALL_DISTINCT_TAKE, LENGTH_TAKE] >>
  ‘LENGTH (opened_fds evs) = k’ by gvs[LENGTH_TAKE] >>
  ‘∀i. i < LENGTH (opened_fds evs) ⇒ EL i (opened_fds evs) = conn_fd s1.sched i’
    by (rpt strip_tac >> gvs[EL_TAKE]) >>
  reverse (Cases_on ‘j < LENGTH (opened_fds evs)’)
  >- (‘ep_written j evs = []’
        by (REWRITE_TAC[ep_written_def] >>
            qpat_x_assum ‘accepted_fds evs = _’ SUBST1_TAC >>
            qpat_x_assum ‘¬(j < _)’ (fn th => REWRITE_TAC[th])) >>
      ‘¬MEM (F2 lfd sk2 j) (opened_fds evs)’
        by (strip_tac >> fs[MEM_EL] >> rename1 ‘i < LENGTH (opened_fds evs)’ >>
            ‘i < nconn sk2 n’ by decide_tac >>
            ‘F2 lfd sk2 i = F2 lfd sk2 j’ by metis_tac[] >>
            ‘∀i i'. i < M + 1 ∧ i' < M + 1 ∧ F2 lfd sk2 i = F2 lfd sk2 i' ⇒ i = i'’
              by (mp_tac F2_fresh >> impl_tac >- fs[server_world2_def] >> simp[]) >>
            qpat_x_assum ‘∀n. nconn sk2 n ≤ M’ (qspec_then ‘n’ assume_tac) >>
            ‘i < M + 1 ∧ j < M + 1’ by decide_tac >>
            ‘i = j’ by metis_tac[] >> fs[]) >>
      ‘FLAT (MAP (event_written (F2 lfd sk2 j)) evs) = []’
        by (irule proj_unopened >> metis_tac[]) >>
      simp[bytes_written_to_def]) >>
  ‘EL j (opened_fds evs) = F2 lfd sk2 j’ by metis_tac[] >>
  qabbrev_tac ‘c = F2 lfd sk2 j’ >>
  mp_tac (Q.INST [‘pr’ |-> ‘event_written’] proj_v1) >>
  impl_tac >- (simp[proj_ok_written] >> metis_tac[]) >> strip_tac >>
  qpat_x_assum ‘accepted_fds evs = _’ (fn th => REWRITE_TAC[ep_written_def, th]) >>
  qpat_x_assum ‘ep_events _ _ _ _ = _’ (fn th => REWRITE_TAC[th]) >>
  asm_simp_tac std_ss [bytes_written_to_def]
QED

(* MAIN: EchoSpec's liveness in the version-1 world is EchoSpec2's in the
   version-2 world *)
Theorem live2_of_v1:
  v1_disciplined lfd prog ∧ server_world2 lfd sk2 ∧ (∀n. nconn sk2 n ≤ M) ∧
  LENGTH sk2.reserved + M + 3 < dimword (:64) ∧
  semantics_prog (init_state (socket_ffi (v1of2 lfd sk2))) init_env prog (Diverge io) ∧
  echo_live (v1of2 lfd sk2) io ⇒
  echo_live2 sk2 io
Proof
  strip_tac >> simp[echo_live2_def] >> rpt gen_tac >>
  reverse (Cases_on ‘j < nconn sk2 n’)
  >- (qexists_tac ‘[]’ >> simp[] >>
      ‘sent2_upto j n sk2 = []’ by (irule sent2_unconn >> fs[] >> metis_tac[]) >>
      simp[]) >>
  ‘sent2_upto j n sk2 = sent_upto (F2 lfd sk2 j) n (v1of2 lfd sk2)’
    by (irule v1of2_sent >> metis_tac[]) >>
  qpat_x_assum ‘echo_live _ _’ (mp_tac o REWRITE_RULE [echo_live_def]) >>
  disch_then (qspecl_then [‘F2 lfd sk2 j’, ‘n’] strip_assume_tac) >>
  qexists_tac ‘evs’ >> simp[] >>
  ‘ep_written j evs = bytes_written_to (F2 lfd sk2 j) evs’
    by (irule v1of2_written >> metis_tac[]) >>
  simp[]
QED

(* MAIN: in a bounded version-2 server world, EchoSpec over the bounded
   version-1 worlds gives a disciplined run, live per episode *)
Theorem v1_live2:
  v1_disciplined lfd prog ∧ echo_spec_le lfd prog ∧
  server_world2 lfd sk ∧ (∀n. nconn sk n ≤ N) ∧ LENGTH sk.reserved + N + 3 < dimword (:64) ⇒
  ∃io. semantics_prog (init_state (socket_ffi (v1of2 lfd sk))) init_env prog (Diverge io) ∧
       semantics_prog (init_state (socket2_ffi sk)) init_env prog (Diverge io) ∧
       fd_disciplined lfd io ∧ echo_safe io ∧ echo_live2 sk io
Proof
  strip_tac >> drule_all v1of2_props >> strip_tac >>
  qpat_assum ‘echo_spec_le _ _’ (mp_tac o REWRITE_RULE [echo_spec_le_def]) >>
  disch_then (qspecl_then [‘v1of2 lfd sk’, ‘N’] mp_tac) >>
  impl_tac >- (fs[sched_connects_le_conns] >> decide_tac) >> strip_tac >>
  qexists_tac ‘io’ >> drule_all v1of2_run >> strip_tac >> simp[] >>
  irule live2_of_v1 >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Safety, per renamed fd
   ------------------------------------------------------------------------ *)

Theorem ren_evs_cons[local]:
  LENGTH (ren_evs k opn [ev]) ≤ 1 ∧
  ∃k' opn'. ∀evs. ren_evs k opn (ev :: evs) = ren_evs k opn [ev] ++ ren_evs k' opn' evs
Proof
  simp[ren_evs_def] >> every_case_tac >> simp[ren_evs_def] >> metis_tac[]
QED

(* A prefix of the renamed trace is the renamed trace of a prefix *)
Theorem ren_evs_prefix_inv:
  ∀evs k opn r. r ≼ ren_evs k opn evs ⇒ ∃evs1. evs1 ≼ evs ∧ r = ren_evs k opn evs1
Proof
  Induct >- (simp[ren_evs_def] >> rpt strip_tac >> qexists_tac ‘[]’ >> simp[ren_evs_def]) >>
  rpt gen_tac >>
  qspecl_then [‘opn’, ‘k’, ‘h’] strip_assume_tac (GEN_ALL ren_evs_cons) >>
  qabbrev_tac ‘x = ren_evs k opn [h]’ >> qpat_x_assum ‘Abbrev _’ kall_tac >>
  simp[] >> strip_tac >>
  Cases_on ‘r’ >- (qexists_tac ‘[]’ >> simp[ren_evs_def]) >>
  rename1 ‘e :: t ≼ _’ >>
  ‘x = [] ∨ ∃y. x = [y]’ by (Cases_on ‘x’ >> fs[] >> Cases_on ‘t'’ >> fs[]) >> gvs[]
  >- (last_x_assum (qspecl_then [‘k'’, ‘opn'’, ‘e :: t’] mp_tac) >> simp[] >>
      strip_tac >> qexists_tac ‘h :: evs1’ >> simp[])
  >> last_x_assum (qspecl_then [‘k'’, ‘opn'’, ‘t’] mp_tac) >> simp[] >>
  strip_tac >> qexists_tac ‘h :: evs1’ >> simp[]
QED

(* MAIN: EchoSpec's safety per fd is the endpoint safety per renamed fd *)
Theorem v1_sym_safe:
  semantics_prog (init_state (socket_ffi s1)) init_env prog (Diverge io) ∧
  fd_disciplined lfd io ∧ v12rel lfd ll0 s1 s2 ∧ sched_wf s1 ∧ s2.open_fds = [] ∧
  echo_safe io ⇒
  sym_safe echo_safe io
Proof
  rw[sym_safe_def, always_def] >> simp[echo_safe_def, LPREFIX_fromList, from_toList] >>
  rpt strip_tac >> drule ren_evs_prefix_inv >> strip_tac >> gvs[] >>
  ‘LPREFIX (fromList evs1) io’
    by (irule LPREFIX_TRANS >> qexists_tac ‘fromList evs’ >> simp[LPREFIX_fromList, from_toList]) >>
  drule_all v1_trace >> strip_tac >>
  ‘ALL_DISTINCT (opened_fds evs1) ∧ LENGTH (opened_fds evs1) ≤ dimword (:64)’
    by gvs[ALL_DISTINCT_TAKE, LENGTH_TAKE] >>
  ‘c = n2w (w2n c) ∧ w2n c < dimword (:64)’ by simp[w2n_lt] >>
  qabbrev_tac ‘j = w2n c’ >> pop_assum kall_tac >>
  qpat_x_assum ‘c = _’ SUBST1_TAC >>
  Cases_on ‘j < LENGTH (opened_fds evs1)’
  >- (qabbrev_tac ‘fd1 = EL j (opened_fds evs1)’ >>
      mp_tac (Q.INST [‘pr’ |-> ‘event_written’, ‘c’ |-> ‘fd1’, ‘evs’ |-> ‘evs1’] proj_v1) >>
      impl_tac >- (simp[proj_ok_written] >> metis_tac[]) >> strip_tac >>
      mp_tac (Q.INST [‘pr’ |-> ‘event_read’, ‘c’ |-> ‘fd1’, ‘evs’ |-> ‘evs1’] proj_v1) >>
      impl_tac >- (simp[proj_ok_read] >> metis_tac[]) >> strip_tac >>
      fs[echo_safe_def, bytes_written_to_def, bytes_read_from_def]) >>
  ‘FLAT (MAP (event_written (n2w j)) (ren_evs 0 [] evs1)) = [] ∧
   FLAT (MAP (event_read (n2w j)) (ren_evs 0 [] evs1)) = []’
    by (conj_tac >> irule proj_ren_beyond >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        simp[proj_ok_written, proj_ok_read] >> gvs[LENGTH_TAKE]) >>
  simp[bytes_written_to_def, bytes_read_from_def]
QED

(* ------------------------------------------------------------------------
   The converse
   ------------------------------------------------------------------------ *)

Theorem ext1_nconn_eq:
  ∀n. nconn (ext1 lfd sk k m) n = if n ≤ k then nconn sk n else nconn sk k + 1
Proof
  Induct >- simp[nconn_def, arrivals2_upto_def] >>
  ‘∀s n. nconn s (SUC n) = nconn s n + LENGTH (FILTER is_conn2 (fut_step s.future n))’
    by simp[nconn_def, arrivals2_upto_SUC, FILTER_APPEND] >>
  simp[ext1_fut] >> rw[] >> fs[is_conn2_def] >>
  ‘n = k’ by decide_tac >> fs[]
QED

(* MAIN: for an fd-disciplined program, EchoSpec over the version-1 server
   worlds connecting at most M clients implies the endpoint echo spec with
   version 1's calls, in every world leaving room for one more client *)
Theorem endpoint_of_echo_spec_le:
  v1_disciplined lfd prog ∧ echo_spec_le lfd prog ⇒
  rg_spec (λw. ep_server_world v1_calls lfd a w ∧ no_backpressure w ∧ open_loop w ∧
               nonsat1 lfd a w)
    ep_echo_guar prog
Proof
  rw[rg_spec_def] >>
  qabbrev_tac ‘w2 = w with calls := v2_calls’ >>
  ‘rclass (λn. MEM n v1_calls) lfd a w2’ by metis_tac[rclass_v1] >>
  ‘w2 with calls := v1_calls = w’
    by fs[Abbr ‘w2’, ep_server_world_def, eworld_component_equality] >>
  ‘v2of lfd a w2 = v2of lfd a w’ by simp[Abbr ‘w2’, v2of_def] >>
  fs[nonsat1_def] >>
  ‘nonsat lfd a w2’
    by (simp[nonsat_def] >> qexists_tac ‘M’ >> asm_rewrite_tac[] >> fs[Abbr ‘w2’]) >>
  qabbrev_tac ‘sk0 = v2of lfd a w’ >>
  ‘server_world2 lfd sk0 ∧ same_answers (socket2_ffi sk0) (ep_ffi w2)’
    by (imp_res_tac rclass_polls >> fs[rclass_def] >>
        drule_all v2of_props_polls >> simp[]) >>
  ‘sk0.reserved = w.reserved’ by simp[Abbr ‘sk0’, v2of_def] >>
  ‘LENGTH sk0.reserved + M + 3 < dimword (:64)’ by fs[] >>
  drule_all v1_live2 >> strip_tac >> qexists_tac ‘io’ >>
  drule_all v1of2_props >> strip_tac >>
  qabbrev_tac ‘s1 = v1of2 lfd sk0’ >>
  ‘sched_wf s1 ∧ sk0.open_fds = []’ by fs[server_world_def, server_world2_def] >>
  ‘∀evs. LPREFIX (fromList evs) io ⇒ EVERY v1_event evs’
    by (rpt strip_tac >> drule_all (Q.INST [‘ll0’ |-> ‘s1.sched’] v1_trace) >> simp[]) >>
  (* the run in the endpoint world with version 1's calls *)
  ‘w2.calls = v2_calls’ by simp[Abbr ‘w2’] >>
  ‘semantics_prog (init_state (ep_ffi w)) init_env prog (Diverge io)’
    by (qpat_x_assum ‘w2 with calls := v1_calls = w’ (SUBST1_TAC o SYM) >>
        irule v1_ep_diverge >> metis_tac[]) >>
  simp[] >>
  (* liveness and ticks, with version 2's calls *)
  mp_tac (Q.INST [‘Q’ |-> ‘λn. MEM n v1_calls’, ‘w’ |-> ‘w2’] endpoint_of_live2) >>
  impl_tac
  >- (asm_rewrite_tac[] >> rpt conj_tac
      >- (rpt strip_tac >> res_tac >> fs[EVERY_MEM, v1_event_def, ev_in_def] >>
          metis_tac[])
      >> rpt strip_tac >>
      ‘∃io'. semantics_prog (init_state (socket_ffi (v1of2 lfd sk1))) init_env prog
               (Diverge io') ∧
             semantics_prog (init_state (socket2_ffi sk1)) init_env prog (Diverge io') ∧
             fd_disciplined lfd io' ∧ echo_safe io' ∧ echo_live2 sk1 io'’
        suffices_by metis_tac[] >>
      irule v1_live2 >> simp[] >> qexists_tac ‘M + 1’ >>
      gvs[ext1_nconn_eq] >> conj_tac
      >- (rw[] >> irule LESS_EQ_TRANS >> qexists_tac ‘M’ >> simp[]) >>
      fs[ext1_def]) >>
  strip_tac >>
  ‘sym_live (λx y. x ≼ y) (w2 with calls := v1_calls) io ∧
   ticks_forever (w2 with calls := v1_calls) io’ by metis_tac[ep_guar_v1] >>
  rfs[] >> simp[ep_echo_guar_def] >>
  irule v1_sym_safe >> metis_tac[]
QED

(* MAIN: the disciplined echo_sym_equiv: for an fd-disciplined program,
   the endpoint echo spec with version 1's calls gives EchoSpec over the
   bounded version-1 worlds, which gives the endpoint spec in every world
   leaving room for one more client *)
Theorem echo_sym_equiv_disc_thm:
  ∀lfd a prog.
    v1_disciplined lfd prog ⇒
    (rg_spec (λw. ep_server_world v1_calls lfd a w ∧ no_backpressure w ∧ open_loop w)
       ep_echo_guar prog ⇒ echo_spec_le lfd prog) ∧
    (echo_spec_le lfd prog ⇒
     rg_spec (λw. ep_server_world v1_calls lfd a w ∧ no_backpressure w ∧ open_loop w ∧
                  nonsat1 lfd a w)
       ep_echo_guar prog)
Proof
  rpt strip_tac
  >- (REWRITE_TAC[echo_spec_le_def] >> rpt strip_tac >>
      drule_all echo_spec_of_endpoint_disc >> simp[])
  >> metis_tac[endpoint_of_echo_spec_le]
QED
