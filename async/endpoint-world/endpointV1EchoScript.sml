(*
  EchoSpec from its endpoint form, for fd-disciplined programs (design/35
  §4; the useful direction of echo_sym_equiv, restricted as
  v1_instance_disc is).

  From a version-1 server world sk that connects at most M clients
  (M + 3 < 2^64): its version-2 world s2 = v2of1 lfd sk and s2's drained
  endpoint world w (endpointEcho2's dworld).  The program's disciplined
  run io in sk is its run in w with version 1's calls (v1_ep_diverge), so
  the endpoint guarantee holds of io; on version 1's events it is w's
  (ep_guar_v1), so EchoSpec2's liveness holds in s2 (echo_live2_of_dworld).
  Episode j is the j-th opened fd, the j-th connection (v1_trace,
  endpointV1Proj), which gives EchoSpec's safety (from the renamed trace)
  and liveness (sent_v2of1).
*)
Theory endpointV1Echo
Ancestors
  llist ffi semantics ffiSpikeSocketFFI ffiSpikeSocketFair EchoSpec socketV2FFI
  socketV2Fair EchoSpec2 endpointWorld endpointFair endpointSpecForms
  endpointSemantics endpointInstances endpointServers endpointEcho2
  endpointV1Sim endpointV1Run endpointV1Inst endpointV1Proj
Libs
  preamble

(* MAIN: a disciplined program meeting the endpoint echo spec with version
   1's calls meets EchoSpec in every version-1 server world that connects
   at most M clients *)
Theorem echo_spec_of_endpoint_disc:
  v1_disciplined lfd prog ∧
  rg_spec (λw. ep_server_world v1_calls lfd a w ∧ no_backpressure w ∧ open_loop w)
    ep_echo_guar prog ∧
  server_world lfd sk ∧ sched_connects_le M sk.sched ∧ M + 3 < dimword (:64) ⇒
  ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog (Diverge io) ∧
       echo_safe io ∧ echo_live sk io
Proof
  strip_tac >>
  ‘∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog (Diverge io) ∧
        fd_disciplined lfd io’ by fs[v1_disciplined_def] >>
  qexists_tac ‘io’ >> simp[] >>
  qabbrev_tac ‘s2 = v2of1 lfd sk’ >>
  ‘v12rel lfd sk.sched sk s2 ∧ server_world2 lfd s2’
    by (simp[Abbr ‘s2’] >> irule v2of1_server_world2 >> simp[] >>
        qexists_tac ‘M’ >> fs[]) >>
  ‘s2.open_fds = [] ∧ sched_wf sk’ by fs[Abbr ‘s2’, v2of1_def, server_world_def] >>
  drule_then (qspec_then ‘a’ strip_assume_tac) dworld_props >>
  qabbrev_tac ‘w = dworld lfd a s2’ >>
  ‘w.calls = v2_calls’ by fs[ep_server_world_def] >>
  ‘semantics_prog (init_state (ep_ffi (w with calls := v1_calls))) init_env prog (Diverge io)’
    by (irule v1_ep_diverge >> metis_tac[]) >>
  ‘semantics_prog (init_state (socket2_ffi s2)) init_env prog (Diverge io)’
    by (irule v12_diverge >> metis_tac[]) >>
  ‘semantics_prog (init_state (ep_ffi w)) init_env prog (Diverge io)’
    by (‘(socket2_ffi s2).io_events = (ep_ffi w).io_events’
          by simp[socket2_ffi_def, ep_ffi_def] >>
        metis_tac[same_answers_semantics]) >>
  ‘ep_echo_guar (w with calls := v1_calls) io’
    by (qpat_x_assum ‘rg_spec _ _ _’ (mp_tac o REWRITE_RULE[rg_spec_def]) >>
        disch_then (qspec_then ‘w with calls := v1_calls’ mp_tac) >>
        impl_tac >- fs[ep_server_world_def, no_backpressure_def, open_loop_def, ep_rely_v1] >>
        strip_tac >> rename1 ‘ep_echo_guar _ io'’ >>
        ‘Diverge io' = Diverge io’ suffices_by (strip_tac >> fs[]) >>
        qpat_x_assum ‘semantics_prog (init_state (ep_ffi (_ with calls := _))) _ _ (Diverge io)’
          (mp_tac o Q.INST [‘b’ |-> ‘Diverge io'’] o MATCH_MP diverge_only) >>
        simp[]) >>
  ‘∀evs. LPREFIX (fromList evs) io ⇒ EVERY v1_event evs’
    by metis_tac[v1_trace] >>
  ‘sym_live (λx y. x ≼ y) w io ∧ ticks_forever w io’
    by (fs[ep_echo_guar_def] >> metis_tac[ep_guar_v1]) >>
  ‘echo_live2 s2 io’ by (irule echo_live2_of_dworld >> metis_tac[]) >>
  conj_tac
  >- ((* safety, from the renamed trace *)
      rw[echo_safe_def, bytes_written_to_def, bytes_read_from_def] >>
      drule_all v1_trace >> strip_tac >>
      Cases_on ‘MEM c (opened_fds evs)’
      >- (‘ALL_DISTINCT (opened_fds evs)’ by gvs[ALL_DISTINCT_TAKE] >>
          ‘LENGTH (opened_fds evs) ≤ dimword (:64)’ by gvs[LENGTH_TAKE] >>
          qabbrev_tac ‘j = findi c (opened_fds evs)’ >>
          ‘j < LENGTH (opened_fds evs) ∧ c = EL j (opened_fds evs)’
            by simp[Abbr ‘j’, MEM_findi, EL_findi] >>
          ‘FLAT (MAP (event_written (n2w j)) (ren_evs 0 [] evs)) =
             FLAT (MAP (event_written c) evs) ∧
           FLAT (MAP (event_read (n2w j)) (ren_evs 0 [] evs)) =
             FLAT (MAP (event_read c) evs)’
            by (conj_tac >>
                qspecl_then [‘event_written’] mp_tac (Q.GEN ‘pr’ proj_v1) >>
                qspecl_then [‘event_read’] mp_tac (Q.GEN ‘pr’ proj_v1) >>
                simp[proj_ok_written, proj_ok_read] >> metis_tac[]) >>
          fs[ep_echo_guar_def, sym_safe_def, always_def] >>
          qpat_x_assum ‘∀evs. _ ⇒ echo_safe _’ (qspec_then ‘evs’ mp_tac) >>
          simp[echo_safe_def] >>
          disch_then (qspecl_then [‘ren_evs 0 [] evs’, ‘n2w j’] mp_tac) >>
          simp[bytes_written_to_def, bytes_read_from_def] >>
          qpat_x_assum ‘FLAT (MAP (event_written _) (ren_evs _ _ _)) = _’ SUBST1_TAC >>
          qpat_x_assum ‘FLAT (MAP (event_read _) (ren_evs _ _ _)) = _’ SUBST1_TAC >>
          qpat_x_assum ‘c = _’ (SUBST1_TAC o SYM) >> simp[]) >>
      ‘FLAT (MAP (event_written c) evs) = []’
        by (irule proj_unopened >> simp[] >> metis_tac[]) >>
      simp[]) >>
  (* liveness, client by client *)
  rw[echo_live_def] >>
  ‘sent_upto c n sk =
     if MEM c (sched_conns n sk.sched)
     then sent2_upto (findi c (sched_conns n sk.sched)) n s2 else []’
    by simp[Abbr ‘s2’, sent_v2of1] >>
  reverse (Cases_on ‘MEM c (sched_conns n sk.sched)’)
  >- (qexists_tac ‘[]’ >> simp[]) >>
  qabbrev_tac ‘j = findi c (sched_conns n sk.sched)’ >>
  fs[echo_live2_def] >>
  first_x_assum (qspecl_then [‘j’, ‘n’] strip_assume_tac) >>
  qexists_tac ‘evs’ >> simp[] >>
  Cases_on ‘sent2_upto j n s2 = []’ >- simp[] >>
  ‘ep_written j evs ≠ []’ by (strip_tac >> fs[]) >>
  drule_all v1_trace >> strip_tac >>
  ‘accepted_fds evs = opened_fds evs ∧ ep_events j 0 [] evs = ch_events j 0 [] evs’
    by metis_tac[ep_events_v1] >>
  ‘j < LENGTH (opened_fds evs)’
    by (qpat_x_assum ‘ep_written j evs ≠ []’ mp_tac >>
        simp[ep_written_def] >> rw[] >> fs[]) >>
  ‘EL j (opened_fds evs) = c’
    by (‘j < LENGTH (sched_conns n sk.sched)’ by simp[Abbr ‘j’, MEM_findi] >>
        ‘j < LENGTH cs’ by gvs[LENGTH_TAKE] >>
        ‘EL j (opened_fds evs) = EL j cs’ by gvs[EL_TAKE] >>
        ‘conn_fd sk.sched j = EL j (sched_conns n sk.sched)’ by simp[conn_fd_EL] >>
        ‘EL j (sched_conns n sk.sched) = c’ by simp[Abbr ‘j’, EL_findi] >>
        metis_tac[]) >>
  ‘ep_written j evs = FLAT (MAP (event_written c) evs)’
    by (‘ALL_DISTINCT (opened_fds evs) ∧ LENGTH (opened_fds evs) ≤ dimword (:64)’
          by gvs[ALL_DISTINCT_TAKE, LENGTH_TAKE] >>
        mp_tac (Q.INST [‘pr’ |-> ‘event_written’] proj_v1) >>
        impl_tac >- (simp[proj_ok_written] >> metis_tac[]) >> strip_tac >>
        qpat_x_assum ‘accepted_fds evs = _’ (fn th => REWRITE_TAC[ep_written_def, th]) >>
        qpat_x_assum ‘ep_events _ _ _ _ = _’ (fn th => REWRITE_TAC[th]) >>
        asm_simp_tac std_ss [bytes_written_to_def]) >>
  fs[bytes_written_to_def]
QED
