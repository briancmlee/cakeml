(*
  The version-1 specs from their endpoint forms, for fd-disciplined
  programs: what echo, HTTP and the key-value server share (design/35 §4;
  the useful direction of the sym_equiv claims, restricted as
  v1_instance_disc is).

  From a version-1 server world sk that connects at most M clients
  (M + 3 < 2^64): its version-2 world v2of1 lfd sk, and that world's
  drained endpoint world (endpointEcho2's dworld) with version 1's calls.
   - v1_endpoint_run: the program's disciplined run io in sk is its run
     in that endpoint world (v1_ep_diverge), so the endpoint guarantee
     holds of io (v1_run_ok collects the facts the rest uses);
   - v1_bytes: per-fd bytes of io are the renamed trace's (endpointServers'
     ren_evs: episode j on fd n2w j), and fds never opened have none;
   - v1_live: endpoint liveness for P is liveness per connection against
     sk's schedule (via EchoSpec2's per episode, live2_of_dworld).
*)
Theory endpointV1Disc
Ancestors
  llist ffi semantics ffiSpikeSocketFFI ffiSpikeSocketFair EchoSpec socketV2FFI
  socketV2Fair EchoSpec2 endpointWorld endpointFair endpointSpecForms
  endpointSemantics endpointInstances endpointServers endpointEcho2
  endpointV1Sim endpointV1Run endpointV1Inst endpointV1Proj
Libs
  preamble

Overload dw1 = “λlfd a sk. dworld lfd a (v2of1 lfd sk)”

(* The facts about a disciplined run used below *)
Definition v1_run_ok_def:
  v1_run_ok lfd a sk prog io ⇔
    server_world lfd sk ∧ fd_disciplined lfd io ∧ v12rel lfd sk.sched sk (v2of1 lfd sk) ∧
    server_world2 lfd (v2of1 lfd sk) ∧ sched_wf sk ∧ (v2of1 lfd sk).open_fds = [] ∧
    semantics_prog (init_state (socket_ffi sk)) init_env prog (Diverge io) ∧
    semantics_prog (init_state (socket2_ffi (v2of1 lfd sk))) init_env prog (Diverge io) ∧
    semantics_prog (init_state (ep_ffi (dw1 lfd a sk))) init_env prog (Diverge io) ∧
    (dw1 lfd a sk).calls = v2_calls
End

(* MAIN: a disciplined program meeting an endpoint spec with version 1's
   calls runs in a bounded version-1 server world as in its endpoint
   world, so the endpoint guarantee holds of its run *)
Theorem v1_endpoint_run:
  v1_disciplined lfd prog ∧
  rg_spec (λw. ep_server_world v1_calls lfd a w ∧ no_backpressure w ∧ open_loop w) G prog ∧
  server_world lfd sk ∧ sched_connects_le M sk.sched ∧ M + 3 < dimword (:64) ⇒
  ∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog (Diverge io) ∧
       v1_run_ok lfd a sk prog io ∧ G (dw1 lfd a sk with calls := v1_calls) io
Proof
  strip_tac >>
  ‘∃io. semantics_prog (init_state (socket_ffi sk)) init_env prog (Diverge io) ∧
        fd_disciplined lfd io’ by fs[v1_disciplined_def] >>
  qexists_tac ‘io’ >> simp[v1_run_ok_def] >>
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
  simp[] >>
  qpat_x_assum ‘rg_spec _ _ _’ (mp_tac o REWRITE_RULE[rg_spec_def]) >>
  disch_then (qspec_then ‘w with calls := v1_calls’ mp_tac) >>
  impl_tac >- fs[ep_server_world_def, no_backpressure_def, open_loop_def, ep_rely_v1] >>
  strip_tac >> rename1 ‘G _ io'’ >>
  ‘Diverge io' = Diverge io’ suffices_by (strip_tac >> fs[]) >>
  qpat_x_assum ‘semantics_prog (init_state (ep_ffi (_ with calls := _))) _ _ (Diverge io)’
    (mp_tac o Q.INST [‘b’ |-> ‘Diverge io'’] o MATCH_MP diverge_only) >>
  simp[]
QED

Theorem v1_run_trace[local]:
  v1_run_ok lfd a sk prog io ∧ LPREFIX (fromList evs) io ⇒
  EVERY v1_event evs ∧
  (∀pre ev post c. evs = pre ++ ev :: post ∧
                   (event_written c ev ≠ [] ∨ event_read c ev ≠ []) ⇒
                   MEM c (opened_fds pre)) ∧
  ∃cs k. opened_fds evs = TAKE k cs ∧ k ≤ LENGTH cs ∧ ALL_DISTINCT cs ∧ ¬MEM lfd cs ∧
         LENGTH cs + 3 < dimword (:64) ∧ ∀j. j < LENGTH cs ⇒ conn_fd sk.sched j = EL j cs
Proof
  rw[v1_run_ok_def] >> drule_all v1_trace >> simp[]
QED

(* MAIN: per-fd bytes are the renamed trace's; an fd never opened has none *)
Theorem v1_bytes:
  v1_run_ok lfd a sk prog io ∧ LPREFIX (fromList evs) io ⇒
  (∀c. MEM c (opened_fds evs) ⇒
       ∃j. bytes_written_to (n2w j) (ren_evs 0 [] evs) = bytes_written_to c evs ∧
           bytes_read_from (n2w j) (ren_evs 0 [] evs) = bytes_read_from c evs) ∧
  (∀c. ¬MEM c (opened_fds evs) ⇒ bytes_written_to c evs = [] ∧ bytes_read_from c evs = [])
Proof
  strip_tac >> drule_all v1_run_trace >> strip_tac >>
  ‘ALL_DISTINCT (opened_fds evs) ∧ LENGTH (opened_fds evs) ≤ dimword (:64)’
    by gvs[ALL_DISTINCT_TAKE, LENGTH_TAKE] >>
  rw[bytes_written_to_def, bytes_read_from_def]
  >- (qexists_tac ‘findi c (opened_fds evs)’ >>
      ‘findi c (opened_fds evs) < LENGTH (opened_fds evs) ∧
       c = EL (findi c (opened_fds evs)) (opened_fds evs)’ by simp[MEM_findi, EL_findi] >>
      conj_tac
      >- (mp_tac (Q.INST [‘pr’ |-> ‘event_written’, ‘j’ |-> ‘findi c (opened_fds evs)’] proj_v1) >>
          impl_tac >- (simp[proj_ok_written] >> metis_tac[]) >> simp[])
      >> mp_tac (Q.INST [‘pr’ |-> ‘event_read’, ‘j’ |-> ‘findi c (opened_fds evs)’] proj_v1) >>
      impl_tac >- (simp[proj_ok_read] >> metis_tac[]) >> simp[])
  >> irule proj_unopened >> simp[] >> metis_tac[]
QED

(* MAIN: endpoint liveness for P (weaker for a shorter input, stronger for
   a longer output) is liveness per connection against the schedule *)
Theorem v1_live:
  v1_run_ok lfd a sk prog io ∧
  (∀x x' y y'. P x' y ∧ x ≼ x' ∧ y ≼ y' ⇒ P x y') ∧ P [] [] ∧
  sym_live P (dw1 lfd a sk with calls := v1_calls) io ∧
  ticks_forever (dw1 lfd a sk with calls := v1_calls) io ⇒
  ∀c n. ∃evs. LPREFIX (fromList evs) io ∧ P (sent_upto c n sk) (bytes_written_to c evs)
Proof
  strip_tac >>
  ‘∀evs. LPREFIX (fromList evs) io ⇒ EVERY v1_event evs’ by metis_tac[v1_run_trace] >>
  ‘sym_live P (dw1 lfd a sk) io ∧ ticks_forever (dw1 lfd a sk) io’
    by (fs[v1_run_ok_def] >> metis_tac[ep_guar_v1]) >>
  ‘∀j n. ∃evs. LPREFIX (fromList evs) io ∧ P (sent2_upto j n (v2of1 lfd sk)) (ep_written j evs)’
    by (irule live2_of_dworld >> fs[v1_run_ok_def] >> metis_tac[]) >>
  rpt gen_tac >>
  ‘server_world lfd sk’ by fs[v1_run_ok_def] >>
  ‘sent_upto c n sk =
     if MEM c (sched_conns n sk.sched)
     then sent2_upto (findi c (sched_conns n sk.sched)) n (v2of1 lfd sk) else []’
    by simp[sent_v2of1] >>
  reverse (Cases_on ‘MEM c (sched_conns n sk.sched)’)
  >- (qexists_tac ‘[]’ >> simp[bytes_written_to_def]) >>
  qabbrev_tac ‘j = findi c (sched_conns n sk.sched)’ >>
  first_x_assum (qspecl_then [‘j’, ‘n’] strip_assume_tac) >>
  drule_all v1_run_trace >> strip_tac >>
  ‘accepted_fds evs = opened_fds evs ∧ ep_events j 0 [] evs = ch_events j 0 [] evs’
    by metis_tac[ep_events_v1] >>
  reverse (Cases_on ‘j < LENGTH (opened_fds evs)’)
  >- (qexists_tac ‘[]’ >> simp[bytes_written_to_def] >>
      ‘ep_written j evs = []’
        by (REWRITE_TAC[ep_written_def] >>
            qpat_x_assum ‘accepted_fds evs = _’ SUBST1_TAC >>
            qpat_x_assum ‘¬(j < _)’ (fn th => REWRITE_TAC[th])) >>
      fs[]) >>
  qexists_tac ‘evs’ >> simp[] >>
  ‘EL j (opened_fds evs) = c’
    by (‘j < LENGTH (sched_conns n sk.sched)’ by simp[Abbr ‘j’, MEM_findi] >>
        ‘j < LENGTH cs’ by gvs[LENGTH_TAKE] >>
        ‘EL j (opened_fds evs) = EL j cs’ by gvs[EL_TAKE] >>
        ‘conn_fd sk.sched j = EL j (sched_conns n sk.sched)’ by simp[conn_fd_EL] >>
        ‘EL j (sched_conns n sk.sched) = c’ by simp[Abbr ‘j’, EL_findi] >>
        metis_tac[]) >>
  ‘ep_written j evs = bytes_written_to c evs’
    by (‘ALL_DISTINCT (opened_fds evs) ∧ LENGTH (opened_fds evs) ≤ dimword (:64)’
          by gvs[ALL_DISTINCT_TAKE, LENGTH_TAKE] >>
        mp_tac (Q.INST [‘pr’ |-> ‘event_written’] proj_v1) >>
        impl_tac >- (simp[proj_ok_written] >> metis_tac[]) >> strip_tac >>
        qpat_x_assum ‘accepted_fds evs = _’ (fn th => REWRITE_TAC[ep_written_def, th]) >>
        qpat_x_assum ‘ep_events _ _ _ _ = _’ (fn th => REWRITE_TAC[th]) >>
        asm_simp_tac std_ss [bytes_written_to_def]) >>
  fs[]
QED
