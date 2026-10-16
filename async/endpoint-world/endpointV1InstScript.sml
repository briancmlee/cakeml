(*
  THE RESULT (design/35 §4): version 1, for fd-disciplined programs, is an
  instance of the endpoint world (endpointInstances' v1_instance_disc,
  with the agreed non-saturation hypothesis).

  From a version-1 server world sk:
   - its version-2 world v2of1 lfd sk is related (v12rel_init) and fair
     (v12rel_sched_wf2), so a server world;
   - v2_forward gives an endpoint world w with version 2's calls answering
     as v2of1 lfd sk;
   - w with version 1's calls answers alike on version 1's calls
     (ep_calls_v1), and the program makes no others (replays_v1_calls);
   - so the disciplined Diverge io carries over (semantics_prog_upto), and
     it is the only behaviour on both sides (diverge_only).
*)
Theory endpointV1Inst
Ancestors
  llist lprefix_lub ffi semantics ffiAgreeUpto ffiSpikeSocketFFI ffiSpikeSocketFair
  EchoSpec socketV2FFI socketV2Fair EchoSpec2 endpointWorld endpointFair
  endpointSpecForms endpointSemantics endpointInstances endpointV2Sim
  endpointV1Sim endpointV1Run
Libs
  preamble

(* ------------------------------------------------------------------------
   The calls a world offers only gate them
   ------------------------------------------------------------------------ *)

Theorem ep_deliver_calls[local]:
  ep_deliver (w with calls := c) a = ep_deliver w a with calls := c
Proof
  Cases_on ‘a’ >> rw[ep_deliver_def, upd_chan_def] >> every_case_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem FOLDL_ep_deliver_calls[local]:
  ∀as w. FOLDL ep_deliver (w with calls := c) as = FOLDL ep_deliver w as with calls := c
Proof
  Induct >> simp[ep_deliver_calls]
QED

Theorem ep_tick_calls[local]:
  ep_tick (w with calls := c) = ep_tick w with calls := c
Proof
  simp[ep_tick_def, GSYM FOLDL_ep_deliver_calls] >>
  AP_THM_TAC >> AP_TERM_TAC >> simp[eworld_component_equality]
QED

Theorem ep_chan_of_calls[local, simp]:
  ep_chan_of (w with calls := c) f = ep_chan_of w f
Proof
  simp[ep_chan_of_def]
QED

Theorem ep_readable_calls[local, simp]:
  ep_readable (w with calls := c) fd = ep_readable w fd
Proof
  simp[ep_readable_def]
QED

Theorem upd_chan_calls[local]:
  upd_chan j g (w with calls := c) = upd_chan j g w with calls := c
Proof
  simp[upd_chan_def]
QED

(* For version 1's calls, a world with fewer calls answers alike *)
Theorem ep_call_calls:
  MEM n v1_calls ∧ MEM n w.calls ∧ MEM n c ⇒
  ep_call n conf bytes (w with calls := c) =
  OPTION_MAP (λ(b, w'). (b, w' with calls := c)) (ep_call n conf bytes w)
Proof
  rw[v1_calls_def] >>
  simp[ep_call_def, ep_tick_calls, ep_accept_def, ep_alloc_def, ep_used_def,
       ep_read_def, ep_send_def, ep_conn_err_def, upd_chan_calls] >>
  every_case_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  gvs[upd_chan_def]
QED

Theorem ep_ffi_fn_calls[local]:
  MEM n v1_calls ∧ MEM n w.calls ⇒
  ep_ffi_fn n conf bytes (w with calls := v1_calls) =
  OPTION_MAP (λ(b, w'). (b, w' with calls := v1_calls)) (ep_ffi_fn n conf bytes w)
Proof
  strip_tac >> simp[ep_ffi_fn_def] >>
  ‘MEM n v1_calls’ by simp[] >>
  drule_all (Q.INST [‘c’ |-> ‘v1_calls’] ep_call_calls) >>
  disch_then (qspecl_then [‘conf’, ‘bytes’] SUBST1_TAC) >>
  Cases_on ‘ep_call n conf bytes w’ >> simp[] >> rename1 ‘SOME p’ >>
  PairCases_on ‘p’ >> simp[]
QED

(* A call keeps the calls offered *)
Theorem ep_deliver_calls_same[local]:
  ∀as w. (FOLDL ep_deliver w as).calls = w.calls
Proof
  Induct >> simp[] >> Cases >> rw[ep_deliver_def, upd_chan_def] >>
  every_case_tac >> simp[] >> rpt (pairarg_tac >> gvs[])
QED

Theorem ep_ffi_fn_calls_same[local]:
  ep_ffi_fn n conf bytes w = SOME (b, w') ⇒ w'.calls = w.calls
Proof
  rw[ep_ffi_fn_def, AllCaseEqs()] >> simp[] >>
  gvs[ep_call_def, AllCaseEqs(), ep_tick_def, ep_deliver_calls_same,
      ep_accept_def, ep_alloc_def, ep_connect_def, ep_read_def, ep_send_def,
      ep_conn_err_def, ep_shutdown_def, ep_close_def, upd_chan_def] >>
  rpt (pairarg_tac >> gvs[AllCaseEqs()])
QED

Theorem ep_ffi_with[local]:
  ep_ffi w with ffi_state := w' = ep_ffi w'
Proof
  simp[ep_ffi_def]
QED

Theorem MEM_v1_v2[local]:
  MEM m v1_calls ⇒ MEM m v2_calls
Proof
  simp[v2_calls_def]
QED

(* MAIN: on version 1's calls, the world with version 1's calls answers
   as the world with version 2's *)
Theorem ep_answers_v1:
  ∀cs w. w.calls = v2_calls ∧
         EVERY (λ(n, conf, bytes). ∃m. n = ExtCall m ∧ MEM m v1_calls) cs ⇒
         ffi_answers (ep_ffi (w with calls := v1_calls)) cs = ffi_answers (ep_ffi w) cs
Proof
  Induct >> simp[ffi_answers_def, FORALL_PROD] >> rpt strip_tac >> gvs[] >>
  simp[ep_ffi_def, ep_oracle_def] >>
  ‘MEM m w.calls’ by simp[MEM_v1_v2] >>
  drule_all ep_ffi_fn_calls >> disch_then (fn th => REWRITE_TAC[th]) >>
  rename1 ‘ep_ffi_fn m cf bs w’ >>
  Cases_on ‘ep_ffi_fn m cf bs w’ >> simp[] >> rename1 ‘SOME p’ >> PairCases_on ‘p’ >>
  simp[] >> REWRITE_TAC[REWRITE_RULE[ep_ffi_def] ep_ffi_with] >>
  REWRITE_TAC[GSYM ep_ffi_def] >> first_x_assum irule >> simp[] >>
  metis_tac[ep_ffi_fn_calls_same]
QED

(* ------------------------------------------------------------------------
   The rely, with version 1's calls
   ------------------------------------------------------------------------ *)

Theorem ep_after_v1[local]:
  ∀cs w w1. w.calls = v2_calls ∧ ep_after (w with calls := v1_calls) cs = SOME w1 ⇒
            ∃w'. ep_after w cs = SOME w' ∧ w1 = w' with calls := v1_calls ∧
                 w'.calls = v2_calls
Proof
  Induct >> simp[ep_after_def, FORALL_PROD] >> rpt gen_tac >> strip_tac >>
  rename1 ‘ep_ffi_fn n conf bytes’ >>
  Cases_on ‘MEM n v1_calls’
  >- (‘MEM n w.calls’ by simp[MEM_v1_v2] >>
      drule_all ep_ffi_fn_calls >> disch_then (qspecl_then [‘conf’, ‘bytes’] assume_tac) >>
      gvs[] >> Cases_on ‘ep_ffi_fn n conf bytes w’ >> gvs[] >>
      rename1 ‘SOME p’ >> PairCases_on ‘p’ >> gvs[] >>
      ‘p1.calls = v2_calls’ by metis_tac[ep_ffi_fn_calls_same] >>
      qpat_x_assum ‘∀w w1. _’ irule >> simp[]) >>
  ‘ep_ffi_fn n conf bytes (w with calls := v1_calls) = NONE’
    by simp[ep_ffi_fn_def, ep_call_def] >>
  gvs[]
QED

Theorem ep_step_ok_calls[local]:
  ∀as w. ep_step_ok (w with calls := c) as = ep_step_ok w as
Proof
  Induct >> simp[ep_step_ok_def, ep_deliver_calls] >> Cases >>
  simp[ep_arrival_ok_def]
QED

Theorem ep_rely_v1[local]:
  ep_rely w ∧ w.calls = v2_calls ⇒ ep_rely (w with calls := v1_calls)
Proof
  rw[ep_rely_def, ep_sched_ok_def] >>
  drule_all ep_after_v1 >> strip_tac >> gvs[] >>
  first_x_assum drule >>
  ‘(w'' with calls := v1_calls) with clock := w''.clock + 1 =
   (w'' with clock := w''.clock + 1) with calls := v1_calls’
    by simp[eworld_component_equality] >>
  simp[ep_step_ok_calls]
QED

(* ------------------------------------------------------------------------
   The result
   ------------------------------------------------------------------------ *)

Theorem run_calls_ffi_answers[local]:
  ∀cs f. run_calls f cs = ffi_answers f cs
Proof
  Induct >> simp[run_calls_def, ffi_answers_def, FORALL_PROD] >>
  rpt gen_tac >> CASE_TAC >> simp[]
QED

(* The non-saturation hypothesis (agreed 2026-10-16): the schedule connects
   at most M clients *)
Definition sched_connects_le_def:
  sched_connects_le M ll ⇔ ∀m. LENGTH (sched_conns m ll) ≤ M
End

(* MAIN: for an fd-disciplined program, a version-1 server world that
   connects at most M clients (M + 3 < 2^64) and an endpoint server world
   with version 1's calls, no backpressure and a fixed schedule have the
   same behaviours (endpointInstances' v1_instance_disc, with the
   hypothesis) *)
Theorem v1_instance_disc_thm:
  ∀lfd sk prog M.
    server_world lfd sk ∧ sched_connects_le M sk.sched ∧ M + 3 < dimword (:64) ∧
    v1_disciplined lfd prog ⇒
    ∃a w. ep_server_world v1_calls lfd a w ∧ no_backpressure w ∧ open_loop w ∧
          ep_rely w ∧
          ∀b. semantics_prog (init_state (socket_ffi sk)) init_env prog b ⇔
              semantics_prog (init_state (ep_ffi w)) init_env prog b
Proof
  rpt strip_tac >>
  fs[v1_disciplined_def] >> first_x_assum drule >> strip_tac >>
  qabbrev_tac ‘s2 = v2of1 lfd sk’ >>
  ‘v12rel lfd sk.sched sk s2’
    by (simp[Abbr ‘s2’] >> irule v12rel_init >> fs[server_world_def, sched_connects_le_def] >>
        gen_tac >> first_x_assum (qspec_then ‘m’ mp_tac) >> decide_tac) >>
  ‘sched_wf2 s2’ by metis_tac[v12rel_sched_wf2, server_world_def] >>
  ‘server_world2 lfd s2’
    by (simp[server_world2_def] >> simp[Abbr ‘s2’, v2of1_def, alloc1_ok]) >>
  drule v2_forward >> strip_tac >>
  qexistsl_tac [‘a’, ‘w with calls := v1_calls’] >>
  ‘w.calls = v2_calls’ by fs[ep_server_world_def] >>
  rpt conj_tac
  >- fs[ep_server_world_def]
  >- fs[no_backpressure_def]
  >- fs[open_loop_def]
  >- simp[ep_rely_v1] >>
  ‘semantics_prog (init_state (ep_ffi (w with calls := v1_calls))) init_env prog (Diverge io)’
    by (‘init_state (ep_ffi (w with calls := v1_calls)) =
         init_state (socket_ffi sk) with ffi := ep_ffi (w with calls := v1_calls)’
          by simp[ml_progTheory.init_state_def,
                  semanticPrimitivesTheory.state_component_equality] >>
        pop_assum SUBST1_TAC >> irule semantics_prog_upto >>
        simp[ml_progTheory.init_state_def, socket_ffi_def, ep_ffi_def] >>
        REWRITE_TAC[GSYM socket_ffi_def, GSYM ep_ffi_def,
                    GSYM ml_progTheory.init_state_def] >>
        rw[agree_upto_def] >>
        ‘ffi_answers (socket_ffi sk) cs = ffi_answers (socket2_ffi s2) cs’
          by (irule v12_agree >> metis_tac[server_world_def]) >>
        ‘ffi_answers (socket2_ffi s2) cs = ffi_answers (ep_ffi w) cs’
          by fs[same_answers_def, GSYM run_calls_ffi_answers] >>
        drule_all v1_clock_calls >> strip_tac >>
        ‘EVERY (λ(n, conf, bytes). ∃m. n = ExtCall m ∧ MEM m v1_calls) cs’
          by metis_tac[replays_v1_calls] >>
        drule_all ep_answers_v1 >> simp[]) >>
  metis_tac[diverge_only]
QED
