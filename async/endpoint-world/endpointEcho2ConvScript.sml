(*
  EchoSpec2 in the endpoint world, the converse direction (a completeness
  check): a program meeting echo_spec2 meets the endpoint form of EchoSpec2
  in the simple class, for worlds that do not saturate the fd space.

  An endpoint world w of the class answers as its version-2 world v2of w
  (endpointV2Sim), so the program has the same trace in both.  Along the
  trace, channel c's peer has sent what client c sends in the ticks so far,
  and accepts are first in, first out (ginv).  So echo_live2 gives the
  endpoint liveness.  The program keeps polling: if it stopped after k
  polls, it would run alike in a world that agrees on the first k steps
  and then connects a new client that sends a byte (endpointV2Prefix), and
  echo_spec2 there forces it to accept that client, which needs one more
  poll.  That world exists unless the fd space is full: hence nonsat.
*)
Theory endpointEcho2Conv
Ancestors
  llist ffi semantics ml_prog ffiSpikeSocketFFI socketV2FFI socketV2Fair EchoSpec2
  endpointWorld endpointFair endpointSpecForms endpointSemantics endpointServers
  endpointInstances endpointV2Sim endpointTrace endpointEcho2 endpointV2Prefix ffiAgreeUpto
Libs
  preamble

(* ------------------------------------------------------------------------
   The run's invariant in any world of the class
   ------------------------------------------------------------------------ *)

Theorem v2rel_after:
  ∀cs w sk w'. v2rel lfd a sk w ∧ ep_after w cs = SOME w' ⇒
               ∃sk'. v2rel lfd a sk' w' ∧ w'.env = w.env
Proof
  Induct >> simp[ep_after_def, FORALL_PROD] >- metis_tac[] >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  drule v2rel_call >>
  disch_then (qspecl_then [‘p_1’, ‘p_1'’, ‘p_2’] strip_assume_tac) >> gvs[] >>
  imp_res_tac ep_ffi_fn_env >> first_x_assum drule_all >> simp[]
QED

Theorem pdata_untr:
  ∀es. pdata c es = data_of c (untr lfd a es)
Proof
  Induct >> simp[pdata_def, data_of_def, untr_def] >> Cases >>
  rw[untr_def] >> fs[pdata_def, data_of_def]
QED

Theorem incoming_untr:
  ∀es w q. ep_step_ok w es ∧ w.listening = [(lfd, a, q)] ⇒
           LENGTH (FILTER ($= (Incoming a)) es) = LENGTH (FILTER is_conn2 (untr lfd a es))
Proof
  Induct >> simp[untr_def] >> rpt gen_tac >> strip_tac >> fs[ep_step_ok_def] >>
  ‘∃q'. (ep_deliver w h).listening = [(lfd, a, q')]’
    by (qspecl_then [‘[h]’, ‘w’, ‘q’] mp_tac deliver_chans_count >> simp[]) >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on ‘h’ >> fs[untr_def, is_conn2_def, ep_arrival_ok_def] >> rw[] >> gvs[]
QED

Definition ginv_def:
  ginv lfd a (w0:eworld) evs (w:eworld) ⇔
    w0.clock ≤ w.clock ∧
    (∀c. recv_of w c = sent2_upto c (w.clock − w0.clock) (v2of lfd a w0)) ∧
    queue_ok lfd a (LENGTH (opened_fds evs)) w ∧
    LENGTH w.chans = nconn (v2of lfd a w0) (w.clock − w0.clock)
End

Definition simple_class_def:
  simple_class lfd a w ⇔
    ep_server_world v2_calls lfd a w ∧ no_backpressure w ∧ open_loop w ∧ ep_rely w
End

Theorem class_reach:
  simple_class lfd a w0 ∧ replay_ok w0 evs ⇒
  ∃sk. v2rel lfd a sk (ep_replay w0 evs) ∧ (ep_replay w0 evs).env = w0.env
Proof
  rw[simple_class_def] >> drule_all v2of_props >> strip_tac >>
  drule replay_ok_after >> strip_tac >> metis_tac[v2rel_after]
QED

Theorem class_inv:
  simple_class lfd a w0 ⇒
  ∀evs. replay_ok w0 evs ⇒ ginv lfd a w0 evs (ep_replay w0 evs)
Proof
  strip_tac >> ho_match_mp_tac SNOC_INDUCT >> conj_tac
  >- (fs[simple_class_def, ep_server_world_def] >>
      simp[ginv_def, ep_replay_def, recv_of_def, queue_ok_def, opened_fds_def,
           sent2_upto_def, arrivals2_upto_def, nconn_def]) >>
  rpt gen_tac >> strip_tac >> REWRITE_TAC[SNOC_APPEND] >> rpt strip_tac >>
  ‘replay_ok w0 evs’ by fs[replay_ok_APPEND] >> fs[] >>
  drule_all class_reach >> strip_tac >>
  drule replay_SNOC >> strip_tac >> gvs[] >>
  qabbrev_tac ‘v0 = ep_replay w0 evs’ >>
  ‘v0.calls = v2_calls’ by fs[v2rel_def] >>
  qpat_x_assum ‘ep_ffi_fn _ _ _ _ = _’ mp_tac >> simp[ep_ffi_fn_def] >>
  rw[AllCaseEqs()] >> rename1 ‘ep_call n conf (MAP FST bs) v0 = SOME (MAP SND bs, w2)’ >>
  fs[ginv_def, opened_fds_SNOC] >>
  qpat_x_assum ‘_ with hist := _ = _’ (SUBST_ALL_TAC o SYM) >> simp[] >>
  Cases_on ‘n = «sock_poll»’
  >- (gvs[] >>
      ‘w2 = ep_tick v0’
        by (qpat_x_assum ‘ep_call _ _ _ _ = _’ mp_tac >> simp[ep_call_def] >> rw[]) >>
      ‘event_opened (IO_event (ExtCall «sock_poll») conf bs) = NONE’
        by simp[event_opened_def, event_accepted_def] >>
      gvs[] >>
      ‘ep_step_ok (settle v0 with clock := v0.clock + 1) (v0.env v0.clock v0.hist)’
        by (fs[simple_class_def, ep_rely_def, ep_sched_ok_def] >>
            ‘∃cs. ep_after w0 cs = SOME v0’ by (drule replay_ok_after >> simp[Abbr ‘v0’]) >>
            first_x_assum drule >> fs[]) >>
      ‘core lfd a sk v0’ by fs[v2rel_def] >>
      imp_res_tac core_all_up >> imp_res_tac settle_id >>
      qabbrev_tac ‘c = v0.clock’ >>
      qabbrev_tac ‘es = w0.env c []’ >>
      ‘v0.env c v0.hist = es’ by fs[simple_class_def, open_loop_def, Abbr ‘es’] >>
      ‘fut_step (v2of lfd a w0).future (c − w0.clock) = untr lfd a es’
        by simp[v2of_def, fut_step_def, LNTH_LGENLIST, Abbr ‘es’] >>
      ‘ep_tick v0 = FOLDL ep_deliver (v0 with clock := c + 1) es’
        by (simp[ep_tick_def, Abbr ‘c’] >>
            qpat_x_assum ‘v0.env _ _ = es’ (SUBST1_TAC o SYM) >> fs[]) >>
      fs[] >>
      drule deliver_all >> disch_then strip_assume_tac >>
      ‘(FOLDL ep_deliver (v0 with clock := c + 1) es).clock = c + 1’
        by simp[ep_deliver_fields] >>
      ‘c + 1 − w0.clock = SUC (c − w0.clock)’ by simp[] >>
      simp[] >> rpt conj_tac
      >- simp[pdata_untr, sent2_upto_SUC]
      >- (irule deliver_all_queue >> simp[])
      >> ‘∃q. v0.listening = [(lfd, a, q)]’ by fs[queue_ok_def] >>
      qspecl_then [‘es’, ‘v0 with clock := c + 1’, ‘q’] mp_tac deliver_chans_count >>
      simp[] >> strip_tac >>
      ‘LENGTH (FILTER ($= (Incoming a)) es) = LENGTH (FILTER is_conn2 (untr lfd a es))’
        by (irule incoming_untr >> qexistsl_tac [‘q’, ‘v0 with clock := c + 1’] >> simp[]) >>
      simp[nconn_def, arrivals2_upto_SUC, FILTER_APPEND] >> fs[nconn_def]) >>
  Cases_on ‘n = «sock_accept»’
  >- (gvs[] >> qabbrev_tac ‘k = LENGTH (opened_fds evs)’ >>
      ‘v0.listening = [(lfd, a, GENLIST (λi. i + k) (LENGTH v0.chans − k))] ∧
       k ≤ LENGTH v0.chans’ by fs[queue_ok_def] >>
      drule_all call_accept_effect >> strip_tac >> gvs[]
      >- (‘event_opened (IO_event (ExtCall «sock_accept») conf bs) = NONE’
            by (simp[event_opened_def, event_accepted_def] >> rw[] >> fs[]) >>
          fs[queue_ok_def]) >>
      drule GENLIST_pop >> strip_tac >> gvs[] >>
      ‘LENGTH bs = 9’
        by (qpat_x_assum ‘MAP SND bs = _’ (mp_tac o Q.AP_TERM ‘LENGTH’) >> simp[]) >>
      ‘event_opened (IO_event (ExtCall «sock_accept») conf bs) = SOME f’
        by simp[event_opened_def, event_accepted_def] >>
      fs[queue_ok_def]) >>
  drule_all call_other_effect >> strip_tac >>
  ‘MEM n v2_calls’
    by (CCONTR_TAC >> qpat_x_assum ‘ep_call _ _ _ _ = _’ mp_tac >> simp[ep_call_def]) >>
  ‘event_opened (IO_event (ExtCall n) conf bs) = NONE’
    by (gvs[v2_calls_def, v1_calls_def] >> simp[event_opened_def, event_accepted_def]) >>
  fs[queue_ok_def]
QED

(* Episode j is channel j *)
Theorem class_chan:
  simple_class lfd a w0 ∧ replay_ok w0 evs ∧ j < LENGTH (opened_fds evs) ⇒
  ep_chan w0 evs j = SOME j
Proof
  strip_tac >> simp[ep_chan_def] >>
  qmatch_goalsub_abbrev_tac ‘FILTER P (COUNT_LIST (LENGTH evs))’ >>
  ‘LENGTH (FILTER P (COUNT_LIST (LENGTH evs))) = LENGTH (opened_fds evs)’
    by (qspec_then ‘LENGTH evs’ mp_tac opened_fds_TAKE >>
        simp[Abbr ‘P’]) >>
  simp[] >>
  ‘j < LENGTH (FILTER P (COUNT_LIST (LENGTH evs)))’ by simp[] >>
  drule EL_FILTER_COUNT_LIST >>
  qmatch_goalsub_abbrev_tac ‘i < LENGTH evs’ >> strip_tac >>
  ‘LENGTH (opened_fds (TAKE i evs)) = j’ by simp[opened_fds_TAKE, Abbr ‘P’] >>
  ‘TAKE (SUC i) evs = TAKE i evs ++ [EL i evs]’
    by (drule TAKE_EL_SNOC >> simp[SNOC_APPEND, ADD1]) >>
  ‘replay_ok w0 (TAKE i evs ++ [EL i evs])’ by metis_tac[replay_ok_TAKE] >>
  ‘replay_ok w0 (TAKE i evs)’ by fs[replay_ok_APPEND] >>
  drule_all class_inv >> strip_tac >>
  drule_all class_reach >> strip_tac >>
  drule replay_SNOC >> strip_tac >> fs[] >>
  qabbrev_tac ‘v0 = ep_replay w0 (TAKE i evs)’ >>
  ‘v0.calls = v2_calls’ by fs[v2rel_def] >>
  qpat_x_assum ‘ep_ffi_fn _ _ _ _ = _’ mp_tac >> simp[ep_ffi_fn_def] >>
  rw[AllCaseEqs()] >> rename1 ‘ep_call n conf (MAP FST bs) v0 = SOME (MAP SND bs, w2)’ >>
  fs[Abbr ‘P’] >> rfs[] >>
  ‘MEM n v2_calls’
    by (CCONTR_TAC >> qpat_x_assum ‘ep_call _ _ _ _ = _’ mp_tac >> simp[ep_call_def]) >>
  ‘n = «sock_accept»’
    by (CCONTR_TAC >> gvs[v2_calls_def, v1_calls_def, event_opened_def, event_accepted_def]) >>
  gvs[] >> fs[ginv_def, queue_ok_def] >>
  drule_all call_accept_effect >> strip_tac >> gvs[]
  >- gvs[event_opened_def, event_accepted_def] >>
  drule GENLIST_pop >> strip_tac >> gvs[] >>
  gvs[event_opened_def, event_accepted_def] >>
  qpat_x_assum ‘w2 with hist := _ = _’ (SUBST_ALL_TAC o SYM) >> fs[]
QED

Theorem replay_clock_npolls:
  ∀w evs. replay_ok w evs ⇒ (ep_replay w evs).clock = w.clock + npolls (calls_of evs)
Proof
  ho_match_mp_tac replay_ok_ind >>
  rw[replay_ok_def, ep_replay_def, calls_of_def, npolls_def] >>
  every_case_tac >> fs[] >> imp_res_tac ep_ffi_fn_clock >>
  fs[calls_of_def, npolls_def]
QED

(* ------------------------------------------------------------------------
   One more client after step k
   ------------------------------------------------------------------------ *)

(* HYPOTHESIS for the converse: the environment opens at most M channels,
   leaving room for one more (else, once the fd space is full, nothing can
   arrive and a program may stop polling) *)
Definition nonsat_def:
  nonsat lfd a (w:eworld) ⇔
    ∃M. LENGTH w.reserved + M + 3 < dimword (:64) ∧ ∀n. nconn (v2of lfd a w) n ≤ M
End

(* The world sk up to step k, then a new client m that sends a byte *)
Definition ext1_def:
  ext1 lfd (sk:sockets2) k m =
    sk with future :=
      LGENLIST (λi. if i < k then fut_step sk.future i
                    else if i = k then [Connect2 lfd; Data2 m [0w]] else []) NONE
End

Theorem ext1_fut:
  fut_step (ext1 lfd sk k m).future i =
    if i < k then fut_step sk.future i
    else if i = k then [Connect2 lfd; Data2 m [0w]] else []
Proof
  simp[ext1_def, fut_step_def, LNTH_LGENLIST]
QED

Theorem ext1_agree:
  sbf sk (ext1 lfd sk k m) ∧ fut_agree k sk.future (ext1 lfd sk k m).future
Proof
  simp[sbf_def, ext1_def, fut_agree_def, fut_step_def, LNTH_LGENLIST] >>
  simp[socketV2FFITheory.sockets2_component_equality]
QED

Theorem ticks2_sbf:
  ∀i s1 s2 k. i ≤ k ∧ sbf s1 s2 ∧ fut_agree k s1.future s2.future ⇒
              sbf (ticks2 i s1) (ticks2 i s2) ∧
              fut_agree (k − i) (ticks2 i s1).future (ticks2 i s2).future
Proof
  Induct >> simp[ticks2_def] >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [‘tick2 s1’, ‘tick2 s2’, ‘k − 1’] mp_tac) >>
  impl_tac
  >- (‘fut_step s1.future 0 = fut_step s2.future 0’ by fs[fut_agree_def] >>
      simp[tick2_sbf] >> irule fut_agree_tick2 >>
      ‘SUC (k − 1) = k’ by simp[] >> simp[]) >>
  simp[ADD1]
QED

Theorem step_ok2_sbf:
  sbf s1 s2 ⇒ (step_ok2 s1 xs ⇔ step_ok2 s2 xs)
Proof
  rw[sbf_eq] >> simp[step_ok2_with_future]
QED

Theorem sbf_ticks2_fields:
  sbf s1 s2 ⇒ s1.reserved = s2.reserved ∧ LENGTH s1.clients = LENGTH s2.clients ∧
              s1.listening = s2.listening
Proof
  rw[sbf_eq] >> simp[]
QED

Theorem ticks2_reserved:
  ∀n s. (ticks2 n s).reserved = s.reserved
Proof
  Induct >> simp[ticks2_def] >> rw[tick2_def] >> every_case_tac >> simp[] >>
  ‘∀xs s. (FOLDL deliver2 s xs).reserved = s.reserved’
    by (Induct >> simp[] >> Cases >> rw[deliver2_def, update_client_def]) >>
  simp[]
QED

Theorem ext1_world:
  server_world2 lfd sk ∧ LENGTH sk.reserved + nconn sk k + 3 < dimword (:64) ⇒
  server_world2 lfd (ext1 lfd sk k (nconn sk k))
Proof
  strip_tac >> qabbrev_tac ‘sk1 = ext1 lfd sk k (nconn sk k)’ >>
  ‘sbf sk sk1 ∧ fut_agree k sk.future sk1.future’ by simp[Abbr ‘sk1’, ext1_agree] >>
  ‘sk1.listening = sk.listening ∧ sk1.clients = sk.clients ∧ sk1.open_fds = sk.open_fds ∧
   sk1.alloc = sk.alloc ∧ sk1.reserved = sk.reserved’ by simp[Abbr ‘sk1’, ext1_def] >>
  fs[server_world2_def, sched_wf2_def] >> gen_tac >>
  simp[next_step2_fut, ticks2_future] >>
  ‘fut_step sk1.future n =
     if n < k then fut_step sk.future n
     else if n = k then [Connect2 lfd; Data2 (nconn sk k) [0w]] else []’
    by simp[Abbr ‘sk1’, ext1_fut] >>
  pop_assum SUBST1_TAC >>
  IF_CASES_TAC
  >- (qspecl_then [‘n’, ‘sk’, ‘sk1’, ‘k’] mp_tac ticks2_sbf >> simp[] >> strip_tac >>
      first_x_assum (qspec_then ‘n’ mp_tac) >>
      simp[next_step2_fut, ticks2_future] >> metis_tac[step_ok2_sbf]) >>
  IF_CASES_TAC >> simp[step_ok2_def] >>
  qpat_x_assum ‘n = k’ SUBST_ALL_TAC >>
  qspecl_then [‘k’, ‘sk’, ‘sk1’, ‘k’] mp_tac ticks2_sbf >> simp[] >> strip_tac >>
  imp_res_tac sbf_ticks2_fields >>
  ‘LENGTH (ticks2 k sk).clients = nconn sk k’
    by (‘sched_wf2 sk’ by simp[sched_wf2_def] >> drule ticks2_clients >> simp[] >> metis_tac[]) >>
  ‘MAP FST (ticks2 k sk).listening = [lfd]’
    by (ONCE_REWRITE_TAC[ticks2_listening] >>
        qpat_assum ‘sk.listening = [_]’ (fn th => REWRITE_TAC[th]) >> simp[]) >>
  Cases_on ‘(ticks2 k sk).listening’ >> fs[] >>
  rename1 ‘(ticks2 k sk).listening = p :: _’ >> PairCases_on ‘p’ >> gvs[] >>
  simp[arrival_ok2_def, deliver2_def, ticks2_reserved, AFUPDKEY_def, EL_APPEND_EQN,
       empty_conn_def] >>
  qpat_x_assum ‘[_] = _’ (SUBST_ALL_TAC o SYM) >>
  simp[AFUPDKEY_def, EL_APPEND_EQN, empty_conn_def]
QED

Theorem diverge_unique:
  semantics_prog st env prog (Diverge io1) ∧ semantics_prog st env prog (Diverge io2) ⇒
  io1 = io2
Proof
  rw[semanticsTheory.semantics_prog_def] >>
  irule LPREFIX_ANTISYM >> fs[lprefix_lub_def] >> metis_tac[]
QED

Theorem arrivals_agree:
  ∀t. fut_agree k f1 f2 ∧ t ≤ k ⇒ arrivals2_upto t f1 = arrivals2_upto t f2
Proof
  Induct >- simp[arrivals2_upto_def] >> strip_tac >>
  REWRITE_TAC[arrivals2_upto_SUC] >> fs[fut_agree_def]
QED

Theorem ext1_nconn:
  t ≤ k ⇒ nconn (ext1 lfd sk k m) t = nconn sk t
Proof
  strip_tac >> simp[nconn_def] >>
  ‘arrivals2_upto t (ext1 lfd sk k m).future = arrivals2_upto t sk.future’
    suffices_by simp[] >>
  irule arrivals_agree >> qexists_tac ‘k’ >> simp[] >>
  metis_tac[ext1_agree, fut_agree_def]
QED

Theorem ext1_sent:
  sent2_upto m (SUC k) (ext1 lfd sk k m) ≠ []
Proof
  simp[sent2_upto_SUC, ext1_fut, data_of_def]
QED

(* ------------------------------------------------------------------------
   The converse
   ------------------------------------------------------------------------ *)

(* echo_spec2 makes a program keep polling in every world of the class
   that does not saturate *)
Theorem echo_spec2_ticks:
  echo_spec2 lfd prog ∧ simple_class lfd a w ∧ nonsat lfd a w ∧
  semantics_prog (init_state (socket2_ffi (v2of lfd a w))) init_env prog (Diverge io) ⇒
  ticks_forever w io
Proof
  rw[ticks_forever_def, eventually_def] >> CCONTR_TAC >> fs[] >>
  ‘simple_class lfd a w’ by simp[] >>
  fs[simple_class_def] >> drule_all v2of_props >> strip_tac >>
  qabbrev_tac ‘sk0 = v2of lfd a w’ >>
  ‘semantics_prog (init_state (ep_ffi w)) init_env prog (Diverge io)’
    by (‘(socket2_ffi sk0).io_events = (ep_ffi w).io_events’
          by simp[socket2_ffi_def, ep_ffi_def] >>
        metis_tac[same_answers_semantics]) >>
  ‘∀evs. LPREFIX (fromList evs) io ⇒
         (ep_replay w evs).clock = w.clock + npolls (calls_of evs)’
    by metis_tac[trace_replay_ok, replay_clock_npolls] >>
  ‘∀evs. LPREFIX (fromList evs) io ⇒ w.clock + npolls (calls_of evs) < n’
    by (rpt strip_tac >>
        ‘¬(n ≤ (ep_replay w evs).clock)’ by metis_tac[] >>
        ‘(ep_replay w evs).clock = w.clock + npolls (calls_of evs)’ by metis_tac[] >>
        decide_tac) >>
  ‘w.clock < n’
    by (‘LPREFIX (fromList []) io’ by simp[] >>
        ‘w.clock + npolls (calls_of []) < n’ by metis_tac[] >>
        fs[npolls_def, calls_of_def]) >>
  qabbrev_tac ‘kk = n − w.clock − 1’ >>
  ‘∀evs. LPREFIX (fromList evs) io ⇒ npolls (calls_of evs) ≤ kk’
    by (rpt strip_tac >> res_tac >> simp[Abbr ‘kk’]) >>
  qabbrev_tac ‘m = nconn sk0 kk’ >>
  ‘LENGTH sk0.reserved + m + 3 < dimword (:64)’
    by (fs[nonsat_def, Abbr ‘m’, Abbr ‘sk0’] >>
        first_x_assum (qspec_then ‘kk’ assume_tac) >> fs[v2of_def]) >>
  qabbrev_tac ‘sk1 = ext1 lfd sk0 kk m’ >>
  ‘server_world2 lfd sk1’ by (simp[Abbr ‘sk1’, Abbr ‘m’] >> irule ext1_world >> fs[]) >>
  ‘semantics_prog (init_state (socket2_ffi sk1)) init_env prog (Diverge io)’
    by (irule diverge_same_prefix >> qexistsl_tac [‘kk’, ‘sk0’] >>
        simp[Abbr ‘sk1’, ext1_agree]) >>
  qpat_assum ‘echo_spec2 _ _’ (mp_tac o SIMP_RULE std_ss [echo_spec2_def]) >>
  disch_then (qspec_then ‘sk1’ mp_tac) >> impl_tac >- fs[] >> strip_tac >>
  ‘io' = io’ by metis_tac[diverge_unique] >> gvs[] >>
  fs[echo_live2_def] >>
  first_x_assum (qspecl_then [‘m’, ‘SUC kk’] strip_assume_tac) >>
  rename1 ‘sent2_upto m (SUC kk) sk1 ≼ ep_written m evs’ >>
  ‘ep_written m evs ≠ []’
    by (strip_tac >> fs[] >> metis_tac[ext1_sent, Abbr ‘sk1’]) >>
  ‘EVERY (event_ok no_conn_send) evs’
    by (qpat_assum ‘semantics_prog (init_state (socket2_ffi sk1)) _ _ _’
          (fn th => mp_tac (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
             (Q.INST [‘P’ |-> ‘no_conn_send’] run_events_ok)) th)) >>
        simp[socket2_ffi_def, socket2_oracle_ok]) >>
  ‘m < LENGTH (opened_fds evs)’
    by (fs[ep_written_def] >> pop_assum mp_tac >> pop_assum mp_tac >> rw[] >>
        metis_tac[opened_accepted_fds]) >>
  drule_then (qspec_then ‘a’ strip_assume_tac) dworld_props >>
  ‘semantics_prog (init_state (ep_ffi (dworld lfd a sk1))) init_env prog (Diverge io)’
    by (‘(socket2_ffi sk1).io_events = (ep_ffi (dworld lfd a sk1)).io_events’
          by simp[socket2_ffi_def, ep_ffi_def] >>
        metis_tac[same_answers_semantics]) >>
  ‘replay_ok (dworld lfd a sk1) evs’ by metis_tac[trace_replay_ok] >>
  drule_all dworld_inv >> simp[dgood_def, queue_ok_def] >> strip_tac >>
  ‘(ep_replay (dworld lfd a sk1) evs).clock = npolls (calls_of evs)’
    by (drule replay_clock_npolls >> simp[dworld_def]) >>
  ‘npolls (calls_of evs) ≤ kk’ by metis_tac[] >>
  ‘nconn sk1 (npolls (calls_of evs)) = nconn sk0 (npolls (calls_of evs))’
    by simp[Abbr ‘sk1’, ext1_nconn] >>
  ‘nconn sk0 (npolls (calls_of evs)) ≤ m’ by simp[Abbr ‘m’, nconn_mono] >>
  fs[]
QED

(* MAIN (completeness check): a program meeting echo_spec2 meets the
   endpoint form of EchoSpec2 in the simple class, in every world that does
   not saturate the fd space *)
Theorem endpoint_of_echo_spec2:
  echo_spec2 lfd prog ⇒
  rg_spec (λw. ep_server_world v2_calls lfd a w ∧ no_backpressure w ∧ open_loop w ∧
               nonsat lfd a w)
    ep_echo2_guar prog
Proof
  rw[rg_spec_def] >>
  ‘simple_class lfd a w’ by simp[simple_class_def] >>
  drule_all v2of_props >> strip_tac >>
  qabbrev_tac ‘sk0 = v2of lfd a w’ >>
  qpat_assum ‘echo_spec2 _ _’ (mp_tac o SIMP_RULE std_ss [echo_spec2_def]) >>
  disch_then (qspec_then ‘sk0’ mp_tac) >> simp[] >> strip_tac >>
  qexists_tac ‘io’ >>
  ‘semantics_prog (init_state (ep_ffi w)) init_env prog (Diverge io)’
    by (‘(socket2_ffi sk0).io_events = (ep_ffi w).io_events’
          by simp[socket2_ffi_def, ep_ffi_def] >>
        metis_tac[same_answers_semantics]) >>
  simp[] >>
  ‘∀evs. LPREFIX (fromList evs) io ⇒ replay_ok w evs’ by metis_tac[trace_replay_ok] >>
  ‘∀evs. LPREFIX (fromList evs) io ⇒ EVERY (event_ok no_conn_send) evs’
    by (rpt strip_tac >>
        qpat_assum ‘semantics_prog (init_state (socket2_ffi _)) _ _ _’
          (fn th => mp_tac (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
             (Q.INST [‘P’ |-> ‘no_conn_send’] run_events_ok)) th)) >>
        simp[socket2_ffi_def, socket2_oracle_ok]) >>
  simp[ep_echo2_guar_def] >> rpt conj_tac
  >- (rw[always_def] >> fs[echo_safe2_def] >> res_tac >>
      metis_tac[ch_sent_ep_written, ch_read_ep_read])
  >- (rw[sym_live_def, eventually_def] >>
      ‘ginv lfd a w evs (ep_replay w evs)’ by metis_tac[class_inv] >>
      fs[ginv_def, peer_at_of] >>
      qabbrev_tac ‘N = (ep_replay w evs).clock − w.clock’ >>
      fs[echo_live2_def] >>
      first_x_assum (qspecl_then [‘c’, ‘N’] strip_assume_tac) >>
      rename1 ‘sent2_upto c N sk0 ≼ ep_written c evs'’ >>
      ‘ep_written c evs' ≠ []’ by (strip_tac >> fs[Abbr ‘sk0’]) >>
      ‘c < LENGTH (opened_fds evs')’
        by (fs[ep_written_def] >> pop_assum mp_tac >> rw[] >>
            metis_tac[opened_accepted_fds]) >>
      qexists_tac ‘evs'’ >> simp[] >> qexists_tac ‘c’ >>
      conj_tac >- metis_tac[class_chan] >>
      metis_tac[ch_sent_ep_written])
  >- (irule echo_spec2_ticks >> simp[] >> metis_tac[])
QED

(* MAIN: EchoSpec2 and its endpoint form, in the simple class.  The
   endpoint form implies EchoSpec2 (the headline is a corollary); EchoSpec2
   implies the endpoint form in every world that does not fill the fd
   space *)
Theorem echo2_sym_equiv_thm:
  ∀lfd a prog.
    (rg_spec (λw. ep_server_world v2_calls lfd a w ∧ no_backpressure w ∧ open_loop w)
       ep_echo2_guar prog ⇒ echo_spec2 lfd prog) ∧
    (echo_spec2 lfd prog ⇒
     rg_spec (λw. ep_server_world v2_calls lfd a w ∧ no_backpressure w ∧ open_loop w ∧
                  nonsat lfd a w)
       ep_echo2_guar prog)
Proof
  metis_tac[echo_spec2_of_endpoint, endpoint_of_echo_spec2]
QED
