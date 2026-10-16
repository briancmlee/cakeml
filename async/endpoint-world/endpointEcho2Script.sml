(*
  EchoSpec2 in the endpoint world (echo2_sym_equiv), the direction
  "the endpoint spec implies echo_spec2".

  From a version-2 world sk we build the endpoint world dworld lfd sk: the
  same schedule, translated, and at each tick the peer of every channel
  reads (a Drain), so that every peer reads fairly.  It is related to sk
  as in endpointV2Sim, so a program behaves the same in both.  Along the
  run:
   - the world's clock counts the version-2 ticks;
   - channel c's peer has sent exactly what client c sends in the first
     clock steps (sent2_upto);
   - accepts are first in, first out: episode j is channel j;
   - every channel's peer reads at every tick.
  So the endpoint guarantee's liveness, with ticks_forever, gives
  echo_live2, and its safety and closing clauses are EchoSpec2's.
*)
Theory endpointEcho2
Ancestors
  llist ffi alist semantics evaluateProps ml_prog ffiSpikeSocketFFI socketV2FFI
  socketV2Fair EchoSpec2 endpointWorld endpointFair endpointSpecForms
  endpointSemantics endpointInstances endpointServers endpointV2Sim
  endpointTrace
Libs
  preamble

(* ------------------------------------------------------------------------
   The schedule, step by step
   ------------------------------------------------------------------------ *)

Definition is_conn2_def:
  is_conn2 (Connect2 l) = T ∧ is_conn2 _ = F
End

Theorem arrivals2_upto_LNIL[simp]:
  arrivals2_upto m [||] = []
Proof
  Cases_on ‘m’ >> simp[arrivals2_upto_def]
QED

Theorem arrivals2_upto_LCONS:
  arrivals2_upto (SUC m) (h:::t) = h ++ arrivals2_upto m t
Proof
  simp[Once arrivals2_upto_def]
QED

Theorem arrivals2_upto_SUC:
  ∀n f. arrivals2_upto (SUC n) f = arrivals2_upto n f ++ fut_step f n
Proof
  Induct
  >- (gen_tac >> qspec_then ‘f’ strip_assume_tac llist_CASES >>
      rewrite_tac[ONE, arrivals2_upto_LCONS] >> simp[arrivals2_upto_def]) >>
  gen_tac >> qspec_then ‘f’ strip_assume_tac llist_CASES >> rveq >- simp[] >>
  REWRITE_TAC[arrivals2_upto_LCONS, fut_step_thm] >>
  first_x_assum (qspec_then ‘t’ SUBST1_TAC) >> simp[]
QED

Theorem ticks2_future:
  ∀n s m. fut_step (ticks2 n s).future m = fut_step s.future (n + m)
Proof
  Induct >> fs[ticks2_def] >> rw[tick2_def] >>
  qspec_then ‘s.future’ strip_assume_tac llist_CASES >>
  fs[deliver2_future, ADD_CLAUSES]
QED

(* The number of connections in the first n steps *)
Definition nconn_def:
  nconn sk n = LENGTH (FILTER is_conn2 (arrivals2_upto n sk.future))
End

(* What client c sends in a list of arrivals *)
Definition data_of_def:
  data_of c xs = FLAT (MAP (λa. case a of Data2 j bs => if j = c then bs else [] | _ => []) xs)
End

Theorem sent2_upto_SUC:
  sent2_upto c (SUC n) sk = sent2_upto c n sk ++ data_of c (fut_step sk.future n)
Proof
  simp[sent2_upto_def, arrivals2_upto_SUC, data_of_def]
QED

Theorem deliver2_with_future:
  deliver2 (s with future := f) x = deliver2 s x with future := f
Proof
  Cases_on ‘x’ >> rw[deliver2_def, update_client_def]
QED

Theorem FOLDL_deliver2_with_future:
  ∀xs s. FOLDL deliver2 (s with future := f) xs = FOLDL deliver2 s xs with future := f
Proof
  Induct >> simp[deliver2_with_future]
QED

Theorem step_ok2_with_future:
  ∀xs s. step_ok2 (s with future := f) xs ⇔ step_ok2 s xs
Proof
  Induct >> fs[step_ok2_def, deliver2_with_future] >> Cases >>
  simp[arrival_ok2_def]
QED

Theorem step_ok2_clients:
  ∀xs s. step_ok2 s xs ⇒
         LENGTH (FOLDL deliver2 s xs).clients = LENGTH s.clients + LENGTH (FILTER is_conn2 xs)
Proof
  Induct >> simp[step_ok2_def] >> Cases >>
  rw[deliver2_def, arrival_ok2_def, is_conn2_def, update_client_def] >>
  res_tac >> gvs[update_client_def]
QED

Theorem ticks2_clients:
  sched_wf2 sk ⇒ ∀n. LENGTH (ticks2 n sk).clients = LENGTH sk.clients + nconn sk n
Proof
  strip_tac >> Induct >- simp[nconn_def, arrivals2_upto_def, ticks2_def] >>
  REWRITE_TAC[ticks2_SUC'] >>
  fs[nconn_def, arrivals2_upto_SUC, FILTER_APPEND] >>
  qpat_x_assum ‘sched_wf2 _’ (fn th => assume_tac th >> mp_tac th) >>
  simp_tac std_ss [sched_wf2_def] >> disch_then (qspec_then ‘n’ assume_tac) >>
  ‘next_step2 (ticks2 n sk) = fut_step sk.future n’
    by simp[next_step2_fut, ticks2_future] >>
  simp[tick2_def] >>
  qspec_then ‘(ticks2 n sk).future’ strip_assume_tac llist_CASES >>
  gvs[next_step2_def, FOLDL_deliver2_with_future] >>
  drule step_ok2_clients >> simp[]
QED

(* ------------------------------------------------------------------------
   The endpoint world of a version-2 world, with drains
   ------------------------------------------------------------------------ *)

(* Tick n: the step's arrivals, then every channel's peer reads *)
Definition dworld_def:
  dworld lfd a sk =
    <| listening := [(lfd, a, [])]; chans := []; open_fds := [];
       reserved := sk.reserved; alloc := sk.alloc;
       takes := (λj b n. n); calls := v2_calls;
       env := (λn h. MAP (tr lfd a) (fut_step sk.future n) ++
                     GENLIST Drain (nconn sk (SUC n)));
       clock := 0; hist := [] |>
End

Theorem al_rel_only_drains:
  ∀ds. EVERY (λe. ∃j. e = Drain j) ds ⇒ al_rel lfd a ds []
Proof
  Induct >> rw[] >> simp[Once al_rel_cases]
QED

Theorem al_rel_append_drains:
  ∀es xs. al_rel lfd a es xs ⇒
          ∀ds. EVERY (λe. ∃j. e = Drain j) ds ⇒ al_rel lfd a (es ++ ds) xs
Proof
  Induct_on ‘al_rel’ >> rw[al_rel_only_drains] >> simp[Once al_rel_cases]
QED

Theorem al_rel_drains:
  al_rel lfd a es xs ⇒ al_rel lfd a (es ++ GENLIST Drain m) xs
Proof
  strip_tac >> irule al_rel_append_drains >> simp[EVERY_GENLIST]
QED

Theorem ep_step_ok_APPEND:
  ∀es1 w. ep_step_ok w (es1 ++ es2) ⇔ ep_step_ok w es1 ∧ ep_step_ok (FOLDL ep_deliver w es1) es2
Proof
  Induct >> simp[ep_step_ok_def] >> metis_tac[]
QED

Theorem ep_step_ok_drains:
  ∀es w. EVERY (λe. ∃j. e = Drain j ∧ j < LENGTH w.chans) es ⇒ ep_step_ok w es
Proof
  Induct >> rw[ep_step_ok_def] >> gvs[ep_arrival_ok_def] >>
  first_x_assum irule >>
  ‘LENGTH (ep_deliver w (Drain j)).chans = LENGTH w.chans’
    by rw[ep_deliver_def, upd_chan_def] >>
  fs[EVERY_MEM]
QED

Theorem v2_call_poll:
  v2_call n conf bs sk = SOME (b, sk') ⇒
  (n = «sock_poll» ∧ sk' = tick2 sk) ∨ (n ≠ «sock_poll» ∧ v2shape sk' = v2shape sk)
Proof
  rw[v2_call_def, socket2_fn_def, AllCaseEqs()] >>
  gvs[ffi_sock_poll2_def, ffi_sock_accept2_def, ffi_sock_read2_def, ffi_sock_write2_def,
      ffi_sock_close2_def, AllCaseEqs(), sock_accept2_def, sock_read2_def,
      sock_write2_def, sock_close2_def] >>
  simp[v2shape_def, MAP_FST_AFUPDKEY, update_client_def] >>
  rw[LIST_EQ_REWRITE, EL_MAP, EL_LUPDATE] >> rw[]
QED

Theorem ep_ffi_fn_clock:
  ep_ffi_fn n conf bs w = SOME (b, w') ⇒
  (n = «sock_poll» ∧ w'.clock = w.clock + 1) ∨ (n ≠ «sock_poll» ∧ w'.clock = w.clock)
Proof
  rw[ep_ffi_fn_def, ep_call_def, AllCaseEqs()] >>
  gvs[ep_tick_def, ep_deliver_fields, ep_accept_def, ep_connect_def,
      ep_alloc_def, ep_read_def, ep_send_def, ep_shutdown_def, ep_close_def,
      ep_conn_err_def,
      upd_chan_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()]
QED

(* The states the program reaches: related to a version-2 state whose shape
   is that of the world left alone for as many ticks *)
Definition dinv_def:
  dinv lfd a sk sk' w ⇔
    v2rel lfd a sk' w ∧ v2shape sk' = v2shape (ticks2 w.clock sk) ∧
    w.env = (dworld lfd a sk).env
End

Theorem dinv_after:
  ∀cs w sk' w'. dinv lfd a sk sk' w ∧ ep_after w cs = SOME w' ⇒ ∃sk''. dinv lfd a sk sk'' w'
Proof
  Induct >> simp[ep_after_def, FORALL_PROD] >- metis_tac[] >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  ‘v2rel lfd a sk' w’ by fs[dinv_def] >>
  drule v2rel_call >>
  disch_then (qspecl_then [‘p_1’, ‘p_1'’, ‘p_2’] strip_assume_tac) >> gvs[] >>
  first_x_assum irule >> first_x_assum (irule_at Any) >>
  qexists_tac ‘sk''’ >> fs[dinv_def] >>
  imp_res_tac ep_ffi_fn_env >> imp_res_tac ep_ffi_fn_clock >>
  imp_res_tac v2_call_poll >> gvs[] >>
  simp[GSYM ADD1, ticks2_SUC'] >> metis_tac[v2shape_tick]
QED

Theorem v2shape_clients:
  v2shape s1 = v2shape s2 ⇒ LENGTH s1.clients = LENGTH s2.clients
Proof
  rw[v2shape_def] >> metis_tac[LENGTH_MAP]
QED

Theorem dworld_init:
  server_world2 lfd sk ⇒ dinv lfd a sk sk (dworld lfd a sk)
Proof
  simp[dinv_def, v2rel_def, core_def, ep_inv_def, dworld_def, no_backpressure_def,
       ticks2_def] >>
  rw[server_world2_def] >> irule al_rel_drains >> simp[al_rel_tr]
QED

Theorem dworld_props:
  server_world2 lfd sk ⇒
  ep_server_world v2_calls lfd a (dworld lfd a sk) ∧ no_backpressure (dworld lfd a sk) ∧
  open_loop (dworld lfd a sk) ∧ ep_rely (dworld lfd a sk) ∧
  same_answers (socket2_ffi sk) (ep_ffi (dworld lfd a sk))
Proof
  strip_tac >>
  ‘dinv lfd a sk sk (dworld lfd a sk)’ by metis_tac[dworld_init] >>
  rpt conj_tac
  >- simp[ep_server_world_def, dworld_def]
  >- simp[no_backpressure_def, dworld_def]
  >- simp[open_loop_def, dworld_def]
  >- (simp[ep_rely_def] >> rpt conj_tac
      >- fs[server_world2_def, dworld_def]
      >- simp[takes_ok_def, dworld_def] >>
      rw[ep_sched_ok_def] >>
      drule_all dinv_after >> strip_tac >>
      rename1 ‘dinv lfd a sk sk' w'’ >>
      ‘v2rel lfd a sk' w' ∧ v2shape sk' = v2shape (ticks2 w'.clock sk) ∧
       w'.env = (dworld lfd a sk).env’ by fs[dinv_def] >>
      ‘core lfd a sk' w'’ by fs[v2rel_def] >>
      imp_res_tac core_all_up >> simp[] >>
      qabbrev_tac ‘c = w'.clock’ >>
      qabbrev_tac ‘xs = fut_step sk.future c’ >>
      simp[dworld_def, ep_step_ok_APPEND] >>
      ‘step_ok2 sk' xs’
        by (fs[server_world2_def, sched_wf2_def] >>
            first_x_assum (qspec_then ‘c’ mp_tac) >>
            simp[next_step2_fut, ticks2_future, Abbr ‘xs’] >>
            metis_tac[v2shape_step_ok2]) >>
      conj_tac
      >- (irule al_rel_ep_step_ok >> simp[al_rel_tr] >> metis_tac[core_with, al_rel_tr]) >>
      irule ep_step_ok_drains >> simp[EVERY_GENLIST] >>
      ‘core lfd a (FOLDL deliver2 sk' xs) (FOLDL ep_deliver (w' with clock := c + 1) (MAP (tr lfd a) xs))’
        by (irule core_deliver_all >> simp[al_rel_tr]) >>
      ‘LENGTH (FOLDL ep_deliver (w' with clock := c + 1) (MAP (tr lfd a) xs)).chans =
       LENGTH (FOLDL deliver2 sk' xs).clients’
        by (fs[core_def] >> metis_tac[LIST_REL_LENGTH]) >>
      drule step_ok2_clients >>
      ‘LENGTH sk'.clients = nconn sk c’
        by (imp_res_tac v2shape_clients >> fs[server_world2_def] >>
            drule ticks2_clients >> simp[]) >>
      simp[nconn_def, arrivals2_upto_SUC, FILTER_APPEND] >> fs[nconn_def])
  >- (simp[same_answers_def] >> rw[] >> irule v2rel_run_calls >> fs[dinv_def] >>
      metis_tac[])
QED

(* ------------------------------------------------------------------------
   The trace replays in the world
   ------------------------------------------------------------------------ *)

(* Every event of evs is a call the world answers as recorded *)
Definition replay_ok_def:
  replay_ok w [] = T ∧
  replay_ok w (IO_event (ExtCall n) conf bs :: evs) =
    (case ep_ffi_fn n conf (MAP FST bs) w of
     | SOME (out, w') => out = MAP SND bs ∧ replay_ok w' evs
     | NONE => F) ∧
  replay_ok w (_ :: evs) = F
End


Theorem replay_ok_APPEND:
  ∀w a b. replay_ok w (a ++ b) ⇔ replay_ok w a ∧ replay_ok (ep_replay w a) b
Proof
  ho_match_mp_tac replay_ok_ind >> rw[replay_ok_def, ep_replay_def] >>
  every_case_tac >> fs[] >> metis_tac[]
QED

Theorem replay_ok_after:
  ∀w evs. replay_ok w evs ⇒ ∃cs. ep_after w cs = SOME (ep_replay w evs)
Proof
  ho_match_mp_tac replay_ok_ind >> rw[replay_ok_def, ep_replay_def]
  >- (qexists_tac ‘[]’ >> simp[ep_after_def]) >>
  every_case_tac >> fs[] >>
  qexists_tac ‘(n, conf, MAP FST bs) :: cs’ >> simp[ep_after_def]
QED

Theorem ep_replay_APPEND:
  ∀w evs. replay_ok w evs ⇒ ∀rest. ep_replay w (evs ++ rest) = ep_replay (ep_replay w evs) rest
Proof
  ho_match_mp_tac replay_ok_ind >> rw[replay_ok_def, ep_replay_def] >>
  every_case_tac >> fs[]
QED

Theorem call_FFI_rel_replay:
  ∀f1 f2. RTC call_FFI_rel f1 f2 ⇒ f1.oracle = ep_oracle ⇒
          ∃new. f2.io_events = f1.io_events ++ new ∧ replay_ok f1.ffi_state new ∧
                ep_replay f1.ffi_state new = f2.ffi_state
Proof
  ho_match_mp_tac RTC_INDUCT >> conj_tac
  >- (rw[] >> TRY (qexists_tac ‘[]’) >> simp[replay_ok_def, ep_replay_def]) >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  imp_res_tac call_FFI_rel_consts >> fs[] >>
  ‘∃e. f1'.io_events = f1.io_events ++ e ∧ replay_ok f1.ffi_state e ∧
       ep_replay f1.ffi_state e = f1'.ffi_state’
    by (qpat_x_assum ‘call_FFI_rel _ _’ mp_tac >>
        simp[call_FFI_rel_def, call_FFI_def] >> rpt strip_tac >>
        qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >>
        IF_CASES_TAC >>
        TRY (rw[] >> TRY (qexists_tac ‘[]’) >> simp[replay_ok_def, ep_replay_def] >> NO_TAC) >>
        Cases_on ‘n’ >> simp[ep_oracle_def] >>
        rename1 ‘ep_ffi_fn s conf bs f1.ffi_state’ >>
        Cases_on ‘ep_ffi_fn s conf bs f1.ffi_state’ >> simp[] >>
        rename1 ‘SOME p’ >> PairCases_on ‘p’ >> simp[] >>
        IF_CASES_TAC >> simp[] >> strip_tac >> rveq >>
        qexists_tac ‘[IO_event (ExtCall s) conf (ZIP (bs, p0))]’ >>
        simp[replay_ok_def, ep_replay_def, MAP_ZIP]) >>
  qexists_tac ‘e ++ new’ >> simp[replay_ok_APPEND, ep_replay_APPEND]
QED

Theorem replay_SNOC:
  replay_ok w (evs ++ [ev]) ⇒
  ∃n conf bs. ev = IO_event (ExtCall n) conf bs ∧
              ep_ffi_fn n conf (MAP FST bs) (ep_replay w evs) =
                SOME (MAP SND bs, ep_replay w (evs ++ [ev]))
Proof
  rw[replay_ok_APPEND] >>
  ‘∀w. replay_ok w [ev] ⇒ ∃n conf bs. ev = IO_event (ExtCall n) conf bs ∧
        ep_ffi_fn n conf (MAP FST bs) w = SOME (MAP SND bs, ep_replay w [ev])’
    by (Cases_on ‘ev’ >> rename1 ‘IO_event nm _ _’ >> Cases_on ‘nm’ >>
        rw[replay_ok_def, ep_replay_def] >> every_case_tac >> fs[]) >>
  metis_tac[ep_replay_APPEND]
QED

Theorem trace_replay_ok:
  semantics_prog (init_state (ep_ffi w)) init_env prog (Diverge io) ∧
  LPREFIX (fromList evs) io ⇒ replay_ok w evs
Proof
  strip_tac >> drule_all diverge_prefix >> strip_tac >>
  fs[evaluate_prog_with_clock_def] >> pairarg_tac >> fs[] >>
  imp_res_tac evaluate_call_FFI_rel_imp >>
  ‘(init_state (ep_ffi w) with clock := k).ffi = ep_ffi w’
    by simp[ml_progTheory.init_state_def] >>
  fs[] >> drule call_FFI_rel_replay >> simp[ep_ffi_def] >> strip_tac >>
  gvs[IS_PREFIX_APPEND] >> fs[ep_ffi_def] >> gvs[replay_ok_APPEND]
QED

(* ------------------------------------------------------------------------
   What a tick does to the peers' side
   ------------------------------------------------------------------------ *)

Definition recv_of_def:
  recv_of (w:eworld) c = if c < LENGTH w.chans then (EL c w.chans).recv else []
End

Definition drained_of_def:
  drained_of (w:eworld) c = if c < LENGTH w.chans then (EL c w.chans).drained else 0
End

Definition pdata_def:
  pdata c es = FLAT (MAP (λe. case e of PData j bs => if j = c then bs else [] | _ => []) es)
End

Definition ndrain_def:
  ndrain c es = LENGTH (FILTER ($= (Drain c)) es)
End

(* The queue of a world whose channels from k on are pending *)
Definition queue_ok_def:
  queue_ok lfd a k (w:eworld) ⇔
    w.listening = [(lfd, a, GENLIST (λi. i + k) (LENGTH w.chans − k))] ∧ k ≤ LENGTH w.chans
End

Theorem deliver_recv:
  ep_arrival_ok w e ⇒ recv_of (ep_deliver w e) c = recv_of w c ++ pdata c [e]
Proof
  Cases_on ‘e’ >>
  rw[ep_arrival_ok_def, ep_deliver_def, recv_of_def, pdata_def, upd_chan_def] >>
  every_case_tac >> gvs[EL_APPEND_EQN, EL_LUPDATE, new_chan_def] >>
  rw[] >> gvs[] >>
  ‘c − LENGTH w.chans = 0’ by simp[] >> simp[]
QED

Theorem deliver_drained:
  ep_arrival_ok w e ⇒ drained_of (ep_deliver w e) c = drained_of w c + ndrain c [e]
Proof
  Cases_on ‘e’ >>
  rw[ep_arrival_ok_def, ep_deliver_def, drained_of_def, ndrain_def, upd_chan_def] >>
  every_case_tac >> gvs[EL_APPEND_EQN, EL_LUPDATE, new_chan_def] >>
  rw[] >> gvs[] >>
  ‘c − LENGTH w.chans = 0’ by simp[] >> simp[]
QED

Theorem deliver_queue:
  queue_ok lfd a k w ⇒ queue_ok lfd a k (ep_deliver w e)
Proof
  Cases_on ‘e’ >> rw[queue_ok_def, ep_deliver_def, upd_chan_def] >>
  every_case_tac >> gvs[AFUPDKEY_def] >>
  ‘LENGTH w.chans + 1 − k = SUC (LENGTH w.chans − k)’ by simp[] >>
  simp[GENLIST, SNOC_APPEND]
QED

Theorem deliver_all:
  ∀es w. ep_step_ok w es ⇒
         (∀c. recv_of (FOLDL ep_deliver w es) c = recv_of w c ++ pdata c es) ∧
         (∀c. drained_of (FOLDL ep_deliver w es) c = drained_of w c + ndrain c es)
Proof
  Induct >> simp[ep_step_ok_def, pdata_def, ndrain_def] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  fs[pdata_def, ndrain_def, deliver_recv |> SIMP_RULE std_ss [pdata_def],
     deliver_drained |> SIMP_RULE std_ss [ndrain_def]] >>
  rw[]
QED

Theorem deliver_all_queue:
  ∀es w. queue_ok lfd a k w ⇒ queue_ok lfd a k (FOLDL ep_deliver w es)
Proof
  Induct >> simp[] >> metis_tac[deliver_queue]
QED

(* ------------------------------------------------------------------------
   Counting openings
   ------------------------------------------------------------------------ *)

Theorem EL_FILTER_COUNT_LIST:
  ∀n j. j < LENGTH (FILTER P (COUNT_LIST n)) ⇒
        EL j (FILTER P (COUNT_LIST n)) < n ∧ P (EL j (FILTER P (COUNT_LIST n))) ∧
        LENGTH (FILTER P (COUNT_LIST (EL j (FILTER P (COUNT_LIST n))))) = j
Proof
  Induct >- simp[COUNT_LIST_def] >>
  REWRITE_TAC[COUNT_LIST_SNOC, SNOC_APPEND] >> simp[FILTER_APPEND] >>
  rpt gen_tac >> strip_tac >>
  Cases_on ‘j < LENGTH (FILTER P (COUNT_LIST n))’
  >- (first_x_assum drule >> simp[EL_APPEND1]) >>
  Cases_on ‘P n’ >> gvs[] >>
  ‘j = LENGTH (FILTER P (COUNT_LIST n))’ by simp[] >>
  simp[EL_APPEND2]
QED

Theorem opened_fds_TAKE:
  ∀i. i ≤ LENGTH evs ⇒
      LENGTH (opened_fds (TAKE i evs)) =
      LENGTH (FILTER (λk. IS_SOME (event_opened (EL k evs))) (COUNT_LIST i))
Proof
  Induct >- simp[opened_fds_def, COUNT_LIST_def] >> strip_tac >>
  REWRITE_TAC[COUNT_LIST_SNOC, SNOC_APPEND] >>
  ‘TAKE (SUC i) evs = TAKE i evs ++ [EL i evs]’
    by (‘i < LENGTH evs’ by simp[] >> drule TAKE_EL_SNOC >> simp[SNOC_APPEND, ADD1]) >>
  fs[opened_fds_def, FILTER_APPEND] >> Cases_on ‘event_opened (EL i evs)’ >> simp[]
QED

(* ------------------------------------------------------------------------
   The run's invariant
   ------------------------------------------------------------------------ *)

(* How often channel c's peer has read after t ticks *)
Definition dcount_def:
  dcount sk c t = LENGTH (FILTER (λk. c < nconn sk (SUC k)) (COUNT_LIST t))
End

Theorem dcount_SUC:
  dcount sk c (SUC t) = dcount sk c t + if c < nconn sk (SUC t) then 1 else 0
Proof
  simp[dcount_def, COUNT_LIST_SNOC, SNOC_APPEND, FILTER_APPEND] >> rw[]
QED

Theorem pdata_tr:
  pdata c (MAP (tr lfd a) xs ++ GENLIST Drain m) = data_of c xs
Proof
  ‘pdata c (GENLIST Drain m) = []’
    by (simp[pdata_def, FLAT_EQ_NIL, EVERY_MEM, MEM_MAP, MEM_GENLIST] >> rw[] >> simp[]) >>
  simp[pdata_def, data_of_def, MAP_MAP_o] >> fs[pdata_def] >>
  AP_TERM_TAC >> irule MAP_CONG >> rw[] >> Cases_on ‘x’ >> rw[tr_def]
QED

Theorem tr_not_drain[simp]:
  tr lfd a x ≠ Drain j ∧ Drain j ≠ tr lfd a x
Proof
  Cases_on ‘x’ >> rw[tr_def]
QED

Theorem ndrain_tr:
  ndrain c (MAP (tr lfd a) xs ++ GENLIST Drain m) = if c < m then 1 else 0
Proof
  ‘FILTER ($= (Drain c)) (MAP (tr lfd a) xs) = []’
    by simp[FILTER_EQ_NIL, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
  simp[ndrain_def, FILTER_APPEND] >>
  Induct_on ‘m’ >> simp[GENLIST, SNOC_APPEND, FILTER_APPEND] >> rw[] >> fs[]
QED

Theorem deliver_chans_count:
  ∀es w q. w.listening = [(lfd, a, q)] ⇒
           LENGTH (FOLDL ep_deliver w es).chans =
           LENGTH w.chans + LENGTH (FILTER ($= (Incoming a)) es) ∧
           ∃q'. (FOLDL ep_deliver w es).listening = [(lfd, a, q')]
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  ‘∃q'. (ep_deliver w h).listening = [(lfd, a, q')] ∧
        LENGTH (ep_deliver w h).chans = LENGTH w.chans + if Incoming a = h then 1 else 0’
    by (Cases_on ‘h’ >> simp[ep_deliver_def, upd_chan_def] >>
        rw[AFUPDKEY_def] >> simp[]) >>
  first_x_assum drule >> strip_tac >> simp[] >> rw[]
QED

Theorem deliver2_keys[simp]:
  MAP FST (deliver2 s x).listening = MAP FST s.listening
Proof
  Cases_on ‘x’ >> rw[deliver2_def, update_client_def, MAP_FST_AFUPDKEY]
QED

(* In a valid step every connection is to the listener *)
Theorem step_ok2_conns:
  ∀xs s. step_ok2 s xs ∧ MAP FST s.listening = [lfd] ⇒
         EVERY (λx. is_conn2 x ⇒ x = Connect2 lfd) xs
Proof
  Induct >> simp[step_ok2_def] >> rpt gen_tac >> strip_tac >>
  conj_tac >- (Cases_on ‘h’ >> fs[is_conn2_def, arrival_ok2_def, ALOOKUP_NONE]) >>
  first_x_assum irule >> qexists_tac ‘deliver2 s h’ >> REWRITE_TAC[deliver2_keys] >> gvs[]
QED

Theorem ticks2_listening:
  ∀n s. MAP FST (ticks2 n s).listening = MAP FST s.listening
Proof
  Induct >> simp[ticks2_def] >> rw[tick2_def] >> every_case_tac >> simp[] >>
  ‘∀xs s. MAP FST (FOLDL deliver2 s xs).listening = MAP FST s.listening’
    by (Induct >> simp[] >> Cases >> rw[deliver2_def, update_client_def, MAP_FST_AFUPDKEY]) >>
  simp[]
QED

Theorem incoming_count:
  EVERY (λx. is_conn2 x ⇒ x = Connect2 lfd) xs ⇒
  LENGTH (FILTER ($= (Incoming a)) (MAP (tr lfd a) xs ++ GENLIST Drain m)) =
  LENGTH (FILTER is_conn2 xs)
Proof
  ‘FILTER ($= (Incoming a)) (GENLIST Drain m) = []’
    by simp[FILTER_EQ_NIL, EVERY_GENLIST] >>
  simp[FILTER_APPEND] >> Induct_on ‘xs’ >> simp[] >> Cases >>
  rw[tr_def, is_conn2_def]
QED

(* Reads, writes and closes change only the program's side of a channel *)
Theorem recv_of_upd[simp]:
  (∀c. (g c).recv = c.recv) ⇒ recv_of (upd_chan j g w) c = recv_of w c
Proof
  rw[upd_chan_def, recv_of_def, EL_LUPDATE] >> rw[]
QED

Theorem drained_of_upd[simp]:
  (∀c. (g c).drained = c.drained) ⇒ drained_of (upd_chan j g w) c = drained_of w c
Proof
  rw[upd_chan_def, drained_of_def, EL_LUPDATE] >> rw[]
QED

Theorem upd_chan_fields[simp]:
  LENGTH (upd_chan j g w).chans = LENGTH w.chans ∧
  (upd_chan j g w).listening = w.listening ∧ (upd_chan j g w).clock = w.clock ∧
  (upd_chan j g w).open_fds = w.open_fds
Proof
  simp[upd_chan_def]
QED

Theorem of_open_fds[simp]:
  recv_of (w with open_fds := x) c = recv_of w c ∧
  drained_of (w with open_fds := x) c = drained_of w c ∧
  recv_of (w with listening := y) c = recv_of w c ∧
  drained_of (w with listening := y) c = drained_of w c ∧
  recv_of (w with hist := h) c = recv_of w c ∧
  drained_of (w with hist := h) c = drained_of w c
Proof
  simp[recv_of_def, drained_of_def]
QED

Theorem call_other_effect:
  ep_call n conf bs v = SOME (out, v') ∧ v.calls = v2_calls ∧
  n ≠ «sock_poll» ∧ n ≠ «sock_accept» ⇒
  v'.clock = v.clock ∧ (∀c. recv_of v' c = recv_of v c) ∧
  (∀c. drained_of v' c = drained_of v c) ∧ LENGTH v'.chans = LENGTH v.chans ∧
  v'.listening = v.listening
Proof
  strip_tac >> qpat_x_assum ‘ep_call _ _ _ _ = _’ mp_tac >>
  simp[ep_call_def, v2_calls_def, v1_calls_def] >>
  rw[AllCaseEqs()] >>
  gvs[ep_read_def, ep_send_def, ep_close_def, ep_conn_err_def, AllCaseEqs()]
QED

Theorem call_accept_effect:
  ep_call «sock_accept» conf bs v = SOME (out, v') ∧ v.listening = [(lfd, a, q)] ⇒
  v'.clock = v.clock ∧ (∀c. recv_of v' c = recv_of v c) ∧
  (∀c. drained_of v' c = drained_of v c) ∧ LENGTH v'.chans = LENGTH v.chans ∧
  ((v'.listening = v.listening ∧ HD out = 0w) ∨
   (∃f j q'. q = j :: q' ∧ v'.listening = [(lfd, a, q')] ∧ out = 1w :: fd_bytes f ∧
             ALOOKUP v'.open_fds f = SOME j))
Proof
  strip_tac >> qpat_x_assum ‘ep_call _ _ _ _ = _’ mp_tac >>
  simp[ep_call_def] >> rw[AllCaseEqs()] >>
  gvs[ep_accept_def, AllCaseEqs(), ep_alloc_def, AFUPDKEY_def] >>
  qexists_tac ‘v.alloc j (ep_used v)’ >> simp[]
QED

(* The run's invariant: after the trace evs, channel c's peer has sent what
   client c sends in the first clock steps, and has read once per tick
   since c arrived; the channels not yet accepted are pending in order *)
Definition dgood_def:
  dgood lfd a sk evs (w:eworld) ⇔
    (∀c. recv_of w c = sent2_upto c w.clock sk) ∧
    (∀c. drained_of w c = dcount sk c w.clock) ∧
    queue_ok lfd a (LENGTH (opened_fds evs)) w ∧
    LENGTH w.chans = nconn sk w.clock
End

Theorem queue_ok_with[simp]:
  (queue_ok lfd a k (w with clock := c) ⇔ queue_ok lfd a k w) ∧
  (queue_ok lfd a k (w with hist := h) ⇔ queue_ok lfd a k w)
Proof
  simp[queue_ok_def]
QED

Theorem of_clock[simp]:
  recv_of (w with clock := c) x = recv_of w x ∧ drained_of (w with clock := c) x = drained_of w x
Proof
  simp[recv_of_def, drained_of_def]
QED

Theorem opened_fds_SNOC:
  opened_fds (evs ++ [ev]) =
  opened_fds evs ++ (case event_opened ev of SOME f => [f] | NONE => [])
Proof
  simp[opened_fds_def]
QED

Theorem dworld_reach:
  server_world2 lfd sk ∧ replay_ok (dworld lfd a sk) evs ⇒
  ∃sk'. dinv lfd a sk sk' (ep_replay (dworld lfd a sk) evs)
Proof
  strip_tac >> drule replay_ok_after >> strip_tac >>
  drule_then assume_tac dworld_init >> metis_tac[dinv_after]
QED

Theorem GENLIST_pop:
  GENLIST (λi. i + k) (L − k) = j :: q' ⇒
  j = k ∧ k < L ∧ q' = GENLIST (λi. i + (k + 1)) (L − (k + 1))
Proof
  Cases_on ‘L − k’ >> simp[GENLIST_CONS] >> strip_tac >>
  ‘n = L − (k + 1)’ by simp[] >> rveq >> fs[combinTheory.o_DEF, ADD1] >>
  rveq >> simp[] >> irule GENLIST_CONG >> simp[]
QED

Theorem dworld_inv:
  server_world2 lfd sk ⇒
  ∀evs. replay_ok (dworld lfd a sk) evs ⇒
        dgood lfd a sk evs (ep_replay (dworld lfd a sk) evs)
Proof
  strip_tac >> ho_match_mp_tac SNOC_INDUCT >> conj_tac
  >- (simp[dgood_def, ep_replay_def, dworld_def, recv_of_def, drained_of_def,
           queue_ok_def, opened_fds_def, sent2_upto_def, arrivals2_upto_def, dcount_def,
           COUNT_LIST_def, nconn_def]) >>
  rpt gen_tac >> strip_tac >> REWRITE_TAC[SNOC_APPEND] >> rpt strip_tac >>
  ‘replay_ok (dworld lfd a sk) evs’ by fs[replay_ok_APPEND] >> fs[] >>
  drule_all dworld_reach >> strip_tac >>
  drule replay_SNOC >> strip_tac >> gvs[] >>
  qabbrev_tac ‘w0 = ep_replay (dworld lfd a sk) evs’ >>
  qabbrev_tac ‘w1 = ep_replay (dworld lfd a sk) (evs ++ [IO_event (ExtCall n) conf bs])’ >>
  ‘w0.calls = v2_calls’ by fs[dinv_def, v2rel_def] >>
  qpat_x_assum ‘ep_ffi_fn _ _ _ _ = _’ mp_tac >> simp[ep_ffi_fn_def] >>
  rw[AllCaseEqs()] >> rename1 ‘ep_call n conf (MAP FST bs) w0 = SOME (MAP SND bs, w2)’ >>
  fs[dgood_def, opened_fds_SNOC] >>
  Cases_on ‘n = «sock_poll»’
  >- (gvs[] >>
      ‘w2 = ep_tick w0’
        by (qpat_x_assum ‘ep_call _ _ _ _ = _’ mp_tac >> simp[ep_call_def] >> rw[]) >>
      ‘event_opened (IO_event (ExtCall «sock_poll») conf bs) = NONE’
        by simp[event_opened_def, event_accepted_def] >>
      gvs[] >>
      ‘ep_step_ok (w0 with clock := w0.clock + 1) (w0.env w0.clock w0.hist)’
        by (drule_then (qspec_then ‘a’ strip_assume_tac) dworld_props >>
            fs[ep_rely_def, ep_sched_ok_def] >> first_x_assum irule >>
            drule replay_ok_after >> simp[Abbr ‘w0’]) >>
      ‘core lfd a sk' w0 ∧ w0.env = (dworld lfd a sk).env’ by fs[dinv_def, v2rel_def] >>
      imp_res_tac core_all_up >>
      qabbrev_tac ‘c = w0.clock’ >>
      qabbrev_tac ‘xs = fut_step sk.future c’ >>
      fs[dworld_def] >>
      qabbrev_tac ‘es = MAP (tr lfd a) xs ++ GENLIST Drain (nconn sk (SUC c))’ >>
      ‘ep_tick w0 = FOLDL ep_deliver (w0 with clock := c + 1) es’
        by simp[ep_tick_def, Abbr ‘es’, Abbr ‘xs’] >>
      drule deliver_all >> disch_then strip_assume_tac >>
      ‘(FOLDL ep_deliver (w0 with clock := c + 1) es).clock = SUC c’
        by simp[ep_deliver_fields, ADD1] >>
      simp[] >> rpt conj_tac
      >- simp[Abbr ‘es’, pdata_tr, sent2_upto_SUC, Abbr ‘xs’]
      >- simp[Abbr ‘es’, ndrain_tr, dcount_SUC]
      >- (irule deliver_all_queue >> simp[])
      >> ‘∃q. w0.listening = [(lfd, a, q)]’ by fs[queue_ok_def] >>
      qspecl_then [‘es’, ‘w0 with clock := c + 1’, ‘q’] mp_tac deliver_chans_count >>
      simp[] >> strip_tac >>
      ‘EVERY (λx. is_conn2 x ⇒ x = Connect2 lfd) xs’
        by (irule step_ok2_conns >> qexists_tac ‘ticks2 c sk’ >>
            REWRITE_TAC[ticks2_listening] >>
            fs[server_world2_def, sched_wf2_def] >>
            qpat_x_assum ‘∀n. step_ok2 _ _’ (qspec_then ‘c’ mp_tac) >>
            simp[next_step2_fut, ticks2_future, Abbr ‘xs’]) >>
      simp[Abbr ‘es’, incoming_count] >>
      simp[nconn_def, arrivals2_upto_SUC, FILTER_APPEND, Abbr ‘xs’]) >>
  Cases_on ‘n = «sock_accept»’
  >- (gvs[] >> qabbrev_tac ‘k = LENGTH (opened_fds evs)’ >>
      ‘w0.listening = [(lfd, a, GENLIST (λi. i + k) (LENGTH w0.chans − k))] ∧
       k ≤ LENGTH w0.chans’ by fs[queue_ok_def] >>
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

(* ------------------------------------------------------------------------
   Episodes are channels, in order
   ------------------------------------------------------------------------ *)

Theorem replay_ok_TAKE:
  replay_ok w evs ⇒ replay_ok w (TAKE n evs)
Proof
  strip_tac >> ‘evs = TAKE n evs ++ DROP n evs’ by simp[] >>
  metis_tac[replay_ok_APPEND]
QED

Theorem dworld_chan:
  server_world2 lfd sk ∧ replay_ok (dworld lfd a sk) evs ∧
  ep_chan (dworld lfd a sk) evs j = SOME c ⇒ c = j
Proof
  rw[ep_chan_def] >> every_case_tac >> fs[] >>
  qmatch_asmsub_abbrev_tac ‘FILTER P (COUNT_LIST (LENGTH evs))’ >>
  drule EL_FILTER_COUNT_LIST >> qmatch_goalsub_abbrev_tac ‘i < LENGTH evs’ >> strip_tac >>
  ‘LENGTH (opened_fds (TAKE i evs)) = j’ by simp[opened_fds_TAKE, Abbr ‘P’] >>
  ‘TAKE (SUC i) evs = TAKE i evs ++ [EL i evs]’
    by (drule TAKE_EL_SNOC >> simp[SNOC_APPEND, ADD1]) >>
  ‘replay_ok (dworld lfd a sk) (TAKE i evs ++ [EL i evs])’
    by metis_tac[replay_ok_TAKE] >>
  ‘replay_ok (dworld lfd a sk) (TAKE i evs)’ by fs[replay_ok_APPEND] >>
  drule_all dworld_inv >> strip_tac >>
  drule_all dworld_reach >> strip_tac >>
  drule replay_SNOC >> strip_tac >> fs[] >>
  qabbrev_tac ‘w0 = ep_replay (dworld lfd a sk) (TAKE i evs)’ >>
  ‘w0.calls = v2_calls’ by fs[dinv_def, v2rel_def] >>
  qpat_x_assum ‘ep_ffi_fn _ _ _ _ = _’ mp_tac >> simp[ep_ffi_fn_def] >>
  rw[AllCaseEqs()] >> rename1 ‘ep_call n conf (MAP FST bs) w0 = SOME (MAP SND bs, w2)’ >>
  fs[Abbr ‘P’] >> rfs[] >>
  ‘MEM n v2_calls’
    by (CCONTR_TAC >> qpat_x_assum ‘ep_call _ _ _ _ = _’ mp_tac >> simp[ep_call_def]) >>
  ‘n = «sock_accept»’
    by (CCONTR_TAC >> gvs[v2_calls_def, v1_calls_def, event_opened_def, event_accepted_def]) >>
  gvs[] >>
  fs[dgood_def, queue_ok_def] >>
  drule_all call_accept_effect >> strip_tac >> gvs[]
  >- gvs[event_opened_def, event_accepted_def] >>
  drule GENLIST_pop >> strip_tac >> gvs[] >>
  gvs[event_opened_def, event_accepted_def] >>
  qpat_x_assum ‘w2 with hist := _ = _’ (SUBST_ALL_TAC o SYM) >> fs[]
QED

(* ------------------------------------------------------------------------
   Monotonicity, fairness
   ------------------------------------------------------------------------ *)

Theorem replay_clock_mono:
  ∀w evs. replay_ok w evs ⇒ w.clock ≤ (ep_replay w evs).clock
Proof
  ho_match_mp_tac replay_ok_ind >> rw[replay_ok_def, ep_replay_def] >>
  every_case_tac >> fs[] >> imp_res_tac ep_ffi_fn_clock >> fs[]
QED

Theorem prefix_clock_mono:
  replay_ok w evs' ∧ evs ≼ evs' ⇒ (ep_replay w evs).clock ≤ (ep_replay w evs').clock
Proof
  rw[IS_PREFIX_APPEND] >> fs[replay_ok_APPEND] >>
  ‘ep_replay w (evs ++ l) = ep_replay (ep_replay w evs) l’ by metis_tac[ep_replay_APPEND] >>
  pop_assum SUBST1_TAC >> metis_tac[replay_clock_mono]
QED

Theorem io_prefixes_total:
  LPREFIX (fromList e1) io ∧ LPREFIX (fromList e2) io ⇒ e1 ≼ e2 ∨ e2 ≼ e1
Proof
  strip_tac >>
  ‘LPREFIX (fromList e1) (fromList e2) ∨ LPREFIX (fromList e2) (fromList e1)’
    by metis_tac[prefixes_lprefix_total] >>
  fs[LPREFIX_fromList, from_toList]
QED

Theorem nconn_mono:
  n ≤ m ⇒ nconn sk n ≤ nconn sk m
Proof
  ‘∀d. nconn sk n ≤ nconn sk (n + d)’ suffices_by metis_tac[LESS_EQ_EXISTS] >>
  Induct >> simp[GSYM ADD_SUC, nconn_def, arrivals2_upto_SUC, FILTER_APPEND] >>
  fs[nconn_def]
QED

Theorem dcount_mono:
  n ≤ m ⇒ dcount sk c n ≤ dcount sk c m
Proof
  ‘∀d. dcount sk c n ≤ dcount sk c (n + d)’ suffices_by metis_tac[LESS_EQ_EXISTS] >>
  Induct >> fs[GSYM ADD_SUC, dcount_SUC]
QED

Theorem sent2_mono:
  n ≤ m ⇒ sent2_upto c n sk ≼ sent2_upto c m sk
Proof
  ‘∀d. sent2_upto c n sk ≼ sent2_upto c (n + d) sk’ suffices_by metis_tac[LESS_EQ_EXISTS] >>
  Induct >> simp[GSYM ADD_SUC, sent2_upto_SUC] >>
  irule IS_PREFIX_TRANS >> qexists_tac ‘sent2_upto c (n + d) sk’ >> simp[]
QED

Theorem peer_at_of:
  peer_sent_at w evs c = recv_of (ep_replay w evs) c ∧
  peer_reads_at w evs c = drained_of (ep_replay w evs) c
Proof
  simp[peer_sent_at_def, peer_reads_at_def, recv_of_def, drained_of_def]
QED

Theorem dworld_reads_fair:
  server_world2 lfd sk ∧
  (∀evs. LPREFIX (fromList evs) io ⇒ replay_ok (dworld lfd a sk) evs) ∧
  ticks_forever (dworld lfd a sk) io ∧ LPREFIX (fromList evs1) io ∧
  c < LENGTH (ep_replay (dworld lfd a sk) evs1).chans ⇒
  reads_fair (dworld lfd a sk) io c
Proof
  rw[reads_fair_def, peer_at_of] >>
  qabbrev_tac ‘w = dworld lfd a sk’ >>
  qabbrev_tac ‘t0 = (ep_replay w evs).clock’ >>
  qabbrev_tac ‘t1 = (ep_replay w evs1).clock’ >>
  fs[ticks_forever_def, eventually_def] >>
  first_x_assum (qspec_then ‘MAX t0 t1 + 1’ strip_assume_tac) >>
  rename1 ‘MAX t0 t1 + 1 ≤ (ep_replay w evs').clock’ >>
  qexists_tac ‘evs'’ >> simp[] >>
  ‘dgood lfd a sk evs (ep_replay w evs) ∧ dgood lfd a sk evs1 (ep_replay w evs1) ∧
   dgood lfd a sk evs' (ep_replay w evs')’ by metis_tac[dworld_inv] >>
  fs[dgood_def] >>
  qabbrev_tac ‘T' = (ep_replay w evs').clock’ >>
  ‘∃k. T' = SUC k ∧ t0 ≤ k ∧ t1 ≤ k’
    by (qexists_tac ‘T' − 1’ >> fs[MAX_DEF] >> every_case_tac >> fs[]) >>
  ‘c < nconn sk (SUC k)’ by (‘nconn sk t1 ≤ nconn sk (SUC k)’ by simp[nconn_mono] >> fs[]) >>
  ‘dcount sk c t0 ≤ dcount sk c k’ by simp[dcount_mono] >>
  simp[dcount_SUC]
QED

(* ------------------------------------------------------------------------
   The endpoint spec gives EchoSpec2
   ------------------------------------------------------------------------ *)

Theorem socket2_oracle_ok:
  oracle_ok no_conn_send socket2_oracle
Proof
  rw[oracle_ok_def] >> Cases_on ‘n’ >>
  fs[socket2_oracle_def, no_conn_send_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[socket2_fn_def]
QED

(* MAIN: a program meeting the endpoint form of EchoSpec2 in the simple
   class meets EchoSpec2 *)
(* MAIN (helper): in the drained world of a version-2 world, endpoint
   liveness for P (weaker for a shorter input, stronger for a longer
   output) is liveness per episode against the schedule *)
Theorem live2_of_dworld:
  (∀x x' y y'. P x' y ∧ x ≼ x' ∧ y ≼ y' ⇒ P x y') ∧ P [] [] ∧
  server_world2 lfd sk ∧
  semantics_prog (init_state (socket2_ffi sk)) init_env prog (Diverge io) ∧
  semantics_prog (init_state (ep_ffi (dworld lfd a sk))) init_env prog (Diverge io) ∧
  sym_live P (dworld lfd a sk) io ∧ ticks_forever (dworld lfd a sk) io ⇒
  ∀j n. ∃evs. LPREFIX (fromList evs) io ∧ P (sent2_upto j n sk) (ep_written j evs)
Proof
  strip_tac >>
  drule_then (qspec_then ‘a’ strip_assume_tac) dworld_props >>
  qabbrev_tac ‘w = dworld lfd a sk’ >>
  ‘∀evs. LPREFIX (fromList evs) io ⇒ replay_ok w evs’ by metis_tac[trace_replay_ok] >>
  ‘∀evs. LPREFIX (fromList evs) io ⇒ EVERY (event_ok no_conn_send) evs’
    by (rpt strip_tac >>
        qpat_assum ‘semantics_prog (init_state (socket2_ffi _)) _ _ _’
          (fn th => mp_tac (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
             (Q.INST [‘P’ |-> ‘no_conn_send’] run_events_ok)) th)) >>
        simp[socket2_ffi_def, socket2_oracle_ok]) >>
  rpt gen_tac >>
  qpat_assum ‘ticks_forever _ _’ (strip_assume_tac o SIMP_RULE std_ss [ticks_forever_def, eventually_def] o Q.SPEC ‘n’ o REWRITE_RULE [ticks_forever_def]) >>
  rename1 ‘n ≤ (ep_replay w evs1).clock’ >>
  Cases_on ‘sent2_upto j n sk = []’
  >- (qexists_tac ‘[]’ >> simp[ep_written_def, accepted_fds_def] >> fs[]) >>
  ‘dgood lfd a sk evs1 (ep_replay w evs1)’ by metis_tac[dworld_inv] >>
  ‘peer_sent_at w evs1 j = sent2_upto j (ep_replay w evs1).clock sk’
    by fs[dgood_def, peer_at_of] >>
  ‘sent2_upto j n sk ≼ peer_sent_at w evs1 j’ by simp[sent2_mono] >>
  ‘peer_sent_at w evs1 j ≠ []’ by (strip_tac >> fs[]) >>
  ‘j < LENGTH (ep_replay w evs1).chans’
    by (CCONTR_TAC >> fs[peer_at_of, recv_of_def]) >>
  ‘reads_fair w io j’
    by (‘w = dworld lfd a sk’ by fs[markerTheory.Abbrev_def] >>
        pop_assum SUBST_ALL_TAC >> irule dworld_reads_fair >> metis_tac[]) >>
  qpat_x_assum ‘sym_live _ _ _’
    (mp_tac o SIMP_RULE std_ss [sym_live_def, eventually_def]) >>
  disch_then (qspecl_then [‘evs1’, ‘j’] mp_tac) >> simp[] >> strip_tac >>
  rename1 ‘ep_chan w evs2 j' = SOME j’ >>
  ‘j' = j’ by metis_tac[dworld_chan] >> gvs[] >>
  qexists_tac ‘evs2’ >> simp[] >>
  ‘ch_sent j evs2 = ep_written j evs2’ by metis_tac[ch_sent_ep_written] >>
  qpat_x_assum ‘∀x x' y y'. _’ irule >> fs[] >> metis_tac[IS_PREFIX_REFL]
QED

(* EchoSpec2's liveness *)
Theorem echo_live2_of_dworld:
  server_world2 lfd sk ∧
  semantics_prog (init_state (socket2_ffi sk)) init_env prog (Diverge io) ∧
  semantics_prog (init_state (ep_ffi (dworld lfd a sk))) init_env prog (Diverge io) ∧
  sym_live (λx y. x ≼ y) (dworld lfd a sk) io ∧ ticks_forever (dworld lfd a sk) io ⇒
  echo_live2 sk io
Proof
  strip_tac >> simp[echo_live2_def] >>
  mp_tac (BETA_RULE (Q.INST [‘P’ |-> ‘λx y. x ≼ y’] live2_of_dworld)) >>
  impl_tac >- (simp[] >> metis_tac[IS_PREFIX_TRANS]) >> simp[]
QED

Theorem echo_spec2_of_endpoint:
  rg_spec (λw. ep_server_world v2_calls lfd a w ∧ no_backpressure w ∧ open_loop w)
    ep_echo2_guar prog ⇒
  echo_spec2 lfd prog
Proof
  rw[echo_spec2_def, rg_spec_def] >>
  drule_then (qspec_then ‘a’ strip_assume_tac) dworld_props >>
  qabbrev_tac ‘w = dworld lfd a sk’ >>
  first_x_assum (qspec_then ‘w’ mp_tac) >> simp[] >> strip_tac >>
  qexists_tac ‘io’ >>
  ‘semantics_prog (init_state (socket2_ffi sk)) init_env prog (Diverge io)’
    by (‘(socket2_ffi sk).io_events = (ep_ffi w).io_events’
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
  fs[ep_echo2_guar_def] >> rpt conj_tac
  >- (rw[echo_safe2_def] >> fs[always_def] >> res_tac >>
      metis_tac[ch_sent_ep_written, ch_read_ep_read]) >>
  irule echo_live2_of_dworld >> fs[markerTheory.Abbrev_def] >> metis_tac[]
QED
