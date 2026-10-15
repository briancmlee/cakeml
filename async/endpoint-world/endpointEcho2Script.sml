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
       reserved := sk.reserved; alloc := sk.alloc; accepts := (λa j. T);
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
  gvs[ep_tick_def, ep_deliver_fields, settle_def, ep_accept_def, ep_connect_def,
      ep_alloc_def, ep_read_def, ep_send_def, ep_shutdown_def, ep_close_def,
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
      imp_res_tac core_all_up >> imp_res_tac settle_id >> simp[] >>
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
