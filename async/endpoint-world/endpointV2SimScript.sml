(*
  Version 2's server worlds are exactly the endpoint server worlds with
  version 2's calls, no backpressure and a fixed schedule (v2_instance).

  The two worlds are related state by state (v2rel): the same listener
  queue, the same open fds, reserved fds and allocation, client j's
  stream is channel j's (unread bytes, EOF), every channel is Up, and the
  arrivals still to come correspond (al_rel; the endpoint world may also
  have Drains, which change nothing visible without backpressure).
  Every call answers the same in related states and keeps them related,
  so the worlds give the same answers.  The relies correspond because an
  arrival makes sense in related states alike, and the states a program
  can reach have the shape of states the world reaches left alone.
*)
Theory endpointV2Sim
Ancestors
  llist ffi alist ffiSpikeSocketFFI socketV2FFI socketV2Fair EchoSpec2
  endpointWorld endpointFair endpointSpecForms endpointSemantics
  endpointInstances
Libs
  preamble

(* ------------------------------------------------------------------------
   The relation
   ------------------------------------------------------------------------ *)

Definition chan_rel_def:
  chan_rel (cn:conn) (c:chan) ⇔
    c.inbox = cn.incoming ∧ c.peer_eof = cn.peer_closed ∧ c.status = Up
End

(* Corresponding arrivals: a connect to the listener (or to nothing), data,
   EOF *)
Definition ar_rel_def:
  ar_rel (lfd:word64) (a:num) e x ⇔
    (e = Incoming a ∧ x = Connect2 lfd) ∨
    (∃a' l. e = Incoming a' ∧ a' ≠ a ∧ x = Connect2 l ∧ l ≠ lfd) ∨
    (∃j bs. e = PData j bs ∧ x = Data2 j bs) ∨
    (∃j. e = PEof j ∧ x = Eof2 j)
End

Inductive al_rel:
  (al_rel lfd a [] []) ∧
  (∀j es xs. al_rel lfd a es xs ⇒ al_rel lfd a (Drain j :: es) xs) ∧
  (∀e x es xs. ar_rel lfd a e x ∧ al_rel lfd a es xs ⇒ al_rel lfd a (e :: es) (x :: xs))
End

(* The endpoint world's bookkeeping: pending and open channels are distinct
   and not shut *)
Definition ep_inv_def:
  ep_inv (q:num list) (w:eworld) ⇔
    ALL_DISTINCT (MAP SND w.open_fds) ∧ ALL_DISTINCT q ∧
    (∀j. MEM j q ⇒ j < LENGTH w.chans ∧ ¬MEM j (MAP SND w.open_fds) ∧
                   ¬(EL j w.chans).shut) ∧
    (∀j. MEM j (MAP SND w.open_fds) ⇒ j < LENGTH w.chans ∧ ¬(EL j w.chans).shut)
End

Definition core_def:
  core lfd a (sk:sockets2) (w:eworld) ⇔
    ∃q. sk.listening = [(lfd, q)] ∧ w.listening = [(lfd, a, q)] ∧
        LIST_REL chan_rel sk.clients w.chans ∧
        w.open_fds = sk.open_fds ∧ w.reserved = sk.reserved ∧ w.alloc = sk.alloc ∧
        ep_inv q w
End

Definition fut_step_def:
  fut_step f n = case LNTH n f of SOME as => as | NONE => []
End

Definition v2rel_def:
  v2rel lfd a sk w ⇔
    core lfd a sk w ∧ w.calls = v2_calls ∧ no_backpressure w ∧
    ∀n h. al_rel lfd a (w.env (w.clock + n) h) (fut_step sk.future n)
End

(* ------------------------------------------------------------------------
   Arrivals
   ------------------------------------------------------------------------ *)

Theorem LIST_REL_LUPDATE_chan[local]:
  LIST_REL chan_rel l1 l2 ∧ j < LENGTH l1 ∧ chan_rel (f (EL j l1)) (g (EL j l2)) ⇒
  LIST_REL chan_rel (LUPDATE (f (EL j l1)) j l1) (LUPDATE (g (EL j l2)) j l2)
Proof
  rw[LIST_REL_EL_EQN, EL_LUPDATE] >> rw[]
QED

Theorem ep_inv_upd_chan[local]:
  (∀c. (g c).shut = c.shut) ⇒ (ep_inv q (upd_chan j g w) ⇔ ep_inv q w)
Proof
  rw[ep_inv_def, upd_chan_def, EL_LUPDATE] >>
  ‘∀k. k < LENGTH w.chans ⇒ (EL k (LUPDATE (g (EL j w.chans)) j w.chans)).shut = (EL k w.chans).shut’
    by rw[EL_LUPDATE] >>
  metis_tac[]
QED

Theorem ep_inv_LUPDATE[local]:
  c.shut = (EL j w.chans).shut ⇒
  (ep_inv q (w with chans := LUPDATE c j w.chans) ⇔ ep_inv q w)
Proof
  strip_tac >>
  ‘∀k. (EL k (LUPDATE c j w.chans)).shut = (EL k w.chans).shut’ by rw[EL_LUPDATE] >>
  simp[ep_inv_def]
QED

Theorem LIST_REL_chan_LUPDATE[local]:
  LIST_REL chan_rel l1 l2 ∧ chan_rel x y ⇒
  LIST_REL chan_rel (LUPDATE x j l1) (LUPDATE y j l2)
Proof
  rw[LIST_REL_EL_EQN, EL_LUPDATE] >> rw[]
QED

Theorem core_deliver:
  core lfd a sk w ∧ ar_rel lfd a e x ⇒ core lfd a (deliver2 sk x) (ep_deliver w e)
Proof
  rw[core_def, ar_rel_def] >> gvs[deliver2_def, ep_deliver_def]
  >- (simp[AFUPDKEY_def] >> gvs[ep_inv_def, LIST_REL_EL_EQN] >> rw[] >>
      gvs[EL_APPEND_EQN, ALL_DISTINCT_APPEND, chan_rel_def, empty_conn_def, new_chan_def] >>
      rw[] >> rpt strip_tac >> res_tac >> fs[])
  >> qexists_tac ‘q’ >> imp_res_tac LIST_REL_LENGTH >> rw[] >> simp[ep_inv_upd_chan] >>
  gvs[update_client_def, upd_chan_def, LIST_REL_EL_EQN, EL_LUPDATE, chan_rel_def] >>
  rw[] >> gvs[]
QED

Theorem core_drain:
  core lfd a sk w ⇒ core lfd a sk (ep_deliver w (Drain j))
Proof
  rw[core_def, ep_deliver_def] >> rw[upd_chan_def]
  >- (fs[LIST_REL_EL_EQN, EL_LUPDATE] >> rw[] >> fs[chan_rel_def])
  >- simp[ep_inv_upd_chan |> SIMP_RULE std_ss [upd_chan_def]]
QED

Theorem core_deliver_all:
  ∀es xs. al_rel lfd a es xs ⇒
          ∀sk w. core lfd a sk w ⇒
                 core lfd a (FOLDL deliver2 sk xs) (FOLDL ep_deliver w es)
Proof
  Induct_on ‘al_rel’ >> rw[] >>
  metis_tac[core_drain, core_deliver]
QED

(* ------------------------------------------------------------------------
   Time
   ------------------------------------------------------------------------ *)

Theorem ep_deliver_fields[local]:
  ∀es w. (FOLDL ep_deliver w es).calls = w.calls ∧
         (FOLDL ep_deliver w es).takes = w.takes ∧
         (FOLDL ep_deliver w es).env = w.env ∧
         (FOLDL ep_deliver w es).clock = w.clock ∧
         (FOLDL ep_deliver w es).hist = w.hist
Proof
  Induct >> simp[] >> Cases >> rw[ep_deliver_def, upd_chan_def] >>
  every_case_tac >> simp[] >> pairarg_tac >> simp[]
QED

Theorem deliver2_future[local]:
  ∀xs s. (FOLDL deliver2 s xs).future = s.future
Proof
  Induct >> simp[] >> Cases >> rw[deliver2_def, update_client_def]
QED

Theorem core_all_up[local]:
  core lfd a sk w ⇒ EVERY (λc. c.status = Up) w.chans
Proof
  rw[core_def, EVERY_EL, LIST_REL_EL_EQN] >> res_tac >> fs[chan_rel_def]
QED

Theorem settle_id[local]:
  EVERY (λc. c.status = Up) w.chans ⇒ settle w = w
Proof
  rw[settle_def, endpointWorldTheory.eworld_component_equality, LIST_EQ_REWRITE, EL_MAPi] >>
  fs[EVERY_EL] >> res_tac >> simp[]
QED

Theorem core_with[simp]:
  (core lfd a sk (w with clock := c) ⇔ core lfd a sk w) ∧
  (core lfd a sk (w with hist := h) ⇔ core lfd a sk w) ∧
  (core lfd a (sk with future := f) w ⇔ core lfd a sk w)
Proof
  simp[core_def, ep_inv_def]
QED

Theorem fut_step_thm[simp]:
  fut_step [||] n = [] ∧
  fut_step (h ::: t) 0 = h ∧
  fut_step (h ::: t) (SUC n) = fut_step t n
Proof
  simp[fut_step_def]
QED

Theorem v2rel_tick:
  v2rel lfd a sk w ⇒ v2rel lfd a (tick2 sk) (ep_tick w)
Proof
  rw[v2rel_def] >> imp_res_tac core_all_up >> imp_res_tac settle_id >>
  simp[ep_tick_def, ep_deliver_fields] >>
  first_assum (qspecl_then [‘0’, ‘w.hist’] assume_tac) >>
  qspec_then ‘sk.future’ strip_assume_tac llist_CASES >>
  gvs[tick2_def, deliver2_future, no_backpressure_def, ep_deliver_fields] >>
  rpt strip_tac >>
  TRY (first_x_assum (qspecl_then [‘SUC n’, ‘h’] mp_tac) >> simp[ADD1] >> NO_TAC) >>
  drule core_deliver_all >>
  TRY (disch_then (qspecl_then [‘sk with future := t’, ‘w with clock := w.clock + 1’] mp_tac) >>
       simp[] >> NO_TAC) >>
  disch_then (qspecl_then [‘sk’, ‘w with clock := w.clock + 1’] mp_tac) >> simp[]
QED

(* ------------------------------------------------------------------------
   The calls
   ------------------------------------------------------------------------ *)

Definition v2_call_def:
  v2_call n conf bytes sk =
    case socket2_fn n of
    | NONE => NONE
    | SOME f => (case f conf bytes sk of
                 | SOME (FFIreturn b s) => SOME (b, s)
                 | _ => NONE)
End

Theorem socket2_oracle_v2_call:
  socket2_oracle (ExtCall n) sk conf bytes =
    case v2_call n conf bytes sk of
    | SOME (b, s) => Oracle_return s b
    | NONE => Oracle_final FFI_failed
Proof
  rw[socket2_oracle_def, v2_call_def] >> every_case_tac >> fs[]
QED

Theorem v2rel_hist[simp]:
  v2rel lfd a sk (w with hist := h) ⇔ v2rel lfd a sk w
Proof
  simp[v2rel_def, no_backpressure_def]
QED

Theorem core_ready[local]:
  core lfd a sk w ⇒ (is_ready2 sk fd ⇔ ep_readable w fd)
Proof
  rw[core_def, is_ready2_def, ep_readable_def, client_of_def, ep_chan_of_def] >>
  Cases_on ‘fd = lfd’ >> simp[] >>
  imp_res_tac LIST_REL_LENGTH >>
  every_case_tac >> gvs[LIST_REL_EL_EQN] >> res_tac >> gvs[chan_rel_def]
QED

Theorem core_chan_of[local]:
  core lfd a sk w ⇒ client_of sk f = ep_chan_of w f
Proof
  rw[core_def, client_of_def, ep_chan_of_def] >> imp_res_tac LIST_REL_LENGTH >> simp[]
QED

Theorem ALOOKUP_MEM_SND[local]:
  ALOOKUP l f = SOME j ⇒ MEM j (MAP SND l)
Proof
  rw[] >> imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP] >> metis_tac[SND]
QED

Theorem ALL_DISTINCT_MAP_FILTER[local]:
  ∀l. ALL_DISTINCT (MAP g l) ⇒ ALL_DISTINCT (MAP g (FILTER P l))
Proof
  Induct >> rw[] >> fs[MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem MEM_SND_UNIQUE[local]:
  ∀l. ALL_DISTINCT (MAP SND l) ∧ MEM (x, j) l ∧ MEM (y, j) l ⇒ x = y
Proof
  Induct >> rw[] >> gvs[MEM_MAP] >> metis_tac[SND]
QED

Theorem ADELKEY_SND[local]:
  ALL_DISTINCT (MAP SND l) ∧ ALOOKUP l f = SOME j ⇒
  ¬MEM j (MAP SND (ADELKEY f l)) ∧ ALL_DISTINCT (MAP SND (ADELKEY f l)) ∧
  ∀k. MEM k (MAP SND (ADELKEY f l)) ⇒ MEM k (MAP SND l)
Proof
  rw[ADELKEY_def, MEM_MAP, MEM_FILTER, ALL_DISTINCT_MAP_FILTER]
  >- (imp_res_tac ALOOKUP_MEM >> Cases_on ‘y’ >> gvs[] >>
      metis_tac[MEM_SND_UNIQUE]) >>
  metis_tac[]
QED

Theorem v2rel_poll[local]:
  v2rel lfd a sk w ⇒
  (v2_call «sock_poll» conf bytes sk = NONE ∧ ep_call «sock_poll» conf bytes w = NONE) ∨
  ∃b sk' w'. v2_call «sock_poll» conf bytes sk = SOME (b, sk') ∧
             ep_call «sock_poll» conf bytes w = SOME (b, w') ∧ v2rel lfd a sk' w'
Proof
  strip_tac >> ‘MEM «sock_poll» w.calls’ by fs[v2rel_def, v2_calls_def, v1_calls_def] >>
  simp[v2_call_def, socket2_fn_def, ffi_sock_poll2_def, ep_call_def] >>
  rw[] >> drule v2rel_tick >> rw[] >>
  ‘core lfd a (tick2 sk) (ep_tick w)’ by fs[v2rel_def] >>
  drule core_ready >> simp[]
QED

Theorem v2rel_accept[local]:
  v2rel lfd a sk w ⇒
  (v2_call «sock_accept» conf bytes sk = NONE ∧ ep_call «sock_accept» conf bytes w = NONE) ∨
  ∃b sk' w'. v2_call «sock_accept» conf bytes sk = SOME (b, sk') ∧
             ep_call «sock_accept» conf bytes w = SOME (b, w') ∧ v2rel lfd a sk' w'
Proof
  strip_tac >> ‘MEM «sock_accept» w.calls’ by fs[v2rel_def, v2_calls_def, v1_calls_def] >>
  simp[v2_call_def, socket2_fn_def, ffi_sock_accept2_def, ep_call_def] >>
  Cases_on ‘LENGTH conf = 8 ∧ LENGTH bytes = 9’ >> simp[] >>
  gvs[v2rel_def, core_def] >>
  simp[sock_accept2_def, ep_accept_def] >>
  Cases_on ‘bytes_fd conf = lfd’ >> simp[] >>
  Cases_on ‘q’ >> simp[] >>
  simp[ep_alloc_def, ep_used_def, used_fds_def] >>
  IF_CASES_TAC >> simp[] >>
  simp[AFUPDKEY_def] >>
  gvs[ep_inv_def, no_backpressure_def] >> rw[] >> res_tac >> fs[] >>
  qpat_x_assum ‘∀j. j = h ∨ _ ⇒ _’ (qspec_then ‘h’ mp_tac) >> simp[]
QED

Theorem v2rel_read[local]:
  v2rel lfd a sk w ⇒
  (v2_call «sock_read» conf bytes sk = NONE ∧ ep_call «sock_read» conf bytes w = NONE) ∨
  ∃b sk' w'. v2_call «sock_read» conf bytes sk = SOME (b, sk') ∧
             ep_call «sock_read» conf bytes w = SOME (b, w') ∧ v2rel lfd a sk' w'
Proof
  strip_tac >> ‘MEM «sock_read» w.calls’ by fs[v2rel_def, v2_calls_def, v1_calls_def] >>
  simp[v2_call_def, socket2_fn_def, ffi_sock_read2_def, ep_call_def] >>
  Cases_on ‘LENGTH conf = 8 ∧ 9 < LENGTH bytes’ >> simp[] >>
  ‘core lfd a sk w’ by fs[v2rel_def] >>
  drule core_chan_of >> disch_then (qspec_then ‘bytes_fd conf’ assume_tac) >>
  simp[sock_read2_def, ep_read_def] >>
  Cases_on ‘ep_chan_of w (bytes_fd conf)’ >> simp[] >>
  rename1 ‘ep_chan_of w _ = SOME j’ >>
  ‘j < LENGTH w.chans’ by gvs[ep_chan_of_def, AllCaseEqs()] >>
  ‘chan_rel (EL j sk.clients) (EL j w.chans)’ by fs[core_def, LIST_REL_EL_EQN] >>
  gvs[chan_rel_def] >> rw[] >>
  gvs[v2rel_def, core_def, update_client_def, upd_chan_def, no_backpressure_def,
      ep_inv_LUPDATE] >>
  irule LIST_REL_chan_LUPDATE >> simp[chan_rel_def]
QED

Theorem v2rel_write[local]:
  v2rel lfd a sk w ⇒
  (v2_call «sock_write» conf bytes sk = NONE ∧ ep_call «sock_write» conf bytes w = NONE) ∨
  ∃b sk' w'. v2_call «sock_write» conf bytes sk = SOME (b, sk') ∧
             ep_call «sock_write» conf bytes w = SOME (b, w') ∧ v2rel lfd a sk' w'
Proof
  strip_tac >> ‘MEM «sock_write» w.calls’ by fs[v2rel_def, v2_calls_def, v1_calls_def] >>
  simp[v2_call_def, socket2_fn_def, ffi_sock_write2_def, ep_call_def] >>
  Cases_on ‘8 ≤ LENGTH conf’ >> simp[] >>
  ‘core lfd a sk w’ by fs[v2rel_def] >>
  drule core_chan_of >> disch_then (qspec_then ‘bytes_fd (TAKE 8 conf)’ assume_tac) >>
  simp[sock_write2_def, ep_send_def] >>
  Cases_on ‘ep_chan_of w (bytes_fd (TAKE 8 conf))’ >> simp[] >>
  rename1 ‘ep_chan_of w _ = SOME j’ >>
  ‘j < LENGTH w.chans ∧ MEM j (MAP SND w.open_fds)’
    by (gvs[ep_chan_of_def, AllCaseEqs()] >> metis_tac[ALOOKUP_MEM_SND]) >>
  ‘chan_rel (EL j sk.clients) (EL j w.chans) ∧ ¬(EL j w.chans).shut’
    by (fs[core_def, LIST_REL_EL_EQN, ep_inv_def] >> res_tac) >>
  gvs[chan_rel_def, v2rel_def, no_backpressure_def] >>
  gvs[core_def, update_client_def, upd_chan_def, ep_inv_LUPDATE] >>
  irule LIST_REL_chan_LUPDATE >> simp[chan_rel_def]
QED

Theorem v2rel_close[local]:
  v2rel lfd a sk w ⇒
  (v2_call «sock_close» conf bytes sk = NONE ∧ ep_call «sock_close» conf bytes w = NONE) ∨
  ∃b sk' w'. v2_call «sock_close» conf bytes sk = SOME (b, sk') ∧
             ep_call «sock_close» conf bytes w = SOME (b, w') ∧ v2rel lfd a sk' w'
Proof
  strip_tac >> ‘MEM «sock_close» w.calls’ by fs[v2rel_def, v2_calls_def, v1_calls_def] >>
  simp[v2_call_def, socket2_fn_def, ffi_sock_close2_def, ep_call_def] >>
  Cases_on ‘LENGTH conf = 8’ >> simp[] >>
  ‘core lfd a sk w’ by fs[v2rel_def] >>
  drule core_chan_of >> disch_then (qspec_then ‘bytes_fd conf’ assume_tac) >>
  simp[sock_close2_def, ep_close_def] >>
  Cases_on ‘ep_chan_of w (bytes_fd conf)’ >> simp[] >>
  rename1 ‘ep_chan_of w _ = SOME j’ >>
  ‘j < LENGTH w.chans ∧ ALOOKUP w.open_fds (bytes_fd conf) = SOME j’
    by gvs[ep_chan_of_def, AllCaseEqs()] >>
  gvs[v2rel_def, core_def, upd_chan_def, no_backpressure_def] >>
  imp_res_tac LIST_REL_LENGTH >>
  conj_tac >- (fs[LIST_REL_EL_EQN, EL_LUPDATE] >> rw[] >> res_tac >> fs[chan_rel_def]) >>
  ‘ALL_DISTINCT (MAP SND sk.open_fds)’ by metis_tac[ep_inv_def] >>
  drule_all ADELKEY_SND >> strip_tac >>
  gvs[ep_inv_def, EL_LUPDATE] >> rw[] >> res_tac >> fs[] >>
  strip_tac >> imp_res_tac ALOOKUP_MEM_SND >> res_tac >> fs[]
QED

Theorem v2rel_call:
  v2rel lfd a sk w ⇒
  (v2_call n conf bytes sk = NONE ∧ ep_ffi_fn n conf bytes w = NONE) ∨
  ∃b sk' w'. v2_call n conf bytes sk = SOME (b, sk') ∧
             ep_ffi_fn n conf bytes w = SOME (b, w') ∧ v2rel lfd a sk' w'
Proof
  strip_tac >> simp[ep_ffi_fn_def] >>
  Cases_on ‘MEM n v2_calls’
  >- (fs[v2_calls_def, v1_calls_def] >> rveq >>
      FIRST (map (fn th => drule_then (qspecl_then [‘conf’, ‘bytes’] strip_assume_tac) th >>
                           gvs[] >> NO_TAC)
                 [v2rel_poll, v2rel_accept, v2rel_read, v2rel_write, v2rel_close])) >>
  ‘socket2_fn n = NONE’ by (fs[socket2_fn_def, v2_calls_def, v1_calls_def] >> rw[]) >>
  ‘w.calls = v2_calls’ by fs[v2rel_def] >>
  simp[v2_call_def, ep_call_def]
QED

Theorem v2rel_run_calls:
  ∀cs sk w. v2rel lfd a sk w ⇒ run_calls (socket2_ffi sk) cs = run_calls (ep_ffi w) cs
Proof
  Induct >> simp[run_calls_def, FORALL_PROD] >> rpt strip_tac >>
  simp[socket2_ffi_def, ep_ffi_def] >>
  Cases_on ‘p_1’ >>
  simp[socket2_oracle_v2_call, ep_oracle_def, socket2_oracle_def] >>
  rename1 ‘v2_call s _ _ sk’ >>
  drule v2rel_call >>
  disch_then (qspecl_then [‘s’, ‘p_1'’, ‘p_2’] strip_assume_tac) >> simp[] >>
  first_x_assum drule >> simp[socket2_ffi_def, ep_ffi_def]
QED

(* ------------------------------------------------------------------------
   The relies: an arrival makes sense in related states alike
   ------------------------------------------------------------------------ *)

Theorem core_arrival_ok[local]:
  core lfd a sk w ∧ ar_rel lfd a e x ⇒ (arrival_ok2 sk x ⇔ ep_arrival_ok w e)
Proof
  rw[core_def, ar_rel_def] >> imp_res_tac LIST_REL_LENGTH >>
  simp[arrival_ok2_def, ep_arrival_ok_def] >>
  rw[EQ_IMP_THM] >> gvs[LIST_REL_EL_EQN, chan_rel_def] >> res_tac >> gvs[]
QED

Theorem al_rel_step_ok2:
  ∀es xs. al_rel lfd a es xs ⇒
          ∀sk w. core lfd a sk w ∧ ep_step_ok w es ⇒ step_ok2 sk xs
Proof
  Induct_on ‘al_rel’ >> rw[step_ok2_def, ep_step_ok_def]
  >- metis_tac[core_drain]
  >- metis_tac[core_arrival_ok]
  >- metis_tac[core_deliver]
QED

Definition no_drain_def:
  no_drain es ⇔ ∀j. ¬MEM (Drain j) es
End

Theorem al_rel_ep_step_ok:
  ∀es xs. al_rel lfd a es xs ⇒
          ∀sk w. no_drain es ∧ core lfd a sk w ∧ step_ok2 sk xs ⇒ ep_step_ok w es
Proof
  Induct_on ‘al_rel’ >> rw[step_ok2_def, ep_step_ok_def, no_drain_def] >>
  metis_tac[core_arrival_ok, core_deliver, no_drain_def]
QED

(* The shape of a version-2 state: what the validity of arrivals depends on *)
Definition v2shape_def:
  v2shape (s:sockets2) =
    (MAP FST s.listening, s.reserved, MAP (λcn. cn.peer_closed) s.clients, s.future)
End

Theorem MAP_FST_AFUPDKEY[local]:
  ∀l. MAP FST (AFUPDKEY k f l) = MAP FST l
Proof
  Induct >> simp[AFUPDKEY_def, FORALL_PROD] >> rw[]
QED

Theorem v2shape_deliver[local]:
  v2shape s1 = v2shape s2 ⇒ v2shape (deliver2 s1 x) = v2shape (deliver2 s2 x)
Proof
  rw[v2shape_def] >>
  ‘LENGTH s1.clients = LENGTH s2.clients’ by metis_tac[LENGTH_MAP] >>
  ‘(ALOOKUP s1.listening l = NONE ⇔ ALOOKUP s2.listening l = NONE) ∧
   ∀j. j < LENGTH s1.clients ⇒ ((EL j s1.clients).peer_closed ⇔ (EL j s2.clients).peer_closed)’
    by (simp[ALOOKUP_NONE] >> rw[] >>
        qpat_x_assum ‘MAP _ s1.clients = _’ (mp_tac o Q.AP_TERM ‘EL j’) >> simp[EL_MAP]) >>
  Cases_on ‘x’ >> rw[deliver2_def, update_client_def, MAP_FST_AFUPDKEY] >>
  gvs[ALOOKUP_NONE, MAP_FST_AFUPDKEY] >>
  rw[LIST_EQ_REWRITE, EL_MAP, EL_LUPDATE] >> rw[] >>
  qpat_x_assum ‘MAP _ s1.clients = _’ (mp_tac o Q.AP_TERM ‘EL x’) >> simp[EL_MAP]
QED

Theorem v2shape_tick[local]:
  v2shape s1 = v2shape s2 ⇒ v2shape (tick2 s1) = v2shape (tick2 s2)
Proof
  ‘∀xs s1 s2. v2shape s1 = v2shape s2 ⇒ v2shape (FOLDL deliver2 s1 xs) = v2shape (FOLDL deliver2 s2 xs)’
    by (Induct >> simp[] >> metis_tac[v2shape_deliver]) >>
  strip_tac >> ‘s1.future = s2.future’ by fs[v2shape_def] >>
  qspec_then ‘s2.future’ strip_assume_tac llist_CASES >> gvs[tick2_def] >>
  first_x_assum irule >> fs[v2shape_def]
QED

Theorem v2shape_step_ok2[local]:
  ∀xs s1 s2. v2shape s1 = v2shape s2 ⇒ (step_ok2 s1 xs ⇔ step_ok2 s2 xs)
Proof
  Induct >> simp[step_ok2_def] >> rpt strip_tac >>
  ‘arrival_ok2 s1 h ⇔ arrival_ok2 s2 h’
    by (fs[v2shape_def] >>
        ‘LENGTH s1.clients = LENGTH s2.clients ∧ LENGTH s1.listening = LENGTH s2.listening’
          by metis_tac[LENGTH_MAP] >>
        Cases_on ‘h’ >> simp[arrival_ok2_def, ALOOKUP_NONE] >>
        rw[EQ_IMP_THM] >>
        qpat_x_assum ‘MAP _ s1.clients = _’ (mp_tac o Q.AP_TERM ‘EL n’) >> simp[EL_MAP]) >>
  metis_tac[v2shape_deliver]
QED

Theorem v2_call_shape[local]:
  v2_call n conf bytes sk = SOME (b, sk') ⇒ v2shape sk' = v2shape sk ∨ sk' = tick2 sk
Proof
  rw[v2_call_def, socket2_fn_def, AllCaseEqs()] >>
  gvs[ffi_sock_poll2_def, ffi_sock_accept2_def, ffi_sock_read2_def, ffi_sock_write2_def,
      ffi_sock_close2_def, AllCaseEqs(), sock_accept2_def, sock_read2_def,
      sock_write2_def, sock_close2_def] >>
  simp[v2shape_def, MAP_FST_AFUPDKEY, update_client_def] >>
  TRY (disj1_tac >> rw[LIST_EQ_REWRITE, EL_MAP, EL_LUPDATE] >> rw[] >> NO_TAC)
QED

Theorem ticks2_SUC'[local]:
  ∀n s. ticks2 (SUC n) s = tick2 (ticks2 n s)
Proof
  Induct >> fs[ticks2_def]
QED

Theorem ep_ffi_fn_env[local]:
  ep_ffi_fn n conf bytes w = SOME (b, w') ⇒ w'.env = w.env
Proof
  rw[ep_ffi_fn_def, ep_call_def, AllCaseEqs()] >>
  gvs[ep_tick_def, ep_deliver_fields, settle_def, ep_accept_def, ep_connect_def,
      ep_alloc_def, ep_read_def, ep_send_def, ep_shutdown_def, ep_close_def,
      upd_chan_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()]
QED

(* The states a program reaches have the shape of states the world reaches
   left alone *)
Theorem ep_after_v2rel:
  ∀cs w sk w'. v2rel lfd a sk w ∧ ep_after w cs = SOME w' ∧
               (∃k. v2shape sk = v2shape (ticks2 k sk0)) ⇒
               ∃sk'. v2rel lfd a sk' w' ∧ w'.env = w.env ∧
                     ∃k. v2shape sk' = v2shape (ticks2 k sk0)
Proof
  Induct >> simp[ep_after_def, FORALL_PROD] >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  drule v2rel_call >>
  disch_then (qspecl_then [‘p_1’, ‘p_1'’, ‘p_2’] strip_assume_tac) >> gvs[] >>
  imp_res_tac ep_ffi_fn_env >>
  first_x_assum (qspecl_then [‘w''’, ‘sk'’, ‘w'’] mp_tac) >> impl_tac
  >- (simp[] >> imp_res_tac v2_call_shape >> gvs[] >- metis_tac[] >>
      qexists_tac ‘SUC k’ >> simp[ticks2_SUC'] >> metis_tac[v2shape_tick]) >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------
   The two directions
   ------------------------------------------------------------------------ *)

Definition tr_def:
  tr lfd a (Connect2 l) = (if l = lfd then Incoming a else Incoming (a + 1)) ∧
  tr lfd a (Data2 j bs) = PData j bs ∧
  tr lfd a (Eof2 j) = PEof j
End

Theorem al_rel_tr[local]:
  ∀xs. al_rel lfd a (MAP (tr lfd a) xs) xs ∧ no_drain (MAP (tr lfd a) xs)
Proof
  Induct >> simp[Once al_rel_cases, no_drain_def] >> fs[no_drain_def] >>
  Cases >> rw[tr_def, ar_rel_def]
QED

Definition untr_def:
  untr lfd a [] = [] ∧
  untr lfd a (Incoming a' :: es) =
    (if a' = a then Connect2 lfd else Connect2 (lfd + 1w)) :: untr lfd a es ∧
  untr lfd a (PData j bs :: es) = Data2 j bs :: untr lfd a es ∧
  untr lfd a (PEof j :: es) = Eof2 j :: untr lfd a es ∧
  untr lfd a (Drain j :: es) = untr lfd a es
End

Theorem al_rel_untr[local]:
  ∀es. al_rel lfd a es (untr lfd a es)
Proof
  Induct >> simp[Once al_rel_cases, untr_def] >>
  Cases >> rw[untr_def, ar_rel_def] >> metis_tac[]
QED

Theorem next_step2_fut[local]:
  next_step2 s = fut_step s.future 0
Proof
  simp[next_step2_def, fut_step_def, LNTH]
QED

Theorem v2_forward:
  server_world2 lfd sk ⇒
  ∃a w. ep_server_world v2_calls lfd a w ∧ no_backpressure w ∧ open_loop w ∧
        ep_rely w ∧ same_answers (socket2_ffi sk) (ep_ffi w)
Proof
  rw[server_world2_def] >>
  qabbrev_tac ‘w0 = <| listening := [(lfd, 0, [])]; chans := []; open_fds := [];
                       reserved := sk.reserved; alloc := sk.alloc;
                       accepts := (λa j. T); takes := (λj b n. n); calls := v2_calls;
                       env := (λn h. MAP (tr lfd 0) (fut_step sk.future n));
                       clock := 0; hist := [] |>’ >>
  ‘v2rel lfd 0 sk w0’
    by simp[Abbr ‘w0’, v2rel_def, core_def, ep_inv_def, no_backpressure_def, al_rel_tr] >>
  qexistsl_tac [‘0’, ‘w0’] >>
  ‘ep_server_world v2_calls lfd 0 w0 ∧ no_backpressure w0 ∧ open_loop w0 ∧
   w0.env = (λn h. MAP (tr lfd 0) (fut_step sk.future n)) ∧ alloc_ok w0.alloc ∧
   takes_ok w0.takes’
    by simp[Abbr ‘w0’, ep_server_world_def, no_backpressure_def, open_loop_def,
            takes_ok_def] >>
  simp[] >>
  reverse conj_tac
  >- (simp[same_answers_def] >> metis_tac[v2rel_run_calls]) >>
  simp[ep_rely_def, ep_sched_ok_def] >> rpt strip_tac >>
  qspecl_then [‘cs’, ‘w0’, ‘sk’, ‘w'’] mp_tac
    (Q.INST [‘sk0’ |-> ‘sk’, ‘a’ |-> ‘0’] ep_after_v2rel) >>
  impl_tac >- (simp[] >> qexists_tac ‘0’ >> simp[ticks2_def]) >>
  strip_tac >>
  ‘step_ok2 sk' (next_step2 sk')’
    by (fs[sched_wf2_def] >>
        first_x_assum (qspec_then ‘k’ mp_tac) >>
        ‘next_step2 sk' = next_step2 (ticks2 k sk)’ by fs[v2shape_def, next_step2_def] >>
        metis_tac[v2shape_step_ok2]) >>
  gvs[v2rel_def] >>
  qpat_x_assum ‘∀n. al_rel _ _ _ (fut_step sk'.future n)’ (qspec_then ‘0’ assume_tac) >>
  fs[] >> drule al_rel_ep_step_ok >> disch_then irule >>
  imp_res_tac core_all_up >> imp_res_tac settle_id >>
  simp[al_rel_tr] >> qexists_tac ‘sk'’ >> fs[next_step2_fut]
QED

Theorem v2_after_polls[local]:
  ∀k w sk. v2rel lfd a sk w ⇒
           ∃wk. ep_after w (REPLICATE k («sock_poll», [], [])) = SOME wk ∧
                v2rel lfd a (ticks2 k sk) wk
Proof
  Induct >> simp[ep_after_def, ticks2_def] >> rpt strip_tac >>
  drule v2rel_call >>
  disch_then (qspecl_then [‘«sock_poll»’, ‘[]’, ‘[]’] strip_assume_tac) >>
  gvs[v2_call_def, socket2_fn_def, ffi_sock_poll2_def]
QED

Theorem v2_converse:
  ep_server_world v2_calls lfd a w ∧ no_backpressure w ∧ open_loop w ∧ ep_rely w ⇒
  ∃sk. server_world2 lfd sk ∧ same_answers (socket2_ffi sk) (ep_ffi w)
Proof
  rw[ep_server_world_def] >>
  qabbrev_tac ‘sk0 = <| listening := [(lfd, [])]; clients := []; open_fds := [];
                        reserved := w.reserved; alloc := w.alloc;
                        future := LGENLIST (λn. untr lfd a (w.env (w.clock + n) [])) NONE |>’ >>
  ‘v2rel lfd a sk0 w’
    by (simp[Abbr ‘sk0’, v2rel_def, core_def, ep_inv_def] >>
        rw[fut_step_def, LNTH_LGENLIST] >> fs[open_loop_def] >>
        metis_tac[al_rel_untr]) >>
  qexists_tac ‘sk0’ >>
  reverse conj_tac
  >- (simp[same_answers_def] >> metis_tac[v2rel_run_calls]) >>
  ‘sk0.listening = [(lfd,[])] ∧ sk0.clients = [] ∧ sk0.open_fds = [] ∧
   sk0.alloc = w.alloc’ by simp[Abbr ‘sk0’] >>
  simp[server_world2_def] >> conj_tac >- fs[ep_rely_def] >>
  simp[sched_wf2_def] >> gen_tac >>
  drule_then (qspec_then ‘n’ strip_assume_tac) v2_after_polls >>
  ‘ep_step_ok (settle wk with clock := wk.clock + 1) (wk.env wk.clock wk.hist)’
    by (qpat_x_assum ‘ep_rely w’ mp_tac >> simp[ep_rely_def, ep_sched_ok_def] >>
        strip_tac >> first_x_assum drule >> simp[]) >>
  gvs[v2rel_def] >>
  first_x_assum (qspecl_then [‘0’, ‘wk.hist’] assume_tac) >> fs[] >>
  drule al_rel_step_ok2 >>
  disch_then (qspecl_then [‘ticks2 n sk0’, ‘settle wk with clock := wk.clock + 1’] mp_tac) >>
  imp_res_tac core_all_up >> imp_res_tac settle_id >>
  simp[next_step2_fut]
QED

(* MAIN: version 2's server worlds are exactly the endpoint server worlds
   with version 2's calls, no backpressure and a fixed schedule *)
Theorem v2_instance_thm:
  v2_instance
Proof
  rw[v2_instance_def] >- metis_tac[v2_forward] >> metis_tac[v2_converse]
QED
