(*
  R2, round by round: in the simple world, a round of L1 (the
  computation's actions, then the poll) is a round of the handle layer
  (asyncHLModel's hacts and hpoll), with the same responses and snapshot,
  and L1's renamed events are the handle layer's with some would-block
  events deleted.

  The server's side of the round discipline is stated on the handle
  layer alone (hacts_disc): it accepts only on the listener and reads only
  handles that were polled, with the fd they had, at the last poll.
*)
Theory honestL1Round
Ancestors
  honestL1Steps honestL1Refine honestL1Model honestL1Simple honestL1Inv
  honestL0World honestL0WorldProps honestL0Rely honestL0 asyncHLModel socketV2FFI
  socketV2Events ffiSpikeSocketFFI asyncM3World asyncCore asyncLevel1 Marshalling
Libs
  preamble

(* ------------------------------------------------------------------------
   The actions of a round
   ------------------------------------------------------------------------ *)

(* The discipline, on the handle layer's run of the actions *)
Definition hacts_disc_def:
  hacts_disc lfd polp sh [] = T ∧
  hacts_disc lfd polp (s, hs) (a :: acts) =
    ((case a of
      | Accept l => l = lfd ∧ MEM (lfd, lfd) polp
      | Read h n => 0 < n ∧ n < 256 ** 8 ∧ ∀f. ALOOKUP hs.tbl h = SOME f ⇒ MEM (h, f) polp
      | Write h bs => LENGTH bs < 256 ** 8) ∧
     case hdo lfd (s, hs) a of
     | SOME (r, sh', evs) => hacts_disc lfd polp sh' acts
     | NONE => T)
End

Theorem act_disc_hl:
  st.tbl = hs.tbl ⇒
  (act_disc lfd polp st a ⇔
   case a of
   | Accept l => l = lfd ∧ MEM (lfd, lfd) polp
   | Read h n => 0 < n ∧ n < 256 ** 8 ∧ ∀f. ALOOKUP hs.tbl h = SOME f ⇒ MEM (h, f) polp
   | Write h bs => LENGTH bs < 256 ** 8)
Proof
  Cases_on ‘a’ >> simp[act_disc_def]
QED

Theorem hdln_mono:
  j ≤ k ⇒ hdln n j ≤ hdln n k
Proof
  rw[hdln_def]
QED

Theorem acts_step:
  ∀acts w st s hs.
    simple_v2 p lfd sched w ∧ l0_rely w ∧ l1v2_rel p lfd sched (w, st) (s, hs) ∧
    rdy_ok lfd polp w st ∧ fds_lt w ∧ hacts_disc lfd polp (s, hs) acts ∧
    LENGTH (l0_used w) + LENGTH acts < 2147483647 ∧
    hdln (w2n lfd) (st.nxt + LENGTH acts) < dimword (:64) ∧ w2n lfd < 2147483648 ⇒
    ∃rs evs w' st' evs' s' hs'.
      l1acts lfd (w, st) acts = SOME (rs, evs, (w', st')) ∧
      hacts lfd (s, hs) acts = SOME (rs, evs', (s', hs')) ∧
      drops (MAP l0_v2_event evs) evs' ∧
      simple_v2 p lfd sched w' ∧ l0_rely w' ∧
      l1v2_rel p lfd sched (w', st') (s', hs') ∧ rdy_ok lfd polp w' st' ∧ fds_lt w' ∧
      st'.nxt ≤ st.nxt + LENGTH acts ∧
      LENGTH (l0_used w') ≤ LENGTH (l0_used w) + LENGTH acts
Proof
  Induct >> simp[l1acts_def, hacts_def] >> rpt gen_tac >> strip_tac >>
  ‘st.tbl = hs.tbl’ by gvs[l1v2_rel_def] >>
  ‘act_disc lfd polp st h’ by (Cases_on ‘h’ >> gvs[act_disc_def, hacts_disc_def]) >>
  ‘LENGTH (l0_used w) < 2147483647’ by decide_tac >>
  ‘hdln (w2n lfd) st.nxt ≤ hdln (w2n lfd) (st.nxt + SUC (LENGTH acts))’
    by (irule hdln_mono >> simp[]) >>
  ‘hdln (w2n lfd) st.nxt < dimword (:64)’ by (fs[] >> decide_tac) >>
  drule_all act_step >> strip_tac >> simp[] >>
  ‘hacts_disc lfd polp (s', hs') acts’ by gvs[hacts_disc_def] >>
  ‘simple_v2 p lfd sched w'’ by metis_tac[simple_v2_same] >>
  ‘l0_rely w'’ by (irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  first_x_assum (qspecl_then [‘w'’, ‘st'’, ‘s'’, ‘hs'’] mp_tac) >>
  impl_tac
  >- (simp[] >> TRY (conj_tac >- decide_tac) >>
      ‘hdln (w2n lfd) (st'.nxt + LENGTH acts) ≤ hdln (w2n lfd) (st.nxt + SUC (LENGTH acts))’
        by (irule hdln_mono >> simp[]) >>
      fs[] >> decide_tac) >>
  strip_tac >> simp[] >>
  rpt conj_tac >> TRY (metis_tac[drops_APPEND] >> NO_TAC) >> decide_tac
QED

(* ------------------------------------------------------------------------
   The poll
   ------------------------------------------------------------------------ *)

(* A polled fd (the listener or an open connection) is readable in L0's
   sense exactly when version 2 reports it ready *)
Theorem fd_readable_core:
  core_rel p lfd w1 s1 ∧ (f = lfd ∨ ALOOKUP w1.open_fds f ≠ NONE) ⇒
  ((byte_revents (fd_revents w1 (f, 1))).rin ∨ (byte_revents (fd_revents w1 (f, 1))).rhup ∨
   (byte_revents (fd_revents w1 (f, 1))).rerr ⇔ is_ready2 s1 f) ∧
  poll_flag (fd_revents w1 (f, 1)) = (if is_ready2 s1 f then 1w else 0w)
Proof
  strip_tac >> gvs[core_rel_def]
  >- (simp[fd_revents_def, l0_chan_of_def, is_ready2_def, client_of_def, poll_flag_def,
           no_revents_def] >>
      rw[] >> gvs[])
  >> Cases_on ‘ALOOKUP s1.open_fds f’ >> gvs[] >>
  rename1 ‘ALOOKUP _ f = SOME j’ >>
  ‘f ≠ lfd’ by (strip_tac >> gvs[]) >>
  ‘j < LENGTH w1.chans ∧ ¬(EL j w1.chans).closed’ by metis_tac[] >>
  ‘chan_rel (EL j w1.chans) (EL j s1.clients)’ by gvs[LIST_REL_EL_EQN] >>
  gvs[chan_rel_def] >>
  imp_res_tac LIST_REL_LENGTH >>
  simp[fd_revents_def, l0_chan_of_def, chan_revents_def, is_ready2_def, client_of_def,
       poll_flag_def] >>
  rw[] >> gvs[] >> metis_tac[]
QED

Theorem poll_set_simple:
  st.outbox = [] ∧ ¬st.exhausted ∧ st.tbl = hs.tbl ⇒
  l1_poll_set lfd hw st hfds = MAP (λf. (f, 1n)) (hpoll_fds lfd hs hfds)
Proof
  strip_tac >> simp[l1_poll_set_def, hpoll_fds_def, MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF] >>
  AP_TERM_TAC >> simp[MAP_EQ_f] >> rw[] >>
  every_case_tac >> gvs[outbox_of_def]
QED

Theorem poll_chunks_small:
  LENGTH l ≤ 4096 ⇒ poll_chunks l = [l]
Proof
  simp[Once poll_chunks_def]
QED

Theorem l1_flush_noout:
  ∀fs w. st.outbox = [] ⇒ l1_flush fs (w, st) = SOME ((w, st), [])
Proof
  Induct >> simp[l1_flush_def, outbox_of_def]
QED

Theorem l1_ready_hready:
  st.tbl = hs.tbl ⇒ l1_ready lfd st rdy hfds = hready lfd hs rdy hfds
Proof
  simp[l1_ready_def, hready_def]
QED

(* The pairs (handle, fd) a poll of the interest hfds polls *)
Definition poll_pairs_def:
  poll_pairs lfd (st : l1st) hfds =
    FLAT (MAP (λh. case ALOOKUP st.tbl h of
                   | SOME f => [(h, f)]
                   | NONE => if h = lfd then [(lfd, lfd)] else []) hfds)
End

Theorem deliver_open[simp]:
  (l0_deliver w a).open_fds = w.open_fds
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def, upd_lchan_def] >> every_case_tac >> simp[]
QED

Theorem tick_open[simp]:
  (l0_tick nm w).open_fds = w.open_fds
Proof
  simp[l0_tick_def] >>
  ‘∀as w0. (FOLDL l0_deliver w0 as).open_fds = w0.open_fds’ by (Induct >> simp[]) >>
  simp[]
QED

(* Over the polled fds, L0's readable set is version 2's ready set, and
   the renamed flags are version 2's *)
Theorem readable_filter:
  ∀fds. core_rel p lfd w1 s1 ∧ EVERY (λf. f = lfd ∨ ALOOKUP w1.open_fds f ≠ NONE) fds ⇒
    readable_fds (ZIP (fds, MAP (λf. byte_revents (fd_revents w1 (f, 1))) fds)) =
      FILTER (is_ready2 s1) fds ∧
    MAP (λf. poll_flag (fd_revents w1 (f, 1))) fds =
      MAP (λfd. if is_ready2 s1 fd then 1w else 0w) fds
Proof
  Induct >> simp[readable_fds_def] >> rpt gen_tac >> strip_tac >>
  drule fd_readable_core >> disch_then (qspec_then ‘h’ mp_tac) >> simp[] >>
  strip_tac >> gvs[readable_fds_def] >> rw[] >> gvs[]
QED

Theorem hpoll_fds_open:
  l1v2_rel p lfd sched (w, st) (s, hs) ⇒
  EVERY (λf. f = lfd ∨ ALOOKUP w.open_fds f ≠ NONE) (hpoll_fds lfd hs hfds)
Proof
  rw[l1v2_rel_def, hpoll_fds_def, EVERY_MEM, MEM_FLAT, MEM_MAP] >>
  gvs[] >> every_case_tac >> gvs[core_rel_def] >> metis_tac[]
QED

Theorem tick_hist_ch[simp]:
  (l0_tick nm w).hist = w.hist ∧ (l0_tick nm w).ch = w.ch
Proof
  simp[l0_tick_def] >>
  ‘∀as w0. (FOLDL l0_deliver w0 as).hist = w0.hist’
    by (Induct >> simp[] >> rpt gen_tac >> Cases_on ‘h’ >>
        rw[l0_deliver_def, upd_lchan_def] >> every_case_tac >> simp[]) >>
  simp[]
QED

(* A poll in the simple world: it never fails or blocks *)
Theorem sys_poll_simple:
  simple_v2 p lfd sched w ∧ EVERY (λ(f, e). w2n f < 2147483648 ∧ e < 256) fes ∧
  LENGTH fes ≤ 4096 ⇒
  sys_poll fes w =
    SOME (poll_out (l0_tick «sys_poll» w) fes,
          l0_tick «sys_poll» w with
            hist := w.hist ++ [(«sys_poll», poll_conf fes, REPLICATE (LENGTH fes + 13) 0w)],
          IO_event (ExtCall «sys_poll») (poll_conf fes)
            (ZIP (REPLICATE (LENGTH fes + 13) 0w, poll_out (l0_tick «sys_poll» w) fes)))
Proof
  strip_tac >>
  ‘EVERY (λ(f, e). e < 256) fes ∧ EVERY (fd_ok o FST) fes’
    by (gvs[EVERY_MEM, FORALL_PROD, fd_ok_def] >> metis_tac[]) >>
  ‘w.ch.transient w.hist = NONE’ by gvs[simple_v2_def, simple0_def] >>
  simp[sys_poll_def, l0_do_def, l0_ffi_fn_def, l0_call_def, l0_hdr_def, poll_conf_def,
       poll_entries_conf, LENGTH_poll_conf]
QED

Theorem poll_pairs_mem:
  st.tbl = hs.tbl ∧ MEM (h, f) (poll_pairs lfd st hfds) ⇒
  MEM f (hpoll_fds lfd hs hfds) ∧
  ((h = lfd ∧ f = lfd ∧ ALOOKUP st.tbl lfd = NONE) ∨ ALOOKUP st.tbl h = SOME f)
Proof
  simp[poll_pairs_def, hpoll_fds_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> rename1 ‘MEM y hfds’ >>
  Cases_on ‘ALOOKUP hs.tbl y’ >> gvs[]
  >- (Cases_on ‘y = lfd’ >> gvs[] >> first_assum (irule_at Any) >> simp[])
  >> first_assum (irule_at Any) >> simp[]
QED

(* The round's poll, in the simple world: one sys_poll; the handle layer's
   ready handles and poll event; the relation kept; and the round
   discipline holds for the pairs just polled *)
Theorem tail_step:
  simple_v2 p lfd sched w ∧ l0_rely w ∧ l1v2_rel p lfd sched (w, st) (s, hs) ∧
  fds_lt w ∧ w2n lfd < 2147483648 ∧ LENGTH (hpoll_fds lfd hs hfds) ≤ 4096 ⇒
  ∃w' st' evs.
    l1_tail lfd hw hfds (w, st) =
      SOME (hready lfd hs (FST (sock_poll2 (hpoll_fds lfd hs hfds) s)) hfds, (w', st'), evs) ∧
    MAP l0_v2_event evs = [spoll2_event (hpoll_fds lfd hs hfds) s] ∧
    l1v2_rel p lfd sched (w', st') (SND (sock_poll2 (hpoll_fds lfd hs hfds) s), hs) ∧
    rdy_ok lfd (poll_pairs lfd st hfds) w' st' ∧ fds_lt w' ∧ st'.nxt = st.nxt ∧
    l0_used w' = l0_used w ∧ w'.env = w.env ∧ w'.ch = w.ch ∧ w'.fd_limit = w.fd_limit
Proof
  strip_tac >>
  ‘st.outbox = [] ∧ ¬st.exhausted ∧ st.tbl = hs.tbl ∧ st.closing = [] ∧
   core_rel p lfd w s ∧ s.future = fut_of p lfd sched (npolls w.hist)’
    by gvs[l1v2_rel_def] >>
  qabbrev_tac ‘fds = hpoll_fds lfd hs hfds’ >>
  qabbrev_tac ‘fes = MAP (λf. (f, 1n)) fds’ >>
  ‘l1_poll_set lfd hw st hfds = fes’ by simp[Abbr ‘fes’, Abbr ‘fds’, poll_set_simple] >>
  ‘poll_chunks fes = [fes]’ by simp[poll_chunks_small, Abbr ‘fes’] >>
  qabbrev_tac ‘w1 = l0_tick «sys_poll» w’ >>
  ‘core_rel p lfd w1 (tick2 s) ∧ (tick2 s).future = fut_of p lfd sched (npolls w.hist + 1)’
    by (simp[Abbr ‘w1’] >> metis_tac[poll_tick_core]) >>
  ‘EVERY (λf. f = lfd ∨ ALOOKUP w.open_fds f ≠ NONE) fds’
    by (qunabbrev_tac ‘fds’ >> drule hpoll_fds_open >>
        disch_then (qspec_then ‘hfds’ mp_tac) >> simp[]) >>
  ‘l0_rely w1’ by (simp[Abbr ‘w1’] >> irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  ‘EVERY (λ(f, e). w2n f < 2147483648 ∧ e < 256) fes’
    by (simp[Abbr ‘fes’, EVERY_MAP] >> gvs[EVERY_MEM] >> rw[] >>
        Cases_on ‘ALOOKUP w.open_fds f’ >> gvs[] >>
        ‘MEM f (l0_used w)’ by (irule open_used >> simp[]) >>
        gvs[fds_lt_def, l0_rely_def] >> res_tac >> decide_tac) >>
  ‘LENGTH fes ≤ 4096’ by simp[Abbr ‘fes’] >>
  drule_all sys_poll_simple >> strip_tac >>
  simp[l1_tail_def, l1_polls_def] >>
  qabbrev_tac ‘out = poll_out w1 fes’ >>
  ‘LENGTH (FILTER (λfe. fd_revents w1 fe ≠ 0w) fes) < 256 ** 8’
    by (irule LESS_EQ_LESS_TRANS >> qexists_tac ‘LENGTH fes’ >> simp[LENGTH_FILTER_LEQ]) >>
  ‘l0_res_of out = Ok (LENGTH (FILTER (λfe. fd_revents w1 fe ≠ 0w) fes))’
    by (simp[Abbr ‘out’, poll_out_def] >> irule l0_res_of_enc_app >> simp[l0_res_ok_def]) >>
  ‘DROP 13 out = MAP (fd_revents w1) fes’
    by (simp[Abbr ‘out’, poll_out_def] >> simp[DROP_APPEND, enc_res_def, LENGTH_n2w8]) >>
  ‘LENGTH out = LENGTH fes + 13’
    by (simp[Abbr ‘out’, poll_out_def] >> simp[enc_res_def, LENGTH_n2w8]) >>
  ‘poll_revents fes out = ZIP (fds, MAP (λf. byte_revents (fd_revents w1 (f, 1))) fds)’
    by (simp[poll_revents_def, Abbr ‘fes’, MAP_MAP_o, combinTheory.o_DEF] >>
        ‘LENGTH (MAP (fd_revents w1) (MAP (λf. (f,1n)) fds)) = LENGTH fds’ by simp[] >>
        simp[TAKE_LENGTH_ID_rwt, MAP_MAP_o, combinTheory.o_DEF]) >>
  ‘EVERY (λf. f = lfd ∨ ALOOKUP w1.open_fds f ≠ NONE) fds’ by gvs[Abbr ‘w1’] >>
  drule_all readable_filter >> strip_tac >>
  simp[l1_flush_noout, l1_reap_def, l1_ready_hready, sock_poll2_def] >>
  ‘l0_used w1 = l0_used w ∧ w1.env = w.env ∧ w1.ch = w.ch ∧ w1.fd_limit = w.fd_limit ∧
   w1.open_fds = w.open_fds ∧ w1.hist = w.hist’
    by simp[Abbr ‘w1’, l0_tick_def] >>
  ‘EVERY (λ(f, e). e < 256) fes’ by (simp[Abbr ‘fes’, EVERY_MAP]) >>
  ‘poll_entries (DROP 1 (poll_conf fes)) = fes’ by simp[poll_conf_def, poll_entries_conf] >>
  ‘«sys_poll» ≠ «sys_recv» ∧ «sys_poll» ≠ «sys_send» ∧ «sys_poll» ≠ «sys_accept» ∧
   «sys_poll» ≠ «sys_close»’ by EVAL_TAC >>
  rpt conj_tac
  (* the event *)
  >- (simp[l0_v2_event_def, spoll2_event_def, MAP_SND_ZIP_REPLICATE] >>
      ‘TAKE (LENGTH fes) (DROP 13 out) = MAP (fd_revents w1) fes’ by simp[] >>
      simp[Abbr ‘fes’, MAP_MAP_o, combinTheory.o_DEF] >>
      gvs[MAP_MAP_o, combinTheory.o_DEF] >>
      ‘TAKE (LENGTH fds) (MAP (λf. fd_revents w1 (f,1)) fds) =
       MAP (λf. fd_revents w1 (f,1)) fds’ by simp[TAKE_LENGTH_ID_rwt] >>
      simp[MAP_MAP_o, combinTheory.o_DEF])
  (* the relation *)
  >- (qpat_x_assum ‘l1v2_rel _ _ _ _ _’ mp_tac >>
      simp[l1v2_rel_def, npolls_snoc] >> strip_tac >> simp[] >> metis_tac[])
  (* the round discipline for the pairs just polled *)
  >- (qpat_x_assum ‘core_rel _ _ w1 _’ mp_tac >> simp[core_rel_def] >> strip_tac >>
      simp[rdy_ok_def, MEM_FILTER] >> rpt conj_tac
      >- (rpt gen_tac >> strip_tac >>
          drule_all poll_pairs_mem >> strip_tac >>
          ‘¬is_ready2 (tick2 s) f’ by metis_tac[] >>
          ‘j < LENGTH w1.chans ∧ ¬(EL j w1.chans).closed’ by metis_tac[] >>
          ‘chan_rel (EL j w1.chans) (EL j (tick2 s).clients)’ by gvs[LIST_REL_EL_EQN] >>
          ‘f ≠ lfd’ by (strip_tac >> gvs[]) >>
          imp_res_tac LIST_REL_LENGTH >>
          qpat_x_assum ‘¬is_ready2 _ _’ mp_tac >>
          simp[is_ready2_def, client_of_def] >> gvs[chan_rel_def])
      >- (rpt strip_tac >> drule_all poll_pairs_mem >> strip_tac >> gvs[] >>
          ‘¬is_ready2 (tick2 s) lfd’ by metis_tac[] >>
          qpat_x_assum ‘¬is_ready2 _ _’ mp_tac >> simp[is_ready2_def] >> gvs[])
      >> rpt gen_tac >> strip_tac >>
      drule_all poll_pairs_mem >> strip_tac >> gvs[l1v2_rel_def] >> metis_tac[])
  >> gvs[fds_lt_def]
QED

(* ------------------------------------------------------------------------
   A whole round
   ------------------------------------------------------------------------ *)

(* The pairs polled, from a handle table (the handle layer's) *)
Definition pairs_of_def:
  pairs_of lfd (tbl : (word64 # word64) list) hfds =
    FLAT (MAP (λh. case ALOOKUP tbl h of
                   | SOME f => [(h, f)]
                   | NONE => if h = lfd then [(lfd, lfd)] else []) hfds)
End

Theorem poll_pairs_of:
  poll_pairs lfd st hfds = pairs_of lfd st.tbl hfds
Proof
  simp[poll_pairs_def, pairs_of_def]
QED

Theorem round_step:
  simple_v2 p lfd sched w ∧ l0_rely w ∧ l1v2_rel p lfd sched (w, st) (s, hs) ∧
  rdy_ok lfd polp w st ∧ fds_lt w ∧ hacts_disc lfd polp (s, hs) acts ∧
  LENGTH (l0_used w) + LENGTH acts < 2147483647 ∧
  hdln (w2n lfd) (st.nxt + LENGTH acts) < dimword (:64) ∧ w2n lfd < 2147483648 ∧
  hacts lfd (s, hs) acts = SOME (rs, hevs, (s1, hs1)) ∧
  LENGTH (hpoll_fds lfd hs1 hfds) ≤ 4096 ⇒
  ∃w' st' evs.
    l1round lfd hw hfds (w, st) acts =
      SOME (ssnap (FST (hpoll lfd hs1 hfds s1)) rs, (w', st'), evs) ∧
    drops (MAP l0_v2_event evs) (hevs ++ [spoll2_event (hpoll_fds lfd hs1 hfds) s1]) ∧
    simple_v2 p lfd sched w' ∧ l0_rely w' ∧
    l1v2_rel p lfd sched (w', st') (SND (hpoll lfd hs1 hfds s1), hs1) ∧
    rdy_ok lfd (pairs_of lfd hs1.tbl hfds) w' st' ∧ fds_lt w' ∧
    st'.nxt ≤ st.nxt + LENGTH acts ∧ LENGTH (l0_used w') ≤ LENGTH (l0_used w) + LENGTH acts
Proof
  strip_tac >> drule_all acts_step >> strip_tac >> gvs[] >>
  ‘st'.tbl = hs'.tbl’ by gvs[l1v2_rel_def] >>
  drule_all tail_step >> disch_then (qspec_then ‘hw’ strip_assume_tac) >>
  gvs[] >>
  simp[l1round_def, hpoll_def] >>
  pairarg_tac >> gvs[sock_poll2_def] >>
  rpt conj_tac
  >- (irule drops_APPEND >> simp[])
  >- metis_tac[simple_v2_same]
  >- (irule l0_rely_ch >> qexists_tac ‘w'’ >> simp[])
  >- gvs[poll_pairs_of]
  >> gvs[]
QED
