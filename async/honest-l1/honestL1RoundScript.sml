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
  socketV2Events ffiSpikeSocketFFI asyncM3World asyncCore asyncLevel1
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
