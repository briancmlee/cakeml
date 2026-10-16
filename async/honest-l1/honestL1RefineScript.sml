(*
  R2: in the simple world, L1 is the handle layer (design/36 §6).

  The simple version-2 class (simple_v2): a simple L0 world (honestL1Simple's
  simple0) with one listener lfd on port p, whose environment delivers
  arrivals only before polls, from a fixed schedule indexed by the number
  of polls so far (open loop, as version 2's schedule).  Its version-2
  counterpart sk_of has the same listener, reserved fds and schedule, and
  POSIX's fd choice (lowest_free).

  The relation l1v2_rel between L1 over the L0 world and the handle layer
  over the version-2 world: equal handle tables; no outbox, closing,
  broken or exhausted state in L1; equal listener queues and open fds; each
  L0 channel is the version-2 client of the same number (while open: its
  input and EOF; always: what was sent); the remaining schedules agree.
  rdy_ok pol carries the round discipline: an fd polled at the last poll
  (pol) and not in L1's readable set really has nothing to read.

  Events are renamed by l0_v2_event: sys_recv ↦ sock_read, sys_send ↦
  sock_write, sys_accept ↦ sock_accept, sys_close ↦ sock_close, sys_poll ↦
  sock_poll.

  This theory: the definitions, the step of time and the arrivals.
*)
Theory honestL1Refine
Ancestors
  honestL1Model honestL1Simple honestL1Inv honestL0World honestL0 asyncHLModel
  socketV2FFI socketV2Events ffiSpikeSocketFFI asyncM3World asyncCore asyncLevel1
  llist Marshalling
Libs
  preamble

(* ------------------------------------------------------------------------
   The simple version-2 class and its version-2 world
   ------------------------------------------------------------------------ *)

Definition npolls_def:
  npolls (h : lcall list) = LENGTH (FILTER (λ(n, c, b). n = «sys_poll») h)
End

(* An L0 arrival as version-2 arrivals: connections to the listener's
   port, data and EOF; drains have no version-2 counterpart (version 2 has
   no backpressure) *)
Definition conv_arr_def:
  conv_arr p lfd (LIncoming p') = (if p' = p then [Connect2 lfd] else []) ∧
  conv_arr p lfd (LData j bs) = [Data2 j bs] ∧
  conv_arr p lfd (LEof j) = [Eof2 j] ∧
  conv_arr p lfd (LBreak j e k) = [] ∧
  conv_arr p lfd (LDrain j k) = []
End

Definition conv_step_def:
  conv_step p lfd as = FLAT (MAP (conv_arr p lfd) as)
End

Definition fut_of_def:
  fut_of p lfd (sched : num -> l0_arrival list) k =
    LGENLIST (λi. conv_step p lfd (sched (k + i))) NONE
End

Definition simple_v2_def:
  simple_v2 p lfd sched (w : l0world) ⇔
    simple0 w ∧ (∀n h nm. w.env n h nm = if nm = «sys_poll» then sched (npolls h) else [])
End

(* The version-2 world of an L0 world *)
Definition sk_of_def:
  sk_of p lfd sched (w : l0world) =
    <| listening := MAP (λ(l, p', q). (l, q)) w.listeners;
       clients := MAP (λc. <| incoming := c.inbox; peer_closed := c.peer_eof;
                              outgoing := c.sent |>) w.chans;
       open_fds := w.open_fds; reserved := w.reserved;
       alloc := (λj used. lowest_free used);
       future := fut_of p lfd sched (npolls w.hist) |>
End

(* ------------------------------------------------------------------------
   The relation
   ------------------------------------------------------------------------ *)

Definition chan_rel_def:
  chan_rel (c : lchan) (cl : conn) ⇔
    ¬c.broken ∧ c.err = NONE ∧ c.sent = cl.outgoing ∧ (c.shut ⇒ c.closed) ∧
    (¬c.closed ⇒ c.inbox = cl.incoming ∧ c.peer_eof = cl.peer_closed)
End

(* The worlds agree (all but the schedules) *)
Definition core_rel_def:
  core_rel p lfd (w : l0world) (s : sockets2) ⇔
    (∃q. w.listeners = [(lfd, p, q)] ∧ s.listening = [(lfd, q)] ∧
         EVERY (λj. j < LENGTH w.chans ∧ ¬(EL j w.chans).closed) q) ∧
    w.open_fds = s.open_fds ∧ w.reserved = s.reserved ∧
    s.alloc = (λj used. lowest_free used) ∧
    LIST_REL chan_rel w.chans s.clients ∧
    (∀f j. ALOOKUP w.open_fds f = SOME j ⇒ j < LENGTH w.chans ∧ ¬(EL j w.chans).closed)
End

Definition l1v2_rel_def:
  l1v2_rel p lfd sched (w : l0world, st : l1st) (s : sockets2, hs : hstate) ⇔
    st.tbl = hs.tbl ∧ st.nxt = hs.nxt ∧ st.outbox = [] ∧ st.closing = [] ∧
    st.gone = [] ∧ ¬st.exhausted ∧ core_rel p lfd w s ∧
    s.future = fut_of p lfd sched (npolls w.hist)
End

(* The round discipline: an fd polled at the last poll and not readable
   since has nothing to read *)
Definition rdy_ok_def:
  rdy_ok lfd pol (w : l0world) (st : l1st) ⇔
    (∀f j. MEM f pol ∧ ¬MEM f st.rdy ∧ ALOOKUP w.open_fds f = SOME j ⇒
           (EL j w.chans).inbox = [] ∧ ¬(EL j w.chans).peer_eof) ∧
    (MEM lfd pol ∧ ¬MEM lfd st.rdy ⇒ ∀p q. MEM (lfd, p, q) w.listeners ⇒ q = [])
End

(* ------------------------------------------------------------------------
   Time
   ------------------------------------------------------------------------ *)

Theorem npolls_snoc:
  npolls (h ++ [(n, c, b)]) = npolls h + if n = «sys_poll» then 1 else 0
Proof
  rw[npolls_def, FILTER_APPEND]
QED

(* Before a call other than a poll nothing arrives *)
Theorem tick_simple_v2:
  simple_v2 p lfd sched w ∧ nm ≠ «sys_poll» ⇒
  l0_tick nm w = w with clock := w.clock + 1
Proof
  rw[simple_v2_def, l0_tick_def]
QED

(* fut_of advances by one at each poll *)
Theorem fut_of_LHD_LTL:
  LHD (fut_of p lfd sched k) = SOME (conv_step p lfd (sched k)) ∧
  LTL (fut_of p lfd sched k) = SOME (fut_of p lfd sched (k + 1))
Proof
  simp[fut_of_def, combinTheory.o_DEF] >>
  AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM, ADD1]
QED

(* ------------------------------------------------------------------------
   Arrivals
   ------------------------------------------------------------------------ *)

Definition no_break_def:
  no_break (LBreak j e k) = F ∧ no_break _ = T
End

Theorem chan_rel_fresh[simp]:
  chan_rel fresh_lchan empty_conn
Proof
  simp[chan_rel_def, fresh_lchan_def, empty_conn_def]
QED

Theorem LIST_REL_LUPDATE_both:
  LIST_REL R l1 l2 ∧ j < LENGTH l1 ∧ R x y ⇒ LIST_REL R (LUPDATE x j l1) (LUPDATE y j l2)
Proof
  rw[LIST_REL_EL_EQN, EL_LUPDATE] >> rw[]
QED

Theorem core_rel_upd:
  core_rel p lfd w s ∧ n < LENGTH w.chans ∧
  chan_rel (g (EL n w.chans)) (k (EL n s.clients)) ∧
  (g (EL n w.chans)).closed = (EL n w.chans).closed ⇒
  core_rel p lfd (upd_lchan n g w) (update_client n k s)
Proof
  rw[core_rel_def, upd_lchan_def, update_client_def] >>
  imp_res_tac LIST_REL_LENGTH >>
  gvs[EVERY_MEM, EL_LUPDATE, LIST_REL_EL_EQN] >> rw[] >> gvs[] >>
  metis_tac[]
QED

Theorem core_rel_upd_left:
  core_rel p lfd w s ∧ n < LENGTH w.chans ∧
  chan_rel (g (EL n w.chans)) (EL n s.clients) ∧
  (g (EL n w.chans)).closed = (EL n w.chans).closed ⇒
  core_rel p lfd (upd_lchan n g w) s
Proof
  rw[core_rel_def, upd_lchan_def] >>
  imp_res_tac LIST_REL_LENGTH >>
  gvs[EVERY_MEM, EL_LUPDATE, LIST_REL_EL_EQN] >> rw[] >> gvs[] >>
  metis_tac[]
QED

Theorem core_rel_upd_right:
  core_rel p lfd w s ∧ n < LENGTH w.chans ∧
  chan_rel (EL n w.chans) (k (EL n s.clients)) ⇒
  core_rel p lfd w (update_client n k s)
Proof
  rw[core_rel_def, update_client_def] >>
  imp_res_tac LIST_REL_LENGTH >>
  gvs[EVERY_MEM, EL_LUPDATE, LIST_REL_EL_EQN] >> rw[] >> gvs[] >>
  metis_tac[]
QED

Theorem core_rel_LENGTH:
  core_rel p lfd w s ⇒ LENGTH s.clients = LENGTH w.chans
Proof
  rw[core_rel_def] >> imp_res_tac LIST_REL_LENGTH >> simp[]
QED

Theorem core_rel_chan:
  core_rel p lfd w s ∧ n < LENGTH w.chans ⇒ chan_rel (EL n w.chans) (EL n s.clients)
Proof
  rw[core_rel_def, LIST_REL_EL_EQN]
QED

(* One arrival keeps the worlds in step *)
Theorem deliver_core:
  core_rel p lfd w s ∧ no_break a ⇒
  core_rel p lfd (l0_deliver w a) (FOLDL deliver2 s (conv_arr p lfd a))
Proof
  Cases_on ‘a’ >> rw[no_break_def, conv_arr_def]
  (* Incoming on the listener's port *)
  >- (gvs[core_rel_def] >> simp[l0_deliver_def, deliver2_def, AFUPDKEY_def] >>
      imp_res_tac LIST_REL_LENGTH >> simp[] >>
      gvs[EVERY_MEM, EL_APPEND1, EL_APPEND2] >> rw[] >>
      TRY (first_x_assum drule >> simp[EL_APPEND1] >> NO_TAC) >>
      TRY (gvs[EL_APPEND_EQN] >> rw[] >> gvs[fresh_lchan_def] >> NO_TAC) >>
      res_tac >> simp[EL_APPEND1])
  (* Incoming on another port: dropped by both *)
  >- (gvs[core_rel_def, l0_deliver_def] >> metis_tac[])
  (* Data *)
  >- (rename1 ‘LData j bs’ >> imp_res_tac core_rel_LENGTH >>
      simp[l0_deliver_def, deliver2_def] >>
      Cases_on ‘j < LENGTH w.chans’ >> simp[] >>
      drule_all core_rel_chan >> strip_tac >>
      Cases_on ‘(EL j w.chans).closed’
      >- (rpt IF_CASES_TAC >> gvs[] >>
          FIRST [irule core_rel_upd, irule core_rel_upd_left, irule core_rel_upd_right] >>
          gvs[chan_rel_def])
      >> gvs[chan_rel_def] >> rw[] >> irule core_rel_upd >> gvs[chan_rel_def])
  (* EOF *)
  >- (rename1 ‘LEof j’ >> imp_res_tac core_rel_LENGTH >>
      simp[l0_deliver_def, deliver2_def] >>
      Cases_on ‘j < LENGTH w.chans’ >> simp[] >>
      drule_all core_rel_chan >> strip_tac >>
      gvs[chan_rel_def] >> irule core_rel_upd >> gvs[chan_rel_def])
  (* Drain: nothing the relation sees *)
  >> simp[l0_deliver_def] >> rw[] >>
  irule core_rel_upd_left >> simp[] >> drule_all core_rel_chan >> simp[chan_rel_def]
QED

Theorem deliver_steps:
  ∀as w s. core_rel p lfd w s ∧ EVERY no_break as ⇒
           core_rel p lfd (FOLDL l0_deliver w as) (FOLDL deliver2 s (conv_step p lfd as))
Proof
  Induct >> simp[conv_step_def, FOLDL_APPEND] >> rpt strip_tac >>
  simp[GSYM conv_step_def] >>
  first_x_assum irule >> simp[] >>
  irule deliver_core >> simp[]
QED

Theorem core_rel_clock[simp]:
  core_rel p lfd (w with clock := c) s ⇔ core_rel p lfd w s
Proof
  simp[core_rel_def]
QED

Theorem core_rel_hist[simp]:
  core_rel p lfd (w with hist := h) s ⇔ core_rel p lfd w s
Proof
  simp[core_rel_def]
QED

Theorem core_rel_future[simp]:
  core_rel p lfd w (s with future := f) ⇔ core_rel p lfd w s
Proof
  simp[core_rel_def]
QED

(* The schedule of a simple version-2 world has no breaks *)
Theorem simple_v2_no_break:
  simple_v2 p lfd sched w ⇒ EVERY no_break (sched k)
Proof
  rw[simple_v2_def, simple0_def, env_simple_def, EVERY_MEM] >>
  first_x_assum (qspecl_then [‘0’, ‘REPLICATE k («sys_poll», [], [])’, ‘«sys_poll»’] mp_tac) >>
  ‘∀k. npolls (REPLICATE k («sys_poll», [], [])) = k’
    by (Induct >> gvs[npolls_def]) >>
  Cases_on ‘e’ >> gvs[no_break_def] >> metis_tac[]
QED

(* MAIN (time): the step of time before a poll is version 2's tick *)
Theorem poll_tick_core:
  simple_v2 p lfd sched w ∧ core_rel p lfd w s ∧
  s.future = fut_of p lfd sched (npolls w.hist) ⇒
  core_rel p lfd (l0_tick «sys_poll» w) (tick2 s) ∧
  (tick2 s).future = fut_of p lfd sched (npolls w.hist + 1)
Proof
  strip_tac >>
  ‘w.env w.clock w.hist «sys_poll» = sched (npolls w.hist)’ by gvs[simple_v2_def] >>
  simp[l0_tick_def, tick2_def, fut_of_LHD_LTL] >>
  ‘∀as (s:sockets2). (FOLDL deliver2 s as).future = s.future’
    by (Induct >> simp[] >> rpt gen_tac >> Cases_on ‘h’ >>
        rw[deliver2_def, update_client_def]) >>
  simp[] >>
  irule deliver_steps >> simp[] >> metis_tac[simple_v2_no_break]
QED
