(*
  Reindexed L0 worlds (L3-09, the blocking L1; design note L3-09 §2 (S2)).

  The L0 world's choices and its environment are functions of the call
  history, and each call (each poll too) is recorded in it.  So a blocking
  poll that waits k steps and k + 1 non-blocking polls reach different
  histories.  To compare a blocking run in w0 with a non-blocking run, the
  non-blocking run is placed in a REINDEXED world: w0's choices and
  environment composed with a history translation tr, which maps the
  non-blocking run's history to the blocking run's.

    reindex tr w0: w0 with every choice f h ... := f (tr h) ...
                  and env n h nm := env n (tr h) nm
    sim tr w' w:   w' is w's state, with w's choices and environment
                  reindexed by tr, and a history h' with tr h' = w.hist

  Nothing here is trusted: l0_rely and l0_server_world's static conditions
  are statements about all histories, so reindexing keeps them
  (l0_rely_reindex).

  MAIN: l0_rely_reindex, sim_tick, sim_ticks, sim_revents, sim_wait.
*)
Theory honestL0Reindex
Ancestors
  honestL0 honestL0World honestL0Rely
Libs
  preamble

Definition reindex_ch_def:
  reindex_ch (tr : lcall list -> lcall list) (c : lchoices) =
    <| takes := (λj h. c.takes j (tr h));
       short := (λj h. c.short j (tr h));
       transient := (λh. c.transient (tr h));
       errno_of := (λh. c.errno_of (tr h));
       listen_fails := (λh. c.listen_fails (tr h));
       emfile_drops := (λh. c.emfile_drops (tr h));
       accept_aborts := (λh. c.accept_aborts (tr h));
       send_pending := (λh. c.send_pending (tr h));
       broken_send := (λh. c.broken_send (tr h));
       broken_recv := (λh. c.broken_recv (tr h));
       show_err := (λh. c.show_err (tr h));
       show_hup := (λh. c.show_hup (tr h));
       show_out := (λh. c.show_out (tr h));
       shut_err := (λh. c.shut_err (tr h));
       close_intr := (λh. c.close_intr (tr h));
       misuse := (λh. c.misuse (tr h));
       reserved_rev := (λh. c.reserved_rev (tr h));
       connect_now := (λh. c.connect_now (tr h));
       pending_err := (λh. c.pending_err (tr h)) |>
End

Definition reindex_def:
  reindex tr (w : l0world) =
    w with <| ch := reindex_ch tr w.ch; env := (λn h nm. w.env n (tr h) nm) |>
End

(* w' is w's state, in w's world reindexed by tr, at a history tr maps to
   w's *)
Definition sim_def:
  sim tr w' w ⇔ ∃h'. w' = reindex tr w with hist := h' ∧ tr h' = w.hist
End

(* ------------------------------------------------------------------------
   Reindexing keeps the rely
   ------------------------------------------------------------------------ *)

Theorem l0_rely_reindex:
  l0_rely w ⇒ l0_rely (reindex tr w)
Proof
  simp[l0_rely_def, reindex_def, reindex_ch_def] >> strip_tac >> rpt conj_tac >>
  rpt gen_tac >> TRY strip_tac >> res_tac >> simp[]
QED

(* ------------------------------------------------------------------------
   Steps of time
   ------------------------------------------------------------------------ *)

(* Arrivals touch only the state *)
Theorem l0_deliver_with:
  ∀a. l0_deliver (w with <| ch := c; env := e; hist := h |>) a =
      l0_deliver w a with <| ch := c; env := e; hist := h |>
Proof
  Cases >> rw[l0_deliver_def, upd_lchan_def] >> every_case_tac >> gvs[] >>
  simp[honestL0WorldTheory.l0world_component_equality]
QED

Theorem FOLDL_l0_deliver_with:
  ∀as w c e hs. FOLDL l0_deliver (w with <| ch := c; env := e; hist := hs |>) as =
                FOLDL l0_deliver w as with <| ch := c; env := e; hist := hs |>
Proof
  Induct >> rw[] >> rename1 ‘l0_deliver _ a’ >>
  ‘l0_deliver (w with <| ch := c; env := e; hist := hs |>) a =
   l0_deliver w a with <| ch := c; env := e; hist := hs |>’ by simp[l0_deliver_with] >>
  simp[]
QED

Theorem FOLDL_l0_deliver_fields:
  ∀as w. (FOLDL l0_deliver w as).ch = w.ch ∧ (FOLDL l0_deliver w as).env = w.env ∧
         (FOLDL l0_deliver w as).hist = w.hist ∧ (FOLDL l0_deliver w as).clock = w.clock
Proof
  Induct >> rw[] >> Cases_on ‘h’ >>
  rw[l0_deliver_def, upd_lchan_def] >> every_case_tac >> gvs[]
QED

(* MAIN: a step of time keeps the simulation *)
Theorem tick_with:
  e w.clock h nm = w.env w.clock w.hist nm ⇒
  l0_tick nm (w with <| ch := c; env := e; hist := h |>) =
  l0_tick nm w with <| ch := c; env := e; hist := h |>
Proof
  rw[l0_tick_def] >>
  qspecl_then [‘w.env w.clock w.hist nm’, ‘w with clock := w.clock + 1’, ‘c’, ‘e’, ‘h’]
    mp_tac FOLDL_l0_deliver_with >>
  simp[]
QED

Theorem tick_fields:
  (l0_tick nm w).ch = w.ch ∧ (l0_tick nm w).env = w.env ∧ (l0_tick nm w).hist = w.hist
Proof
  simp[l0_tick_def, FOLDL_l0_deliver_fields]
QED

(* MAIN: a step of time keeps the simulation *)
Theorem sim_tick:
  sim tr w' w ⇒ sim tr (l0_tick nm w') (l0_tick nm w)
Proof
  rw[sim_def] >> qexists_tac ‘h'’ >> simp[reindex_def] >>
  qspecl_then [‘λn h nm. w.env n (tr h) nm’, ‘w’, ‘h'’, ‘nm’, ‘reindex_ch tr w.ch’]
    mp_tac (Q.GENL [‘e’, ‘w’, ‘h’, ‘nm’, ‘c’] tick_with) >>
  simp[] >> disch_then kall_tac >>
  simp[honestL0WorldTheory.l0world_component_equality, tick_fields]
QED

Theorem sim_ticks:
  ∀n w' w. sim tr w' w ⇒ sim tr (l0_ticks nm n w') (l0_ticks nm n w)
Proof
  Induct >> rw[l0_ticks_def] >> first_x_assum irule >> simp[sim_tick]
QED

(* ------------------------------------------------------------------------
   Readiness
   ------------------------------------------------------------------------ *)

Theorem sim_fields:
  sim tr w' w ⇒
  w'.listeners = w.listeners ∧ w'.chans = w.chans ∧ w'.open_fds = w.open_fds ∧
  w'.reserved = w.reserved ∧ w'.fd_limit = w.fd_limit ∧ w'.clock = w.clock ∧
  w'.ch = reindex_ch tr w.ch ∧ tr w'.hist = w.hist
Proof
  rw[sim_def] >> simp[reindex_def]
QED

(* MAIN: the simulating world reports the same readiness *)
Theorem sim_revents:
  sim tr w' w ⇒ fd_revents w' fe = fd_revents w fe
Proof
  strip_tac >> drule sim_fields >> strip_tac >>
  PairCases_on ‘fe’ >>
  simp[fd_revents_def, l0_chan_of_def, chan_revents_def] >>
  every_case_tac >> gvs[reindex_ch_def]
QED

Theorem sim_any_revents:
  sim tr w' w ⇒ (any_revents w' fes ⇔ any_revents w fes)
Proof
  rw[any_revents_def] >> drule sim_revents >> simp[]
QED

Theorem sim_poll_out:
  sim tr w' w ⇒ poll_out w' fes = poll_out w fes
Proof
  rw[poll_out_def] >> drule sim_revents >> simp[] >> strip_tac >>
  ‘fd_revents w' = fd_revents w’ by simp[FUN_EQ_THM] >> simp[]
QED

(* MAIN: a blocking poll waits as long in both worlds *)
Theorem sim_wait:
  sim tr w' w ⇒ l0_wait fes w' = l0_wait fes w
Proof
  strip_tac >>
  ‘∀n. any_revents (l0_ticks «sys_poll» n w') fes ⇔ any_revents (l0_ticks «sys_poll» n w) fes’
    by (gen_tac >> irule sim_any_revents >> metis_tac[sim_ticks]) >>
  simp[l0_wait_def]
QED
