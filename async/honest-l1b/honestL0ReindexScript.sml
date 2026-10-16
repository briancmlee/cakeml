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

(* ========================================================================
   The calls: every L0 operation, run in the reindexed world at a history
   that tr maps to w's, is the operation run in w, lifted
   ======================================================================== *)

Definition lift_def:
  lift tr h' (v : l0world) = reindex tr v with hist := h'
End

Theorem lift_fields[simp]:
  (lift tr h' v).listeners = v.listeners ∧ (lift tr h' v).chans = v.chans ∧
  (lift tr h' v).open_fds = v.open_fds ∧ (lift tr h' v).reserved = v.reserved ∧
  (lift tr h' v).fd_limit = v.fd_limit ∧ (lift tr h' v).clock = v.clock ∧
  (lift tr h' v).hist = h' ∧ (lift tr h' v).ch = reindex_ch tr v.ch ∧
  (lift tr h' v).env = (λn h nm. v.env n (tr h) nm)
Proof
  simp[lift_def, reindex_def]
QED

Theorem lift_upd[simp]:
  (lift tr h' v with listeners := L) = lift tr h' (v with listeners := L) ∧
  (lift tr h' v with chans := C) = lift tr h' (v with chans := C) ∧
  (lift tr h' v with open_fds := OF) = lift tr h' (v with open_fds := OF) ∧
  (lift tr h' v with reserved := R) = lift tr h' (v with reserved := R) ∧
  (lift tr h' v with <| listeners := L; chans := C |>) =
    lift tr h' (v with <| listeners := L; chans := C |>) ∧
  (lift tr h' v with <| chans := C; open_fds := OF |>) =
    lift tr h' (v with <| chans := C; open_fds := OF |>)
Proof
  simp[lift_def, reindex_def, honestL0WorldTheory.l0world_component_equality]
QED

Theorem lift_upd_lchan[simp]:
  upd_lchan j g (lift tr h' v) = lift tr h' (upd_lchan j g v)
Proof
  simp[upd_lchan_def]
QED

Theorem lift_reads[simp]:
  l0_chan_of (lift tr h' v) f = l0_chan_of v f ∧
  is_listener_fd (lift tr h' v) f = is_listener_fd v f ∧
  l0_used (lift tr h' v) = l0_used v ∧
  lowest_fd (lift tr h' v) = lowest_fd v ∧
  l0_alloc (lift tr h' v) = l0_alloc v
Proof
  simp[l0_chan_of_def, is_listener_fd_def, l0_used_def, lowest_fd_def, l0_alloc_def]
QED

(* The world's choices, read at the current history *)
Theorem lift_ch[simp]:
  tr h' = v.hist ⇒
  (lift tr h' v).ch.transient h' = v.ch.transient v.hist ∧
  (lift tr h' v).ch.errno_of h' = v.ch.errno_of v.hist ∧
  (lift tr h' v).ch.misuse h' = v.ch.misuse v.hist ∧
  (lift tr h' v).ch.listen_fails h' = v.ch.listen_fails v.hist ∧
  (lift tr h' v).ch.accept_aborts h' = v.ch.accept_aborts v.hist ∧
  (lift tr h' v).ch.emfile_drops h' = v.ch.emfile_drops v.hist ∧
  (lift tr h' v).ch.pending_err h' = v.ch.pending_err v.hist ∧
  (lift tr h' v).ch.short j h' = v.ch.short j v.hist ∧
  (lift tr h' v).ch.broken_recv h' = v.ch.broken_recv v.hist ∧
  (lift tr h' v).ch.send_pending h' = v.ch.send_pending v.hist ∧
  (lift tr h' v).ch.broken_send h' = v.ch.broken_send v.hist ∧
  (lift tr h' v).ch.takes j h' = v.ch.takes j v.hist ∧
  (lift tr h' v).ch.shut_err h' = v.ch.shut_err v.hist ∧
  (lift tr h' v).ch.connect_now h' = v.ch.connect_now v.hist ∧
  (lift tr h' v).ch.close_intr h' = v.ch.close_intr v.hist
Proof
  simp[reindex_ch_def]
QED

Theorem lift_fail:
  tr h' = v.hist ⇒
  fail (lift tr h' v) e = fail v e ∧ not_chan (lift tr h' v) f = not_chan v f ∧
  enc_err_val (lift tr h' v) e x = enc_err_val v e x ∧
  enc_listen_fail (lift tr h' v) ke = enc_listen_fail v ke
Proof
  strip_tac >> PairCases_on ‘ke’ >>
  fs[fail_def, not_chan_def, enc_err_val_def, enc_listen_fail_def, reindex_ch_def]
QED

Theorem lift_FOLDL_break[local]:
  ∀q u. FOLDL (λw j. upd_lchan j (break_lchan E_CONNRESET F) w) (lift tr h' u) q =
        lift tr h' (FOLDL (λw j. upd_lchan j (break_lchan E_CONNRESET F) w) u q)
Proof
  Induct >> simp[]
QED

Theorem lift_close_fd:
  close_fd f (lift tr h' v) = lift tr h' (close_fd f v)
Proof
  simp[close_fd_def] >> every_case_tac >> simp[lift_FOLDL_break]
QED

(* MAIN: each operation *)
Theorem lift_ops:
  tr h' = w.hist ⇒
  l0_listen p (lift tr h' w) = (λ(r, v). (r, lift tr h' v)) (l0_listen p w) ∧
  l0_accept l (lift tr h' w) = (λ(r, v). (r, lift tr h' v)) (l0_accept l w) ∧
  l0_recv f n (lift tr h' w) = (λ(r, d, v). (r, d, lift tr h' v)) (l0_recv f n w) ∧
  l0_send f bs (lift tr h' w) = (λ(r, v). (r, lift tr h' v)) (l0_send f bs w) ∧
  l0_shutdown f (lift tr h' w) = (λ(r, v). (r, lift tr h' v)) (l0_shutdown f w) ∧
  l0_connect p (lift tr h' w) = (λ(r, x, v). (r, x, lift tr h' v)) (l0_connect p w) ∧
  l0_connerr f (lift tr h' w) = (λ(r, v). (r, lift tr h' v)) (l0_connerr f w) ∧
  l0_close f (lift tr h' w) = (λ(r, v). (r, lift tr h' v)) (l0_close f w)
Proof
  strip_tac >>
  ‘∀e f x ke. fail (lift tr h' w) e = fail w e ∧ not_chan (lift tr h' w) f = not_chan w f’
    by (rpt gen_tac >> drule lift_fail >> simp[]) >>
  rpt conj_tac
  >- (fs[l0_listen_def, reindex_ch_def] >> every_case_tac >> fs[])
  >- (fs[l0_accept_def, reindex_ch_def] >> every_case_tac >> fs[])
  >- (fs[l0_recv_def, reindex_ch_def] >> every_case_tac >> fs[])
  >- (fs[l0_send_def, reindex_ch_def] >> every_case_tac >> fs[])
  >- (fs[l0_shutdown_def, reindex_ch_def] >> every_case_tac >> fs[])
  >- (fs[l0_connect_def, reindex_ch_def] >> every_case_tac >> fs[])
  >- (fs[l0_connerr_def, reindex_ch_def] >> every_case_tac >> fs[])
  >> fs[l0_close_def, lift_close_fd, reindex_ch_def] >> every_case_tac >> fs[lift_close_fd]
QED

Theorem lift_tick:
  tr h' = w.hist ⇒ l0_tick nm (lift tr h' w) = lift tr h' (l0_tick nm w)
Proof
  strip_tac >> simp[lift_def, reindex_def] >>
  qspecl_then [‘λn h nm. w.env n (tr h) nm’, ‘w’, ‘h'’, ‘nm’, ‘reindex_ch tr w.ch’]
    mp_tac (Q.GENL [‘e’, ‘w’, ‘h’, ‘nm’, ‘c’] tick_with) >>
  simp[] >> disch_then kall_tac >>
  simp[honestL0WorldTheory.l0world_component_equality, tick_fields]
QED

Theorem lift_ticks:
  ∀k w. tr h' = w.hist ⇒ l0_ticks nm k (lift tr h' w) = lift tr h' (l0_ticks nm k w)
Proof
  Induct >> rw[l0_ticks_def] >> simp[lift_tick] >>
  first_x_assum irule >> simp[tick_fields]
QED

Theorem sim_lift:
  tr h' = w.hist ⇒ sim tr (lift tr h' w) w
Proof
  rw[sim_def, lift_def] >> metis_tac[]
QED

Definition lift_res_def:
  lift_res tr h' (SOME (FFIreturn b v)) = SOME (FFIreturn b (lift tr h' v)) ∧
  lift_res tr h' r = r
End

(* MAIN: a call in the reindexed world is the call in w, lifted *)
Theorem lift_call:
  tr h' = w.hist ⇒
  l0_call n conf bytes (lift tr h' w) = lift_res tr h' (l0_call n conf bytes w)
Proof
  strip_tac >> drule lift_ops >> strip_tac >>
  drule sim_lift >> strip_tac >>
  drule_then (fn th => simp[th]) sim_wait >>
  ‘∀fes. poll_out (lift tr h' w) fes = poll_out w fes’ by metis_tac[sim_poll_out] >>
  ‘∀k. sim tr (l0_ticks «sys_poll» k (lift tr h' w)) (l0_ticks «sys_poll» k w)’
    by metis_tac[sim_ticks] >>
  ‘∀k fes. poll_out (l0_ticks «sys_poll» k (lift tr h' w)) fes =
           poll_out (l0_ticks «sys_poll» k w) fes’ by metis_tac[sim_poll_out] >>
  ‘∀e x ke. enc_err_val (lift tr h' w) e x = enc_err_val w e x ∧
            enc_listen_fail (lift tr h' w) ke = enc_listen_fail w ke ∧
            fail (lift tr h' w) e = fail w e’
    by (rpt gen_tac >> drule lift_fail >> simp[]) >>
  simp[l0_call_def] >>
  rpt (IF_CASES_TAC >> simp[lift_res_def]) >>
  TRY (rpt (pairarg_tac >> gvs[lift_res_def]) >> NO_TAC)
  >> TRY (‘∀fes. l0_wait fes (lift tr h' w) = l0_wait fes w’ by metis_tac[sim_wait] >>
          simp[reindex_ch_def] >> every_case_tac >> fs[lift_res_def, lift_ticks] >> NO_TAC)
  >> TRY (Cases_on ‘l0_listen (w22n conf) w’ >> simp[] >>
          rename1 ‘(r0, _)’ >> Cases_on ‘r0’ >> simp[lift_res_def] >> NO_TAC)
  >> TRY (Cases_on ‘l0_connerr (bytes_fd conf) w’ >> simp[] >>
          rename1 ‘(r0, _)’ >> Cases_on ‘r0’ >> simp[lift_res_def] >>
          rename1 ‘INL o0’ >> Cases_on ‘o0’ >> simp[lift_res_def] >> NO_TAC)
  >> ‘∃a b c. l0_connect (w22n conf) w = (a, b, c)’ by metis_tac[pairTheory.PAIR]
  >> simp[] >> Cases_on ‘a’ >> simp[lift_res_def]
QED

Theorem tick_hist_eq[local]:
  (l0_tick nm w).hist = w.hist
Proof
  simp[l0_tick_def] >>
  ‘∀as w0. (FOLDL l0_deliver w0 as).hist = w0.hist’
    by (Induct >> simp[] >> rpt gen_tac >> Cases_on ‘h’ >>
        rw[l0_deliver_def, upd_lchan_def] >> every_case_tac >> simp[]) >>
  simp[]
QED

(* MAIN: an FFI call in the reindexed world is the call in w, lifted; the
   reindexing must map the new history to the old one *)
Theorem lift_ffi_fn:
  tr h' = w.hist ∧ tr (h' ++ [(n, conf, bytes)]) = w.hist ++ [(n, conf, bytes)] ⇒
  l0_ffi_fn n conf bytes (lift tr h' w) =
  lift_res tr (h' ++ [(n, conf, bytes)]) (l0_ffi_fn n conf bytes w)
Proof
  strip_tac >> simp[l0_ffi_fn_def] >>
  drule_then (fn th => simp[th]) lift_tick >>
  ‘tr h' = (l0_tick n w).hist’ by simp[tick_hist_eq] >>
  drule_then (fn th => simp[th]) lift_call >>
  Cases_on ‘l0_call n conf bytes (l0_tick n w)’ >> simp[lift_res_def] >>
  rename1 ‘SOME r’ >> Cases_on ‘r’ >> simp[lift_res_def, lift_def, reindex_def]
QED
