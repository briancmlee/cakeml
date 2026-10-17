(*
  L3-09 (S3), D32 step 3b: an open fd keeps its channel until a close call
  on it.  Only close removes an fd from the fd table; accept, connect and
  listen allocate the lowest fd not in use [P 2.6], which is never an open
  one; steps of time leave the fd table alone and only add channels.

  MAIN: world_at_chan_keep.
*)
Theory honestL1BChanKeep
Ancestors
  honestL1BChan honestL1BStmts honestL1PFRound honestL1Model honestL0Part honestL0WorldInv
  honestL0WorldProps honestL0Rely honestL0World honestL0
Libs
  preamble

Theorem chan_of_deliver[local]:
  l0_chan_of w f = SOME c ⇒ l0_chan_of (l0_deliver w a) f = SOME c
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def, l0_chan_of_def, upd_lchan_def] >>
  every_case_tac >> gvs[]
QED

Theorem chan_of_tick:
  l0_chan_of w f = SOME c ⇒ l0_chan_of (l0_tick nm w) f = SOME c
Proof
  rw[l0_tick_def] >>
  ‘∀as w. l0_chan_of w f = SOME c ⇒ l0_chan_of (FOLDL l0_deliver w as) f = SOME c’
    by (Induct >> simp[] >> metis_tac[chan_of_deliver]) >>
  first_x_assum irule >> fs[l0_chan_of_def]
QED

Theorem chan_of_ticks:
  ∀k w. l0_chan_of w f = SOME c ⇒ l0_chan_of (l0_ticks nm k w) f = SOME c
Proof
  Induct >> simp[l0_ticks_def] >> metis_tac[chan_of_tick]
QED

Theorem chan_of_hist[simp]:
  l0_chan_of (w with hist := hh) f = l0_chan_of w f
Proof
  simp[l0_chan_of_def]
QED

Theorem FOLDL_break_fields[local]:
  ∀q w. (FOLDL (λw' j. w' with chans := LUPDATE (break_lchan e kp (EL j w'.chans)) j w'.chans)
                w q).open_fds = w.open_fds ∧
        LENGTH (FOLDL (λw' j. w' with chans := LUPDATE (break_lchan e kp (EL j w'.chans)) j w'.chans)
                w q).chans = LENGTH w.chans
Proof
  Induct >> simp[]
QED

Theorem lowest_not_open[local]:
  fds_lt w ∧ w.fd_limit ≤ 2 ** 31 ⇒ ALOOKUP w.open_fds (lowest_fd w) = NONE
Proof
  strip_tac >>
  ‘¬MEM (lowest_fd w) (l0_used w)’
    by (irule lowest_fd_free_lim >> fs[fds_lt_def]) >>
  fs[l0_used_def, ALOOKUP_NONE]
QED

Theorem FOLDL_deliver_fd_limit[local]:
  ∀as w. (FOLDL l0_deliver w as).fd_limit = w.fd_limit
Proof
  Induct >> simp[]
QED

Theorem FOLDL_step_NONE[local]:
  ∀cs. FOLDL l0_step NONE cs = NONE
Proof
  Induct >> simp[l0_step_def]
QED

Theorem l0_call_chan_keep:
  l0_call n conf bytes w = SOME (FFIreturn out w') ∧ l0_chan_of w f = SOME c ∧
  fds_lt w ∧ w.fd_limit ≤ 2 ** 31 ∧
  ¬(n = «sys_close» ∧ LENGTH conf = 8 ∧ bytes_fd conf = f) ⇒
  l0_chan_of w' f = SOME c
Proof
  strip_tac >> drule_all lowest_not_open >> strip_tac >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >>
  simp[l0_call_def] >> rw[] >> gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  TRY (irule chan_of_ticks >> simp[] >> NO_TAC) >>
  gvs[l0_send_def, l0_recv_def, l0_connerr_def, l0_shutdown_def, l0_close_def,
      close_fd_def, l0_accept_def, l0_listen_def, l0_connect_def, l0_alloc_def,
      AllCaseEqs(), fail_def, upd_lchan_def, l0_chan_of_def] >>
  rpt (pairarg_tac >> gvs[AllCaseEqs()]) >> rw[] >>
  TRY (simp[alistTheory.ALOOKUP_ADELKEY] >> NO_TAC) >>
  TRY (simp[FOLDL_break_fields] >> NO_TAC) >>
  metis_tac[optionTheory.NOT_SOME_NONE]
QED

(* One step of the replay keeps winv and f's channel *)
Theorem step_chan_keep:
  l0_step (SOME w) (n, conf, bytes) = SOME w' ∧ winv w ∧ l0_chan_of w f = SOME c ∧
  n ≠ «sys_connect» ∧ ¬(n = «sys_close» ∧ LENGTH conf = 8 ∧ bytes_fd conf = f) ⇒
  winv w' ∧ l0_chan_of w' f = SOME c
Proof
  rw[l0_step_def, AllCaseEqs()] >> rename1 ‘FFIreturn out1 w'’ >>
  ‘l0_do_buf n conf bytes w = SOME (out1, w', IO_event (ExtCall n) conf (ZIP (bytes, out1)))’
    by simp[l0_do_buf_def]
  >- (drule_all winv_do_buf >> simp[]) >>
  fs[l0_ffi_fn_def, AllCaseEqs()] >> gvs[] >>
  ‘l0_chan_of (l0_tick n w) f = SOME c’ by simp[chan_of_tick] >>
  irule l0_call_chan_keep >> simp[] >>
  qexistsl_tac [‘bytes’, ‘conf’, ‘n’, ‘out1’] >> simp[] >>
  fs[winv_def, l0_rely_def] >>
  ‘(l0_tick n w).fd_limit = w.fd_limit’ by simp[l0_tick_def, FOLDL_deliver_fd_limit] >>
  qexists_tac ‘l0_tick n w’ >> simp[]
QED

Theorem step_chan_keep_ev:
  l0_step (SOME w) (ev_lcall ev) = SOME w' ∧ winv w ∧ l0_chan_of w f = SOME c ∧
  FST (ev_lcall ev) ≠ «sys_connect» ∧ ¬l0_close_call f ev ⇒
  winv w' ∧ l0_chan_of w' f = SOME c
Proof
  Cases_on ‘ev’ >> rename1 ‘IO_event nm cf bs’ >>
  Cases_on ‘nm’ >> simp[ev_lcall_def, l0_close_call_def] >> strip_tac >>
  drule step_chan_keep >> disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >> simp[]
QED

(* MAIN: along a replay with no close call on f (and no connect) *)
Theorem replay_chan_keep:
  ∀B x y. FOLDL l0_step (SOME x) (MAP ev_lcall B) = SOME y ∧ winv x ∧
          l0_chan_of x f = SOME c ∧
          EVERY (λev. ¬l0_close_call f ev ∧ FST (ev_lcall ev) ≠ «sys_connect») B ⇒
          winv y ∧ l0_chan_of y f = SOME c
Proof
  Induct >- simp[] >> rpt gen_tac >> simp[] >>
  Cases_on ‘l0_step (SOME x) (ev_lcall h)’ >> simp[FOLDL_step_NONE] >> strip_tac >>
  first_x_assum irule >> simp[] >> qexists_tac ‘x'’ >> simp[] >>
  irule step_chan_keep_ev >> metis_tac[]
QED
