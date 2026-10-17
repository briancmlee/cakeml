(*
  Moonshot step 12: the proxy bridge's world facts (ep_ok, moonshotProxyGlue)
  for any process of an l0sys run, from the per-process invariant (pinv)
  that B2's system invariant carries along the run:
   - accepts_known (W4): an accept succeeds only on a listener, and every
     listener is one a successful listen of the trace returned;
   - opens_ok (W1), for events that do not get fd 0: an open's fd is the
     same in both vocabularies;
   - ops_live (W3): a send or recv succeeds only on an open fd, and an open
     fd other than 0 was opened since it was last closed.
  W2 (no open gets fd 0) is not here: it waits on the launch contract.
*)
Theory moonshotWorldFacts
Ancestors
  moonshotProxyGlue proxyL0StmtsCopy honestEchoL0SpecCopy l0sysEpisodesEcho
  honestL0World honestL0WorldProps honestL0Rely l0sys l0sysEpisodes l0sysInv l0sysInvCall
  l0sysStep l0sysRun l0sysProj honestL0 Marshalling
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* An induction over process k's calls in a run *)

Theorem run_calls_induct:
  sys_init ps s0 ∧ sys_steps s0 rs ss ∧ k < LENGTH ps ∧ Q [] ∧
  (∀evs w cs nm conf bytes out w1.
     Q evs ∧ pinv evs w cs ∧ l0_rely w ∧ small_ch w.ch ∧ poll_may_return nm conf bytes w ∧
     l0_call nm (unblock nm conf) bytes w = SOME (FFIreturn out w1) ⇒
     Q (evs ++ [IO_event (ExtCall nm) conf (ZIP (bytes, out))])) ⇒
  Q (proc_events k rs)
Proof
  strip_tac >> drule sys_steps_EL >> strip_tac >>
  ‘sinv [] s0 (K [])’
    by (irule sinv_init >> qexists_tac ‘ps’ >> rw[] >> irule l0_rely_small_ch >>
        fs[sys_init_def, LET_THM]) >>
  ‘∀t. t ≤ LENGTH rs ⇒ sinv (TAKE t rs) (EL t ss) (ghost ss rs (K []) t)’
    by (match_mp_tac sinv_run >> simp[]) >>
  ‘∀d. 0 + d ≤ LENGTH rs ⇒
       hist_inv (EL 0 ss) (ghost ss rs (K []) 0) (EL (0 + d) ss) (ghost ss rs (K []) (0 + d))’
    by (match_mp_tac hist_run >> simp[]) >>
  ‘EL 0 ss = s0’ by (Cases_on ‘ss’ >> fs[]) >>
  ‘∀t. t ≤ LENGTH rs ⇒ k < LENGTH (EL t ss).procs’
    by (rpt strip_tac >> first_x_assum (qspec_then ‘t’ mp_tac) >> simp[hist_inv_def] >>
        fs[sys_init_def]) >>
  ‘∀t. t ≤ LENGTH rs ⇒ Q (proc_events k (TAKE t rs))’ suffices_by
    (disch_then (qspec_then ‘LENGTH rs’ mp_tac) >> simp[]) >>
  Induct >- simp[proc_events_def] >>
  strip_tac >> ‘t < LENGTH rs’ by simp[] >> fs[] >>
  simp[ADD1, TAKE_SUC_SNOC, proc_events_SNOC] >>
  Cases_on ‘EL t rs’ >> simp[] >>
  rename1 ‘Call k0 nm conf bytes out’ >> rw[] >>
  ‘sys_step (EL t ss) (Call k nm conf bytes out) (EL (t + 1) ss)’ by metis_tac[] >>
  ‘sinv (TAKE t rs) (EL t ss) (ghost ss rs (K []) t) ∧ k < LENGTH (EL t ss).procs’ by simp[] >>
  fs[sys_step_def, sinv_def, pk_def, LET_THM] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* W4: accepts_known *)

Theorem accepts_known_SNOC:
  accepts_known (evs ++ [ev]) ⇔
  accepts_known evs ∧ ∀f l. ev_new ev = SOME (f, INR l) ⇒ ALOOKUP (lsn evs) l ≠ NONE
Proof
  simp[accepts_known_def] >> eq_tac >> rpt strip_tac
  >- (first_x_assum (qspecl_then [‘p’, ‘f’, ‘l’] mp_tac) >> simp[EL_APPEND1, TAKE_APPEND1])
  >- (first_x_assum (qspecl_then [‘LENGTH evs’, ‘f’, ‘l’] mp_tac) >>
      simp[EL_APPEND2, TAKE_LENGTH_APPEND]) >>
  Cases_on ‘p < LENGTH evs’
  >- (first_x_assum (qspecl_then [‘p’, ‘f’, ‘l’] mp_tac) >> fs[EL_APPEND1, TAKE_APPEND1]) >>
  ‘p = LENGTH evs’ by fs[] >> rveq >> fs[EL_APPEND2, TAKE_LENGTH_APPEND] >> metis_tac[]
QED

(* An accept succeeds only on a listener, and pinv knows each listener's
   listen *)
Theorem call_accept_known:
  pinv evs w cs ∧ l0_rely w ∧
  l0_call nm (unblock nm conf) bytes w = SOME (FFIreturn out w1) ∧
  ev_new (IO_event (ExtCall nm) conf (ZIP (bytes, out))) = SOME (f, INR l) ⇒
  ALOOKUP (lsn evs) l ≠ NONE
Proof
  strip_tac >> drule ev_new_INR >> strip_tac >> rveq >> fs[unblock_other] >>
  drule_all accept_new_chan >> strip_tac >>
  ‘MEM (l1, p, pop_chan w l :: q) (FILTER (λ(l', p, q). l' = l) w.listeners)’ by simp[] >>
  pop_assum mp_tac >> rewrite_tac[MEM_FILTER] >> pairarg_tac >> fs[] >> strip_tac >> rveq >>
  qpat_x_assum ‘pinv _ _ _’ mp_tac >> rewrite_tac[pinv_def] >> strip_tac >>
  first_x_assum drule >> simp[]
QED

(* W4, for any process of an l0sys run *)
Theorem l0sys_accepts_known:
  sys_init ps s0 ∧ sys_steps s0 rs ss ∧ k < LENGTH ps ⇒ accepts_known (proc_events k rs)
Proof
  strip_tac >> irule run_calls_induct >> simp[] >> rpt conj_tac >>
  TRY (simp[accepts_known_def] >> NO_TAC) >>
  TRY (qexistsl_tac [‘ps’, ‘s0’, ‘ss’] >> simp[] >> NO_TAC) >>
  rpt strip_tac >> simp[accepts_known_SNOC] >> rpt strip_tac >>
  metis_tac[call_accept_known]
QED

(*---------------------------------------------------------------------------*)
(* W1: opens_ok, for events that do not get fd 0 *)

(* A connect's answer always decodes *)
Theorem connect_dec_res:
  l0_rely w ∧ l0_call «sys_connect» conf bytes w = SOME (FFIreturn out w1) ⇒
  dec_res out ≠ NONE
Proof
  strip_tac >>
  ‘∀e v. v < 256 ** 8 ⇒ dec_res (enc_err_val w e v) ≠ NONE’
    by (rpt strip_tac >> drule_all enc_err_val_dec >> disch_then (qspec_then ‘e’ strip_assume_tac) >>
        fs[]) >>
  gvs[l0_call_def, AllCaseEqs()]
  >- simp[dec_res_def, enc_res_def, LENGTH_n2w8] >>
  drule l0_connect_cases >> simp[LET_THM] >> strip_tac >> gvs[] >>
  first_x_assum irule >> qspec_then ‘f’ assume_tac w2n_lt >> fs[]
QED

Theorem call_opens_ok:
  l0_rely w ∧ l0_call nm (unblock nm conf) bytes w = SOME (FFIreturn out w1) ∧
  (∀r. ev_new (IO_event (ExtCall nm) conf (ZIP (bytes, out))) ≠ SOME (0w, r)) ⇒
  opens_ok (IO_event (ExtCall nm) conf (ZIP (bytes, out)))
Proof
  strip_tac >>
  ‘LENGTH out = LENGTH bytes’ by metis_tac[l0_call_length] >>
  ‘MAP SND (ZIP (bytes, out)) = out’ by simp[MAP_ZIP] >>
  ‘nm = «sys_connect» ⇒ dec_res out ≠ NONE’
    by (strip_tac >> rveq >> fs[unblock_other] >> metis_tac[connect_dec_res]) >>
  ‘∀r. dec_res out = SOME r ⇒
       13 ≤ LENGTH out ∧ DROP 1 out = TL out ∧ ∀n. r = Ok n ⇒ n = w82n (TAKE 8 (TL out))’
    by (rw[dec_res_def] >> Cases_on ‘out’ >> fs[]) >>
  fs[opens_ok_def, l0_event_opened_def, l0_event_accepted_def, l0_event_connected_def,
     l0_ev_res_def, ev_new_def, res_val_def] >>
  rw[] >> every_case_tac >> fs[] >> res_tac >> fs[] >> rfs[]
QED

(* W1, for any process of an l0sys run: with W2 (no open gets fd 0) it is
   ep_ok's EVERY opens_ok *)
Theorem l0sys_opens_ok:
  sys_init ps s0 ∧ sys_steps s0 rs ss ∧ k < LENGTH ps ⇒
  EVERY (λev. (∀r. ev_new ev ≠ SOME (0w, r)) ⇒ opens_ok ev) (proc_events k rs)
Proof
  strip_tac >> irule run_calls_induct >> simp[] >> rpt conj_tac >>
  TRY (qexistsl_tac [‘ps’, ‘s0’, ‘ss’] >> simp[] >> NO_TAC) >>
  rpt strip_tac >> simp[] >> rpt strip_tac >> irule call_opens_ok >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* W3: ops_live.  Every open fd other than 0 is live in the trace (fds_live),
   and a send or recv succeeds only on an open fd *)

Theorem live_after_SNOC:
  ∀evs b. live_after f b (evs ++ [ev]) =
          if (∃h. ev_new ev = SOME (f, h)) then T
          else if l0_event_closed ev = SOME f then F else live_after f b evs
Proof
  Induct >> rw[live_after_def]
QED

Definition fds_live_def:
  fds_live evs (w : l0world) ⇔
    ∀f c. ALOOKUP w.open_fds f = SOME c ∧ f ≠ 0w ⇒ live_after f T evs
End

Theorem fds_live_deliver:
  ∀as w. fds_live evs w ⇒ fds_live evs (FOLDL l0_deliver w as)
Proof
  ‘∀a w. (l0_deliver w a).open_fds = w.open_fds’
    by (Cases >> rw[l0_deliver_def, upd_lchan_def] >> every_case_tac >> simp[]) >>
  ‘∀as w. (FOLDL l0_deliver w as).open_fds = w.open_fds’ by (Induct >> fs[]) >>
  simp[fds_live_def]
QED

Theorem upd_lchan_open_fds[simp]:
  (upd_lchan j g w).open_fds = w.open_fds
Proof
  simp[upd_lchan_def]
QED

Theorem close_fd_open_fds_sub:
  ALOOKUP (close_fd g w).open_fds f = SOME c ⇒ ALOOKUP w.open_fds f = SOME c
Proof
  ‘∀h q w. (FOLDL (λw j. upd_lchan j h w) w q).open_fds = w.open_fds’
    by (gen_tac >> Induct >> fs[]) >>
  rw[close_fd_def] >> every_case_tac >> fs[ALOOKUP_ADELKEY] >> rw[] >> fs[] >>
  qpat_x_assum ‘ALOOKUP _ _ = _’ mp_tac >>
  qpat_x_assum ‘∀h q w. _’ (fn th => rewrite_tac[th]) >> simp[]
QED

Theorem l0_ticks_open_fds:
  ∀k w. (l0_ticks nm k w).open_fds = w.open_fds
Proof
  ‘∀a w. (l0_deliver w a).open_fds = w.open_fds’
    by (Cases >> rw[l0_deliver_def, upd_lchan_def] >> every_case_tac >> simp[]) >>
  ‘∀as w. (FOLDL l0_deliver w as).open_fds = w.open_fds’ by (Induct >> fs[]) >>
  Induct >> fs[l0_ticks_def, l0_tick_def]
QED

(* A call other than accept, connect or close leaves the open fds *)
Theorem call_open_fds_same:
  nm ≠ «sys_accept» ∧ nm ≠ «sys_connect» ∧ nm ≠ «sys_close» ∧
  l0_call nm conf bytes w = SOME (FFIreturn out w1) ⇒ w1.open_fds = w.open_fds
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs(), l0_ticks_open_fds] >> rpt (pairarg_tac >> gvs[]) >>
  TRY (gvs[l0_listen_def, AllCaseEqs()] >> NO_TAC) >>
  TRY (drule l0_recv_cases >> strip_tac >> gvs[] >> NO_TAC) >>
  TRY (drule l0_send_cases >> strip_tac >> gvs[] >> NO_TAC) >>
  TRY (gvs[l0_shutdown_def, AllCaseEqs()] >> NO_TAC) >>
  gvs[l0_connerr_def, AllCaseEqs()]
QED

(* How one call changes the open fds: a closed fd is gone, and any other
   open fd was open before or is the event's new one *)
Theorem call_fds:
  pinv evs w cs ∧ l0_rely w ∧
  l0_call nm (unblock nm conf) bytes w = SOME (FFIreturn out w1) ⇒
  (∀g c. l0_event_closed (IO_event (ExtCall nm) conf (ZIP (bytes, out))) = SOME g ⇒
         ALOOKUP w1.open_fds g ≠ SOME c) ∧
  (∀f c. ALOOKUP w1.open_fds f = SOME c ∧ f ≠ 0w ⇒
         ALOOKUP w.open_fds f = SOME c ∨
         ∃h. ev_new (IO_event (ExtCall nm) conf (ZIP (bytes, out))) = SOME (f, h))
Proof
  strip_tac >>
  ‘LENGTH out = LENGTH bytes’ by metis_tac[l0_call_length] >>
  ‘MAP SND (ZIP (bytes, out)) = out’ by simp[MAP_ZIP] >>
  ‘∀f c. ALOOKUP w.open_fds f = SOME c ⇒ c < LENGTH w.chans’
    by (rpt strip_tac >> imp_res_tac ALOOKUP_MEM >> fs[pinv_def, EVERY_MEM] >>
        res_tac >> fs[]) >>
  Cases_on ‘nm ≠ «sys_accept» ∧ nm ≠ «sys_connect» ∧ nm ≠ «sys_close»’
  >- (‘w1.open_fds = w.open_fds’
        by (irule call_open_fds_same >> fs[] >> metis_tac[]) >>
      simp[l0_event_closed_def] >> rw[] >> fs[]) >>
  fs[unblock_other] >> rveq
  >- ((* accept *)
      simp[l0_event_closed_def] >> fs[unblock_other] >>
      qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def] >> rw[] >>
      pairarg_tac >> fs[] >> rveq >> drule l0_accept_cases >> strip_tac >> gvs[] >>
      rw[] >> fs[ALOOKUP_def] >> every_case_tac >> fs[] >> rveq >>
      simp[ev_new_def] >>
      ‘enc_res (Ok (w2n f)) = enc_res (Ok (w2n f)) ++ []’ by simp[] >>
      pop_assum SUBST1_TAC >>
      ‘w2n f < 256 ** 8’ by (qspec_then ‘f’ assume_tac w2n_lt >> fs[]) >>
      simp[dec_res_ok])
  >- ((* connect *)
      simp[l0_event_closed_def] >> fs[unblock_other] >>
      qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def] >> rw[] >>
      every_case_tac >> fs[] >> rveq >> drule l0_connect_cases >> simp[LET_THM] >>
      strip_tac >> gvs[] >> rw[] >> fs[ALOOKUP_def, upd_lchan_def] >> every_case_tac >>
      fs[] >> rveq >> simp[ev_new_def] >> fs[fail_def] >>
      rename1 ‘l0_alloc w = SOME fd’ >>
      ‘w2n fd < 256 ** 8’ by (qspec_then ‘fd’ assume_tac w2n_lt >> fs[]) >>
      FIRST [
        ‘enc_res (Ok (w2n fd)) = enc_res (Ok (w2n fd)) ++ []’ by simp[] >>
        pop_assum SUBST1_TAC >> simp[dec_res_ok] >> NO_TAC,
        rename1 ‘enc_err_val w ee (w2n fd)’ >>
        drule_all enc_err_val_dec >> disch_then (qspec_then ‘ee’ strip_assume_tac) >>
        simp[] >> fs[w2n_eq_0]]) >>
  (* close *)
  ‘∀e v. dec_res (enc_res (fail w e)) ≠ SOME (Ok v)’
    by (rpt gen_tac >> ‘enc_res (fail w e) = enc_res (fail w e) ++ []’ by simp[] >>
        pop_assum SUBST1_TAC >> simp[dec_res_fail]) >>
  ‘∀g c. ALOOKUP (close_fd g w).open_fds g ≠ SOME c’
    by (rpt gen_tac >> Cases_on ‘l0_chan_of w g’
        >- (strip_tac >> imp_res_tac close_fd_open_fds_sub >> res_tac >>
            fs[l0_chan_of_def]) >>
        simp[close_fd_def, ALOOKUP_ADELKEY]) >>
  fs[unblock_other] >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def] >> rw[] >>
  pairarg_tac >> fs[] >> rveq >> fs[l0_close_def, AllCaseEqs()] >> rveq >>
  fs[l0_event_closed_def, l0_ev_res_def] >> rw[] >>
  TRY (imp_res_tac close_fd_open_fds_sub >> fs[] >> NO_TAC) >>
  every_case_tac >> fs[] >> rfs[]
QED

Theorem fds_live_call:
  fds_live evs w ∧ pinv evs w cs ∧ l0_rely w ∧
  l0_call nm (unblock nm conf) bytes w = SOME (FFIreturn out w1) ⇒
  fds_live (evs ++ [IO_event (ExtCall nm) conf (ZIP (bytes, out))]) (w1 with <| clock := n; hist := h |>)
Proof
  strip_tac >> drule_all call_fds >> strip_tac >>
  simp[fds_live_def, live_after_SNOC] >> rpt gen_tac >> strip_tac >>
  Cases_on ‘∃h. ev_new (IO_event (ExtCall nm) conf (ZIP (bytes, out))) = SOME (f, h)’ >>
  fs[] >> conj_tac >- (strip_tac >> res_tac) >>
  ‘ALOOKUP w.open_fds f = SOME c’ by metis_tac[] >> fs[fds_live_def] >> metis_tac[]
QED

(* A send or recv that moved bytes was on an open fd *)
Theorem call_op_open:
  l0_rely w ∧ l0_call nm (unblock nm conf) bytes w = SOME (FFIreturn out w1) ∧
  (ev_sent (IO_event (ExtCall nm) conf (ZIP (bytes, out))) = SOME (f, bs) ∨
   ev_recvd (IO_event (ExtCall nm) conf (ZIP (bytes, out))) = SOME (f, bs)) ∧ bs ≠ [] ⇒
  ∃c. ALOOKUP w.open_fds f = SOME c
Proof
  strip_tac >>
  ‘LENGTH out = LENGTH bytes’ by metis_tac[l0_call_length] >>
  ‘MAP SND (ZIP (bytes, out)) = out’ by simp[MAP_ZIP] >>
  ‘∀e v rest. dec_res (enc_res (fail w e) ++ rest) ≠ SOME (Ok v)’ by simp[dec_res_fail] >>
  fs[ev_sent_def, ev_recvd_def, AllCaseEqs()] >> rveq >> fs[unblock_other] >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def] >> rw[] >>
  pairarg_tac >> fs[] >> rveq
  >- (drule l0_send_cases >> strip_tac >> gvs[]
      >- (‘enc_res (fail w e) = enc_res (fail w e) ++ []’ by simp[] >> metis_tac[])
      >- (‘enc_res (fail w e) = enc_res (fail w e) ++ []’ by simp[] >> metis_tac[]) >>
      fs[l0_chan_of_def, AllCaseEqs()]) >>
  drule l0_recv_cases >> strip_tac >> gvs[] >>
  TRY (fs[] >> NO_TAC) >>
  TRY (qpat_x_assum ‘dec_res (enc_res (Ok 0) ++ _) = _’ mp_tac >> simp[dec_res_ok] >>
       NO_TAC) >>
  qexists_tac ‘j’ >> fs[l0_chan_of_def, AllCaseEqs()]
QED

Theorem ops_live_SNOC:
  ops_live (evs ++ [e]) ⇔
  ops_live evs ∧
  ∀f bs. (ev_sent e = SOME (f, bs) ∨ ev_recvd e = SOME (f, bs)) ∧ bs ≠ [] ∧ f ≠ 0w ⇒
         live_after f T evs
Proof
  simp[ops_live_def] >> eq_tac >> rpt strip_tac
  >- (first_x_assum (qspecl_then [‘pre’, ‘ev’, ‘post ++ [e]’, ‘f’, ‘bs’] mp_tac) >> simp[])
  >- (first_x_assum (qspecl_then [‘pre’, ‘ev’, ‘post ++ [e]’, ‘f’, ‘bs’] mp_tac) >> simp[])
  >- (first_x_assum (qspecl_then [‘evs’, ‘e’, ‘[]’, ‘f’, ‘bs’] mp_tac) >> simp[])
  >- (first_x_assum (qspecl_then [‘evs’, ‘e’, ‘[]’, ‘f’, ‘bs’] mp_tac) >> simp[]) >>
  Cases_on ‘post’ using SNOC_CASES >> fs[SNOC_APPEND] >> rveq >> fs[] >> metis_tac[]
QED

(* The induction over k's calls, with a world invariant Inv kept by arrivals
   and calls while k is alive *)
Theorem run_calls_induct_inv:
  sys_init ps s0 ∧ sys_steps s0 rs ss ∧ k < LENGTH ps ∧ Q [] ∧ Inv [] (EL k s0.procs) ∧
  (∀evs w as. Inv evs w ⇒ Inv evs (FOLDL l0_deliver w as)) ∧
  (∀evs w cs nm conf bytes out w1.
     Inv evs w ∧ pinv evs w cs ∧ l0_rely w ∧ small_ch w.ch ∧
     l0_call nm (unblock nm conf) bytes w = SOME (FFIreturn out w1) ⇒
     Inv (evs ++ [IO_event (ExtCall nm) conf (ZIP (bytes, out))])
       (w1 with <| clock := w.clock + 1; hist := w.hist ++ [(nm, conf, bytes)] |>)) ∧
  (∀evs w cs nm conf bytes out w1.
     Q evs ∧ Inv evs w ∧ pinv evs w cs ∧ l0_rely w ∧ small_ch w.ch ∧
     l0_call nm (unblock nm conf) bytes w = SOME (FFIreturn out w1) ⇒
     Q (evs ++ [IO_event (ExtCall nm) conf (ZIP (bytes, out))])) ⇒
  Q (proc_events k rs)
Proof
  strip_tac >> drule sys_steps_EL >> strip_tac >>
  ‘sinv [] s0 (K [])’
    by (irule sinv_init >> qexists_tac ‘ps’ >> rw[] >> irule l0_rely_small_ch >>
        fs[sys_init_def, LET_THM]) >>
  ‘∀t. t ≤ LENGTH rs ⇒ sinv (TAKE t rs) (EL t ss) (ghost ss rs (K []) t)’
    by (match_mp_tac sinv_run >> simp[]) >>
  ‘∀d. 0 + d ≤ LENGTH rs ⇒
       hist_inv (EL 0 ss) (ghost ss rs (K []) 0) (EL (0 + d) ss) (ghost ss rs (K []) (0 + d))’
    by (match_mp_tac hist_run >> simp[]) >>
  ‘EL 0 ss = s0’ by (Cases_on ‘ss’ >> fs[]) >>
  ‘∀t. t ≤ LENGTH rs ⇒ k < LENGTH (EL t ss).procs’
    by (rpt strip_tac >> first_x_assum (qspec_then ‘t’ mp_tac) >> simp[hist_inv_def] >>
        fs[sys_init_def]) >>
  ‘∀t. t ≤ LENGTH rs ⇒
       Q (proc_events k (TAKE t rs)) ∧
       ((EL t ss).alive k ⇒ Inv (proc_events k (TAKE t rs)) (EL k (EL t ss).procs))’
    suffices_by (disch_then (qspec_then ‘LENGTH rs’ mp_tac) >> simp[]) >>
  Induct >- simp[proc_events_def] >>
  strip_tac >> ‘t < LENGTH rs’ by simp[] >> fs[] >>
  ‘∃as. kstep k (EL t ss) (EL t rs) (EL (t + 1) ss) as’
    by (irule kstep_exists >> simp[]) >>
  ‘sinv (TAKE t rs) (EL t ss) (ghost ss rs (K []) t) ∧ k < LENGTH (EL t ss).procs’ by simp[] >>
  qabbrev_tac ‘wk = EL k (EL t ss).procs’ >>
  ‘pinv (proc_events k (TAKE t rs)) wk (ghost ss rs (K []) t k) ∧ l0_rely wk ∧ small_ch wk.ch’
    by fs[sinv_def, pk_def, Abbr ‘wk’] >>
  simp[ADD1, TAKE_SUC_SNOC, proc_events_SNOC] >>
  qpat_x_assum ‘kstep _ _ _ _ _’ mp_tac >> Cases_on ‘EL t rs’ >> simp[kstep_def] >>
  TRY (rename1 ‘Call k0 nm conf bytes out’ >> Cases_on ‘k0 = k’) >>
  TRY (rename1 ‘Exit k0’ >> Cases_on ‘k0 = k’) >>
  rw[] >> fs[] >> metis_tac[]
QED

(* W3, for any process of an l0sys run *)
Theorem l0sys_ops_live:
  sys_init ps s0 ∧ sys_steps s0 rs ss ∧ k < LENGTH ps ⇒ ops_live (proc_events k rs)
Proof
  strip_tac >>
  qspecl_then [‘ps’, ‘s0’, ‘rs’, ‘ss’, ‘k’, ‘ops_live’, ‘fds_live’] mp_tac
    (Q.GENL [‘ps’, ‘s0’, ‘rs’, ‘ss’, ‘k’, ‘Q’, ‘Inv’] run_calls_induct_inv) >>
  simp[] >> disch_then irule >> rpt conj_tac >>
  TRY (simp[ops_live_def] >> NO_TAC) >>
  TRY (fs[fds_live_def, sys_init_def, LET_THM] >> NO_TAC) >>
  TRY (metis_tac[fds_live_deliver] >> NO_TAC) >>
  TRY (rpt strip_tac >> irule fds_live_call >> metis_tac[] >> NO_TAC) >>
  rpt strip_tac >> simp[ops_live_SNOC] >> rpt strip_tac >>
  ‘∃c. ALOOKUP w.open_fds f = SOME c’ by (irule call_op_open >> metis_tac[]) >>
  fs[fds_live_def] >> metis_tac[]
QED

(* ep_ok for any process of an l0sys run, given W2 *)
Theorem l0sys_ep_ok:
  sys_init ps s0 ∧ sys_steps s0 rs ss ∧ k < LENGTH ps ∧
  EVERY (λev. ∀r. ev_new ev ≠ SOME (0w, r)) (proc_events k rs) ⇒
  ep_ok (proc_events k rs)
Proof
  strip_tac >> simp[ep_ok_def] >> rpt conj_tac
  >- (drule_all l0sys_opens_ok >> strip_tac >> fs[EVERY_MEM] >> metis_tac[])
  >- (drule_all l0sys_ops_live >> simp[])
  >- (drule_all l0sys_accepts_known >> simp[])
QED
