(*
  One round of the prefetching L1, seen from one fd f (a lemma layer for
  R1-live, design/36 §6): if f's channel has input pending and L1 wants
  input on f, the round polls f; a poll that is not retried makes L1 recv
  on f; a recv that is not retried is logged.

  Calls are read off the round's IO events, with their observed results,
  as [F1] (D11′) speaks of them.  The world invariant winv collects what a
  round needs of the L0 world: the rely, well-formed channels (l0wf), no
  connect in progress (L1 never connects), fds below the limit, and a
  pending error only on a broken channel.
*)
Theory honestL1PFRound
Ancestors
  honestL1PFInv honestL1PFRefine honestL1PFModel honestL1Steps honestL1Props honestL1Inv honestL1Model
  honestL0WorldInv honestL0WorldProps honestL0Rely honestL0World honestL0
  asyncCore asyncLevel1 asyncM3World ffi alist
Libs
  preamble

(* ------------------------------------------------------------------------
   Calls, as observed in the IO events
   ------------------------------------------------------------------------ *)

(* The fds a call involves: its fd, or every fd a poll lists *)
Definition call_fds_def:
  call_fds (nm : mlstring) (conf : word8 list) =
    if nm = «sys_poll» then MAP FST (poll_entries (DROP 1 conf))
    else [bytes_fd (TAKE 8 conf)]
End

(* Event ev is a call nm involving fd f *)
Definition ev_on_def:
  ev_on nm f (IO_event n conf bs) ⇔ n = ExtCall nm ∧ MEM f (call_fds nm conf)
End

(* Event ev's result is one L1 retries (D11′): any failed poll; an
   l1_transient error of any other call *)
Definition retried_def:
  retried (IO_event n conf bs) ⇔
    case l0_res_of (MAP SND bs) of
    | Fail e _ => n = ExtCall «sys_poll» ∨ l1_transient e
    | Ok _ => F
End

(* A fetch log mentions f's input *)
Definition fetched_def:
  fetched f log ⇔ EXISTS (λx. x = FEof f ∨ x = FReset f ∨ ∃bs. x = FData f bs) log
End

Theorem call_fds_fd[simp]:
  nm ≠ «sys_poll» ⇒ call_fds nm (fd_bytes f) = [f]
Proof
  rw[call_fds_def] >> ‘LENGTH (fd_bytes f) = 8’ by simp[] >>
  metis_tac[TAKE_LENGTH_ID, fd_bytes_lfd]
QED

Theorem call_fds_poll:
  EVERY (λ(f, e). e < 256) fes ⇒ call_fds «sys_poll» (poll_conf fes) = MAP FST fes
Proof
  rw[call_fds_def, poll_conf_def, poll_entries_conf]
QED

(* ------------------------------------------------------------------------
   The world invariant
   ------------------------------------------------------------------------ *)

(* A pending error only on a broken channel *)
Definition errb_def:
  errb (w : l0world) ⇔
    ∀j. j < LENGTH w.chans ∧ (EL j w.chans).err ≠ NONE ⇒ (EL j w.chans).broken
End

Definition winv_def:
  winv w ⇔ l0_rely w ∧ l0wf w ∧ noconn w ∧ fds_lt w ∧ errb w
End

Theorem errb_upd:
  errb w ∧ (((g (EL j w.chans)).err ≠ NONE ⇒ (g (EL j w.chans)).broken) ∨
            ((g (EL j w.chans)).err = NONE ∨ (EL j w.chans).err ≠ NONE) ∧
            (EL j w.chans).broken = (g (EL j w.chans)).broken) ⇒
  errb (upd_lchan j g w)
Proof
  rw[errb_def, upd_lchan_def, EL_LUPDATE] >> rw[] >> gvs[]
QED

Theorem errb_simple[simp]:
  errb (w with clock := c) = errb w ∧ errb (w with hist := h) = errb w ∧
  errb (w with listeners := ls) = errb w ∧ errb (w with open_fds := ofs) = errb w ∧
  errb (w with reserved := rs) = errb w
Proof
  simp[errb_def]
QED

Theorem errb_deliver:
  errb w ⇒ errb (l0_deliver w a)
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >> gvs[] >>
  TRY (irule errb_upd >> rw[break_lchan_def] >> NO_TAC) >>
  every_case_tac >> gvs[] >> rw[errb_def, EL_APPEND_EQN] >> rw[] >>
  gvs[errb_def, fresh_lchan_def] >>
  ‘j = LENGTH w.chans’ by decide_tac >> gvs[]
QED

Theorem errb_tick:
  errb w ⇒ errb (l0_tick nm w)
Proof
  rw[l0_tick_def] >>
  ‘∀as w'. errb w' ⇒ errb (FOLDL l0_deliver w' as)’
    by (Induct >> rw[] >> metis_tac[errb_deliver]) >>
  first_x_assum irule >> simp[]
QED

Theorem errb_ticks:
  ∀k w. errb w ⇒ errb (l0_ticks nm k w)
Proof
  Induct >> rw[l0_ticks_def] >> metis_tac[errb_tick]
QED

Theorem errb_FOLDL_break:
  ∀q w. errb w ⇒ errb (FOLDL (λw j. upd_lchan j (break_lchan e F) w) w q)
Proof
  Induct >> rw[] >> first_x_assum irule >> irule errb_upd >> rw[break_lchan_def]
QED

Theorem errb_ops:
  (errb w ∧ l0_listen p w = (x, w') ⇒ errb w') ∧
  (errb w ∧ l0_accept l w = (r, w') ⇒ errb w') ∧
  (errb w ∧ l0_recv f n w = (r, d, w') ⇒ errb w') ∧
  (errb w ∧ l0_send f bs w = (r, w') ⇒ errb w') ∧
  (errb w ∧ l0_shutdown f w = (r, w') ⇒ errb w') ∧
  (errb w ∧ l0_close f w = (r, w') ⇒ errb w') ∧
  (errb w ∧ l0_connerr f w = (y, w') ⇒ errb w')
Proof
  rpt conj_tac >>
  rw[l0_listen_def, l0_accept_def, l0_recv_def, l0_send_def, l0_shutdown_def,
     l0_close_def, l0_connerr_def, AllCaseEqs()] >> gvs[] >>
  TRY (irule errb_upd >> rw[break_lchan_def] >> NO_TAC) >>
  simp[close_fd_def] >> every_case_tac >> gvs[] >>
  TRY (irule errb_FOLDL_break >> simp[] >> NO_TAC) >>
  irule errb_upd >> simp[]
QED

Theorem fd_limit_FOLDL_upd[simp]:
  ∀q w. (FOLDL (λw j. upd_lchan j g w) w q).fd_limit = w.fd_limit
Proof
  Induct >> simp[upd_lchan_def]
QED

Theorem fds_lt_close:
  fds_lt w ∧ l0_close f w = (r, w') ⇒ fds_lt w'
Proof
  rw[fds_lt_def] >> drule_all close_used_sub >> strip_tac >>
  ‘w'.fd_limit = w.fd_limit’
    by (gvs[l0_close_def, close_fd_def, AllCaseEqs()] >> every_case_tac >>
        gvs[upd_lchan_def]) >>
  metis_tac[]
QED

Theorem fds_lt_ops:
  (fds_lt w ∧ l0_recv f n w = (r, d, w') ⇒ fds_lt w') ∧
  (fds_lt w ∧ l0_send f bs w = (r, w') ⇒ fds_lt w') ∧
  (fds_lt w ∧ l0_listen p w = (x, w') ⇒ fds_lt w') ∧
  (fds_lt w ∧ l0_shutdown f w = (r, w') ⇒ fds_lt w') ∧
  (fds_lt w ∧ l0_connerr f w = (y, w') ⇒ fds_lt w')
Proof
  rpt conj_tac >>
  rw[l0_recv_def, l0_send_def, l0_listen_def, l0_shutdown_def,
     l0_connerr_def, l0_alloc_def, AllCaseEqs()] >> gvs[] >>
  gvs[fds_lt_def, l0_used_def, close_fd_def, AllCaseEqs()] >> rw[] >>
  gvs[MEM_FST_ADELKEY, MEM_FILTER, MEM_MAP, EXISTS_PROD] >>
  metis_tac[]
QED

Theorem fds_lt_ticks:
  ∀k w. fds_lt (l0_ticks nm k w) ⇔ fds_lt w
Proof
  Induct >> simp[l0_ticks_def]
QED

Theorem fds_lt_call:
  fds_lt w ∧ n ≠ «sys_connect» ∧ l0_call n conf bytes w = SOME (FFIreturn bytes' w') ⇒
  fds_lt w'
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs(), fds_lt_ticks] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac fds_lt_ops >> imp_res_tac fds_lt_close >>
  imp_res_tac l0_accept_fds_lt >> gvs[]
QED

(* An L0 call (made through l0_do) keeps winv, unless it is a connect *)
Theorem l0_do_cases:
  l0_do n conf alen w = SOME (out, w', ev) ⇒
  ∃w1. l0_call n conf (REPLICATE alen 0w) (l0_tick n w) = SOME (FFIreturn out w1) ∧
       w' = w1 with hist := w.hist ++ [(n, conf, REPLICATE alen 0w)] ∧
       ev = IO_event (ExtCall n) conf (ZIP (REPLICATE alen 0w, out))
Proof
  rw[l0_do_def, l0_ffi_fn_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem winv_do:
  winv w ∧ n ≠ «sys_connect» ∧ l0_do n conf alen w = SOME (out, w', ev) ⇒ winv w'
Proof
  strip_tac >>
  ‘l0_rely w'’ by (irule l0_do_rely >> gvs[winv_def] >> metis_tac[]) >>
  gvs[winv_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  ‘l0wf (l0_tick n w) ∧ noconn (l0_tick n w) ∧ fds_lt (l0_tick n w) ∧
   errb (l0_tick n w)’
    by simp[l0wf_tick, noconn_tick, errb_tick] >>
  rpt conj_tac
  >- (drule_all l0wf_call >> simp[])
  >- (drule_all noconn_call >> simp[noconn_def])
  >- (drule_all fds_lt_call >> simp[fds_lt_def, l0_used_def])
  >> qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >>
  rw[l0_call_def] >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> imp_res_tac errb_ops >>
  TRY (drule_then irule errb_ticks) >> gvs[]
QED

(* An event's call and result *)
Theorem ev_do:
  l0_rely w ∧ l0_do n conf alen w = SOME (out, w', ev) ⇒
  (retried ev ⇔ ∃e x. l0_res_of out = Fail e x ∧ (n = «sys_poll» ∨ l1_transient e)) ∧
  (∀nm f. ev_on nm f ev ⇔ n = nm ∧ MEM f (call_fds nm conf))
Proof
  strip_tac >>
  ‘LENGTH out = alen’
    by (gvs[l0_do_def, AllCaseEqs()] >> drule_all l0_ffi_fn_length >> simp[]) >>
  drule l0_do_cases >> strip_tac >> gvs[retried_def, ev_on_def, MAP_SND_ZIP_REPLICATE] >>
  Cases_on ‘l0_res_of out’ >> simp[] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Pending input across one call
   ------------------------------------------------------------------------ *)

Theorem pend_simple[simp]:
  pend (w with hist := h) f = pend w f ∧ pend (w with clock := c) f = pend w f
Proof
  simp[pend_def, l0_chan_of_def]
QED

(* Pending input on f survives any call but a recv or close on f *)
Theorem pend_do:
  winv w ∧ pend w f ∧ n ≠ «sys_connect» ∧
  ¬((n = «sys_recv» ∨ n = «sys_close») ∧ bytes_fd conf = f) ∧
  l0_do n conf alen w = SOME (out, w', ev) ⇒ pend w' f
Proof
  strip_tac >> drule l0_do_cases >> strip_tac >> gvs[] >>
  irule pend_call >> qexistsl_tac [‘REPLICATE alen 0w’, ‘out’, ‘conf’, ‘n’] >>
  simp[] >> qexists_tac ‘l0_tick n w’ >>
  gvs[winv_def, l0wf_tick, pend_tick] >>
  ‘fds_lt (l0_tick n w)’ by simp[] >> gvs[fds_lt_def, l0_rely_def]
QED


(* ------------------------------------------------------------------------
   The round's actions, seen from f (f's handle h is not written to)
   ------------------------------------------------------------------------ *)

(* What L1 keeps about f while nothing is fetched on it: h is f's only
   handle, f has no input in L1 and no EOF, and is not closing, not
   pre-accepted, not the listener; handles are issued *)
Definition fkeep_def:
  fkeep lfd h f ps ⇔
    ALOOKUP ps.b.tbl h = SOME f ∧ (∀h'. ALOOKUP ps.b.tbl h' = SOME f ⇒ h' = h) ∧
    inb_of ps f = [] ∧ ¬MEM f ps.eof ∧ ¬MEM f ps.b.closing ∧ ¬MEM f ps.acq ∧
    f ≠ lfd ∧
    (∀h' g. ALOOKUP ps.b.tbl h' = SOME g ⇒
            ∃i. i < ps.b.nxt ∧ h' = l1hdl lfd i ∧ l1hdln (w2n lfd) i < dimword (:64))
End

Definition ev_name_def:
  ev_name (IO_event n conf bs) = n
End

Theorem ev_on_name:
  ev_on nm f ev ⇒ ev_name ev = ExtCall nm
Proof
  Cases_on ‘ev’ >> rw[ev_on_def, ev_name_def]
QED

Theorem outbox_of_after_send:
  outbox_of (after_send g r st) f =
    if f = g then outbox_of (after_send g r st) f else outbox_of st f
Proof
  rw[] >> rw[after_send_def] >> every_case_tac >> rw[outbox_of_set_outbox] >>
  simp[outbox_of_def]
QED

Theorem after_send_shrinks:
  LENGTH (outbox_of (after_send f r st) f) ≤ LENGTH (outbox_of st f)
Proof
  rw[after_send_def] >> every_case_tac >> rw[outbox_of_set_outbox]
QED

Theorem names_ne[simp]:
  «sys_poll» ≠ «sys_connect» ∧ «sys_recv» ≠ «sys_connect» ∧
  «sys_send» ≠ «sys_connect» ∧ «sys_close» ≠ «sys_connect» ∧
  «sys_accept» ≠ «sys_connect»
Proof
  EVAL_TAC
QED

Theorem sys_winv:
  (winv w ∧ sys_close g w = SOME (out, w', ev) ⇒ winv w') ∧
  (winv w ∧ sys_send g bs w = SOME (out, w', ev) ⇒ winv w') ∧
  (winv w ∧ sys_recv g k w = SOME (out, w', ev) ⇒ winv w') ∧
  (winv w ∧ sys_accept g w = SOME (out, w', ev) ⇒ winv w') ∧
  (winv w ∧ sys_poll fes w = SOME (out, w', ev) ⇒ winv w')
Proof
  rw[sys_close_def, sys_send_def, sys_recv_def, sys_accept_def, sys_poll_def] >>
  drule_at (Pos last) winv_do >> simp[]
QED

Theorem l1_close_f:
  l1_close g (w, st) = SOME ((w', st'), evs) ∧ winv w ∧ pend w f ∧ g ≠ f ⇒
  winv w' ∧ pend w' f ∧ st'.tbl = st.tbl ∧ st'.nxt = st.nxt ∧
  st'.closing = FILTER ($≠ g) st.closing ∧ outbox_of st' f = outbox_of st f ∧
  EVERY (λev. ev_name ev = ExtCall «sys_close») evs
Proof
  rw[l1_close_def, AllCaseEqs()] >> gvs[]
  >- metis_tac[sys_winv]
  >- (gvs[sys_close_def] >> drule_at (Pos last) pend_do >> simp[])
  >- gvs[forget_def, set_outbox_def]
  >- gvs[forget_def, set_outbox_def]
  >- gvs[forget_def, set_outbox_def]
  >- (gvs[forget_def, outbox_of_set_outbox] >> simp[outbox_of_def])
  >> gvs[sys_close_def] >> drule l0_do_cases >> rw[] >> simp[ev_name_def]
QED

Theorem fkeep_b_same:
  fkeep lfd h f ps ∧ b'.tbl = ps.b.tbl ∧ b'.nxt = ps.b.nxt ∧
  (∀x. MEM x b'.closing ⇒ MEM x ps.b.closing) ⇒
  fkeep lfd h f (ps with b := b')
Proof
  rw[fkeep_def, inb_of_def] >> metis_tac[]
QED



(* ------------------------------------------------------------------------
   The poll
   ------------------------------------------------------------------------ *)

Theorem DROP_poll_out:
  DROP 13 (poll_out w fes) = MAP (fd_revents w) fes
Proof
  simp[poll_out_def] >>
  ‘LENGTH (enc_res (Ok (LENGTH (FILTER (λfe. fd_revents w fe ≠ 0w) fes)))) = 13’
    by simp[] >>
  metis_tac[DROP_LENGTH_APPEND]
QED


(* ------------------------------------------------------------------------
   The flush and the closes
   ------------------------------------------------------------------------ *)



(* ------------------------------------------------------------------------
   The fetch
   ------------------------------------------------------------------------ *)


(* ------------------------------------------------------------------------
   Every round keeps winv
   ------------------------------------------------------------------------ *)

Theorem l1_close_winv:
  l1_close g (w, st) = SOME ((w', st'), evs) ∧ winv w ⇒ winv w'
Proof
  rw[l1_close_def, AllCaseEqs()] >> gvs[] >> metis_tac[sys_winv]
QED



Theorem l1_polls_winv:
  ∀chs w rv w' evs. l1_polls chs w = SOME (rv, w', evs) ∧ winv w ⇒ winv w'
Proof
  Induct >> simp[l1_polls_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[sys_winv]
QED





(* ------------------------------------------------------------------------
   The round, seen from f
   ------------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------
   WORK IN PROGRESS (kept as a comment until proved; the statements are
   the plan for R1-live's round step, design/36 §6; the *_winv lemmas
   below loop on TRY metis_tac[] and need targeted tactics):

Theorem pdo_winv:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ winv w ⇒ winv w'
Proof
  Cases_on ‘a’ >> rw[pdo_def, AllCaseEqs()] >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >> TRY (metis_tac[l1_close_winv]) >>
  gvs[l1do_def, AllCaseEqs()] >> metis_tac[sys_winv]
QED

Theorem pacts_winv:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ winv w ⇒ winv w'
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> PairCases_on ‘ws1’ >> metis_tac[pdo_winv]
QED

Theorem l1_flush_winv:
  ∀fs w st w' st' evs. l1_flush fs (w, st) = SOME ((w', st'), evs) ∧ winv w ⇒ winv w'
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> rw[] >>
  gvs[AllCaseEqs()] >> TRY (metis_tac[]) >>
  Cases_on ‘ws’ >> gvs[] >> metis_tac[sys_winv]
QED

Theorem l1_reap_winv:
  ∀fs w st w' st' evs. l1_reap fs (w, st) = SOME ((w', st'), evs) ∧ winv w ⇒ winv w'
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> rw[] >>
  gvs[AllCaseEqs()] >> TRY (metis_tac[]) >>
  Cases_on ‘ws’ >> Cases_on ‘ws'’ >> gvs[] >> metis_tac[l1_close_winv]
QED

Theorem pf_fetch_winv:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ∧ winv w ⇒ winv w'
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[] >>
  gvs[AllCaseEqs()] >> TRY (metis_tac[]) >>
  rpt (pairarg_tac >> gvs[]) >> Cases_on ‘ws’ >> gvs[] >> metis_tac[sys_winv]
QED

Theorem pround_winv:
  pround lfd hw hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧ winv w ⇒ winv w'
Proof
  rw[pround_def, pf_tail_def, AllCaseEqs()] >>
  PairCases_on ‘ws1’ >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >>
  imp_res_tac pacts_winv >> imp_res_tac l1_polls_winv >>
  imp_res_tac l1_flush_winv >> imp_res_tac pf_fetch_winv >>
  imp_res_tac l1_reap_winv >> metis_tac[]
QED

(-* ... and a retried recv on f *-)
Theorem pend_recv_retried:
  winv w ∧ pend w f ∧ sys_recv f k w = SOME (out, w', ev) ∧ retried ev ⇒ pend w' f
Proof
  rw[sys_recv_def] >>
  ‘l0_rely w’ by gvs[winv_def] >> drule_all ev_do >> strip_tac >> gvs[] >>
  drule l0_do_cases >> strip_tac >> gvs[] >>
  qabbrev_tac ‘wt = l0_tick «sys_recv» w’ >>
  ‘pend wt f ∧ noconn wt ∧ errb wt ∧ l0_rely wt’
    by (gvs[Abbr ‘wt’, winv_def, pend_tick, noconn_tick, errb_tick] >>
        irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >>
  simp[l0_call_def, l0_hdr_def] >> rw[] >> pairarg_tac >> gvs[] >>
  ‘TAKE 8 (fd_bytes f ++ []) = fd_bytes f’ by simp[TAKE_DROP_fd_bytes] >> gvs[] >>
  gvs[pend_def] >>
  qpat_x_assum ‘l0_recv _ _ _ = _’ mp_tac >>
  simp[l0_recv_def] >> rpt (CASE_TAC >> gvs[]) >> rw[] >> gvs[noconn_def] >>
  TRY (‘j < LENGTH wt.chans’ by gvs[l0_chan_of_def, AllCaseEqs()] >> gvs[] >> NO_TAC) >>
  cheat
QED

Theorem pdo_f:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ winv w ∧ pend w f ∧
  fkeep lfd h f ps ∧ (∀bs. a ≠ Write h bs) ⇒
  winv w' ∧ pend w' f ∧ fkeep lfd h f ps' ∧
  LENGTH (outbox_of ps'.b f) ≤ LENGTH (outbox_of ps.b f) ∧
  EVERY (λev. ev_name ev = ExtCall «sys_send» ∨ ev_name ev = ExtCall «sys_close») evs
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> strip_tac
  >- ((-* Accept *-)
      gvs[AllCaseEqs()] >> gvs[fkeep_def] >> rw[] >>
      gvs[AllCaseEqs()]
      >- (first_x_assum drule >> strip_tac >>
          ‘l1hdln (w2n lfd) i < dimword (:64)’ by simp[] >>
          drule_all l1hdl_11 >> simp[])
      >- (first_x_assum drule >> rw[] >> metis_tac[])
      >- (rename1 ‘ALOOKUP _ h' = SOME g’ >> Cases_on ‘h' = l1hdl lfd ps.b.nxt’ >> gvs[]
          >- (qexists_tac ‘ps.b.nxt’ >> simp[])
          >> first_x_assum drule >> rw[] >> qexists_tac ‘i’ >> simp[]))
  >- ((-* Read *-)
      gvs[AllCaseEqs()] >> cheat)
  >> (-* Write *-)
  cheat
QED

Theorem pacts_f:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ winv w ∧ pend w f ∧
    fkeep lfd h f ps ∧ (∀bs. ¬MEM (Write h bs) acts) ⇒
    winv w' ∧ pend w' f ∧ fkeep lfd h f ps' ∧
    LENGTH (outbox_of ps'.b f) ≤ LENGTH (outbox_of ps.b f) ∧
    EVERY (λev. ev_name ev = ExtCall «sys_send» ∨ ev_name ev = ExtCall «sys_close») evs
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  drule pdo_f >> simp[] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem l1_polls_f:
  ∀chs w rv w' evs.
    l1_polls chs w = SOME (rv, w', evs) ∧ winv w ∧ pend w f ∧
    (∀c. MEM c chs ⇒ EVERY (λ(g, e). e < 256 ∧ (g = f ⇒ ODD e)) c) ⇒
    winv w' ∧ pend w' f ∧
    EVERY (λev. ev_name ev = ExtCall «sys_poll») evs ∧
    (∀c. MEM c chs ∧ MEM f (MAP FST c) ⇒ EXISTS (ev_on «sys_poll» f) evs) ∧
    (∀ev. MEM ev evs ∧ ev_on «sys_poll» f ev ∧ ¬retried ev ⇒ MEM f (readable_fds rv))
Proof
  cheat
QED

Theorem l1_flush_f:
  ∀fs w st w' st' evs.
    l1_flush fs (w, st) = SOME ((w', st'), evs) ∧ winv w ∧ pend w f ⇒
    winv w' ∧ pend w' f ∧ st'.tbl = st.tbl ∧ st'.nxt = st.nxt ∧
    st'.closing = st.closing ∧
    LENGTH (outbox_of st' f) ≤ LENGTH (outbox_of st f) ∧
    EVERY (λev. ev_name ev = ExtCall «sys_send») evs
Proof
  cheat
QED

Theorem l1_reap_f:
  ∀fs w st w' st' evs.
    l1_reap fs (w, st) = SOME ((w', st'), evs) ∧ winv w ∧ pend w f ∧ ¬MEM f fs ⇒
    winv w' ∧ pend w' f ∧ st'.tbl = st.tbl ∧ st'.nxt = st.nxt ∧
    (∀x. MEM x st'.closing ⇒ MEM x st.closing) ∧
    outbox_of st' f = outbox_of st f ∧
    EVERY (λev. ev_name ev = ExtCall «sys_close») evs
Proof
  cheat
QED

Theorem pf_fetch_f:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ∧ winv w ∧ pend w f ∧
    fkeep lfd h f ps ∧ LENGTH (outbox_of ps.b f) ≤ hw ⇒
    winv w' ∧
    EVERY (λev. ev_name ev = ExtCall «sys_accept» ∨ ev_name ev = ExtCall «sys_recv») evs ∧
    (MEM f fs ⇒ EXISTS (ev_on «sys_recv» f) evs) ∧
    (∀ev. MEM ev evs ∧ ev_on «sys_recv» f ev ∧ ¬retried ev ⇒ fetched f log) ∧
    (¬fetched f log ⇒ pend w' f ∧ fkeep lfd h f ps' ∧ outbox_of ps'.b f = outbox_of ps.b f)
Proof
  cheat
QED

Theorem pround_f:
  pround lfd hw hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧
  winv w ∧ pend w f ∧ fkeep lfd h f ps ∧ MEM h hs ∧
  LENGTH (outbox_of ps.b f) ≤ hw ∧ (∀bs. ¬MEM (Write h bs) acts) ⇒
  EXISTS (ev_on «sys_poll» f) evs ∧
  (∀ev. MEM ev evs ∧ ev_on «sys_poll» f ev ∧ ¬retried ev ⇒
        EXISTS (ev_on «sys_recv» f) evs) ∧
  (∀ev. MEM ev evs ∧ ev_on «sys_recv» f ev ∧ ¬retried ev ⇒ fetched f log) ∧
  (¬fetched f log ⇒ pend w' f ∧ fkeep lfd h f ps')
Proof
  cheat
QED

   ------------------------------------------------------------------------ *)
