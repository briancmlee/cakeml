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

Theorem names_distinct[simp]:
  «sys_poll» ≠ «sys_recv» ∧ «sys_poll» ≠ «sys_send» ∧ «sys_poll» ≠ «sys_close» ∧
  «sys_poll» ≠ «sys_accept» ∧ «sys_recv» ≠ «sys_send» ∧ «sys_recv» ≠ «sys_close» ∧
  «sys_recv» ≠ «sys_accept» ∧ «sys_send» ≠ «sys_close» ∧ «sys_send» ≠ «sys_accept» ∧
  «sys_close» ≠ «sys_accept»
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

Theorem after_send_fields[simp]:
  (after_send g r st).tbl = st.tbl ∧ (after_send g r st).nxt = st.nxt ∧
  (after_send g r st).closing = st.closing
Proof
  rw[after_send_def] >> every_case_tac >> rw[set_outbox_def]
QED

Theorem after_send_le:
  LENGTH (outbox_of (after_send g r st) f) ≤ LENGTH (outbox_of st f)
Proof
  Cases_on ‘f = g’ >> simp[after_send_shrinks] >> simp[Once outbox_of_after_send]
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

Theorem inb_of_upd[simp]:
  inb_of (ps with b := x) f = inb_of ps f ∧ inb_of (ps with eof := e) f = inb_of ps f ∧
  inb_of (ps with acq := q) f = inb_of ps f
Proof
  simp[inb_of_def]
QED

Theorem outbox_of_upd[simp]:
  outbox_of (b with tbl := t) f = outbox_of b f ∧
  outbox_of (b with closing := c) f = outbox_of b f ∧
  outbox_of (b with nxt := n) f = outbox_of b f ∧
  outbox_of (b with exhausted := x) f = outbox_of b f
Proof
  simp[outbox_of_def]
QED

Theorem fkeep_exhausted[simp]:
  fkeep lfd h f (ps with b := ps.b with exhausted := x) ⇔ fkeep lfd h f ps
Proof
  simp[fkeep_def]
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

Theorem pdo_winv:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ winv w ⇒ winv w'
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> rw[AllCaseEqs()] >> gvs[] >>
  PairCases_on ‘z’ >> gvs[] >>
  TRY (drule_all l1_close_winv >> simp[] >> NO_TAC) >>
  gvs[l1do_def, AllCaseEqs(), sys_send_def] >> drule_at (Pos last) winv_do >> simp[]
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
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> rename1 ‘sys_send _ _ _ = SOME (out, w1, ev)’ >>
  ‘winv w1’ by (gvs[sys_send_def, sys_recv_def, sys_accept_def] >>
                 drule_at (Pos last) winv_do >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem l1_reap_winv:
  ∀fs w st w' st' evs. l1_reap fs (w, st) = SOME ((w', st'), evs) ∧ winv w ⇒ winv w'
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> Cases_on ‘ws’ >> drule_all l1_close_winv >>
  strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem pf_fetch_winv:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ∧ winv w ⇒ winv w'
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘SOME (out, w1, ev)’ >>
  ‘winv w1’ by (gvs[sys_recv_def, sys_accept_def] >>
                 drule_at (Pos last) winv_do >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem pround_winv:
  pround lfd hw hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧ winv w ⇒ winv w'
Proof
  rw[pround_def, AllCaseEqs()] >>
  PairCases_on ‘ws1’ >> drule_all pacts_winv >> strip_tac >>
  gvs[pf_tail_def, AllCaseEqs()] >>
  drule_all l1_polls_winv >> strip_tac >> drule_all l1_flush_winv >> strip_tac >>
  drule_all pf_fetch_winv >> strip_tac >> drule_all l1_reap_winv >> simp[]
QED

(* A recv on a pending fd either succeeds or leaves the input pending *)
Theorem recv_pend_or_ok:
  pend w f ∧ noconn w ∧ errb w ∧ l0_recv f n w = (r, d, w') ⇒
  pend w' f ∨ ∃k. r = Ok k ∧ k ≤ n
Proof
  rw[pend_def] >> gvs[l0_recv_def, AllCaseEqs()] >>
  ‘j < LENGTH w.chans’ by gvs[l0_chan_of_def, AllCaseEqs()] >>
  gvs[noconn_def, errb_def, upd_lchan_def, l0_chan_of_def, EL_LUPDATE]
QED

(* ... and a retried recv on f *)
Theorem pend_recv_retried:
  winv w ∧ pend w f ∧ k < 256 ** 8 ∧ sys_recv f k w = SOME (out, w', ev) ∧ retried ev ⇒
  pend w' f
Proof
  rw[sys_recv_def] >>
  ‘l0_rely w’ by gvs[winv_def] >> drule_all ev_do >> strip_tac >> gvs[] >>
  drule l0_do_cases >> strip_tac >> gvs[] >>
  ‘pend (l0_tick «sys_recv» w) f ∧ noconn (l0_tick «sys_recv» w) ∧
   errb (l0_tick «sys_recv» w)’
    by gvs[winv_def, pend_tick, noconn_tick, errb_tick] >>
  gvs[l0_call_def, l0_hdr_def, AllCaseEqs()] >> pairarg_tac >> gvs[] >>
  drule_all recv_pend_or_ok >> rw[] >> gvs[] >>
  qspecl_then [‘Ok k'’, ‘d ++ REPLICATE (k − LENGTH d) 0w’] mp_tac
    (Q.GENL [‘r’, ‘rest’] l0_res_of_enc_app) >>
  gvs[l0_res_ok_def]
QED

Theorem pdo_f:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ winv w ∧ pend w f ∧
  fkeep lfd h f ps ∧ (∀bs. a ≠ Write h bs) ⇒
  winv w' ∧ pend w' f ∧ fkeep lfd h f ps' ∧
  LENGTH (outbox_of ps'.b f) ≤ LENGTH (outbox_of ps.b f) ∧
  EVERY (λev. ev_name ev = ExtCall «sys_send» ∨ ev_name ev = ExtCall «sys_close») evs
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> strip_tac
  >- ((* Accept *)
      gvs[AllCaseEqs()] >> gvs[fkeep_def, outbox_of_def, inb_of_def] >>
      rw[] >> gvs[] >>
      TRY (qexists_tac ‘ps.b.nxt’ >> simp[] >> NO_TAC) >>
      first_x_assum drule >> rw[] >> TRY (qexists_tac ‘i’ >> simp[] >> NO_TAC) >>
      qspecl_then [‘c’, ‘ps.b.nxt’, ‘i’] mp_tac (Q.GENL [‘lfd’, ‘i’, ‘j’] l1hdl_11) >>
      simp[])
  >- ((* Read *)
      Cases_on ‘ALOOKUP ps.b.tbl c’ >> gvs[] >> rename1 ‘ALOOKUP _ c = SOME g’ >>
      ‘g = f ⇒ c = h’ by gvs[fkeep_def] >>
      Cases_on ‘g = f’ >- gvs[fkeep_def] >>
      ‘c ≠ h’ by (strip_tac >> gvs[fkeep_def]) >>
      gvs[AllCaseEqs()] >>
      TRY (PairCases_on ‘z’ >> gvs[] >> drule_all l1_close_f >> strip_tac >> gvs[]) >>
      gvs[fkeep_def, ALOOKUP_ADELKEY, MEM_FILTER, EVERY_MEM] >> rw[] >>
      gvs[ALOOKUP_ADELKEY])
  >> (* Write *)
  PairCases_on ‘z’ >> gvs[l1do_def, AllCaseEqs()] >>
  TRY (‘ps with b := ps.b = ps’ by simp[l1p_component_equality] >> gvs[] >> NO_TAC) >>
  rename1 ‘ALOOKUP _ c = SOME g’ >>
  ‘g ≠ f’ by (strip_tac >> gvs[fkeep_def] >> res_tac) >>
  TRY (conj_tac >- (irule fkeep_b_same >> simp[set_outbox_def]) >>
       simp[outbox_of_set_outbox] >> NO_TAC) >>
  ‘winv w' ∧ pend w' f’
    by (qpat_x_assum ‘sys_send _ _ _ = _’ mp_tac >> simp[sys_send_def] >> strip_tac >>
        conj_tac >- (drule_at (Pos last) winv_do >> simp[]) >>
        drule_at (Pos last) pend_do >> simp[]) >>
  simp[outbox_of_after_send, outbox_of_set_outbox] >> conj_tac
  >- (irule fkeep_b_same >> simp[after_send_def, set_outbox_def] >>
      every_case_tac >> simp[])
  >> ‘f ≠ g’ by simp[] >>
  simp[Once outbox_of_after_send, outbox_of_set_outbox] >>
  gvs[sys_send_def] >> drule l0_do_cases >> rw[] >> simp[ev_name_def]
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
  drule pdo_f >> simp[] >> disch_then (qspecl_then [‘h’, ‘f’] mp_tac) >>
  simp[] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem l1_flush_f:
  ∀fs w st w' st' evs.
    l1_flush fs (w, st) = SOME ((w', st'), evs) ∧ winv w ∧ pend w f ⇒
    winv w' ∧ pend w' f ∧ st'.tbl = st.tbl ∧ st'.nxt = st.nxt ∧
    st'.closing = st.closing ∧
    LENGTH (outbox_of st' f) ≤ LENGTH (outbox_of st f) ∧
    EVERY (λev. ev_name ev = ExtCall «sys_send») evs
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> rename1 ‘sys_send _ _ _ = SOME (out, w1, ev)’ >>
  ‘winv w1 ∧ pend w1 f ∧ ev_name ev = ExtCall «sys_send»’
    by (gvs[sys_send_def] >> rpt conj_tac
        >- (drule_at (Pos last) winv_do >> simp[])
        >- (drule_at (Pos last) pend_do >> simp[])
        >> drule l0_do_cases >> rw[] >> simp[ev_name_def]) >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  irule LESS_EQ_TRANS >> goal_assum drule >> simp[after_send_le]
QED

Theorem l1_reap_f:
  ∀fs w st w' st' evs.
    l1_reap fs (w, st) = SOME ((w', st'), evs) ∧ winv w ∧ pend w f ∧ ¬MEM f fs ⇒
    winv w' ∧ pend w' f ∧ st'.tbl = st.tbl ∧ st'.nxt = st.nxt ∧
    (∀x. MEM x st'.closing ⇒ MEM x st.closing) ∧
    outbox_of st' f = outbox_of st f ∧
    EVERY (λev. ev_name ev = ExtCall «sys_close») evs
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (gvs[AllCaseEqs()] >> Cases_on ‘ws’ >> drule l1_close_f >> disch_then (qspec_then ‘f’ mp_tac) >> simp[] >> strip_tac >>
      first_x_assum drule_all >> strip_tac >> gvs[MEM_FILTER])
  >> first_x_assum drule_all >> simp[]
QED

Theorem res_of_fail:
  LENGTH (w.ch.errno_of w.hist) = 4 ⇒
  l0_res_of (enc_res (fail w e) ++ rest) = Fail e (w.ch.errno_of w.hist)
Proof
  rw[fail_def] >> irule l0_res_of_enc_app >> simp[l0_res_ok_def]
QED

Theorem pend_used:
  pend w f ⇒ MEM f (l0_used w)
Proof
  rw[pend_def, l0_chan_of_def, AllCaseEqs(), l0_used_def] >>
  imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

Theorem readable_zip:
  ∀fes. MEM (f, e) fes ∧ (g (f, e)).rin ⇒
        MEM f (readable_fds (ZIP (MAP FST fes, MAP g fes)))
Proof
  Induct >> simp[FORALL_PROD, readable_fds_def] >> rw[] >> gvs[readable_fds_def]
QED

(* One poll, seen from f: if it lists f (for input) and is not retried, it
   reports f readable *)
Theorem sys_poll_f:
  sys_poll fes w = SOME (out, w', ev) ∧ winv w ∧ pend w f ∧
  EVERY (λ(g, e). e < 256 ∧ (g = f ⇒ ODD e)) fes ⇒
  winv w' ∧ pend w' f ∧ ev_name ev = ExtCall «sys_poll» ∧
  (MEM f (MAP FST fes) ⇒ ev_on «sys_poll» f ev) ∧
  (ev_on «sys_poll» f ev ∧ ¬retried ev ⇒ MEM f (readable_fds (poll_revents fes out)))
Proof
  strip_tac >> ‘l0_rely w’ by gvs[winv_def] >>
  ‘EVERY (λ(g, e). e < 256) fes’
    by (qpat_x_assum ‘EVERY _ fes’ mp_tac >> match_mp_tac EVERY_MONOTONIC >>
        simp[FORALL_PROD]) >>
  drule_all call_fds_poll >> strip_tac >>
  qpat_x_assum ‘sys_poll _ _ = _’ mp_tac >> simp[sys_poll_def] >> strip_tac >>
  drule_all ev_do >> strip_tac >>
  ‘winv w' ∧ pend w' f’
    by (conj_tac >- (drule_at (Pos last) winv_do >> simp[]) >>
        drule_at (Pos last) pend_do >> simp[]) >>
  drule l0_do_cases >> strip_tac >> gvs[ev_name_def] >>
  rw[] >> gvs[] >>
  ‘poll_entries (DROP 1 (poll_conf fes)) = fes ∧ HD (poll_conf fes) = 0w’
    by simp[poll_conf_def, poll_entries_conf] >>
  qabbrev_tac ‘wt = l0_tick «sys_poll» w’ >>
  ‘noconn wt ∧ pend wt f ∧ LENGTH (wt.ch.errno_of wt.hist) = 4’
    by gvs[Abbr ‘wt’, winv_def, noconn_tick, pend_tick, l0_rely_def] >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def] >>
  rw[AllCaseEqs()] >> gvs[] >>
  TRY (gvs[res_of_fail] >> NO_TAC) >>
  gvs[MEM_MAP] >> rename1 ‘MEM y fes’ >> PairCases_on ‘y’ >> gvs[] >>
  ‘ODD y1’ by (qpat_x_assum ‘EVERY (λ(g, e). _ ∧ _) fes’ mp_tac >>
                simp[EVERY_MEM] >> disch_then drule >> simp[]) >>
  simp[poll_revents_def] >> CASE_TAC >> gvs[] >>
  simp[DROP_poll_out] >>
  ‘TAKE (LENGTH fes) (MAP (fd_revents w1) fes) = MAP (fd_revents w1) fes’
    by metis_tac[LENGTH_MAP, TAKE_LENGTH_ID] >>
  simp[MAP_MAP_o] >> irule readable_zip >> qexists_tac ‘y1’ >>
  simp[pend_revents_in]
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
  Induct >> simp[l1_polls_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs(), DISJ_IMP_THM, FORALL_AND_THM] >>
  drule_all sys_poll_f >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  simp[readable_fds_def, FILTER_APPEND] >> gvs[readable_fds_def] >>
  rw[] >> gvs[] >> metis_tac[]
QED

Theorem pf_fetch_names:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ⇒
    EVERY (λev. ev_name ev = ExtCall «sys_accept» ∨ ev_name ev = ExtCall «sys_recv») evs
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> simp[] >>
  gvs[sys_recv_def, sys_accept_def] >> drule l0_do_cases >> rw[] >> simp[ev_name_def]
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
  Induct >- simp[pf_fetch_def, fetched_def] >>
  rpt gen_tac >> rename1 ‘g :: fs’ >> strip_tac >>
  ‘inb_of ps f = [] ∧ ¬MEM f ps.eof ∧ f ≠ lfd’
    by (qpat_x_assum ‘fkeep _ _ _ _’ mp_tac >> simp[fkeep_def]) >>
  ‘wants_input lfd hw ps f’ by simp[wants_input_def] >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ mp_tac >> simp[Once pf_fetch_def] >>
  IF_CASES_TAC
  >- (strip_tac >> ‘g ≠ f’ by (strip_tac >> fs[]) >>
      first_x_assum (drule_all_then strip_assume_tac) >> simp[] >> metis_tac[])
  >> IF_CASES_TAC
  >- ((* accept on the listener *)
      ‘g ≠ f’ by (strip_tac >> fs[]) >>
      simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
      pairarg_tac >> fs[AllCaseEqs()] >> rveq >>
      ‘winv w1 ∧ pend w1 f ∧ ev_name ev = ExtCall «sys_accept»’
        by (fs[sys_accept_def] >> rpt conj_tac
            >- (drule_at (Pos last) winv_do >> simp[])
            >- (drule_at (Pos last) pend_do >> simp[])
            >> drule l0_do_cases >> rw[] >> simp[ev_name_def]) >>
      ‘¬ev_on «sys_recv» f ev’ by (Cases_on ‘ev’ >> gvs[ev_on_def, ev_name_def]) >>
      gvs[AllCaseEqs()] >>
      first_x_assum drule >> impl_tac
      >- (simp[] >>
          TRY (qpat_x_assum ‘fkeep _ _ _ _’ mp_tac >> simp[fkeep_def] >> NO_TAC) >>
          ‘¬MEM (n2w k) (l0_used w)’
            by (irule sys_accept_fresh >> gvs[winv_def] >> metis_tac[]) >>
          ‘n2w k ≠ f’ by metis_tac[pend_used] >>
          qpat_x_assum ‘fkeep _ _ _ _’ mp_tac >> simp[fkeep_def])
      >> strip_tac >> fs[fetched_def] >> rpt strip_tac >> gvs[] >> res_tac >> fs[])
  >> Cases_on ‘g = f’
  >- ((* recv on f *)
      gvs[] >> simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
      ‘l0_rely w’ by fs[winv_def] >>
      qpat_assum ‘sys_recv _ _ _ = _’ (strip_assume_tac o REWRITE_RULE [sys_recv_def]) >>
      drule_all ev_do >> strip_tac >>
      ‘winv w1 ∧ ev_name ev = ExtCall «sys_recv» ∧ ev_on «sys_recv» f ev’
        by (rpt conj_tac
            >- (drule_at (Pos last) winv_do >> simp[])
            >> drule l0_do_cases >> rw[] >> simp[ev_name_def, ev_on_def]) >>
      Cases_on ‘∃e x. l0_res_of out = Fail e x ∧ l1_transient e’
      >- ((* retried: L1 keeps its state, the input stays pending *)
          gvs[AllCaseEqs()] >> ‘retried ev’ by simp[] >>
          ‘pf_chunk < 256 ** 8’ by EVAL_TAC >>
          drule_all pend_recv_retried >> strip_tac >>
          first_x_assum drule_all >> strip_tac >> simp[] >>
          rpt strip_tac >> gvs[] >> metis_tac[])
      >> (* logged *)
      Cases_on ‘l0_res_of out’ >> gvs[] >> TRY (rename1 ‘Ok n’ >> Cases_on ‘0 < n’) >>
      gvs[AllCaseEqs()] >>
      drule_all pf_fetch_winv >> drule pf_fetch_names >> rw[] >> gvs[fetched_def])
  >> (* recv on another fd *)
  simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  pairarg_tac >> fs[AllCaseEqs()] >> rveq >>
  ‘winv w1 ∧ pend w1 f ∧ ev_name ev = ExtCall «sys_recv» ∧ ¬ev_on «sys_recv» f ev’
    by (fs[sys_recv_def] >> rpt conj_tac
        >- (drule_at (Pos last) winv_do >> simp[])
        >- (drule_at (Pos last) pend_do >> simp[])
        >> drule l0_do_cases >> rw[] >> simp[ev_name_def, ev_on_def]) >>
  gvs[AllCaseEqs()] >>
  first_x_assum drule >> impl_tac >>
  TRY (simp[] >> qpat_x_assum ‘fkeep _ _ _ _’ mp_tac >> simp[fkeep_def] >> NO_TAC) >>
  strip_tac >> fs[fetched_def] >> rpt strip_tac >> gvs[] >> res_tac >> fs[]
QED

Theorem l1_reap_names:
  ∀fs w st w' st' evs.
    l1_reap fs (w, st) = SOME ((w', st'), evs) ⇒
    EVERY (λev. ev_name ev = ExtCall «sys_close») evs
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> strip_tac
  >- (gvs[AllCaseEqs()] >> Cases_on ‘ws’ >> first_x_assum drule >> simp[] >>
      gvs[l1_close_def, AllCaseEqs(), sys_close_def] >>
      drule l0_do_cases >> rw[] >> simp[ev_name_def])
  >> first_x_assum drule >> simp[]
QED

Theorem FLAT_poll_chunks:
  ∀l. FLAT (poll_chunks l) = l
Proof
  gen_tac >> completeInduct_on ‘LENGTH l’ >> rw[] >>
  simp[Once poll_chunks_def] >> IF_CASES_TAC >> simp[] >>
  first_x_assum (qspec_then ‘LENGTH (DROP 4096 l)’ mp_tac) >> simp[] >>
  disch_then (qspec_then ‘DROP 4096 l’ mp_tac) >> simp[]
QED

(* f's handle is in the interest and L1 wants input on f: the poll set lists
   f, always for input *)
Theorem pf_poll_set_f:
  ALOOKUP ps.b.tbl h = SOME f ∧ (∀h'. ALOOKUP ps.b.tbl h' = SOME f ⇒ h' = h) ∧
  f ≠ lfd ∧ MEM h hs ∧ wants_input lfd hw ps f ⇒
  (∃e. MEM (f, e) (pf_poll_set lfd hw ps hs)) ∧
  (∀e. MEM (f, e) (pf_poll_set lfd hw ps hs) ⇒ ODD e) ∧
  EVERY (λ(g, e). e < 256) (pf_poll_set lfd hw ps hs)
Proof
  strip_tac >> simp[pf_poll_set_def] >> rpt conj_tac
  >- (qexists_tac ‘1 + (if outbox_of ps.b f = [] then 0 else 2)’ >>
      simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> disj1_tac >> qexists_tac ‘h’ >>
      rw[])
  >- (rw[MEM_FLAT, MEM_MAP, MEM_FILTER, EXISTS_PROD] >> gvs[AllCaseEqs()] >>
      every_case_tac >> gvs[] >> res_tac >> gvs[] >>
      first_x_assum (qspecl_then [‘(if outbox_of ps.b f = [] then 0 else 2) + 1’,
                                  ‘[(f, (if outbox_of ps.b f = [] then 0 else 2) + 1)]’]
                     mp_tac) >>
      simp[] >> qexists_tac ‘h’ >> simp[])
  >> simp[EVERY_MEM, FORALL_PROD, MEM_FLAT, MEM_MAP, MEM_FILTER, PULL_EXISTS] >>
  rw[] >> every_case_tac >> gvs[] >> rw[]
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
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >>
  gvs[pf_tail_def, AllCaseEqs()] >>
  drule_all pacts_f >> strip_tac >>
  rename1 ‘pacts _ _ _ = SOME (rs, aevs, wa, pa)’ >>
  qabbrev_tac ‘fes = pf_poll_set lfd hw pa hs’ >>
  ‘inb_of pa f = [] ∧ ¬MEM f pa.eof ∧ f ≠ lfd ∧ ALOOKUP pa.b.tbl h = SOME f ∧
   (∀h'. ALOOKUP pa.b.tbl h' = SOME f ⇒ h' = h) ∧ ¬MEM f pa.b.closing’
    by (qpat_x_assum ‘fkeep _ _ _ pa’ mp_tac >> simp[fkeep_def]) >>
  ‘wants_input lfd hw pa f’
    by (simp[wants_input_def] >> fs[] >> metis_tac[LESS_EQ_TRANS]) >>
  ‘(∃e. MEM (f, e) fes) ∧ (∀e. MEM (f, e) fes ⇒ ODD e) ∧
   EVERY (λ(g, e). e < 256) fes’
    by (qunabbrev_tac ‘fes’ >> match_mp_tac pf_poll_set_f >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
  ‘∀c. MEM c (poll_chunks fes) ⇒ EVERY (λ(g, e). e < 256 ∧ (g = f ⇒ ODD e)) c’
    by (‘EVERY (λ(g, e). e < 256 ∧ (g = f ⇒ ODD e)) fes’
          by (gvs[EVERY_MEM, FORALL_PROD] >> rw[] >> res_tac) >>
        drule poll_chunks_ok >> simp[EVERY_MEM] >> metis_tac[]) >>
  drule_all l1_polls_f >> strip_tac >>
  ‘EXISTS (ev_on «sys_poll» f) pevs’
    by (‘MEM (f, e) (FLAT (poll_chunks fes))’ by simp[FLAT_poll_chunks] >>
        gvs[MEM_FLAT] >> first_x_assum irule >> qexists_tac ‘l’ >>
        simp[MEM_MAP] >> qexists_tac ‘(f, e)’ >> simp[]) >>
  drule_all l1_flush_f >> strip_tac >>
  ‘fkeep lfd h f (pa with b := b2) ∧ LENGTH (outbox_of b2 f) ≤ hw’
    by (conj_tac >- (irule fkeep_b_same >> fs[]) >> metis_tac[LESS_EQ_TRANS]) >>
  drule pf_fetch_f >> disch_then (drule_at Any) >> simp[] >> strip_tac >>
  ‘MEM f (in_fds fes)’
    by (simp[in_fds_def, MEM_MAP, MEM_FILTER, EXISTS_PROD] >> metis_tac[]) >>
  drule l1_reap_names >> strip_tac >>
  conj_tac
  >- (rpt strip_tac >> imp_res_tac ev_on_name >> fs[EVERY_MEM] >> res_tac >> fs[] >>
      ‘MEM f (readable_fds rv)’ by metis_tac[] >> fs[MEM_FILTER])
  >> conj_tac
  >- (rpt strip_tac >> imp_res_tac ev_on_name >> fs[EVERY_MEM] >> res_tac >> fs[])
  >> strip_tac >> gvs[] >>
  ‘¬MEM f ps3.b.closing’ by (qpat_x_assum ‘fkeep _ _ _ ps3’ mp_tac >> simp[fkeep_def]) >>
  drule_all l1_reap_f >> strip_tac >> simp[] >>
  irule fkeep_b_same >> fs[]
QED
