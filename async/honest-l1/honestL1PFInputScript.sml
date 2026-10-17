(*
  The input side of R1, at L0 (for async-spike's echo chain, design/47 D
  step 2): what c's peer has sent is what L1 has fetched on f, then what is
  still in c's kernel inbox, unless c broke and its inbox was flushed.

    peer_sent c (rworld n) = fdata f (rlogs a (n − a)) ++ inbox c (rworld n)
      ∨ flushed (rworld n) f

  for f accepted (pre-accepted, FConn f) at round a and not again before n.
  The world facts: a channel's peer_sent is T ++ inbox, where T is what
  recvs took from it (pinchan); a queued channel has had nothing taken
  (qinb); deliveries append to both, a break either keeps the inbox or
  flushes it, and only a recv on the channel's fd takes from it.
*)
Theory honestL1PFInput
Ancestors
  honestL1PFS4w honestL1PFOutLive honestL1PFDead honestL1PFFlushLive honestL1PFOut
  honestL1PFClient honestL1PFStream honestL1PFConnRun honestL1PFConn honestL1PFLive
  honestL1PFRound honestL1PFRefine honestL1PFInv honestL1PFModel honestL1Steps
  honestL1Props honestL1Inv honestL1Model honestL0WorldInv honestL0WorldProps
  honestL0Rely honestL0World honestL0 asyncCore
Libs
  preamble

(* ------------------------------------------------------------------------
   One channel
   ------------------------------------------------------------------------ *)

(* tak0 was tak0 from channel c by recvs: what its peer sent is tak0, then its
   inbox; or it broke and its inbox was flushed *)
Definition pinchan_def:
  pinchan (tak0 : word8 list) (c : lchan) ⇔ c.peer_sent = tak0 ++ c.inbox ∨ c.broken ∧ c.inbox = []
End

Definition chin_def:
  chin j tak0 w ⇔ j < LENGTH w.chans ∧ pinchan tak0 (EL j w.chans)
End

Theorem chin_upd:
  chin j tak0 w ∧ (k = j ⇒ ∀x. pinchan tak0 x ⇒ pinchan tak0 (g x)) ⇒ chin j tak0 (upd_lchan k g w)
Proof
  rw[chin_def, upd_lchan_def, EL_LUPDATE] >> rw[]
QED

Theorem pinchan_break:
  pinchan tak0 x ⇒ pinchan tak0 (break_lchan e keep x)
Proof
  rw[pinchan_def, break_lchan_def] >> rw[]
QED

Theorem chin_FOLDL_break:
  ∀q w. chin j tak0 w ⇒ chin j tak0 (FOLDL (λw k. upd_lchan k (break_lchan e F) w) w q)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  irule chin_upd >> simp[pinchan_break]
QED

Theorem chin_fields[simp]:
  (chin j tak0 (w with listeners := x) ⇔ chin j tak0 w) ∧
  (chin j tak0 (w with open_fds := y) ⇔ chin j tak0 w) ∧
  (chin j tak0 (w with hist := h) ⇔ chin j tak0 w) ∧
  (chin j tak0 (w with clock := k) ⇔ chin j tak0 w) ∧
  (chin j tak0 (w with reserved := r) ⇔ chin j tak0 w)
Proof
  simp[chin_def]
QED

Theorem chin_deliver:
  chin j tak0 w ⇒ chin j tak0 (l0_deliver w a)
Proof
  strip_tac >> Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >> gvs[] >>
  TRY (irule chin_upd >> rw[pinchan_break] >> gvs[pinchan_def] >> NO_TAC) >>
  gvs[chin_def, EL_APPEND1, upd_lchan_def, EL_LUPDATE] >> rw[] >> gvs[pinchan_def]
QED

Theorem chin_tick:
  chin j tak0 w ⇒ chin j tak0 (l0_tick nm w)
Proof
  simp[l0_tick_def] >>
  ‘∀as w. chin j tak0 w ⇒ chin j tak0 (FOLDL l0_deliver w as)’
    by (Induct >> simp[] >> metis_tac[chin_deliver]) >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem chin_ticks:
  ∀k w. chin j tak0 w ⇒ chin j tak0 (l0_ticks nm k w)
Proof
  Induct >> simp[l0_ticks_def] >> metis_tac[chin_tick]
QED

(* A recv on the channel's fd: what it returns joins tak0 *)
Theorem chin_recv:
  l0_recv f n w = (r, d, w') ∧ l0_chan_of w f = SOME j ∧ chin j tak0 w ⇒ chin j (tak0 ++ d) w'
Proof
  rw[l0_recv_def, AllCaseEqs()] >> gvs[] >>
  TRY (irule chin_upd >> simp[] >> rw[pinchan_def] >> gvs[] >> NO_TAC) >>
  gvs[chin_def, upd_lchan_def, EL_LUPDATE, pinchan_def] >>
  metis_tac[TAKE_DROP, APPEND_ASSOC]
QED

(* Any other recv leaves channel j alone *)
Theorem chin_recv_other:
  l0_recv f n w = (r, d, w') ∧ l0_chan_of w f ≠ SOME j ∧ chin j tak0 w ⇒ chin j tak0 w'
Proof
  rw[l0_recv_def, AllCaseEqs()] >> gvs[] >> irule chin_upd >> simp[]
QED

(* Every call but connect, shutdown and a recv on j's fd *)
Theorem chin_call:
  l0_call n conf bytes w = SOME (FFIreturn bytes' w') ∧ n ≠ «sys_shutdown» ∧
  n ≠ «sys_connect» ∧ chin j tak0 w ∧
  (n = «sys_recv» ⇒ l0_chan_of w (bytes_fd conf) ≠ SOME j) ⇒ chin j tak0 w'
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  TRY (gvs[l0_listen_def, AllCaseEqs()] >> NO_TAC) >>
  TRY (irule chin_ticks >> simp[] >> NO_TAC) >>
  TRY (drule_all chin_recv_other >> simp[] >> NO_TAC) >>
  TRY (gvs[l0_send_def, l0_connerr_def, AllCaseEqs(), fail_def] >>
       irule chin_upd >> simp[pinchan_def] >> NO_TAC) >>
  TRY (gvs[l0_send_def, l0_connerr_def, AllCaseEqs(), fail_def] >> NO_TAC) >>
  TRY (gvs[l0_accept_def, AllCaseEqs(), fail_def] >>
       TRY (irule chin_upd >> simp[pinchan_break]) >> NO_TAC) >>
  gvs[l0_close_def, AllCaseEqs(), fail_def] >> simp[close_fd_def] >> every_case_tac >>
  gvs[] >>
  TRY (irule chin_FOLDL_break >> simp[] >> NO_TAC) >>
  TRY (simp[] >> NO_TAC) >>
  irule chin_upd >> simp[pinchan_def]
QED

(* ------------------------------------------------------------------------
   Queued channels: nothing has been taken from them
   ------------------------------------------------------------------------ *)

Definition qinb_def:
  qinb w ⇔ ∀l p q j. MEM (l, p, q) w.listeners ∧ MEM j q ⇒ chin j [] w
End

Theorem qinb_simple[simp]:
  (qinb (w with hist := h) ⇔ qinb w) ∧ (qinb (w with clock := c) ⇔ qinb w) ∧
  (qinb (w with open_fds := fs) ⇔ qinb w) ∧ (qinb (w with reserved := rs) ⇔ qinb w)
Proof
  simp[qinb_def]
QED

Theorem qinb_upd:
  qinb w ∧ (∀x. pinchan [] x ⇒ pinchan [] (g x)) ⇒ qinb (upd_lchan j g w)
Proof
  rw[qinb_def] >> ‘MEM (l, p, q) w.listeners’ by gvs[upd_lchan_def] >>
  res_tac >> irule chin_upd >> simp[]
QED

(* An update of an open (so not queued) channel *)
Theorem qinb_upd_open:
  qinb w ∧ l0wf w ∧ ALOOKUP w.open_fds f = SOME j ⇒ qinb (upd_lchan j g w)
Proof
  rw[qinb_def] >> ‘MEM (l, p, q) w.listeners’ by gvs[upd_lchan_def] >>
  res_tac >> irule chin_upd >> simp[] >> strip_tac >> gvs[] >>
  metis_tac[open_not_queued]
QED

Theorem qinb_deliver:
  qinb w ⇒ qinb (l0_deliver w a)
Proof
  strip_tac >> Cases_on ‘∃p. a = LIncoming p’
  >- (gvs[] >> rw[l0_deliver_def] >> every_case_tac >> gvs[] >>
      gvs[qinb_def] >> rpt gen_tac >> strip_tac >>
      drule MEM_AFUPDKEY_imp >> strip_tac >> gvs[]
      >- (res_tac >> gvs[chin_def, EL_APPEND1])
      >> pairarg_tac >> gvs[]
      >- (res_tac >> gvs[chin_def, EL_APPEND1])
      >> simp[chin_def, EL_APPEND2, fresh_lchan_def, pinchan_def]) >>
  ‘(l0_deliver w a).listeners = w.listeners’
    by (Cases_on ‘a’ >> gvs[l0_deliver_def] >> rw[upd_lchan_def]) >>
  gvs[qinb_def] >> rpt strip_tac >> irule chin_deliver >> metis_tac[]
QED

Theorem qinb_tick:
  qinb w ⇒ qinb (l0_tick nm w)
Proof
  simp[l0_tick_def] >>
  ‘∀as w. qinb w ⇒ qinb (FOLDL l0_deliver w as)’
    by (Induct >> simp[] >> metis_tac[qinb_deliver]) >>
  rw[] >> first_x_assum irule >> simp[]
QED

Theorem qinb_ticks:
  ∀k w. qinb w ⇒ qinb (l0_ticks nm k w)
Proof
  Induct >> simp[l0_ticks_def] >> metis_tac[qinb_tick]
QED

Theorem qinb_FOLDL_break:
  ∀q w. qinb w ⇒ qinb (FOLDL (λw j. upd_lchan j (break_lchan e F) w) w q)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  irule qinb_upd >> simp[pinchan_break]
QED

Theorem qinb_listen:
  qinb w ∧ l0_listen p w = (x, w') ⇒ qinb w'
Proof
  strip_tac >> gvs[l0_listen_def, AllCaseEqs()] >> gvs[qinb_def] >> rw[] >> gvs[] >>
  metis_tac[]
QED

Theorem qinb_send:
  qinb w ∧ l0wf w ∧ l0_send g bs w = (r, w') ⇒ qinb w'
Proof
  strip_tac >> gvs[l0_send_def, AllCaseEqs()] >>
  TRY (irule qinb_upd >> simp[pinchan_def] >> NO_TAC) >>
  gvs[l0_chan_of_def, AllCaseEqs()] >> irule qinb_upd_open >> metis_tac[]
QED

Theorem qinb_recv:
  qinb w ∧ l0wf w ∧ l0_recv g n w = (r, d, w') ⇒ qinb w'
Proof
  strip_tac >> gvs[l0_recv_def, AllCaseEqs()] >>
  gvs[l0_chan_of_def, AllCaseEqs()] >> irule qinb_upd_open >> metis_tac[]
QED

Theorem qinb_shutdown:
  qinb w ∧ l0wf w ∧ l0_shutdown g w = (r, w') ⇒ qinb w'
Proof
  strip_tac >> gvs[l0_shutdown_def, AllCaseEqs()] >>
  TRY (irule qinb_upd >> simp[pinchan_def] >> NO_TAC) >>
  gvs[l0_chan_of_def, AllCaseEqs()] >> irule qinb_upd_open >> metis_tac[]
QED

Theorem qinb_connerr:
  qinb w ∧ l0_connerr g w = (y, w') ⇒ qinb w'
Proof
  strip_tac >> gvs[l0_connerr_def, AllCaseEqs()] >> irule qinb_upd >> simp[pinchan_def]
QED

Theorem qinb_close:
  qinb w ∧ l0_close g w = (r, w') ⇒ qinb w'
Proof
  strip_tac >> gvs[l0_close_def, AllCaseEqs()] >> simp[close_fd_def] >> every_case_tac >> gvs[] >>
  TRY (irule qinb_upd >> simp[pinchan_def] >> NO_TAC) >>
  irule qinb_FOLDL_break >> gvs[qinb_def, MEM_FILTER] >> metis_tac[]
QED

Theorem qinb_pop:
  qinb w ∧ FILTER (λ(l', p, q). l' = l) w.listeners = (x, p, j :: q') :: t ⇒
  qinb (w with listeners := AFUPDKEY l (K (p, q')) w.listeners)
Proof
  simp[qinb_def] >> strip_tac >>
  ‘MEM (x, p, j :: q') w.listeners ∧ x = l’
    by (qpat_x_assum ‘FILTER _ _ = _’ (mp_tac o Q.AP_TERM ‘MEM (x, p, j :: q')’) >>
        simp[MEM_FILTER]) >>
  rpt gen_tac >> strip_tac >>
  drule MEM_AFUPDKEY_imp >> strip_tac >- (res_tac >> simp[]) >>
  gvs[] >> metis_tac[MEM]
QED

Theorem qinb_accept:
  qinb w ∧ l0_accept g w = (r, w') ⇒ qinb w'
Proof
  strip_tac >> gvs[l0_accept_def, AllCaseEqs(), fail_def] >>
  drule_all qinb_pop >> strip_tac >>
  TRY (irule qinb_upd >> simp[pinchan_break] >> NO_TAC) >>
  fs[qinb_def] >> metis_tac[]
QED

Theorem qinb_call:
  l0_call n conf bytes w = SOME (FFIreturn bytes' w') ∧ n ≠ «sys_connect» ∧
  qinb w ∧ l0wf w ⇒ qinb w'
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac qinb_listen >> imp_res_tac qinb_send >> imp_res_tac qinb_recv >>
  imp_res_tac qinb_shutdown >> imp_res_tac qinb_connerr >> imp_res_tac qinb_close >>
  imp_res_tac qinb_accept >> gvs[qinb_ticks]
QED

Theorem wpres_qinb:
  wpres qinb
Proof
  rw[wpres_def] >- (irule qinb_tick >> simp[]) >>
  drule_all qinb_call >> simp[]
QED

(* ------------------------------------------------------------------------
   One fd: while f is open, tak0 was taken from its channel
   ------------------------------------------------------------------------ *)

Definition finb_def:
  finb f tak0 w ⇔ ∀j. ALOOKUP w.open_fds f = SOME j ⇒ chin j tak0 w
End

Theorem finb_tick:
  finb f tak0 w ⇒ finb f tak0 (l0_tick nm w)
Proof
  rw[finb_def] >> irule chin_tick >> gvs[l0_tick_def] >>
  ‘∀as w. (FOLDL l0_deliver w as).open_fds = w.open_fds’
    by (Induct >> simp[] >> rpt gen_tac >> Cases_on ‘h’ >>
        rw[l0_deliver_def] >> every_case_tac >> simp[upd_lchan_def]) >>
  gvs[]
QED

Theorem finb_ticks:
  ∀k w. finb f tak0 w ⇒ finb f tak0 (l0_ticks nm k w)
Proof
  Induct >> simp[l0_ticks_def] >> metis_tac[finb_tick]
QED

Theorem finb_hist[simp]:
  finb f tak0 (w with hist := h) ⇔ finb f tak0 w
Proof
  simp[finb_def]
QED

Theorem FOLDL_break_open_fds:
  ∀q w. (FOLDL (λw j. upd_lchan j (break_lchan e F) w) w q).open_fds = w.open_fds
Proof
  Induct >> simp[] >> simp[upd_lchan_def]
QED

Theorem ops_open_fds:
  (l0_send g bs w = (r, w') ⇒ w'.open_fds = w.open_fds) ∧
  (l0_recv g n w = (r, d, w') ⇒ w'.open_fds = w.open_fds) ∧
  (l0_connerr g w = (y, w') ⇒ w'.open_fds = w.open_fds) ∧
  (l0_close g w = (r, w') ⇒ ∀f j. ALOOKUP w'.open_fds f = SOME j ⇒ ALOOKUP w.open_fds f = SOME j)
Proof
  rpt conj_tac >> strip_tac
  >- gvs[l0_send_def, AllCaseEqs(), fail_def, upd_lchan_def]
  >- gvs[l0_recv_def, AllCaseEqs(), fail_def, upd_lchan_def]
  >- gvs[l0_connerr_def, AllCaseEqs(), fail_def, upd_lchan_def]
  >> gvs[l0_close_def, AllCaseEqs(), fail_def] >> rw[close_fd_def] >>
  every_case_tac >> gvs[upd_lchan_def, ALOOKUP_ADELKEY, FOLDL_break_open_fds] >>
  rw[] >> gvs[]
QED

(* Every call but connect, shutdown, accept, and a recv on f *)
Theorem finb_call:
  l0_call n conf bytes w = SOME (FFIreturn bytes' w') ∧ n ≠ «sys_shutdown» ∧
  n ≠ «sys_connect» ∧ n ≠ «sys_accept» ∧ l0wf w ∧ finb f tak0 w ∧
  ¬(n = «sys_recv» ∧ bytes_fd conf = f) ⇒ finb f tak0 w'
Proof
  rw[finb_def] >>
  ‘ALOOKUP w.open_fds f = SOME j’
    by (gvs[l0_call_def, AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
        TRY (gvs[l0_listen_def, AllCaseEqs()] >> NO_TAC) >>
        TRY (‘∀k w. (l0_ticks «sys_poll» k w).open_fds = w.open_fds’
               by (Induct >> simp[l0_ticks_def, l0_tick_def] >> rpt gen_tac >>
                   ‘∀as w. (FOLDL l0_deliver w as).open_fds = w.open_fds’
                     by (Induct >> simp[] >> rpt gen_tac >> Cases_on ‘h’ >>
                         rw[l0_deliver_def] >> every_case_tac >> simp[upd_lchan_def]) >>
                   simp[]) >> gvs[] >> NO_TAC) >>
        imp_res_tac ops_open_fds >> gvs[]) >>
  irule chin_call >> simp[] >>
  goal_assum drule >> simp[] >> rpt strip_tac >> gvs[] >>
  gvs[l0_chan_of_def, AllCaseEqs()] >>
  metis_tac[open_chan_ne]
QED

(* A recv on f: what it returned joins tak0 *)
Theorem finb_recv:
  l0_recv f n w = (r, d, w') ∧ finb f tak0 w ⇒ finb f (tak0 ++ d) w'
Proof
  rw[finb_def] >>
  ‘ALOOKUP w.open_fds f = SOME j’
    by gvs[l0_recv_def, AllCaseEqs(), fail_def, upd_lchan_def] >>
  res_tac >> irule chin_recv >> qexistsl [‘f’, ‘n’, ‘r’, ‘w’] >>
  gvs[l0_chan_of_def, chin_def]
QED

(* An accept: it returns f, with nothing taken from f's channel yet (it
   was queued), or it leaves f as it was *)
Theorem finb_accept:
  l0_accept g w = (r, w') ∧ finb f tak0 w ∧ qinb w ⇒
  (∃k. r = Ok k ∧ n2w k = f ∧ finb f [] w') ∨ ((∀k. r = Ok k ⇒ n2w k ≠ f) ∧ finb f tak0 w')
Proof
  rw[l0_accept_def, AllCaseEqs(), fail_def] >> gvs[] >>
  TRY (gvs[finb_def] >> rw[] >> res_tac >>
       TRY (irule chin_upd >> simp[pinchan_break]) >> gvs[chin_def] >> NO_TAC) >>
  rename1 ‘FILTER _ _ = (lx, p, j :: q') :: _’ >>
  ‘MEM (lx, p, j :: q') w.listeners’
    by (‘MEM (lx, p, j :: q') (FILTER (λ(l',p,q). l' = g) w.listeners)’ by simp[] >>
        fs[MEM_FILTER]) >>
  TRY (gvs[finb_def] >> rpt strip_tac >> gvs[upd_lchan_def] >> res_tac >>
       gvs[chin_def, EL_LUPDATE] >> rw[] >> irule pinchan_break >> simp[] >> NO_TAC) >>
  rename1 ‘l0_alloc w = SOME f'’ >>
  Cases_on ‘f' = f’ >> gvs[finb_def, qinb_def] >> metis_tac[MEM]
QED

(* ------------------------------------------------------------------------
   L1's calls
   ------------------------------------------------------------------------ *)

Theorem finb_do:
  winv w ∧ finb f tak0 w ∧ n ≠ «sys_connect» ∧ n ≠ «sys_shutdown» ∧ n ≠ «sys_accept» ∧
  ¬(n = «sys_recv» ∧ bytes_fd conf = f) ∧
  l0_do n conf alen w = SOME (out, w', ev) ⇒ finb f tak0 w'
Proof
  strip_tac >> drule l0_do_cases >> strip_tac >> gvs[] >>
  irule finb_call >> qexistsl_tac [‘REPLICATE alen 0w’, ‘out’, ‘conf’, ‘n’] >>
  simp[] >> qexists_tac ‘l0_tick n w’ >>
  gvs[winv_def, l0wf_tick, finb_tick]
QED

Theorem finb_do_buf:
  winv w ∧ finb f tak0 w ∧ n ≠ «sys_connect» ∧ n ≠ «sys_shutdown» ∧ n ≠ «sys_accept» ∧
  ¬(n = «sys_recv» ∧ bytes_fd conf = f) ∧
  l0_do_buf n conf bs w = SOME (out, w', ev) ⇒ finb f tak0 w'
Proof
  strip_tac >> drule l0_do_buf_cases >> strip_tac >> gvs[] >>
  irule finb_call >> qexistsl_tac [‘bs’, ‘out’, ‘conf’, ‘n’] >>
  simp[] >> qexists_tac ‘l0_tick n w’ >>
  gvs[winv_def, l0wf_tick, finb_tick]
QED

Theorem sys_finb:
  (winv w ∧ finb f tak0 w ∧ sys_send g bs w = SOME (out, w', ev) ⇒ finb f tak0 w') ∧
  (winv w ∧ finb f tak0 w ∧ sys_close g w = SOME (out, w', ev) ⇒ finb f tak0 w') ∧
  (winv w ∧ finb f tak0 w ∧ g ≠ f ∧ sys_recv g k w = SOME (out, w', ev) ⇒ finb f tak0 w') ∧
  (winv w ∧ finb f tak0 w ∧ sys_poll fes w = SOME (out, w', ev) ⇒ finb f tak0 w')
Proof
  rw[sys_close_def, sys_send_def, sys_recv_def, sys_poll_def] >>
  TRY (drule_at (Pos last) finb_do_buf >> simp[] >> NO_TAC) >>
  drule_at (Pos last) finb_do >> simp[]
QED

(* What a recv returned, as L1 reads it back (its log's FData) *)
Definition rdata_def:
  rdata out = case l0_res_of out of Ok m => TAKE m (DROP 13 out) | _ => []
End

Theorem recv_data:
  l0_rely w ∧ l0_recv f n w = (r, d, w') ⇒
  (∀m. r = Ok m ⇒ LENGTH d = m) ∧ (∀e x. r = Fail e x ⇒ d = [])
Proof
  rw[l0_recv_def, AllCaseEqs(), fail_def] >> gvs[not_chan_def] >>
  TRY (every_case_tac >> gvs[fail_def] >> NO_TAC) >>
  rename1 ‘l0_chan_of w f = SOME j’ >>
  ‘0 < LENGTH (EL j w.chans).inbox’ by (Cases_on ‘(EL j w.chans).inbox’ >> fs[]) >>
  qpat_x_assum ‘l0_rely _’ (strip_assume_tac o REWRITE_RULE [l0_rely_def]) >>
  first_x_assum (qspecl_then [‘j’, ‘w.hist’, ‘LENGTH (EL j w.chans).inbox’] mp_tac) >>
  simp[]
QED

Theorem sys_recv_finb:
  winv w ∧ finb f tak0 w ∧ k < 256 ** 8 ∧ sys_recv f k w = SOME (out, w', ev) ⇒
  finb f (tak0 ++ rdata out) w'
Proof
  rw[sys_recv_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  qabbrev_tac ‘wt = l0_tick «sys_recv» w’ >>
  ‘finb f tak0 wt ∧ l0_rely wt’
    by (gvs[Abbr ‘wt’, winv_def, finb_tick] >>
        irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def, l0_hdr_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  ‘l0_res_ok r’
    by (qspecl_then [‘wt’, ‘f’, ‘k’, ‘r’, ‘d’, ‘w'’] mp_tac
          (Q.GENL [‘w’, ‘f’, ‘n’, ‘r’, ‘d’, ‘w'’] recv_res_ok) >> simp[]) >>
  ‘l0_res_of (enc_res r ++ d ++ REPLICATE (k − LENGTH d) 0w) = r’
    by (REWRITE_TAC [GSYM APPEND_ASSOC] >> irule l0_res_of_enc_app >> simp[]) >>
  ‘DROP 13 (enc_res r ++ d ++ REPLICATE (k − LENGTH d) 0w) =
   d ++ REPLICATE (k − LENGTH d) 0w’
    by (‘LENGTH (enc_res r) = 13’ by (irule LENGTH_enc_res >> simp[]) >>
        REWRITE_TAC [GSYM APPEND_ASSOC] >>
        qpat_x_assum ‘LENGTH _ = 13’ (SUBST1_TAC o SYM) >> simp[DROP_APPEND, DROP_LENGTH_NIL] >>
        ‘LENGTH (enc_res r) − (LENGTH d + LENGTH (enc_res r)) = 0’ by decide_tac >>
        simp[]) >>
  drule_all recv_data >> strip_tac >>
  drule_all finb_recv >> strip_tac >>
  ‘rdata (enc_res r ++ d ++ REPLICATE (k − LENGTH d) 0w) = d’
    by (simp[rdata_def] >> Cases_on ‘r’ >> gvs[TAKE_LENGTH_APPEND]) >>
  simp[]
QED

Theorem sys_accept_finb:
  winv w ∧ finb f tak0 w ∧ qinb w ∧ sys_accept g w = SOME (out, w', ev) ⇒
  (∃k. l0_res_of out = Ok k ∧ n2w k = f ∧ finb f [] w') ∨
  ((∀k. l0_res_of out = Ok k ⇒ n2w k ≠ f) ∧ finb f tak0 w')
Proof
  rw[sys_accept_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  qabbrev_tac ‘wt = l0_tick «sys_accept» w’ >>
  ‘finb f tak0 wt ∧ qinb wt ∧ l0_rely wt’
    by (gvs[Abbr ‘wt’, winv_def, finb_tick, qinb_tick] >>
        irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def, l0_hdr_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule_all l0_accept_res >> strip_tac >>
  ‘l0_res_of (enc_res r) = r’ by (irule l0_res_of_enc >> simp[]) >>
  drule_all finb_accept >> simp[]
QED

(* A recv on an fd that is not open returns no data *)
Theorem sys_recv_notopen:
  winv w ∧ ALOOKUP w.open_fds f = NONE ∧ k < 256 ** 8 ∧ sys_recv f k w = SOME (out, w', ev) ⇒
  rdata out = []
Proof
  rw[sys_recv_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  qabbrev_tac ‘wt = l0_tick «sys_recv» w’ >>
  ‘l0_rely wt ∧ ALOOKUP wt.open_fds f = NONE’
    by (gvs[Abbr ‘wt’, winv_def] >> irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def, l0_hdr_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  ‘l0_res_ok r’
    by (qspecl_then [‘wt’, ‘f’, ‘k’, ‘r’, ‘d’, ‘w'’] mp_tac
          (Q.GENL [‘w’, ‘f’, ‘n’, ‘r’, ‘d’, ‘w'’] recv_res_ok) >> simp[]) >>
  ‘∃e x. r = Fail e x ∧ d = []’
    by (gvs[l0_recv_def, l0_chan_of_def, not_chan_def, fail_def, AllCaseEqs()] >> rw[]) >>
  gvs[rdata_def] >>
  ‘l0_res_of (enc_res (Fail e x) ++ REPLICATE k 0w) = Fail e x’
    by (irule l0_res_of_enc_app >> simp[]) >>
  simp[]
QED

Theorem l1_close_finb:
  l1_close g (w, st) = SOME ((w', st'), evs) ∧ winv w ∧ finb f tak0 w ⇒ finb f tak0 w'
Proof
  rw[l1_close_def, AllCaseEqs()] >> metis_tac[sys_finb]
QED

Theorem pdo_finb:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ winv w ∧ finb f tak0 w ⇒ finb f tak0 w'
Proof
  strip_tac >> Cases_on ‘a’ >> gvs[pdo_def, AllCaseEqs()] >>
  TRY (PairCases_on ‘z’) >> gvs[] >>
  rpt (qpat_x_assum ‘l1do _ _ _ = _’ mp_tac) >> rpt (qpat_x_assum ‘l1_close _ _ = _’ mp_tac) >>
  simp[l1do_def, l1_close_def, AllCaseEqs()] >> rw[] >> metis_tac[sys_finb]
QED

Theorem pacts_finb:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ winv w ∧ finb f tak0 w ⇒
    finb f tak0 w'
Proof
  Induct >> simp[pacts_def] >> rw[AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  metis_tac[pdo_finb, pdo_winv]
QED

Theorem l1_polls_finb:
  ∀chs w rv w' evs. l1_polls chs w = SOME (rv, w', evs) ∧ winv w ∧ finb f tak0 w ⇒
    finb f tak0 w'
Proof
  Induct >> simp[l1_polls_def] >> rw[AllCaseEqs()] >> metis_tac[sys_finb, sys_winv]
QED

Theorem l1_flush_finb:
  ∀fs w st w' st' evs. l1_flush fs (w, st) = SOME ((w', st'), evs) ∧ winv w ∧
    finb f tak0 w ⇒ finb f tak0 w'
Proof
  Induct >> simp[l1_flush_def] >> rw[AllCaseEqs()] >> metis_tac[sys_finb, sys_winv]
QED

Theorem l1_reap_finb:
  ∀fs w st w' st' evs. l1_reap fs (w, st) = SOME ((w', st'), evs) ∧ winv w ∧
    finb f tak0 w ⇒ finb f tak0 w'
Proof
  Induct >> simp[l1_reap_def] >> rw[AllCaseEqs()] >> TRY (Cases_on ‘ws’) >>
  metis_tac[l1_close_finb, l1_close_winv]
QED

Theorem fdata_simps[simp]:
  fdata f [] = [] ∧ fdata f (xs ++ ys) = fdata f xs ++ fdata f ys ∧
  fdata f (FData g bs :: l) = (if g = f then bs else []) ++ fdata f l ∧
  fdata f (FEof g :: l) = fdata f l ∧ fdata f (FReset g :: l) = fdata f l ∧
  fdata f (FConn g :: l) = fdata f l
Proof
  simp[fdata_def]
QED

(* The fetch: its recvs on f join tak0; an accept that returns f starts
   afresh (nothing was taken from a queued channel) *)
Theorem pf_fetch_finb:
  ∀fs w ps w' ps' log evs tak0.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ winv w ∧ qinb w ∧
    finb f tak0 w ⇒
    finb f (if MEM (FConn f) log then fdata f log else tak0 ++ fdata f log) w'
Proof
  Induct >- simp[pf_fetch_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ mp_tac >> simp[Once pf_fetch_def] >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  IF_CASES_TAC
  >- ((* the accept *)
      simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
      rename1 ‘sys_accept _ _ = SOME (out, w1, ev)’ >>
      ‘winv w1’ by (drule_all (cj 4 sys_winv) >> simp[]) >>
      ‘qinb w1’ by (mp_tac wpres_qinb >> strip_tac >> drule_all sys_wpres >> strip_tac >> res_tac) >>
      drule_all sys_accept_finb >> strip_tac >>
      Cases_on ‘l0_res_of out’ >> gvs[AllCaseEqs()] >>
      first_x_assum drule_all >> every_case_tac >> gvs[]) >>
  (* a recv *)
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 ‘sys_recv _ _ _ = SOME (out, w1, ev)’ >>
  ‘winv w1’ by (drule_all (cj 3 sys_winv) >> simp[]) >>
  ‘qinb w1’ by (mp_tac wpres_qinb >> strip_tac >> drule_all sys_wpres >> strip_tac >> res_tac) >>
  Cases_on ‘h = f’
  >- (gvs[] >>
      ‘pf_chunk < 256 ** 8’ by simp[pf_chunk_def] >>
      drule_all sys_recv_finb >> strip_tac >>
      ‘MEM f (l0_used w1) ∨ rdata out = []’
        by (Cases_on ‘ALOOKUP w.open_fds f’
            >- (disj2_tac >> drule_all sys_recv_notopen >> simp[]) >>
            disj1_tac >> gvs[sys_recv_def] >> drule l0_do_used >> simp[] >> strip_tac >>
            simp[l0_used_def] >> imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >>
            metis_tac[]) >>
      qpat_x_assum ‘∀w ps w' ps' log evs tak0. _’ mp_tac >>
      Cases_on ‘l0_res_of out’ >> fs[rdata_def] >>
      TRY (rename1 ‘l0_res_of out = Ok n’ >> Cases_on ‘0 < n’) >>
      TRY (rename1 ‘l0_res_of out = Fail e x’ >> Cases_on ‘l1_transient e’) >>
      fs[AllCaseEqs()] >> rveq >>
      disch_then drule_all >> rw[] >> fs[] >>
      TRY (‘TAKE n (DROP 13 out) = []’
             by (‘DROP 13 out = []’ by (irule DROP_LENGTH_TOO_LONG >> fs[]) >>
                 asm_rewrite_tac[] >> simp[]) >>
           pop_assum SUBST1_TAC >> fs[] >> NO_TAC) >>
      drule_all pf_fetch_conns >> simp[log_conns_FConn]) >>
  ‘finb f tak0 w1’ by (drule_all (cj 3 sys_finb) >> simp[]) >>
  qpat_x_assum ‘∀w ps w' ps' log evs tak0. _’ mp_tac >>
  Cases_on ‘l0_res_of out’ >> fs[] >>
  TRY (rename1 ‘l0_res_of out = Ok n’ >> Cases_on ‘0 < n’) >>
  TRY (rename1 ‘l0_res_of out = Fail e x’ >> Cases_on ‘l1_transient e’) >>
  fs[AllCaseEqs()] >> rveq >>
  disch_then drule_all >> simp[]
QED

(* One round: what it fetched on f joins tak0; a round that (pre-)accepts
   f starts afresh *)
Theorem pround_finb:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧ winv w ∧ qinb w ∧
  finb f tak0 w ⇒
  finb f (if MEM (FConn f) log then fdata f log else tak0 ++ fdata f log) w'
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >>
  gvs[pf_tail_def, AllCaseEqs()] >>
  ‘winv ws10 ∧ qinb ws10 ∧ finb f tak0 ws10’
    by metis_tac[pacts_winv, pacts_wpres, wpres_qinb, pacts_finb] >>
  ‘winv w1 ∧ qinb w1 ∧ finb f tak0 w1’
    by metis_tac[l1_polls_winv, l1_polls_wpres, wpres_qinb, l1_polls_finb] >>
  ‘winv w2 ∧ qinb w2 ∧ finb f tak0 w2’
    by metis_tac[l1_flush_winv, l1_flush_wpres, wpres_qinb, l1_flush_finb] >>
  drule_all pf_fetch_finb >> strip_tac >>
  ‘winv w3’ by metis_tac[pf_fetch_winv] >>
  drule_all l1_reap_finb >> simp[]
QED

(* The round that (pre-)accepts f: f is not open when its fetch starts
   (an accept returns a free fd), so the round ends with what it fetched
   on f *)
Theorem pround_finb_conn:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧ winv w ∧ qinb w ∧
  MEM (FConn f) log ⇒
  finb f (fdata f log) w'
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >>
  gvs[pf_tail_def, AllCaseEqs()] >>
  ‘winv ws10 ∧ qinb ws10’ by metis_tac[pacts_winv, pacts_wpres, wpres_qinb] >>
  ‘winv w1 ∧ qinb w1’ by metis_tac[l1_polls_winv, l1_polls_wpres, wpres_qinb] >>
  ‘winv w2 ∧ qinb w2’ by metis_tac[l1_flush_winv, l1_flush_wpres, wpres_qinb] >>
  ‘finb f [] w2’
    by (simp[finb_def] >> rpt strip_tac >>
        ‘MEM f (l0_used w2)’
          by (simp[l0_used_def] >> imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >>
              metis_tac[]) >>
        drule_all pf_fetch_conns >> simp[log_conns_FConn]) >>
  drule_all pf_fetch_finb >> simp[] >> strip_tac >>
  ‘winv w3’ by metis_tac[pf_fetch_winv] >>
  drule_all l1_reap_finb >> simp[]
QED

(* The start: no listener, or no queued connection with anything taken *)
Theorem qinb_start:
  w.listeners = [] ⇒ qinb w
Proof
  simp[qinb_def]
QED

Theorem run_qinb:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ qinb w0 ⇒ ∀n. qinb (rworld lfd pol ifds m w0 n)
Proof
  strip_tac >> irule run_wpres >> simp[wpres_qinb]
QED

(* MAIN (the input side of R1, for the echo chain): if L1 (pre-)accepted f
   at round a, and has not accepted it again since, then at every later
   round n, what f's channel's peer sent is what L1 fetched on f in rounds
   a … n − 1, then the channel's kernel inbox; unless the channel broke and
   its inbox was flushed *)
Theorem run_peer_sent:
  oassm lfd pol ifds m w0 ∧ qinb w0 ∧
  MEM (FConn f) (rlog lfd pol ifds m w0 a) ∧
  (∀k. a < k ∧ k < n ⇒ ¬MEM (FConn f) (rlog lfd pol ifds m w0 k)) ∧ a < n ∧
  l0_chan_of (rworld lfd pol ifds m w0 n) f = SOME c ⇒
  (EL c (rworld lfd pol ifds m w0 n).chans).peer_sent =
    fdata f (rlogs lfd pol ifds m w0 a (n − a)) ++
    (EL c (rworld lfd pol ifds m w0 n).chans).inbox ∨
  flushed (rworld lfd pol ifds m w0 n) f
Proof
  strip_tac >> fs[oassm_def] >>
  ‘∀k. winv (rworld lfd pol ifds m w0 k) ∧ qinb (rworld lfd pol ifds m w0 k)’
    by metis_tac[winv_run, run_qinb] >>
  ‘∀d. 0 < d ∧ (∀k. a < k ∧ k < a + d ⇒ ¬MEM (FConn f) (rlog lfd pol ifds m w0 k)) ⇒
       finb f (fdata f (rlogs lfd pol ifds m w0 a d)) (rworld lfd pol ifds m w0 (a + d))’
    by (Induct >> simp[] >> strip_tac >>
        drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘a + d’] strip_assume_tac) >>
        Cases_on ‘d = 0’
        >- (gvs[] >>
            ‘rlogs lfd pol ifds m w0 a 1 = rlog lfd pol ifds m w0 a’
              by simp[rlogs_def] >>
            drule pround_finb_conn >> simp[ADD1]) >>
        ‘finb f (fdata f (rlogs lfd pol ifds m w0 a d)) (rworld lfd pol ifds m w0 (a + d))’
          by (first_x_assum irule >> simp[]) >>
        ‘¬MEM (FConn f) (rlog lfd pol ifds m w0 (a + d))’ by (first_x_assum irule >> simp[]) >>
        drule pround_finb >> simp[] >>
        disch_then (qspecl_then [‘fdata f (rlogs lfd pol ifds m w0 a d)’, ‘f’] mp_tac) >>
        simp[ADD_CLAUSES, pars_rlogs_SUC]) >>
  first_x_assum (qspec_then ‘n − a’ mp_tac) >> simp[] >>
  TRY (impl_tac >- (rpt strip_tac >> first_x_assum irule >> simp[])) >>
  rw[finb_def] >>
  ‘ALOOKUP (rworld lfd pol ifds m w0 n).open_fds f = SOME c’
    by gvs[l0_chan_of_def, AllCaseEqs()] >>
  first_x_assum drule >> rw[chin_def, pinchan_def, flushed_def] >> gvs[]
QED
