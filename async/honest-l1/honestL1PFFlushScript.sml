(*
  R1-live, the output side (moonshot step 8; design/36 §6, correction of
  D15): if f's peer drains and nothing new is written to f, f's outbox
  shrinks.  This is what S4 ("writes don't outrun the client") rests on.

  The argument: with nothing sent to c, the peer reads what is in flight
  (drains); with nothing in flight, the kernel takes a byte ([F2]), so a
  poll that asks for f's output reports it writable; L1 flushes f; and by
  [F1] some send on f is not retried, so it takes a byte (a send of a
  non-empty buffer that takes none fails with EAGAIN) or fails hard (the
  outbox is dropped).

  L0 level first: a channel's in-flight bytes grow only by what a send on
  its fd takes; a broken channel stays broken; L1 never shuts a channel
  down.
*)
Theory honestL1PFFlush
Ancestors
  honestL1PFOut honestL0WorldProps honestL1PFConnRun honestL1PFConn honestL1PFClient
  honestL1PFLive honestL1PFRound honestL1PFRefine honestL1PFInv honestL1PFModel
  honestL1Steps honestL1Inv honestL1Props honestL1Model honestL0WorldInv honestL0Rely honestL0World
  honestL0 socketV2FFI asyncHLModel asyncCore Marshalling
Libs
  preamble

(* ------------------------------------------------------------------------
   The hypotheses
   ------------------------------------------------------------------------ *)

(* [F2] (D12, trusted): with nothing in flight, a send of n > 0 bytes
   takes at least one ([P 2.10.7]: "as much as is available") *)
Definition F2_def:
  F2 (w0 : l0world) ⇔ ∀j h k. 0 < k ⇒ 0 < w0.ch.takes j h 0 k
End

(* D(c), made precise (design/36 §6): if nothing more is sent on channel
   j from round n on, the peer eventually reads everything in flight *)
Definition drains_def:
  drains lfd pol ifds m w0 j ⇔
    ∀n. (∀k. n ≤ k ⇒ csent (rworld lfd pol ifds m w0 k) j = csent (rworld lfd pol ifds m w0 n) j) ⇒
        ∃n'. n ≤ n' ∧ (EL j (rworld lfd pol ifds m w0 n').chans).inflight = 0
End

(* The actions L2 issues in round n *)
Definition racts_def:
  racts lfd pol ifds m w0 n = new_actions (log_of m) (rhist lfd pol ifds m w0 n)
End

(* ------------------------------------------------------------------------
   L0: a channel's flow.  Its in-flight bytes grow only by what sends take
   (which its sent records), it stays broken once broken, and its shut
   flag changes only by a shutdown or a close of its own fd
   ------------------------------------------------------------------------ *)

Definition cflow_def:
  cflow w w' c ⇔
    (EL c w'.chans).inflight + LENGTH (csent w c) ≤
      (EL c w.chans).inflight + LENGTH (csent w' c) ∧
    ((EL c w.chans).broken ⇒ (EL c w'.chans).broken) ∧
    (EL c w'.chans).shut = (EL c w.chans).shut ∧ w'.ch = w.ch
End

Theorem cflow_refl[simp]:
  cflow w w c
Proof
  simp[cflow_def]
QED

Theorem cflow_trans:
  cflow w1 w2 c ∧ cflow w2 w3 c ⇒ cflow w1 w3 c
Proof
  rw[cflow_def] >> decide_tac
QED

Theorem cflow_deliver:
  c < LENGTH w.chans ⇒ cflow w (l0_deliver w a) c
Proof
  strip_tac >> drule csent_deliver >> disch_then (qspec_then ‘a’ strip_assume_tac) >>
  simp[cflow_def] >>
  Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >>
  gvs[upd_lchan_def, EL_LUPDATE, EL_APPEND1] >> rw[] >> gvs[break_lchan_def] >> rw[]
QED

Theorem cflow_tick:
  c < LENGTH w.chans ⇒ cflow w (l0_tick nm w) c
Proof
  simp[l0_tick_def] >>
  ‘∀as w. c < LENGTH w.chans ⇒
          c < LENGTH (FOLDL l0_deliver w as).chans ∧ cflow w (FOLDL l0_deliver w as) c’
    by (Induct >> simp[] >> rpt gen_tac >> strip_tac >>
        drule csent_deliver >> disch_then (qspec_then ‘h’ strip_assume_tac) >>
        ‘cflow w (l0_deliver w h) c’ by simp[cflow_deliver] >>
        first_x_assum drule >> strip_tac >> simp[] >>
        irule cflow_trans >> qexists_tac ‘l0_deliver w h’ >> simp[]) >>
  strip_tac >> first_x_assum (qspecl_then [‘w.env w.clock w.hist nm’,
                                            ‘w with clock := w.clock + 1’] mp_tac) >>
  simp[] >> strip_tac >> gvs[cflow_def, csent_def]
QED

Theorem cflow_ticks:
  ∀k w. c < LENGTH w.chans ⇒ c < LENGTH (l0_ticks nm k w).chans ∧ cflow w (l0_ticks nm k w) c
Proof
  Induct >> simp[l0_ticks_def] >> rpt gen_tac >> strip_tac >>
  ‘c < LENGTH (l0_tick nm w).chans’ by (drule csent_tick >> simp[]) >>
  first_x_assum drule >> strip_tac >> simp[] >>
  irule cflow_trans >> qexists_tac ‘l0_tick nm w’ >> simp[cflow_tick]
QED

Theorem cflow_FOLDL_break:
  ∀q w. c < LENGTH w.chans ⇒
        c < LENGTH (FOLDL (λw j. upd_lchan j (break_lchan e F) w) w q).chans ∧
        cflow w (FOLDL (λw j. upd_lchan j (break_lchan e F) w) w q) c
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  ‘c < LENGTH (upd_lchan h (break_lchan e F) w).chans ∧
   cflow w (upd_lchan h (break_lchan e F) w) c’
    by (simp[cflow_def, csent_def, upd_lchan_def] >> rw[EL_LUPDATE] >>
        rw[break_lchan_def]) >>
  first_x_assum drule >> metis_tac[cflow_trans]
QED

(* The calls other than send, connect and shutdown, and a close of
   another fd: no flow on f's channel *)
Theorem cflow_ops:
  l0wf w ∧ l0_chan_of w f = SOME c ⇒
  (l0_listen p w = (x, w') ⇒ cflow w w' c) ∧
  (l0_recv g n w = (r, d, w') ⇒ cflow w w' c) ∧
  (l0_connerr g w = (y, w') ⇒ cflow w w' c) ∧
  (l0_close g w = (r, w') ∧ g ≠ f ⇒ cflow w w' c)
Proof
  strip_tac >> ‘c < LENGTH w.chans’ by metis_tac[chan_lt] >>
  rpt conj_tac >> strip_tac
  >- gvs[l0_listen_def, AllCaseEqs(), cflow_def, csent_def]
  >- (gvs[l0_recv_def, AllCaseEqs()] >> rw[] >>
      simp[cflow_def, csent_def, upd_lchan_def] >> rw[EL_LUPDATE])
  >- (gvs[l0_connerr_def, AllCaseEqs()] >> rw[] >>
      simp[cflow_def, csent_def, upd_lchan_def] >> rw[EL_LUPDATE])
  >> gvs[l0_close_def, AllCaseEqs()] >> simp[close_fd_def] >> every_case_tac >>
  TRY (irule cflow_trans >>
       qexists_tac ‘w with listeners := FILTER (λ(l,p,q). l ≠ g) w.listeners’ >>
       conj_tac >- simp[cflow_def, csent_def] >>
       irule (cj 2 (SPEC_ALL cflow_FOLDL_break)) >> simp[] >> NO_TAC) >>
  TRY (simp[cflow_def, csent_def] >> NO_TAC) >>
  rename1 ‘l0_chan_of w g = SOME j’ >>
  ‘j ≠ c’ by (gvs[l0_chan_of_def, AllCaseEqs()] >> metis_tac[open_chan_ne]) >>
  simp[cflow_def, csent_def, upd_lchan_def] >> rw[EL_LUPDATE]
QED

Theorem cflow_accept:
  l0_accept l w = (r, w') ∧ c < LENGTH w.chans ⇒ cflow w w' c
Proof
  rw[l0_accept_def] >> gvs[AllCaseEqs(), fail_def] >> rw[] >>
  simp[cflow_def, csent_def, upd_lchan_def] >> rw[EL_LUPDATE] >> rw[break_lchan_def]
QED

Theorem cflow_send:
  l0_send g bs w = (r, w') ∧ l0_chan_of w f = SOME c ∧ l0wf w ⇒ cflow w w' c
Proof
  rw[l0_send_def] >> gvs[AllCaseEqs(), fail_def] >> rw[] >>
  ‘c < LENGTH w.chans’ by metis_tac[chan_lt] >>
  simp[cflow_def, csent_def, upd_lchan_def] >> rw[EL_LUPDATE] >>
  simp[LENGTH_TAKE_EQ, MIN_DEF] >> rw[]
QED

Theorem cflow_call:
  l0_chan_of w f = SOME c ∧ l0wf w ∧ fds_lt w ∧ l0_rely w ∧
  n ≠ «sys_connect» ∧ n ≠ «sys_shutdown» ∧ ¬(n = «sys_close» ∧ bytes_fd conf = f) ∧
  l0_call n conf bytes w = SOME (FFIreturn bytes' w') ⇒
  l0_chan_of w' f = SOME c ∧ cflow w w' c ∧
  (¬(n = «sys_send» ∧ bytes_fd (TAKE 8 conf) = f) ⇒ csent w' c = csent w c)
Proof
  strip_tac >> ‘c < LENGTH w.chans’ by metis_tac[chan_lt] >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >>
  rw[l0_call_def] >> gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac csent_ops >> imp_res_tac cflow_ops >> gvs[] >>
  TRY (rename1 ‘l0_ticks _ k w’ >>
       qspecl_then [‘k’, ‘w’] mp_tac
         (Q.GENL [‘k’, ‘w’] (Q.INST [‘nm’ |-> ‘«sys_poll»’] (SPEC_ALL csent_ticks))) >>
       simp[] >> strip_tac >>
       qspecl_then [‘k’, ‘w’] mp_tac
         (Q.GENL [‘k’, ‘w’] (Q.INST [‘nm’ |-> ‘«sys_poll»’] (SPEC_ALL cflow_ticks))) >>
       simp[] >> NO_TAC) >>
  TRY (rename1 ‘l0_accept l w = (r, w')’ >>
       qspecl_then [‘l’, ‘w’, ‘r’, ‘w'’, ‘f’, ‘c’] mp_tac
         (Q.GENL [‘l’, ‘w’, ‘r’, ‘w'’, ‘f’, ‘c’] csent_accept) >>
       impl_tac >- fs[l0_rely_def] >> simp[] >> strip_tac >>
       irule cflow_accept >> metis_tac[] >> NO_TAC) >>
  TRY (drule_all csent_send >> strip_tac >> drule_all cflow_send >> simp[] >> NO_TAC) >>
  gvs[] >> metis_tac[]
QED

(* An L0 call through L1's wrappers *)
Theorem cflow_do:
  winv w ∧ l0_chan_of w f = SOME c ∧ n ≠ «sys_connect» ∧ n ≠ «sys_shutdown» ∧
  ¬(n = «sys_close» ∧ bytes_fd conf = f) ∧ l0_do n conf alen w = SOME (out, w', ev) ⇒
  l0_chan_of w' f = SOME c ∧ cflow w w' c ∧
  (¬(n = «sys_send» ∧ bytes_fd (TAKE 8 conf) = f) ⇒ csent w' c = csent w c)
Proof
  strip_tac >> drule l0_do_cases >> strip_tac >> gvs[] >>
  qabbrev_tac ‘wt = l0_tick n w’ >>
  ‘c < LENGTH w.chans’ by metis_tac[chan_lt] >>
  ‘l0_chan_of wt f = SOME c ∧ cflow w wt c’
    by (qspecl_then [‘w’, ‘n’] mp_tac (Q.GENL [‘w’, ‘nm’] csent_tick) >>
        simp[Abbr ‘wt’, cflow_tick] >> gvs[l0_chan_of_def, AllCaseEqs()]) >>
  ‘l0wf wt ∧ fds_lt wt ∧ l0_rely wt’
    by (gvs[Abbr ‘wt’, winv_def, l0wf_tick] >> irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  drule_at (Pos last) cflow_call >> disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >>
  impl_tac >- (fs[] >> metis_tac[]) >> strip_tac >>
  simp[] >> conj_tac
  >- (irule cflow_trans >> qexists_tac ‘wt’ >> simp[] >> gvs[cflow_def, csent_def]) >>
  strip_tac >> ‘csent wt c = csent w c’ by simp[Abbr ‘wt’, csent_tick] >>
  fs[csent_def]
QED

Theorem cflow_do_buf:
  winv w ∧ l0_chan_of w f = SOME c ∧ n ≠ «sys_connect» ∧ n ≠ «sys_shutdown» ∧
  ¬(n = «sys_close» ∧ bytes_fd conf = f) ∧ l0_do_buf n conf bs w = SOME (out, w', ev) ⇒
  l0_chan_of w' f = SOME c ∧ cflow w w' c ∧
  (¬(n = «sys_send» ∧ bytes_fd (TAKE 8 conf) = f) ⇒ csent w' c = csent w c)
Proof
  strip_tac >> drule l0_do_buf_cases >> strip_tac >> gvs[] >>
  qabbrev_tac ‘wt = l0_tick n w’ >>
  ‘c < LENGTH w.chans’ by metis_tac[chan_lt] >>
  ‘l0_chan_of wt f = SOME c ∧ cflow w wt c’
    by (qspecl_then [‘w’, ‘n’] mp_tac (Q.GENL [‘w’, ‘nm’] csent_tick) >>
        simp[Abbr ‘wt’, cflow_tick] >> gvs[l0_chan_of_def, AllCaseEqs()]) >>
  ‘l0wf wt ∧ fds_lt wt ∧ l0_rely wt’
    by (gvs[Abbr ‘wt’, winv_def, l0wf_tick] >> irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  drule_at (Pos last) cflow_call >> disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >>
  impl_tac >- (fs[] >> metis_tac[]) >> strip_tac >>
  simp[] >> conj_tac
  >- (irule cflow_trans >> qexists_tac ‘wt’ >> simp[] >> gvs[cflow_def, csent_def]) >>
  strip_tac >> ‘csent wt c = csent w c’ by simp[Abbr ‘wt’, csent_tick] >>
  fs[csent_def]
QED

Theorem call_names_ne[simp]:
  «sys_poll» ≠ «sys_connect» ∧ «sys_recv» ≠ «sys_connect» ∧ «sys_accept» ≠ «sys_connect» ∧
  «sys_close» ≠ «sys_connect» ∧ «sys_send» ≠ «sys_connect» ∧
  «sys_poll» ≠ «sys_shutdown» ∧ «sys_recv» ≠ «sys_shutdown» ∧ «sys_accept» ≠ «sys_shutdown» ∧
  «sys_close» ≠ «sys_shutdown» ∧ «sys_send» ≠ «sys_shutdown» ∧
  «sys_poll» ≠ «sys_send» ∧ «sys_recv» ≠ «sys_send» ∧ «sys_accept» ≠ «sys_send» ∧
  «sys_close» ≠ «sys_send» ∧ «sys_poll» ≠ «sys_close» ∧ «sys_recv» ≠ «sys_close» ∧
  «sys_accept» ≠ «sys_close» ∧ «sys_send» ≠ «sys_close»
Proof
  EVAL_TAC
QED

(* L1's calls: every one but a close of f keeps f's channel and its flow *)
Theorem sys_cflow:
  (winv w ∧ l0_chan_of w f = SOME c ∧ sys_recv g k w = SOME (out, w', ev) ⇒
   l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c) ∧
  (winv w ∧ l0_chan_of w f = SOME c ∧ sys_accept g w = SOME (out, w', ev) ⇒
   l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c) ∧
  (winv w ∧ l0_chan_of w f = SOME c ∧ sys_poll fes w = SOME (out, w', ev) ⇒
   l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c) ∧
  (winv w ∧ l0_chan_of w f = SOME c ∧ sys_send g bs w = SOME (out, w', ev) ⇒
   l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ (g ≠ f ⇒ csent w' c = csent w c)) ∧
  (winv w ∧ l0_chan_of w f = SOME c ∧ g ≠ f ∧ sys_close g w = SOME (out, w', ev) ⇒
   l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c)
Proof
  rpt conj_tac >> strip_tac >>
  gvs[sys_recv_def, sys_accept_def, sys_poll_def, sys_send_def, sys_close_def] >>
  TRY (drule_at (Pos last) cflow_do_buf >>
       disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >> simp[] >> NO_TAC) >>
  TRY (drule_at (Pos last) cflow_do >>
       disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >> simp[] >> NO_TAC) >>
  drule_at (Pos last) cflow_do >>
  disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >> simp[] >> strip_tac >> simp[] >> strip_tac >>
  ‘LENGTH (fd_bytes g) = 8’ by simp[] >>
  metis_tac[TAKE_LENGTH_APPEND]
QED

Theorem l1_close_cflow:
  l1_close g (w, st) = SOME ((w', st'), evs) ∧ winv w ∧ l0_chan_of w f = SOME c ∧ g ≠ f ⇒
  l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c
Proof
  rw[l1_close_def, AllCaseEqs()] >> drule_all (cj 5 sys_cflow) >> simp[]
QED

Theorem l1_polls_cflow:
  ∀chs w rv w' evs.
    l1_polls chs w = SOME (rv, w', evs) ∧ winv w ∧ l0_chan_of w f = SOME c ⇒
    l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c
Proof
  Induct >> simp[l1_polls_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘sys_poll _ w = SOME (out, w1, ev)’ >>
  ‘winv w1’ by metis_tac[sys_winv] >>
  drule_all (cj 3 sys_cflow) >> strip_tac >>
  first_x_assum drule_all >> metis_tac[cflow_trans]
QED

Theorem l1_flush_cflow:
  ∀fs w st w' st' evs.
    l1_flush fs (w, st) = SOME ((w', st'), evs) ∧ winv w ∧ l0_chan_of w f = SOME c ⇒
    l0_chan_of w' f = SOME c ∧ cflow w w' c
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> rename1 ‘sys_send _ _ w = SOME (out, w1, ev)’ >>
  ‘winv w1’ by metis_tac[sys_winv] >>
  drule_all (cj 4 sys_cflow) >> strip_tac >>
  first_x_assum drule_all >> metis_tac[cflow_trans]
QED

Theorem pf_fetch_cflow:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ winv w ∧
    l0_chan_of w f = SOME c ⇒
    l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘SOME (out, w1, ev)’ >>
  ‘winv w1’ by metis_tac[sys_winv] >>
  TRY (drule_all (cj 2 sys_cflow) >> strip_tac) >>
  TRY (drule_all (cj 1 sys_cflow) >> strip_tac) >>
  first_x_assum drule_all >> metis_tac[cflow_trans]
QED

Theorem l1_reap_cflow:
  ∀fs w st w' st' evs.
    l1_reap fs (w, st) = SOME ((w', st'), evs) ∧ winv w ∧ l0_chan_of w f = SOME c ∧
    ¬MEM f fs ⇒
    l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> Cases_on ‘ws’ >> rename1 ‘l1_close h' _ = SOME ((w1, st1), _)’ >>
  ‘winv w1’ by metis_tac[l1_close_winv] >>
  ‘h' ≠ f’ by (strip_tac >> gvs[]) >>
  drule_all l1_close_cflow >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  irule cflow_trans >> qexists_tac ‘w1’ >> simp[]
QED

(* A send of a non-empty buffer (shorter than 2^64, so its count decodes):
   it takes at least one byte, or it fails *)
Theorem sys_send_res:
  sys_send g bs w = SOME (out, w', ev) ∧ winv w ∧ bs ≠ [] ∧ LENGTH bs < 256 ** 8 ⇒
  (∃k. l0_res_of out = Ok k ∧ 0 < k ∧ k ≤ LENGTH bs) ∨ (∃e x. l0_res_of out = Fail e x)
Proof
  rw[sys_send_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def] >> rw[AllCaseEqs()] >>
  pairarg_tac >> gvs[] >>
  ‘LENGTH (fd_bytes g) = 8’ by simp[] >>
  ‘TAKE 8 (fd_bytes g ++ bs) = fd_bytes g ∧ DROP 8 (fd_bytes g ++ bs) = bs’
    by metis_tac[TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND] >>
  gvs[] >>
  ‘l0_rely (l0_tick «sys_send» w)’
    by (gvs[winv_def] >> irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  ‘l0_res_ok r’
    by (qpat_x_assum ‘l0_send _ _ _ = _’ mp_tac >>
        simp[l0_send_def, not_chan_def] >> rw[AllCaseEqs()] >>
        TRY (irule fail_ok >> first_assum ACCEPT_TAC >> NO_TAC) >>
        simp[l0_res_ok_def, MIN_DEF] >> rw[] >> fs[]) >>
  simp[l0_res_of_enc] >>
  qpat_x_assum ‘l0_send _ _ _ = _’ mp_tac >>
  simp[l0_send_def, not_chan_def] >> rw[AllCaseEqs()] >> gvs[fail_def] >>
  simp[MIN_DEF] >> rw[] >> fs[] >> Cases_on ‘bs’ >> fs[]
QED

Theorem ev_on_send:
  sys_send g bs w = SOME (out, w', ev) ⇒ (ev_on «sys_send» f ev ⇔ g = f)
Proof
  rw[sys_send_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  simp[ev_on_def, call_fds_def] >>
  ‘LENGTH (fd_bytes g) = 8’ by simp[] >>
  ‘TAKE 8 (fd_bytes g ++ bs) = fd_bytes g’ by metis_tac[TAKE_LENGTH_APPEND] >>
  simp[] >> metis_tac[]
QED

Theorem retried_send:
  sys_send g bs w = SOME (out, w', ev) ∧ winv w ⇒
  (retried ev ⇔ ∃e x. l0_res_of out = Fail e x ∧ l1_transient e)
Proof
  rw[sys_send_def] >>
  ‘LENGTH out = 13’
    by (gvs[l0_do_def, AllCaseEqs(), winv_def] >> drule_all l0_ffi_fn_length >> simp[]) >>
  drule l0_do_cases >> strip_tac >> gvs[] >>
  simp[retried_def, MAP_SND_ZIP_REPLICATE] >> every_case_tac >> simp[]
QED

(* ------------------------------------------------------------------------
   L1's state, seen from the output of f: f's outbox is not empty and f
   is not gone.  While that lasts L1 never closes f (an EOF on its handle
   moves it to closing; the reap closes only drained or gone fds), every
   poll asks for f's output, and a write to f only appends (L1 sends at
   write time only from an empty outbox)
   ------------------------------------------------------------------------ *)

Definition olive_def:
  olive lfd f ps ⇔ f ≠ lfd ∧ outbox_of ps.b f ≠ [] ∧ ¬MEM f ps.b.gone
End

Theorem pdo_live:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ winv w ∧ olive lfd f ps ∧
  l0_chan_of w f = SOME c ⇒
  winv w' ∧ olive lfd f ps' ∧ l0_chan_of w' f = SOME c ∧ cflow w w' c ∧
  csent w' c = csent w c ∧ LENGTH (outbox_of ps.b f) ≤ LENGTH (outbox_of ps'.b f) ∧
  ¬EXISTS (ev_on «sys_send» f) evs
Proof
  strip_tac >> ‘winv w'’ by metis_tac[pdo_winv] >> simp[] >>
  qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >>
  Cases_on ‘a’ >> simp[pdo_def] >> strip_tac
  >- ((* Accept *)
      gvs[AllCaseEqs()] >> gvs[olive_def, outbox_of_def] >> metis_tac[])
  >- ((* Read *)
      Cases_on ‘ALOOKUP ps.b.tbl c'’ >> gvs[] >> rename1 ‘ALOOKUP _ c' = SOME g’ >>
      gvs[AllCaseEqs()] >>
      TRY (gvs[olive_def, set_inb_def, outbox_of_def] >> NO_TAC) >>
      (* g closed: g is not f *)
      PairCases_on ‘z’ >> gvs[] >>
      ‘g ≠ f’ by (strip_tac >> gvs[olive_def]) >>
      gvs[l1_close_def, AllCaseEqs()] >>
      drule_all (cj 5 sys_cflow) >> strip_tac >>
      gvs[sys_close_def] >> drule l0_do_cases >> strip_tac >> gvs[ev_on_def] >>
      gvs[olive_def, forget_def, outbox_of_set_outbox, MEM_FILTER, MEM_MAP, EXISTS_PROD,
          ALOOKUP_ADELKEY] >> gvs[outbox_of_def])
  >> (* Write *)
  PairCases_on ‘z’ >> gvs[l1do_def, AllCaseEqs()] >>
  TRY (‘ps with b := ps.b = ps’ by simp[l1p_component_equality] >> gvs[] >> NO_TAC) >>
  rename1 ‘ALOOKUP _ c' = SOME g’ >>
  TRY ((* buffered: only g's outbox grows *)
       Cases_on ‘g = f’ >> gvs[olive_def, outbox_of_set_outbox] >> NO_TAC) >>
  (* sent at once: from an empty outbox, so not f's *)
  ‘g ≠ f’ by (strip_tac >> gvs[olive_def]) >>
  drule_all (cj 4 sys_cflow) >> strip_tac >>
  drule ev_on_send >> disch_then (qspec_then ‘f’ assume_tac) >> gvs[] >>
  simp[outbox_of_after_send_other, outbox_of_set_outbox] >>
  gvs[olive_def, after_send_def, set_outbox_def] >> every_case_tac >>
  gvs[MEM_FILTER, outbox_of_def, ALOOKUP_ADELKEY]
QED

Theorem pacts_live:
  ∀acts w ps rs evs w' ps'.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ winv w ∧ olive lfd f ps ∧
    l0_chan_of w f = SOME c ⇒
    winv w' ∧ olive lfd f ps' ∧ l0_chan_of w' f = SOME c ∧ cflow w w' c ∧
    csent w' c = csent w c ∧ LENGTH (outbox_of ps.b f) ≤ LENGTH (outbox_of ps'.b f) ∧
    ¬EXISTS (ev_on «sys_send» f) evs
Proof
  Induct >> simp[pacts_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  drule_all pdo_live >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  conj_tac >- (irule cflow_trans >> qexists_tac ‘ws10’ >> simp[]) >>
  gvs[EVERY_MEM, EXISTS_MEM] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The flush, seen from f
   ------------------------------------------------------------------------ *)

Theorem res_of_enc_ok:
  ∃v'. l0_res_of (enc_res (Ok v)) = Ok v'
Proof
  simp[l0_res_of_def, dec_res_def, enc_res_def, LENGTH_n2w8]
QED

(* A send that failed took nothing (whatever its length) *)
Theorem sys_send_fail_csent:
  sys_send g bs w = SOME (out, w', ev) ∧ winv w ∧ l0_chan_of w f = SOME c ∧
  l0_res_of out = Fail e x ⇒ csent w' c = csent w c
Proof
  rw[sys_send_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def] >> rw[AllCaseEqs()] >>
  pairarg_tac >> gvs[] >>
  ‘c < LENGTH w.chans’ by metis_tac[chan_lt] >>
  ‘l0_chan_of (l0_tick «sys_send» w) f = SOME c ∧
   csent (l0_tick «sys_send» w) c = csent w c’
    by (qspecl_then [‘w’, ‘«sys_send»’] mp_tac (Q.GENL [‘w’, ‘nm’] csent_tick) >>
        simp[] >> gvs[l0_chan_of_def, AllCaseEqs()]) >>
  ‘l0wf (l0_tick «sys_send» w)’ by gvs[winv_def, l0wf_tick] >>
  drule_all csent_send >> strip_tac >>
  Cases_on ‘r’ >> gvs[csent_def] >>
  qspec_then ‘n’ strip_assume_tac (Q.GEN ‘v’ res_of_enc_ok) >> gvs[]
QED

(* The flush, without a bound on the outbox: if no send on f went through
   (took bytes, or failed hard), f's outbox, its channel's sent and its
   gone flag are as they were; and f, listed, with output, gets a send *)
Theorem l1_flush_live:
  ∀fs w b w' b' evs.
    l1_flush fs (w, b) = SOME ((w', b'), evs) ∧ winv w ∧ l0_chan_of w f = SOME c ⇒
    (¬(∃ev. MEM ev evs ∧ ev_on «sys_send» f ev ∧ ¬retried ev) ⇒
     outbox_of b' f = outbox_of b f ∧ csent w' c = csent w c ∧
     (MEM f b'.gone ⇔ MEM f b.gone)) ∧
    (MEM f fs ∧ outbox_of b f ≠ [] ∧ ¬MEM f b.gone ⇒ EXISTS (ev_on «sys_send» f) evs)
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> strip_tac >>
  Cases_on ‘outbox_of b h = [] ∨ MEM h b.gone’
  >- (gvs[] >> first_x_assum drule_all >> strip_tac >> simp[] >> rw[] >> gvs[]) >>
  gvs[AllCaseEqs()] >> rename1 ‘sys_send g _ w = SOME (out, w1, ev)’ >>
  ‘winv w1’ by metis_tac[sys_winv] >>
  drule_all (cj 4 sys_cflow) >> strip_tac >>
  drule ev_on_send >> disch_then (qspec_then ‘f’ assume_tac) >>
  drule_all retried_send >> strip_tac >>
  Cases_on ‘g = f’
  >- (gvs[] >> Cases_on ‘retried ev’ >> gvs[]
      >- ((* retried: L1 keeps its state, the send took nothing *)
          ‘csent w1 c = csent w c’ by metis_tac[sys_send_fail_csent] >>
          gvs[after_send_def] >> first_x_assum drule_all >> strip_tac >> simp[] >>
          metis_tac[]) >>
      rw[] >> metis_tac[]) >>
  ‘outbox_of (after_send g (l0_res_of out) b) f = outbox_of b f ∧
   (MEM f (after_send g (l0_res_of out) b).gone ⇔ MEM f b.gone)’
    by metis_tac[outbox_of_after_send_other] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem pf_fetch_b:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ⇒ ps'.b = ps.b
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> rw[] >> gvs[set_inb_def]
QED

Theorem l1_flush_out:
  ∀fs w b w' b' evs.
    l1_flush fs (w, b) = SOME ((w', b'), evs) ∧ winv w ∧ l0_chan_of w f = SOME c ∧
    LENGTH (outbox_of b f) < 256 ** 8 ⇒
    LENGTH (outbox_of b' f) ≤ LENGTH (outbox_of b f) ∧
    ((∃ev. MEM ev evs ∧ ev_on «sys_send» f ev ∧ ¬retried ev) ⇒
     LENGTH (outbox_of b' f) < LENGTH (outbox_of b f)) ∧
    (¬(∃ev. MEM ev evs ∧ ev_on «sys_send» f ev ∧ ¬retried ev) ⇒
     outbox_of b' f = outbox_of b f ∧ csent w' c = csent w c) ∧
    (MEM f fs ∧ outbox_of b f ≠ [] ∧ ¬MEM f b.gone ⇒ EXISTS (ev_on «sys_send» f) evs)
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> strip_tac >>
  Cases_on ‘outbox_of b h = [] ∨ MEM h b.gone’
  >- (gvs[] >> first_x_assum drule_all >> strip_tac >> simp[] >> rw[] >> gvs[]) >>
  gvs[AllCaseEqs()] >> rename1 ‘sys_send g _ w = SOME (out, w1, ev)’ >>
  ‘winv w1’ by metis_tac[sys_winv] >>
  drule_all (cj 4 sys_cflow) >> strip_tac >>
  drule ev_on_send >> disch_then (qspec_then ‘f’ assume_tac) >>
  drule_all retried_send >> strip_tac >>
  Cases_on ‘g = f’
  >- ((* a send on f *)
      gvs[] >>
      ‘outbox_of b f ≠ []’ by gvs[] >>
      ‘LENGTH (outbox_of b f) < 256 ** 8’ by simp[] >>
      Cases_on ‘retried ev’
      >- ((* retried: L1 keeps its state *)
          gvs[after_send_def] >>
          ‘csent w1 c = csent w c’
            by (drule sys_send_csent >> disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >>
                impl_tac >- (gvs[sys_send_def] >> drule l0_do_cases >> strip_tac >>
                             gvs[small_send_def]) >>
                simp[]) >>
          first_x_assum drule_all >> strip_tac >> simp[] >> metis_tac[]) >>
      (* not retried: the outbox shrank *)
      drule_all sys_send_res >> strip_tac >>
      ‘∀e x. l0_res_of out = Fail e x ⇒ ¬l1_transient e’ by (rpt strip_tac >> gvs[] >> metis_tac[]) >>
      ‘LENGTH (outbox_of (after_send f (l0_res_of out) b) f) < LENGTH (outbox_of b f)’
        by (Cases_on ‘l0_res_of out’ >> gvs[after_send_def, outbox_of_set_outbox] >>
            rw[] >> Cases_on ‘outbox_of b f’ >> gvs[]) >>
      ‘LENGTH (outbox_of (after_send f (l0_res_of out) b) f) < 18446744073709551616’
        by decide_tac >>
      first_x_assum drule_all >> strip_tac >> simp[] >> rw[] >> TRY decide_tac >>
      TRY (first_x_assum (qspec_then ‘ev’ mp_tac) >> simp[] >> NO_TAC) >>
      res_tac >> decide_tac) >>
  (* a send on another fd: f's outbox and channel untouched *)
  ‘outbox_of (after_send g (l0_res_of out) b) f = outbox_of b f ∧
   (MEM f (after_send g (l0_res_of out) b).gone ⇔ MEM f b.gone)’
    by metis_tac[outbox_of_after_send_other] >>
  qpat_x_assum ‘∀w b w' b' evs. _’
    (qspecl_then [‘w1’, ‘after_send g (l0_res_of out) b’, ‘w'’, ‘b'’, ‘evs'’] mp_tac) >>
  impl_tac >- fs[] >> strip_tac >> gvs[] >>
  rw[] >> gvs[] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The poll, seen from f's output
   ------------------------------------------------------------------------ *)

(* A connected channel, neither broken nor shut down, asked for output,
   with room for a byte: POLLOUT *)
Theorem out_revents:
  noconn w ∧ l0_chan_of w f = SOME c ∧ ¬(EL c w.chans).broken ∧ ¬(EL c w.chans).shut ∧
  2 ≤ ev MOD 4 ∧ 0 < w.ch.takes c w.hist (EL c w.chans).inflight 1 ⇒
  (byte_revents (fd_revents w (f, ev))).rout
Proof
  rw[fd_revents_def] >> simp[byte_revents_revents_byte] >>
  ‘c < LENGTH w.chans’ by metis_tac[chan_lt] >>
  gvs[noconn_def, chan_revents_def]
QED

Theorem writable_zip:
  ∀fes. MEM (f, e) fes ∧ (g (f, e)).rout ⇒
        MEM f (writable_fds (ZIP (MAP FST fes, MAP g fes)))
Proof
  Induct >> simp[FORALL_PROD, writable_fds_def] >> rw[] >> gvs[writable_fds_def]
QED

(* One poll, seen from f's output: if it lists f for output, is not retried,
   and f's channel (at the poll) is up with nothing in flight, [F2] makes
   it report f writable *)
Theorem sys_poll_out:
  sys_poll fes w = SOME (out, w', ev) ∧ winv w ∧ l0_chan_of w f = SOME c ∧
  EVERY (λ(g, e). small g ∧ e < 4) fes ∧ MEM (f, e) fes ∧ 2 ≤ e ∧
  ¬(EL c w'.chans).broken ∧ ¬(EL c w'.chans).shut ∧ (EL c w'.chans).inflight = 0 ∧
  (∀h. 0 < w.ch.takes c h 0 1) ∧ ¬retried ev ⇒
  MEM f (writable_fds (poll_revents fes out))
Proof
  strip_tac >> ‘l0_rely w’ by gvs[winv_def] >>
  qpat_x_assum ‘sys_poll _ _ = _’ mp_tac >> simp[sys_poll_def] >> strip_tac >>
  ‘LENGTH out = LENGTH (poll_buf fes)’
    by (gvs[l0_do_buf_def, AllCaseEqs(), winv_def] >> drule_all l0_ffi_fn_length >> simp[]) >>
  drule_all ev_do_buf >> strip_tac >>
  drule l0_do_buf_cases >> strip_tac >> gvs[ev_name_def] >>
  qabbrev_tac ‘wt = l0_tick «sys_poll» w’ >>
  ‘noconn wt ∧ LENGTH (wt.ch.errno_of wt.hist) = 4 ∧ wt.ch = w.ch’
    by gvs[Abbr ‘wt’, winv_def, noconn_tick, l0_rely_def] >>
  ‘l0_chan_of wt f = SOME c’
    by (qspecl_then [‘w’, ‘«sys_poll»’] mp_tac (Q.GENL [‘w’, ‘nm’] csent_tick) >>
        ‘c < LENGTH w.chans’ by metis_tac[chan_lt] >>
        simp[Abbr ‘wt’] >> gvs[l0_chan_of_def, AllCaseEqs()]) >>
  ‘EVERY pe_ok (pollfd_entries (DROP 16 (poll_buf fes)))’
    by (simp[pollfd_entries_buf, EVERY_MAP] >> gvs[EVERY_MEM, FORALL_PROD] >>
        metis_tac[pe_pfd_bytes]) >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[l0_call_def] >>
  rw[AllCaseEqs()] >> gvs[] >>
  TRY (rename1 ‘poll_failed ww ee (poll_buf fes)’ >>
       ‘LENGTH (ww.ch.errno_of ww.hist) = 4’ by gvs[] >>
       drule res_of_poll_failed >>
       disch_then (qspecl_then [‘ee’, ‘poll_buf fes’] assume_tac) >>
       gvs[retried_def, MAP_ZIP] >> NO_TAC) >>
  qmatch_goalsub_rename_tac ‘poll_out ww (poll_buf fes)’ >>
  Cases_on ‘l0_res_of (poll_out ww (poll_buf fes))’ >> gvs[]
  >- (drule_all poll_revents_ok >> strip_tac >> simp[] >>
      irule writable_zip >> qexists_tac ‘e’ >> simp[] >>
      irule out_revents >> simp[] >>
      ‘e = 2 ∨ e = 3’ by (gvs[EVERY_MEM] >> first_x_assum drule >> simp[]) >>
      gvs[]) >>
  gvs[retried_def, MAP_ZIP]
QED

(* ------------------------------------------------------------------------
   The round's tail, seen from f's output
   ------------------------------------------------------------------------ *)

Theorem drop_out_f:
  ∀dl b. LENGTH (outbox_of (FOLDL drop_out b dl) f) ≤ LENGTH (outbox_of b f) ∧
         (FOLDL drop_out b dl).nxt = b.nxt ∧
         ((MEM f b.gone ⇒ outbox_of b f = []) ⇒
          MEM f (FOLDL drop_out b dl).gone ⇒ outbox_of (FOLDL drop_out b dl) f = [])
Proof
  Induct >> simp[] >> rpt gen_tac >>
  first_x_assum (qspec_then ‘drop_out b h’ strip_assume_tac) >>
  gvs[drop_out_def, outbox_of_set_outbox] >> rw[] >> gvs[MEM_FILTER] >>
  Cases_on ‘f = h’ >> gvs[MEM_FILTER]
QED

Theorem hup_f:
  ps' = hup_step hfs ob log ps ⇒
  ps'.b.tbl = ps.b.tbl ∧ ps'.b.closing = ps.b.closing ∧ ps'.acq = ps.acq ∧
  ps'.b.nxt = ps.b.nxt ∧
  LENGTH (outbox_of ps'.b f) ≤ LENGTH (outbox_of ps.b f) ∧
  ((MEM f ps.b.gone ⇒ outbox_of ps.b f = []) ⇒
   MEM f ps'.b.gone ⇒ outbox_of ps'.b f = [])
Proof
  strip_tac >> gvs[hup_out] >> simp[hup_step_def] >> metis_tac[drop_out_f]
QED

Theorem drop_out_kept:
  ∀dl b. ¬MEM f (FOLDL drop_out b dl).gone ⇒
         ¬MEM f dl ∧ ¬MEM f b.gone ∧ outbox_of (FOLDL drop_out b dl) f = outbox_of b f
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[drop_out_def, MEM_FILTER, outbox_of_set_outbox] >>
  Cases_on ‘f = h’ >> gvs[]
QED

Theorem hup_kept:
  ps' = hup_step hfs ob log ps ∧ ¬MEM f ps'.b.gone ⇒
  ¬MEM f ps.b.gone ∧ outbox_of ps'.b f = outbox_of ps.b f
Proof
  strip_tac >> gvs[hup_step_def] >> drule drop_out_kept >> simp[]
QED

Theorem l1_reap_live:
  ∀fs w b w' b' evs.
    l1_reap fs (w, b) = SOME ((w', b'), evs) ∧ winv w ∧ l0_chan_of w f = SOME c ∧
    outbox_of b f ≠ [] ∧ ¬MEM f b.gone ⇒
    l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c ∧
    outbox_of b' f = outbox_of b f ∧ ¬MEM f b'.gone
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> Cases_on ‘ws’ >> rename1 ‘l1_close g _ = SOME ((w1, b1), _)’ >>
  ‘g ≠ f’ by (strip_tac >> gvs[]) >>
  ‘winv w1’ by metis_tac[l1_close_winv] >>
  drule_all l1_close_cflow >> strip_tac >>
  ‘outbox_of b1 f = outbox_of b f ∧ ¬MEM f b1.gone’
    by (gvs[l1_close_def, AllCaseEqs(), forget_def, outbox_of_set_outbox, MEM_FILTER] >>
        gvs[outbox_of_def]) >>
  ‘outbox_of b1 f ≠ []’ by fs[] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  irule cflow_trans >> qexists_tac ‘w1’ >> simp[]
QED

Theorem l1_reap_tbl:
  ∀fs w b w' b' evs. l1_reap fs (w, b) = SOME ((w', b'), evs) ⇒ b'.tbl = b.tbl ∧ b'.nxt = b.nxt
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs(), l1_close_def] >>
  first_x_assum drule >> simp[forget_def]
QED

Theorem pf_fetch_acq:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ winv w ∧
    l0_chan_of w f = SOME c ⇒
    (MEM f ps'.acq ⇒ MEM f ps.acq)
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘SOME (out, w1, ev)’ >>
  ‘winv w1’ by metis_tac[sys_winv] >>
  TRY (drule_all (cj 2 sys_cflow) >> strip_tac) >>
  TRY (drule_all (cj 1 sys_cflow) >> strip_tac) >>
  first_x_assum drule_all >> strip_tac >> gvs[set_inb_def] >>
  rename1 ‘l0_res_of out = Ok k’ >>
  ‘¬MEM (n2w k) (l0_used w)’
    by (irule sys_accept_fresh >> gvs[winv_def] >> metis_tac[]) >>
  metis_tac[chan_used]
QED

(* An fd with a non-empty outbox is polled for output *)
Theorem pf_poll_set_out:
  outbox_of ps.b f ≠ [] ∧ f ≠ lfd ⇒
  ∃e. MEM (f, e) (pf_poll_set lfd pol ps hs) ∧ 2 ≤ e ∧ e < 4
Proof
  strip_tac >> simp[pf_poll_set_def] >>
  qabbrev_tac ‘ins = FLAT (MAP (λh. case ALOOKUP ps.b.tbl h of
                                   | SOME f =>
                                       (let i = (if wants_input lfd pol ps f then 1n else 0);
                                            ou = (if outbox_of ps.b f = [] then 0 else 2n) in
                                          if i + ou = 0 then [] else [(f, i + ou)])
                                   | NONE => if h = lfd ∧ wants_input lfd pol ps lfd
                                             then [(lfd, 1n)] else []) hs)’ >>
  Cases_on ‘MEM f (MAP FST ins)’
  >- (gvs[MEM_MAP, EXISTS_PROD] >> rename1 ‘MEM (f, e) ins’ >>
      qexists_tac ‘e’ >> simp[] >>
      qpat_x_assum ‘MEM (f, e) ins’ mp_tac >>
      simp[Abbr ‘ins’, MEM_FLAT, MEM_MAP] >> rw[] >> every_case_tac >> gvs[] >> rw[]) >>
  qexists_tac ‘2’ >> simp[MEM_MAP, MEM_FILTER, EXISTS_PROD] >>
  disj2_tac >> gvs[outbox_of_def] >>
  Cases_on ‘ALOOKUP ps.b.outbox f’ >> gvs[] >> rename1 ‘ALOOKUP _ f = SOME bs’ >>
  qexists_tac ‘bs’ >> imp_res_tac ALOOKUP_MEM >> simp[] >>
  gvs[MEM_MAP, FORALL_PROD] >> metis_tac[]
QED

Theorem l1_reap_empty:
  ∀fs w b w' b' evs.
    l1_reap fs (w, b) = SOME ((w', b'), evs) ∧ outbox_of b f = [] ⇒ outbox_of b' f = []
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs(), l1_close_def, forget_def] >>
  first_x_assum drule >> disch_then irule >>
  simp[outbox_of_set_outbox] >> rw[] >> gvs[outbox_of_def]
QED

Theorem sys_poll_on:
  sys_poll fes w = SOME (out, w', ev) ∧ winv w ∧ EVERY (λ(g, e). small g ∧ e < 4) fes ⇒
  ∀nm g. ev_on nm g ev ⇔ nm = «sys_poll» ∧ MEM g (MAP FST fes)
Proof
  strip_tac >> ‘l0_rely w’ by gvs[winv_def] >>
  qpat_x_assum ‘sys_poll _ _ = _’ mp_tac >> simp[sys_poll_def] >> strip_tac >>
  drule_all ev_do_buf >> strip_tac >> simp[] >> rpt gen_tac >>
  eq_tac >> rw[] >> gvs[call_fds_poll]
QED

(* ------------------------------------------------------------------------
   One round, seen from f's output.  Either a send on f went through (took
   bytes, or failed hard), or L1 emptied f's outbox itself (D19's drop),
   or everything about f is as it was: then the round polled f for output,
   and a poll that went through while f's channel was up with nothing in
   flight led to a send on f ([F2])
   ------------------------------------------------------------------------ *)

Theorem pround_live:
  pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ∧
  winv w ∧ psmall lfd ps ∧ olive lfd f ps ∧ l0_chan_of w f = SOME c ⇒
  (∃ev. MEM ev evs ∧ ev_on «sys_send» f ev ∧ ¬retried ev) ∨ outbox_of ps'.b f = [] ∨
  (olive lfd f ps' ∧ l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c ∧
   EXISTS (ev_on «sys_poll» f) evs ∧
   ∀ev. MEM ev evs ∧ ev_on «sys_poll» f ev ∧ ¬retried ev ∧
        ¬(EL c w'.chans).broken ∧ ¬(EL c w.chans).shut ∧ (EL c w.chans).inflight = 0 ∧
        (∀hh. 0 < w.ch.takes c hh 0 1) ⇒
        EXISTS (ev_on «sys_send» f) evs)
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >>
  gvs[pf_tail_def, AllCaseEqs()] >>
  rename1 ‘pacts _ _ _ = SOME (rs, aevs, wa, pa)’ >>
  drule_all pacts_live >> strip_tac >>
  drule pacts_names >> strip_tac >>
  ‘psmall lfd pa’ by metis_tac[pacts_psmall] >>
  qabbrev_tac ‘fes = pf_poll_set lfd pol pa hs’ >>
  ‘EVERY (λ(g, e). small g ∧ e < 4) fes’
    by (qunabbrev_tac ‘fes’ >> irule pf_poll_set_small >> simp[]) >>
  (* the poll *)
  qpat_x_assum ‘l1_polls [fes] _ = _’ mp_tac >> simp[l1_polls_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> rename1 ‘sys_poll fes wa = SOME (out, w1, pev)’ >>
  ‘winv w1’ by metis_tac[sys_winv] >>
  drule_all (cj 3 sys_cflow) >> strip_tac >>
  drule_all sys_poll_on >> strip_tac >>
  ‘olive lfd f pa’ by simp[] >>
  ‘∃e. MEM (f, e) fes ∧ 2 ≤ e ∧ e < 4’
    by (qunabbrev_tac ‘fes’ >> irule pf_poll_set_out >> gvs[olive_def]) >>
  (* the flush *)
  rename1 ‘l1_flush _ (w1, pa.b) = SOME ((w2, b2), fevs)’ >>
  ‘winv w2’ by metis_tac[l1_flush_winv] >>
  qpat_assum ‘l1_flush _ _ = _’ (strip_assume_tac o MATCH_MP l1_flush_names) >>
  drule_all l1_flush_cflow >> strip_tac >>
  drule_all l1_flush_live >> strip_tac >>
  Cases_on ‘∃ev. MEM ev fevs ∧ ev_on «sys_send» f ev ∧ ¬retried ev’
  >- (disj1_tac >> metis_tac[]) >>
  gvs[] >>
  (* the fetch *)
  rename1 ‘pf_fetch _ _ _ (w2, pa with b := b2) = SOME ((w3, ps3'), log, gevs)’ >>
  ‘winv w3’ by metis_tac[pf_fetch_winv] >>
  drule_all pf_fetch_cflow >> strip_tac >>
  drule pf_fetch_b >> strip_tac >>
  drule pf_fetch_names >> strip_tac >>
  (* the hang-up policy: a drop empties f's outbox *)
  qabbrev_tac ‘ps3 = hup_step (hup_fds (poll_revents fes out)) (outbox_of pa.b) log ps3'’ >>
  ‘¬MEM f ps3'.b.gone ∧ outbox_of ps3'.b f = outbox_of pa.b f’ by gvs[olive_def] >>
  Cases_on ‘MEM f ps3.b.gone’
  >- ((* dropped (D19): f's outbox is empty, and stays so *)
      disj2_tac >> disj1_tac >>
      ‘outbox_of ps3.b f = []’
        by (qspecl_then [‘hup_fds (poll_revents fes out)’, ‘outbox_of pa.b’, ‘log’, ‘ps3'’,
                         ‘ps3’, ‘f’] mp_tac (Q.GENL [‘hfs’, ‘ob’, ‘log’, ‘ps’, ‘ps'’, ‘f’] hup_f) >>
            simp[Abbr ‘ps3’]) >>
      metis_tac[l1_reap_empty]) >>
  ‘¬MEM f ps3'.b.gone ∧ outbox_of ps3.b f = outbox_of ps3'.b f’
    by (irule hup_kept >> simp[Abbr ‘ps3’] >> metis_tac[]) >>
  ‘outbox_of ps3.b f ≠ []’ by gvs[olive_def] >>
  drule_all l1_reap_live >> strip_tac >>
  drule l1_reap_names >> strip_tac >>
  disj2_tac >> disj2_tac >>
  rpt conj_tac
  >- gvs[olive_def]
  >- simp[]
  >- (irule cflow_trans >> qexists_tac ‘w3’ >> simp[] >>
      irule cflow_trans >> qexists_tac ‘w2’ >> simp[] >>
      irule cflow_trans >> qexists_tac ‘w1’ >> simp[] >>
      irule cflow_trans >> qexists_tac ‘wa’ >> simp[])
  >- gvs[]
  >- (simp[MEM_MAP, EXISTS_PROD] >> metis_tac[])
  >> rpt gen_tac >> strip_tac >> imp_res_tac ev_on_name >> gvs[EVERY_MEM] >>
  TRY (res_tac >> gvs[] >> NO_TAC) >>
  (* the round's poll went through with f's channel up and empty: f writable *)
  ‘cflow w w1 c’ by (irule cflow_trans >> qexists_tac ‘wa’ >> simp[]) >>
  ‘cflow w1 w' c’
    by (irule cflow_trans >> qexists_tac ‘w3’ >> simp[] >>
        irule cflow_trans >> qexists_tac ‘w2’ >> simp[]) >>
  ‘¬(EL c w1.chans).broken ∧ ¬(EL c w1.chans).shut ∧ (EL c w1.chans).inflight = 0 ∧
   wa.ch = w.ch’
    by (gvs[cflow_def] >> metis_tac[]) >>
  qmatch_asmsub_rename_tac ‘sys_poll fes wa = SOME (out, w1, pev)’ >>
  ‘MEM f (writable_fds (poll_revents fes out))’
    by (qspecl_then [‘fes’, ‘wa’, ‘out’, ‘w1’, ‘pev’, ‘f’, ‘c’, ‘e’] mp_tac
          (Q.GENL [‘fes’, ‘w’, ‘out’, ‘w'’, ‘ev’, ‘f’, ‘c’, ‘e’] sys_poll_out) >>
        impl_tac >- (rw[EVERY_MEM] >> gvs[]) >> simp[]) >>
  gvs[]
QED

