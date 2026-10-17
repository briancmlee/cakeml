(*
  L3-09 (S3): what steps of time do to a channel's send side.  A channel
  stays; the count of the peer's reads (drained) never goes down; and the
  bytes in flight change only when the peer reads (LDrain, which counts a
  read).  Used to carry D(c) (drains) through an idle segment.

  MAIN: ticks_chan.
*)
Theory honestL1BChan
Ancestors
  honestL1BPoll honestL0Part honestL0World honestL0
Libs
  preamble

(* c's send side after w', compared with w *)
Definition chan_mono_def:
  chan_mono c (w : l0world) (w' : l0world) ⇔
    c < LENGTH w.chans ⇒
    c < LENGTH w'.chans ∧
    (EL c w.chans).drained ≤ (EL c w'.chans).drained ∧
    ((EL c w'.chans).drained = (EL c w.chans).drained ⇒
     (EL c w'.chans).inflight = (EL c w.chans).inflight)
End

Theorem chan_mono_refl[simp]:
  chan_mono c w w
Proof
  simp[chan_mono_def]
QED

Theorem chan_mono_trans:
  chan_mono c w1 w2 ∧ chan_mono c w2 w3 ⇒ chan_mono c w1 w3
Proof
  rw[chan_mono_def] >> fs[]
QED

Theorem deliver_chan[local]:
  chan_mono c w (l0_deliver w a)
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def, chan_mono_def, upd_lchan_def, EL_LUPDATE] >>
  every_case_tac >> gvs[EL_APPEND1, EL_LUPDATE] >> rw[] >> gvs[break_lchan_def] >> rw[]
QED

Theorem FOLDL_deliver_chan[local]:
  ∀as w. chan_mono c w (FOLDL l0_deliver w as)
Proof
  Induct >> simp[] >> metis_tac[chan_mono_trans, deliver_chan]
QED

Theorem tick_chan:
  chan_mono c w (l0_tick nm w)
Proof
  simp[l0_tick_def] >>
  irule chan_mono_trans >> qexists_tac ‘w with clock := w.clock + 1’ >>
  simp[FOLDL_deliver_chan] >> simp[chan_mono_def]
QED

(* MAIN *)
Theorem ticks_chan:
  ∀k w. chan_mono c w (l0_ticks nm k w)
Proof
  Induct >> simp[l0_ticks_def] >> metis_tac[chan_mono_trans, tick_chan]
QED

(* c stays, and its drained count does not go down *)
Definition dmono_def:
  dmono c (w : l0world) (w' : l0world) ⇔
    c < LENGTH w.chans ⇒
    c < LENGTH w'.chans ∧ (EL c w.chans).drained ≤ (EL c w'.chans).drained
End

Theorem dmono_trans:
  dmono c w1 w2 ∧ dmono c w2 w3 ⇒ dmono c w1 w3
Proof
  rw[dmono_def] >> fs[]
QED

Theorem chan_mono_dmono:
  chan_mono c w w' ⇒ dmono c w w'
Proof
  rw[chan_mono_def, dmono_def]
QED

Theorem upd_lchan_dmono[local]:
  (∀x. (g x).drained = x.drained) ⇒ dmono c w (upd_lchan j g w)
Proof
  rw[dmono_def, upd_lchan_def, EL_LUPDATE] >> rw[]
QED

Theorem FOLDL_dmono:
  ∀q w1. (∀w' j. dmono c w' (f w' j)) ∧ dmono c w w1 ⇒ dmono c w (FOLDL f w1 q)
Proof
  Induct >> rw[] >> first_x_assum irule >> simp[] >> metis_tac[dmono_trans]
QED

Theorem l0_call_dmono:
  l0_call n conf bytes w = SOME (FFIreturn out w') ⇒ dmono c w w'
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  TRY (irule chan_mono_dmono >> simp[ticks_chan] >> NO_TAC) >>
  TRY (simp[dmono_def] >> NO_TAC) >>
  gvs[l0_listen_def, l0_accept_def, l0_recv_def, l0_send_def, l0_shutdown_def,
      l0_connect_def, l0_connerr_def, l0_close_def, close_fd_def, l0_alloc_def,
      AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[AllCaseEqs()]) >>
  TRY (irule FOLDL_dmono >> conj_tac >> rpt gen_tac >>
       rw[dmono_def, EL_LUPDATE, upd_lchan_def, break_lchan_def] >> rw[] >> NO_TAC) >>
  rw[dmono_def, upd_lchan_def, EL_LUPDATE, break_lchan_def, EL_APPEND1] >> rw[]
QED

Theorem step_dmono:
  l0_step (SOME w) lc = SOME w' ⇒ dmono c w w'
Proof
  PairCases_on ‘lc’ >> rw[l0_step_def, l0_ffi_fn_def, AllCaseEqs()] >>
  irule dmono_trans >> qexists_tac ‘l0_tick lc0 w’ >>
  conj_tac >- (irule chan_mono_dmono >> simp[tick_chan]) >>
  drule l0_call_dmono >> simp[dmono_def]
QED

Theorem FOLDL_step_NONE[local]:
  ∀cs. FOLDL l0_step NONE cs = NONE
Proof
  Induct >> simp[l0_step_def]
QED

(* MAIN: along a replay, channels stay and drained counts only grow *)
Theorem replay_dmono:
  ∀cs w w'. FOLDL l0_step (SOME w) cs = SOME w' ⇒ dmono c w w'
Proof
  Induct >- simp[dmono_def] >> rpt gen_tac >> simp[] >>
  Cases_on ‘l0_step (SOME w) h’ >> simp[FOLDL_step_NONE] >> strip_tac >>
  irule dmono_trans >> qexists_tac ‘x’ >>
  conj_tac >- (irule step_dmono >> qexists_tac ‘h’ >> first_assum ACCEPT_TAC) >>
  first_x_assum irule >> first_assum ACCEPT_TAC
QED

Theorem ticks_add:
  ∀a w. l0_ticks nm (a + b) w = l0_ticks nm b (l0_ticks nm a w)
Proof
  Induct >> simp[l0_ticks_def, ADD_CLAUSES]
QED

(* Steps of time never add bytes in flight: an existing channel's count
   does not grow, and a new one has none *)
Definition inflight_le_def:
  inflight_le c (w : l0world) (w' : l0world) ⇔
    c < LENGTH w'.chans ⇒
    if c < LENGTH w.chans then (EL c w'.chans).inflight ≤ (EL c w.chans).inflight
    else (EL c w'.chans).inflight = 0
End

Theorem inflight_le_trans:
  inflight_le c w1 w2 ∧ inflight_le c w2 w3 ∧ (c < LENGTH w1.chans ⇒ c < LENGTH w2.chans) ⇒
  inflight_le c w1 w3
Proof
  rw[inflight_le_def] >> Cases_on ‘c < LENGTH w2.chans’ >> fs[] >> rw[] >> fs[]
QED

Theorem deliver_inflight[local]:
  inflight_le c w (l0_deliver w a)
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def, inflight_le_def, upd_lchan_def, EL_LUPDATE] >>
  every_case_tac >> gvs[EL_APPEND1, EL_APPEND2, EL_LUPDATE, fresh_lchan_def] >> rw[] >>
  gvs[break_lchan_def, EL_APPEND1, EL_APPEND2] >> rw[] >> fs[] >>
  TRY (‘c = LENGTH w.chans’ by decide_tac >> gvs[EL_APPEND2, fresh_lchan_def] >> NO_TAC)
QED

Theorem deliver_len[local]:
  c < LENGTH w.chans ⇒ c < LENGTH (l0_deliver w a).chans
Proof
  strip_tac >> qspecl_then [‘c’, ‘w’, ‘a’] mp_tac (Q.GENL [‘c’, ‘w’, ‘a’] deliver_chan) >>
  simp[chan_mono_def]
QED

Theorem FOLDL_deliver_inflight[local]:
  ∀as w. inflight_le c w (FOLDL l0_deliver w as)
Proof
  Induct >- simp[inflight_le_def] >> rw[] >>
  irule inflight_le_trans >> qexists_tac ‘l0_deliver w h’ >> simp[deliver_inflight, deliver_len]
QED

Theorem tick_inflight:
  inflight_le c w (l0_tick nm w)
Proof
  simp[l0_tick_def] >>
  qspecl_then [‘w.env w.clock w.hist nm’, ‘w with clock := w.clock + 1’] mp_tac FOLDL_deliver_inflight >>
  simp[inflight_le_def]
QED

(* MAIN *)
Theorem ticks_inflight:
  ∀k w. inflight_le c w (l0_ticks nm k w)
Proof
  Induct >- simp[l0_ticks_def, inflight_le_def] >> rw[l0_ticks_def] >>
  irule inflight_le_trans >> qexists_tac ‘l0_tick nm w’ >> simp[tick_inflight] >>
  qspecl_then [‘c’, ‘w’, ‘nm’] mp_tac (Q.GENL [‘c’, ‘w’, ‘nm’] tick_chan) >> simp[chan_mono_def]
QED
