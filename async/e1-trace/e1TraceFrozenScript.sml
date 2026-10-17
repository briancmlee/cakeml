(*
  chan_frozen from the trace to round boundaries (close-v2's part (d)):
  a channel's peer_eof, broken and closed flags are only ever set along a
  replay (fmono, as smono), so a channel frozen at some prefix of io is
  frozen at every round boundary from some point on, and conversely.

  MAIN: frozen_bounds, bounds_frozen.
*)
Theory e1TraceFrozen
Ancestors
  e1TraceDrains e1TraceWorld clientLiveCopy honestL0World
Libs
  preamble

Definition frz_def:
  frz (w : l0world) c ⇔
    c < LENGTH w.chans ∧
    ((EL c w.chans).peer_eof ∨ (EL c w.chans).broken ∨ (EL c w.chans).closed)
End

Definition fmono_def:
  fmono c (w : l0world) (w' : l0world) ⇔
    c < LENGTH w.chans ⇒
    c < LENGTH w'.chans ∧
    ((EL c w.chans).peer_eof ⇒ (EL c w'.chans).peer_eof) ∧
    ((EL c w.chans).broken ⇒ (EL c w'.chans).broken) ∧
    ((EL c w.chans).closed ⇒ (EL c w'.chans).closed)
End

Theorem fmono_refl[simp]:
  fmono c w w
Proof
  simp[fmono_def]
QED

Theorem fmono_trans:
  fmono c w1 w2 ∧ fmono c w2 w3 ⇒ fmono c w1 w3
Proof
  rw[fmono_def] >> fs[]
QED

Theorem fmono_frz:
  fmono c w w' ∧ frz w c ⇒ frz w' c
Proof
  rw[fmono_def, frz_def] >> fs[]
QED

Theorem deliver_fmono[local]:
  fmono c w (l0_deliver w a)
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def, fmono_def, upd_lchan_def, EL_LUPDATE] >>
  every_case_tac >> gvs[EL_APPEND1, EL_LUPDATE] >> rw[] >> gvs[break_lchan_def] >> rw[]
QED

Theorem FOLDL_deliver_fmono[local]:
  ∀as w. fmono c w (FOLDL l0_deliver w as)
Proof
  Induct >> simp[] >> metis_tac[fmono_trans, deliver_fmono]
QED

Theorem tick_fmono[local]:
  fmono c w (l0_tick nm w)
Proof
  simp[l0_tick_def] >>
  irule fmono_trans >> qexists_tac ‘w with clock := w.clock + 1’ >>
  simp[FOLDL_deliver_fmono] >> simp[fmono_def]
QED

Theorem ticks_fmono[local]:
  ∀k w. fmono c w (l0_ticks nm k w)
Proof
  Induct >> simp[l0_ticks_def] >> metis_tac[fmono_trans, tick_fmono]
QED

Theorem FOLDL_fmono[local]:
  ∀q w1. (∀w' j. fmono c w' (f w' j)) ∧ fmono c w w1 ⇒ fmono c w (FOLDL f w1 q)
Proof
  Induct >> rw[] >> first_x_assum irule >> simp[] >> metis_tac[fmono_trans]
QED

Theorem l0_call_fmono[local]:
  l0_call n conf bytes w = SOME (FFIreturn out w') ⇒ fmono c w w'
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  TRY (simp[ticks_fmono] >> NO_TAC) >>
  TRY (simp[fmono_def] >> NO_TAC) >>
  gvs[l0_listen_def, l0_accept_def, l0_recv_def, l0_send_def, l0_shutdown_def,
      l0_connect_def, l0_connerr_def, l0_close_def, close_fd_def, l0_alloc_def,
      AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[AllCaseEqs()]) >>
  TRY (irule FOLDL_fmono >> conj_tac >> rpt gen_tac >>
       rw[fmono_def, EL_LUPDATE, upd_lchan_def, break_lchan_def] >> rw[] >> NO_TAC) >>
  rw[fmono_def, upd_lchan_def, EL_LUPDATE, break_lchan_def, EL_APPEND1] >> rw[] >>
  gvs[]
QED

Theorem step_fmono[local]:
  l0_step (SOME w) lc = SOME w' ⇒ fmono c w w'
Proof
  PairCases_on ‘lc’ >> rw[l0_step_def, l0_ffi_fn_def, AllCaseEqs()] >>
  irule fmono_trans >> qexists_tac ‘l0_tick lc0 w’ >>
  conj_tac >- simp[tick_fmono] >>
  drule l0_call_fmono >> simp[fmono_def]
QED

Theorem FOLDL_step_NONE[local]:
  ∀cs. FOLDL l0_step NONE cs = NONE
Proof
  Induct >> simp[l0_step_def]
QED

Theorem replay_fmono[local]:
  ∀cs w w'. FOLDL l0_step (SOME w) cs = SOME w' ⇒ fmono c w w'
Proof
  Induct >- simp[] >> rpt gen_tac >> simp[] >>
  Cases_on ‘l0_step (SOME w) h’ >> simp[FOLDL_step_NONE] >> strip_tac >>
  irule fmono_trans >> qexists_tac ‘x’ >>
  conj_tac >- (irule step_fmono >> qexists_tac ‘h’ >> first_assum ACCEPT_TAC) >>
  first_x_assum irule >> first_assum ACCEPT_TAC
QED

Theorem world_at_fmono:
  world_at w0 a = SOME x ∧ world_at w0 (a ++ b) = SOME y ⇒ fmono c x y
Proof
  rw[world_at_def, l0_replay_def, FOLDL_APPEND] >> gvs[] >> metis_tac[replay_fmono]
QED

Theorem bounds_fmono:
  bounds w0 io B ∧ a ≤ b ⇒ fmono c (bworld w0 B a) (bworld w0 B b)
Proof
  strip_tac >>
  ‘B a ≼ B b’ by fs[bounds_def] >>
  fs[IS_PREFIX_APPEND] >>
  irule world_at_fmono >> qexistsl_tac [‘B a’, ‘l’, ‘w0’] >>
  metis_tac[bounds_world]
QED

Theorem chan_frozen_frz:
  chan_frozen w0 io c ⇔ ∃evs w. LPREFIX (fromList evs) io ∧ world_at w0 evs = SOME w ∧ frz w c
Proof
  simp[chan_frozen_def, frz_def]
QED

(* MAIN: frozen on the trace ⇒ frozen at all late boundaries *)
Theorem frozen_bounds:
  bounds w0 io B ∧ chan_frozen w0 io c ⇒ ∃n. ∀m. n ≤ m ⇒ frz (bworld w0 B m) c
Proof
  rw[chan_frozen_frz] >>
  drule_all bounds_locate >> disch_then (qspec_then ‘0’ strip_assume_tac) >>
  qexists_tac ‘M’ >> rpt strip_tac >>
  irule fmono_frz >> qexists_tac ‘w’ >> simp[] >>
  ‘B M ≼ B m’ by fs[bounds_def] >>
  ‘evs ≼ B m’ by metis_tac[IS_PREFIX_TRANS] >>
  ‘∃t. B m = evs ++ t’ by metis_tac[IS_PREFIX_APPEND] >>
  irule world_at_fmono >> qexistsl_tac [‘evs’, ‘t’, ‘w0’] >>
  metis_tac[bounds_world]
QED

(* and back *)
Theorem bounds_frozen:
  bounds w0 io B ∧ frz (bworld w0 B n) c ⇒ chan_frozen w0 io c
Proof
  rw[chan_frozen_frz] >>
  qexistsl_tac [‘B n’, ‘bworld w0 B n’] >>
  fs[bounds_def] >> metis_tac[bounds_world, bounds_def]
QED
