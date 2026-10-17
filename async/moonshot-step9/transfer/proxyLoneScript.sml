(*
  Moonshot step 9: ep_ok (moonshotProxyGlue) for every prefix of a lone
  program's trace on a fresh honest L0 world, given that it checked fd 0
  before getting it and never closes it (W2's two trace conditions).  The
  four parts come from moonshotLoneTrace's induction with moonshotWorldFacts'
  per-call lemmas, as l0sys_ep_ok does for a process of an l0sys run.
*)
Theory proxyLone
Ancestors
  moonshotLoneTrace moonshotWorldFacts moonshotW2 moonshotProxyGlue
Libs
  preamble

(* W1 for a lone run, for events that do not get fd 0 *)
Theorem lone_opens_ok:
  w0.listeners = [] ∧ w0.chans = [] ∧ w0.open_fds = [] ∧ fds_lt w0 ∧ l0_rely w0 ∧
  semantics_prog (init_state (l0_ffi w0)) init_env prog beh ∧
  LPREFIX (fromList evs) (beh_io beh) ⇒
  EVERY (λev. (∀r. ev_new ev ≠ SOME (0w, r)) ⇒ opens_ok ev) evs
Proof
  strip_tac >>
  qspecl_then [‘EVERY (λev. (∀r. ev_new ev ≠ SOME (0w, r)) ⇒ opens_ok ev)’, ‘K (K T)’]
    mp_tac (Q.GENL [‘Q’, ‘Inv’] lone_induct) >>
  simp[] >> disch_then irule >> rpt strip_tac >> simp[] >>
  rpt strip_tac >> irule call_opens_ok >> metis_tac[]
QED

(* W4 for a lone run *)
Theorem lone_accepts_known:
  w0.listeners = [] ∧ w0.chans = [] ∧ w0.open_fds = [] ∧ fds_lt w0 ∧ l0_rely w0 ∧
  semantics_prog (init_state (l0_ffi w0)) init_env prog beh ∧
  LPREFIX (fromList evs) (beh_io beh) ⇒ accepts_known evs
Proof
  strip_tac >>
  qspecl_then [‘accepts_known’, ‘K (K T)’] mp_tac (Q.GENL [‘Q’, ‘Inv’] lone_induct) >>
  simp[] >> disch_then irule >> rpt conj_tac >>
  FIRST [simp[accepts_known_def] >> NO_TAC,
         rpt strip_tac >> simp[accepts_known_SNOC] >> rpt strip_tac >>
         drule_all call_accept_known >> simp[]]
QED

Theorem lone_ep_ok:
  w0.listeners = [] ∧ w0.chans = [] ∧ w0.open_fds = [] ∧ fds_lt w0 ∧ l0_rely w0 ∧
  semantics_prog (init_state (l0_ffi w0)) init_env prog beh ∧
  LPREFIX (fromList evs) (beh_io beh) ∧ fd0_checked evs ∧ no_close0 evs ⇒
  ep_ok evs
Proof
  strip_tac >>
  ‘EVERY (λev. ∀r. ev_new ev ≠ SOME (0w, r)) evs’ by (drule_all lone_no_fd0 >> simp[]) >>
  simp[ep_ok_def] >> rpt conj_tac
  >- (drule_all lone_opens_ok >> strip_tac >> fs[EVERY_MEM])
  >- (drule_all lone_ops_live >> simp[])
  >- (drule_all lone_accepts_known >> simp[])
QED
