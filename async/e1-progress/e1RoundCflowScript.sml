(*
  Channel flow along E1's calls (close-v2, shared E1 progress layer,
  post-R3): honest-l1's cflow lemmas (honestL1PFFlush) on ewinv, and for
  the calls PF does not make: a connect (a new channel; the others are
  kept) and a shutdown of another fd.

  MAIN: sys_ecflow.
*)
Theory e1RoundCflow
Ancestors
  e1RoundInv honestL1EPModel honestL1PFClose honestL1PFFlush honestL1PFOut honestL1PFRefine
  honestL1PFRound honestL1Model honestL0WorldInv honestL0WorldProps honestL0Rely honestL0World
Libs
  preamble

Theorem cflow_connect_call:
  l0_chan_of w f = SOME c ∧ fds_lt w ∧ w.fd_limit ≤ 2 ** 31 ∧
  l0_call «sys_connect» conf bytes w = SOME (FFIreturn bytes' w') ⇒
  l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c
Proof
  strip_tac >>
  ‘c < LENGTH w.chans’ by metis_tac[chan_lt] >>
  ‘MEM f (l0_used w)’
    by (gvs[l0_chan_of_def, AllCaseEqs(), l0_used_def] >> imp_res_tac ALOOKUP_MEM >>
        simp[MEM_MAP] >> metis_tac[FST]) >>
  ‘lowest_fd w ≠ f’ by metis_tac[lowest_fd_fresh] >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >>
  simp[l0_call_def, l0_connect_def, l0_alloc_def, AllCaseEqs()] >> rw[] >>
  rpt (qpat_x_assum ‘fail _ _ = _’ kall_tac) >>
  gvs[cflow_def, csent_def, l0_chan_of_def, AllCaseEqs(), upd_lchan_def, EL_LUPDATE, EL_APPEND1]
QED

Theorem cflow_shutdown_call:
  l0_chan_of w f = SOME c ∧ l0wf w ∧ bytes_fd conf ≠ f ∧
  l0_call «sys_shutdown» conf bytes w = SOME (FFIreturn bytes' w') ⇒
  l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c
Proof
  strip_tac >>
  ‘c < LENGTH w.chans’ by metis_tac[chan_lt] >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >>
  simp[l0_call_def] >> rw[] >> pairarg_tac >> gvs[] >>
  qpat_x_assum ‘l0_shutdown _ _ = _’ mp_tac >>
  simp[l0_shutdown_def, AllCaseEqs()] >> rw[] >> simp[] >>
  rename1 ‘l0_chan_of w g = SOME j’ >>
  ‘j ≠ c’
    by (gvs[l0_chan_of_def, AllCaseEqs()] >> metis_tac[open_chan_ne]) >>
  gvs[cflow_def, csent_def, l0_chan_of_def, upd_lchan_def, EL_LUPDATE]
QED

(* An L0 call through L1's wrappers, connects and shutdowns included *)
Theorem ecflow_do:
  ewinv w ∧ l0_chan_of w f = SOME c ∧
  ¬(n = «sys_shutdown» ∧ bytes_fd conf = f) ∧ ¬(n = «sys_close» ∧ bytes_fd conf = f) ∧
  l0_do n conf alen w = SOME (out, w', ev) ⇒
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
    by (gvs[Abbr ‘wt’, ewinv_def, l0wf_tick] >> irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  ‘wt.fd_limit ≤ 2 ** 31’ by gvs[l0_rely_def] >>
  ‘l0_chan_of w1 f = SOME c ∧ cflow wt w1 c ∧
   (¬(n = «sys_send» ∧ bytes_fd (TAKE 8 conf) = f) ⇒ csent w1 c = csent wt c)’
    by (Cases_on ‘n = «sys_connect»’
        >- (gvs[] >> drule_at (Pos last) cflow_connect_call >> simp[] >>
            disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >> simp[]) >>
        Cases_on ‘n = «sys_shutdown»’
        >- (gvs[] >> drule_at (Pos last) cflow_shutdown_call >> simp[] >>
            disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >> simp[]) >>
        drule_at (Pos last) cflow_call >> disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >>
        impl_tac >- (fs[] >> metis_tac[]) >> simp[]) >>
  simp[] >> conj_tac
  >- (irule cflow_trans >> qexists_tac ‘wt’ >> simp[] >> gvs[cflow_def, csent_def]) >>
  strip_tac >> ‘csent wt c = csent w c’ by simp[Abbr ‘wt’, csent_tick] >>
  fs[csent_def]
QED

Theorem ecflow_do_buf:
  ewinv w ∧ l0_chan_of w f = SOME c ∧
  ¬(n = «sys_shutdown» ∧ bytes_fd conf = f) ∧ ¬(n = «sys_close» ∧ bytes_fd conf = f) ∧
  l0_do_buf n conf bs w = SOME (out, w', ev) ⇒
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
    by (gvs[Abbr ‘wt’, ewinv_def, l0wf_tick] >> irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  ‘wt.fd_limit ≤ 2 ** 31’ by gvs[l0_rely_def] >>
  ‘l0_chan_of w1 f = SOME c ∧ cflow wt w1 c ∧
   (¬(n = «sys_send» ∧ bytes_fd (TAKE 8 conf) = f) ⇒ csent w1 c = csent wt c)’
    by (Cases_on ‘n = «sys_connect»’
        >- (gvs[] >> drule_at (Pos last) cflow_connect_call >> simp[] >>
            disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >> simp[]) >>
        Cases_on ‘n = «sys_shutdown»’
        >- (gvs[] >> drule_at (Pos last) cflow_shutdown_call >> simp[] >>
            disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >> simp[]) >>
        drule_at (Pos last) cflow_call >> disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >>
        impl_tac >- (fs[] >> metis_tac[]) >> simp[]) >>
  simp[] >> conj_tac
  >- (irule cflow_trans >> qexists_tac ‘wt’ >> simp[] >> gvs[cflow_def, csent_def]) >>
  strip_tac >> ‘csent wt c = csent w c’ by simp[Abbr ‘wt’, csent_tick] >>
  fs[csent_def]
QED

(* L1's calls: every one but a close or shutdown of f keeps f's channel
   and its flow; only a send on f adds to what was sent on it *)
Theorem sys_ecflow:
  (ewinv w ∧ l0_chan_of w f = SOME c ∧ sys_recv g k w = SOME (out, w', ev) ⇒
   l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c) ∧
  (ewinv w ∧ l0_chan_of w f = SOME c ∧ sys_accept g w = SOME (out, w', ev) ⇒
   l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c) ∧
  (ewinv w ∧ l0_chan_of w f = SOME c ∧ sys_poll fes w = SOME (out, w', ev) ⇒
   l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c) ∧
  (ewinv w ∧ l0_chan_of w f = SOME c ∧ sys_send g bs w = SOME (out, w', ev) ⇒
   l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ (g ≠ f ⇒ csent w' c = csent w c)) ∧
  (ewinv w ∧ l0_chan_of w f = SOME c ∧ g ≠ f ∧ sys_close g w = SOME (out, w', ev) ⇒
   l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c) ∧
  (ewinv w ∧ l0_chan_of w f = SOME c ∧ sys_connerr g w = SOME (out, w', ev) ⇒
   l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c) ∧
  (ewinv w ∧ l0_chan_of w f = SOME c ∧ g ≠ f ∧ sys_shutdown g w = SOME (out, w', ev) ⇒
   l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c) ∧
  (ewinv w ∧ l0_chan_of w f = SOME c ∧ sys_connect p w = SOME (out, w', ev) ⇒
   l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c)
Proof
  rpt conj_tac >> strip_tac >>
  gvs[sys_recv_def, sys_accept_def, sys_poll_def, sys_send_def, sys_close_def,
      sys_connerr_def, sys_shutdown_def, sys_connect_def] >>
  TRY (drule_at (Pos last) ecflow_do_buf >>
       disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >> simp[] >> NO_TAC) >>
  TRY (drule_at (Pos last) ecflow_do >>
       disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >> simp[] >> NO_TAC) >>
  drule_at (Pos last) ecflow_do >>
  disch_then (qspecl_then [‘f’, ‘c’] mp_tac) >> simp[] >> strip_tac >> simp[] >> strip_tac >>
  ‘LENGTH (fd_bytes g) = 8’ by simp[] >>
  metis_tac[TAKE_LENGTH_APPEND]
QED
