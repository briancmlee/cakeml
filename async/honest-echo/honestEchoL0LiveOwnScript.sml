(*
  The ownership invariant (honestEchoL0Inv's own_ok) along honest-l1's
  plain run (honestL1PFLive: prun / rstate / rworld / revs / rrev), for
  async-spike's echo liveness (the excuse mapping): every fd L1 holds (in
  its table, closing, or pending) is open in the spec's episode map at
  that point of the trace.

  run_own: at every round boundary.
  call_open: at every send or recv call of a round, the call's fd is open
  in the episode map of the trace before it.
*)
Theory honestEchoL0LiveOwn
Ancestors
  alist ffi honestL0 honestL0World honestL0WorldProps honestL0Rely
  asyncHLModel honestL1Model honestL1Steps honestL1PFModel honestL1PFInv
  honestL1PFRound honestL1PFLive honestL1PFFlush
  asyncM3World honestEchoL0Spec honestEchoL0Trace honestEchoL0Events
  honestEchoL0Model honestEchoL0Inv honestEchoL0Round honestEchoL0Out
Libs
  preamble

(* A round keeps the outboxes on held fds *)
Theorem pround_okb:
  pround lfd hw hs (w, ps) acts = SOME (sn, (w', ps'), log, evs) ∧
  wown lfd w ps ∧ own_ok lfd (k, opn) ps ∧ LENGTH ps.acq ≤ 1 ∧ okb ps.b ∧
  ps.b.nxt + naccepts acts < dimword (:64) ⇒
  okb ps'.b
Proof
  strip_tac >> qpat_x_assum ‘pround _ _ _ _ _ = _’ mp_tac >>
  simp[pround_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  rename1 ‘pacts _ _ _ = SOME (rs, evs1, ws1)’ >> PairCases_on ‘ws1’ >>
  ‘l0_rely w’ by gvs[wown_def] >>
  drule_all pacts_in >> strip_tac >>
  drule_all pacts_wown >> strip_tac >>
  drule_all pacts_okb >> strip_tac >>
  drule pacts_nxt_acc >> strip_tac >>
  drule pacts_nxt >> strip_tac >>
  Cases_on ‘l0_ep_st (k, opn) evs1’ >> gvs[] >>
  rename1 ‘own_ok lfd (k, opn1) ws11’ >>
  ‘LENGTH ws11.acq ≤ 1’ by (Cases_on ‘acts’ >> gvs[own_ok_def]) >>
  ‘ws11.b.nxt < dimword (:64)’ by fs[] >>
  ‘hdln (w2n lfd) 0 < dimword (:64)’ by rw[hdln_def] >>
  ‘oi lfd ws11 opn1 [] (obp lfd ws11 opn1 0) 0’
    by (irule oi_triv >> fs[] >> qexists_tac ‘k’ >> fs[]) >>
  drule_all pf_tail_out >> simp[]
QED

(* MAIN (a): along the run, L1 owns only fds of open episodes, its
   handles are episodes' (own_ok), and the world's ownership holds *)
Theorem run_own:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ⇒
  ∀n. wown lfd (rworld lfd pol ifds m w0 n) (rstate lfd pol ifds m w0 n) ∧
      own_ok lfd (l0_ep_st (0, []) (revs lfd pol ifds m w0 n)) (rstate lfd pol ifds m w0 n) ∧
      LENGTH (rstate lfd pol ifds m w0 n).acq ≤ 1 ∧ okb (rstate lfd pol ifds m w0 n).b
Proof
  strip_tac >> Induct
  >- (simp[rworld_def, rstate_def, revs_def, prun_0] >>
      gvs[winv_def, wown_def, owned_def, own_ok_def, ep_ok_def, pinit_def, l1init_def,
          inb_of_def, okb_def, outbox_of_def]) >>
  drule prun_round >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  drule prun_some >> disch_then (qspec_then ‘n’ assume_tac) >>
  ‘(rstate lfd pol ifds m w0 n).b.nxt +
   naccepts (new_actions (log_of m) (rhist lfd pol ifds m w0 n)) < dimword (:64)’
    by (Cases_on ‘prun lfd pol ifds m w0 n’ >> rename1 ‘_ = (hh, r)’ >> PairCases_on ‘r’ >>
        gvs[rstate_def, rhist_def, run_ok_def, pl2_ok_def] >>
        first_x_assum drule >> simp[]) >>
  Cases_on ‘l0_ep_st (0, []) (revs lfd pol ifds m w0 n)’ >>
  qpat_x_assum ‘wown _ _ _ ∧ _’ strip_assume_tac >>
  drule_all pround_in >> strip_tac >>
  drule_all pround_okb >> strip_tac >> gvs[]
QED

(* ------------------------------------------------------------------------
   (b) At every send or recv call, its fd is open
   ------------------------------------------------------------------------ *)

(* Every send or recv in evs is on a fd open (in the episode map) just
   before it, the map starting from s *)
Definition sr_open_def:
  sr_open s [] = T ∧
  sr_open s (ev :: evs) =
    ((∀f. ev_on «sys_send» f ev ∨ ev_on «sys_recv» f ev ⇒ ∃j. ALOOKUP (SND s) f = SOME j) ∧
     sr_open (l0_ep_step s ev) evs)
End

Theorem sr_open_APPEND:
  ∀xs s. sr_open s (xs ++ ys) ⇔ sr_open s xs ∧ sr_open (l0_ep_st s xs) ys
Proof
  Induct >> simp[sr_open_def] >> metis_tac[]
QED

Theorem sr_open_at:
  sr_open s (pre ++ [ev] ++ post) ∧ (ev_on «sys_send» f ev ∨ ev_on «sys_recv» f ev) ⇒
  ∃j. ALOOKUP (SND (l0_ep_st s pre)) f = SOME j
Proof
  rw[sr_open_APPEND, sr_open_def] >> metis_tac[]
QED

(* Events that are neither sends nor recvs *)
Theorem sr_open_quiet:
  ∀evs s. EVERY (λev. ev_name ev ≠ ExtCall «sys_send» ∧ ev_name ev ≠ ExtCall «sys_recv») evs ⇒
          sr_open s evs
Proof
  Induct >> simp[sr_open_def] >> rpt strip_tac >> imp_res_tac ev_on_name >> gvs[]
QED

Theorem sys_close_name:
  sys_close f w = SOME (out, w', ev) ⇒ ev_name ev = ExtCall «sys_close»
Proof
  rw[sys_close_def] >> drule l0_do_cases >> strip_tac >> gvs[ev_name_def]
QED

Theorem sys_poll_name:
  sys_poll fes w = SOME (out, w', ev) ⇒ ev_name ev = ExtCall «sys_poll»
Proof
  rw[sys_poll_def] >> drule l0_do_buf_cases >> strip_tac >> gvs[ev_name_def]
QED

Theorem sys_accept_name:
  sys_accept l w = SOME (out, w', ev) ⇒ ev_name ev = ExtCall «sys_accept»
Proof
  rw[sys_accept_def] >> drule l0_do_cases >> strip_tac >> gvs[ev_name_def]
QED

Theorem sys_send_name:
  sys_send f bs w = SOME (out, w', ev) ⇒ ev_name ev = ExtCall «sys_send»
Proof
  rw[sys_send_def] >> drule l0_do_cases >> strip_tac >> gvs[ev_name_def]
QED

Theorem ev_on_recv:
  sys_recv g n w = SOME (out, w', ev) ⇒ (ev_on «sys_recv» f ev ⇔ g = f) ∧
                                         ev_name ev = ExtCall «sys_recv»
Proof
  rw[sys_recv_def] >> drule l0_do_cases >> strip_tac >> gvs[ev_name_def] >>
  simp[ev_on_def, call_fds_def] >>
  ‘LENGTH (fd_bytes g) = 8’ by simp[] >>
  ‘TAKE 8 (fd_bytes g) = fd_bytes g’ by simp[TAKE_LENGTH_ID_rwt] >>
  simp[] >> metis_tac[]
QED

(* A send: open if its fd is *)
Theorem sr_open_send:
  sys_send g bs w = SOME (out, w', ev) ∧ ALOOKUP (SND s) g = SOME j ⇒ sr_open s [ev]
Proof
  rw[sr_open_def] >> imp_res_tac sys_send_name >>
  TRY (drule ev_on_name >> simp[] >> NO_TAC) >>
  metis_tac[ev_on_send]
QED

Theorem sr_open_recv:
  sys_recv g n w = SOME (out, w', ev) ∧ ALOOKUP (SND s) g = SOME j ⇒ sr_open s [ev]
Proof
  rw[sr_open_def] >> drule ev_on_recv >> disch_then (qspec_then ‘f’ strip_assume_tac) >>
  imp_res_tac ev_on_name >> gvs[]
QED

Theorem sr_open_one_quiet:
  ev_name ev = ExtCall nm ∧ nm ≠ «sys_send» ∧ nm ≠ «sys_recv» ⇒ sr_open s [ev]
Proof
  rw[sr_open_def] >> imp_res_tac ev_on_name >> gvs[]
QED

(* One action *)
Theorem pdo_so:
  pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ∧ l0_rely w ∧ own_ok lfd (k, opn) ps ⇒
  sr_open (k, opn) evs
Proof
  strip_tac >> Cases_on ‘a’
  >- (drule pdo_accept_in >> strip_tac >> gvs[sr_open_def])
  >- (qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def] >>
      rw[AllCaseEqs()] >> gvs[sr_open_def] >>
      PairCases_on ‘z’ >> gvs[] >>
      drule l1_close_shape >> strip_tac >> gvs[] >>
      irule sr_open_one_quiet >> imp_res_tac sys_close_name >> simp[]) >>
  qpat_x_assum ‘pdo _ _ _ = _’ mp_tac >> simp[pdo_def, PULL_EXISTS] >> rpt gen_tac >>
  PairCases_on ‘z’ >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum ‘l1do _ _ _ = _’ mp_tac >> simp[l1do_def] >>
  rw[AllCaseEqs()] >> gvs[sr_open_def] >>
  drule_all own_tbl_lookup >> strip_tac >>
  ‘ALOOKUP (SND (k, opn)) f = SOME j’ by simp[] >>
  ‘sr_open (k, opn) [ev]’ by metis_tac[sr_open_send] >>
  fs[sr_open_def]
QED

Theorem pacts_so:
  ∀acts w ps rs evs w' ps' opn.
    pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ∧ l0_rely w ∧
    own_ok lfd (k, opn) ps ∧ ps.b.nxt + naccepts acts < dimword (:64) ⇒
    sr_open (k, opn) evs
Proof
  Induct >> simp[pacts_def, sr_open_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  PairCases_on ‘ws1’ >> rename1 ‘pdo lfd (w, ps) a = SOME (r, (w1, ps1), evs1)’ >>
  ‘ps.b.nxt < dimword (:64)’ by simp[] >>
  ‘ps1.b.nxt + naccepts acts < dimword (:64)’
    by (drule pdo_nxt_acc >>
        ‘naccepts (a :: acts) = naccepts [a] + naccepts acts’ by (Cases_on ‘a’ >> simp[]) >>
        fs[]) >>
  drule_all pdo_in >> strip_tac >>
  drule_all pdo_rely >> strip_tac >>
  drule_all pdo_so >> strip_tac >>
  Cases_on ‘l0_ep_st (k, opn) evs1’ >> gvs[] >>
  simp[sr_open_APPEND] >> first_x_assum irule >> metis_tac[]
QED

Theorem l1_polls_so:
  ∀cs w rv w' evs. l1_polls cs w = SOME (rv, w', evs) ∧ l0_rely w ⇒ ∀s. sr_open s evs
Proof
  Induct >> simp[l1_polls_def, sr_open_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> drule_all sys_poll_event >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> gen_tac >>
  simp[sr_open_def] >> imp_res_tac sys_poll_name >> rpt strip_tac >>
  imp_res_tac ev_on_name >> gvs[]
QED

Theorem l1_reap_so:
  ∀fs w b w' b' evs.
    l1_reap fs (w, b) = SOME ((w', b'), evs) ∧ l0_rely w ⇒ ∀s. sr_open s evs
Proof
  Induct >> simp[l1_reap_def, sr_open_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  PairCases_on ‘ws’ >> drule l1_close_shape >> strip_tac >> gvs[] >>
  drule_all sys_close_event >> strip_tac >>
  ‘l0_rely ws0’ by (gvs[sys_close_def] >> metis_tac[l0_do_rely]) >>
  first_x_assum drule_all >> strip_tac >> gen_tac >>
  simp[sr_open_def] >> imp_res_tac sys_close_name >> rpt strip_tac >>
  imp_res_tac ev_on_name >> gvs[]
QED

Theorem after_send_nfields2[local]:
  (after_send f r st).tbl = st.tbl ∧ (after_send f r st).nxt = st.nxt ∧
  (after_send f r st).closing = st.closing
Proof
  rw[after_send_def] >> every_case_tac >> simp[set_outbox_def]
QED

(* A fd L1 holds belongs to a handed-out episode (as honestEchoL0NoGuard's
   own_held) *)
Theorem own_held2[local]:
  own_ok lfd (k, opn) ps ∧ (MEM f (MAP SND ps.b.tbl) ∨ MEM f ps.b.closing) ⇒
  ∃i. i < ps.b.nxt ∧ ALOOKUP opn f = SOME i
Proof
  rw[own_ok_def, MEM_MAP, EXISTS_PROD] >> res_tac >> metis_tac[]
QED

Theorem l1_flush_so:
  ∀fs w b w' b' evs.
    l1_flush fs (w, b) = SOME ((w', b'), evs) ∧ l0_rely w ∧ okb b ∧
    own_ok lfd (k, opn) (ps with b := b) ⇒
    sr_open (k, opn) evs
Proof
  Induct >> simp[l1_flush_def, sr_open_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >> IF_CASES_TAC >> simp[]
  >- (strip_tac >>
      first_x_assum (qspecl_then [‘w’, ‘b’, ‘w'’, ‘b'’, ‘evs’] mp_tac) >> simp[]) >>
  simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >> gvs[] >>
  rename1 ‘sys_send h _ w = SOME (out, w1, ev)’ >>
  drule_all sys_send_event >> strip_tac >>
  ‘MEM h (MAP SND b.tbl) ∨ MEM h b.closing’ by gvs[okb_def] >>
  ‘∃i. i < b.nxt ∧ ALOOKUP opn h = SOME i’
    by (mp_tac (Q.INST [‘ps’ |-> ‘ps with b := b’, ‘f’ |-> ‘h’] own_held2) >> simp[]) >>
  ‘l0_rely w1’ by (gvs[sys_send_def] >> metis_tac[l0_do_rely]) >>
  ‘okb (after_send h (l0_res_of out) b)’ by (irule okb_after_send >> simp[]) >>
  ‘own_ok lfd (k, opn) (ps with b := after_send h (l0_res_of out) b)’
    by (mp_tac (Q.INST [‘ps'’ |-> ‘ps with b := after_send h (l0_res_of out) b’,
                        ‘ps’ |-> ‘ps with b := b’, ‘es’ |-> ‘(k, opn)’] own_ok_cong) >>
        simp[after_send_nfields2]) >>
  ‘sr_open (k, opn) evs'’
    by (first_x_assum (qspecl_then [‘w1’, ‘after_send h (l0_res_of out) b’, ‘w'’, ‘b'’, ‘evs'’]
          mp_tac) >> simp[]) >>
  ‘ALOOKUP (SND (k, opn)) h = SOME i’ by simp[] >>
  ‘sr_open (k, opn) [ev]’ by metis_tac[sr_open_send] >>
  ‘l0_ep_step (k, opn) ev = (k, opn)’ by simp[l0_ep_step_def] >>
  mp_tac (Q.INST [‘ys’ |-> ‘evs'’] (Q.SPECL [‘[ev]’, ‘(k, opn)’] sr_open_APPEND)) >>
  simp[] >> disch_then SUBST1_TAC >> fs[]
QED

Theorem pf_fetch_so:
  ∀fs w ps k opn w' ps' log evs.
    pf_fetch lfd hw fs (w, ps) = SOME ((w', ps'), log, evs) ∧
    wown lfd w ps ∧ own_ok lfd (k, opn) ps ∧ LENGTH ps.acq ≤ 1 ∧
    ps.b.nxt < dimword (:64) ∧
    (∀f. MEM f fs ⇒ f = lfd ∨ MEM f (MAP SND ps.b.tbl)) ⇒
    sr_open (k, opn) evs
Proof
  Induct >- (rw[pf_fetch_def] >> simp[sr_open_def]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘pf_fetch _ _ _ _ = _’ mp_tac >>
  simp[Once pf_fetch_def] >> IF_CASES_TAC >> simp[]
  >- (strip_tac >>
      first_x_assum (qspecl_then [‘w’, ‘ps’, ‘k’, ‘opn’, ‘w'’, ‘ps'’, ‘log’, ‘evs’] mp_tac) >>
      impl_tac >- (fs[] >> metis_tac[]) >> simp[]) >>
  IF_CASES_TAC >> simp[]
  >- (qpat_x_assum ‘h = lfd’ SUBST_ALL_TAC >>
      ‘ps.acq = [] ∧ ps.pause = 0’ by gvs[wants_input_def] >>
      Cases_on ‘sys_accept lfd w’ >> simp[] >> PairCases_on ‘x’ >> simp[] >>
      rename1 ‘sys_accept lfd w = SOME (out, w1, ev)’ >>
      pairarg_tac >> simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
      ‘ps1 = case l0_res_of out of
             | Ok k' => ps with acq := ps.acq ++ [n2w k']
             | Fail e _ => if e = E_MFILE then ps with pause := pf_backoff else ps’
        by (every_case_tac >> gvs[]) >>
      drule_all fetch_acc_step >> strip_tac >>
      ‘∃k1 opn1. l0_ep_step (k, opn) ev = (k1, opn1)’ by metis_tac[PAIR] >>
      first_x_assum (qspecl_then [‘w1’, ‘ps1’, ‘k1’, ‘opn1’, ‘w'’, ‘ps'’, ‘log'’, ‘evs'’] mp_tac) >>
      impl_tac
      >- (gvs[] >> rpt conj_tac >> TRY (every_case_tac >> gvs[] >> NO_TAC) >> metis_tac[]) >>
      strip_tac >> gvs[sr_open_def] >> rpt strip_tac >>
      imp_res_tac sys_accept_name >> imp_res_tac ev_on_name >> gvs[]) >>
  ‘inb_of ps h = [] ∧ MEM h (MAP SND ps.b.tbl)’ by (gvs[wants_input_def] >> metis_tac[]) >>
  Cases_on ‘sys_recv h pf_chunk w’ >> simp[] >> PairCases_on ‘x’ >> simp[] >>
  rename1 ‘sys_recv h pf_chunk w = SOME (out, w1, ev)’ >>
  pairarg_tac >> simp[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  ‘ps1 = case l0_res_of out of
         | Ok n => if 0 < n then set_inb h (TAKE n (DROP 13 out)) ps
                   else ps with eof := h :: ps.eof
         | Fail e _ => if l1_transient e then ps else ps with eof := h :: ps.eof’
    by (every_case_tac >> gvs[]) >>
  drule_all fetch_recv_step >> strip_tac >>
  ‘l0_ep_step (k, opn) ev = (k, opn)’
    by (‘l0_rely w’ by gvs[wown_def] >> drule_all sys_recv_event >> simp[l0_ep_step_def]) >>
  first_x_assum (qspecl_then [‘w1’, ‘ps1’, ‘k’, ‘opn’, ‘w'’, ‘ps'’, ‘log'’, ‘evs'’] mp_tac) >>
  impl_tac
  >- (gvs[] >> rpt conj_tac >> TRY (every_case_tac >> gvs[] >> NO_TAC) >> metis_tac[]) >>
  strip_tac >>
  ‘∃i. i < ps.b.nxt ∧ ALOOKUP opn h = SOME i’ by metis_tac[own_held2] >>
  ‘ALOOKUP (SND (k, opn)) h = SOME i’ by simp[] >>
  ‘sr_open (k, opn) [ev]’ by metis_tac[sr_open_recv] >>
  gvs[] >>
  mp_tac (Q.INST [‘ys’ |-> ‘evs'’] (Q.SPECL [‘[ev]’, ‘(k, opn)’] sr_open_APPEND)) >>
  simp[] >> disch_then SUBST1_TAC >> fs[]
QED

Theorem l1p_b_id[local]:
  (ps : l1p) with b := ps.b = ps
Proof
  simp[l1p_component_equality]
QED

Theorem pf_tail_so:
  pf_tail lfd hw hs (w, ps) = SOME (rdy, (w', ps'), log, evs) ∧
  wown lfd w ps ∧ own_ok lfd (k, opn) ps ∧ LENGTH ps.acq ≤ 1 ∧
  ps.b.nxt < dimword (:64) ∧ okb ps.b ⇒
  sr_open (k, opn) evs
Proof
  strip_tac >> qpat_x_assum ‘pf_tail _ _ _ _ = _’ mp_tac >>
  simp[pf_tail_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  rename1 ‘l1_polls _ w = SOME (rv, w1, pevs)’ >>
  rename1 ‘l1_flush _ _ = SOME ((w2, b2), fevs)’ >>
  rename1 ‘pf_fetch _ _ _ _ = SOME ((w3, ps3'), log, gevs)’ >>
  rename1 ‘l1_reap _ _ = SOME ((w4, b4), cevs)’ >>
  ‘l0_rely w’ by gvs[wown_def] >>
  drule_all l1_polls_in >> disch_then (qspec_then ‘(k, opn)’ strip_assume_tac) >>
  drule_all l1_polls_so >> strip_tac >>
  drule_all l1_polls_wown >> strip_tac >>
  drule_all l1_flush_in >> disch_then (qspec_then ‘(k, opn)’ strip_assume_tac) >>
  ‘wown lfd w2 (ps with b := b2)’ by (irule l1_flush_wown >> metis_tac[]) >>
  ‘own_ok lfd (k, opn) (ps with b := ps.b)’ by simp[l1p_b_id] >>
  ‘sr_open (k, opn) fevs’
    by (mp_tac (Q.SPECL [‘writable_fds rv’, ‘w1’, ‘ps.b’, ‘w2’, ‘b2’, ‘fevs’] l1_flush_so) >>
        impl_tac >- fs[] >> simp[]) >>
  ‘own_ok lfd (k, opn) (ps with b := b2)’
    by (mp_tac (Q.INST [‘ps'’ |-> ‘ps with b := b2’, ‘es’ |-> ‘(k, opn)’] own_ok_cong) >>
        simp[]) >>
  ‘sr_open (k, opn) gevs’
    by (irule pf_fetch_so >>
        qexistsl [‘FILTER (λf. MEM f (in_fds (pf_poll_set lfd hw ps hs))) (readable_fds rv)’,
                  ‘hw’, ‘lfd’, ‘log’, ‘ps with b := b2’, ‘ps3'’, ‘w2’, ‘w3’] >>
        simp[] >>
        rw[MEM_FILTER] >> TRY (drule in_fds_poll_set >> simp[] >> NO_TAC) >> fs[]) >>
  drule pf_fetch_in >> disch_then (qspecl_then [‘k’, ‘opn’] mp_tac) >> simp[] >>
  impl_tac
  >- (rw[MEM_FILTER] >> TRY (drule in_fds_poll_set >> simp[] >> NO_TAC) >> fs[]) >>
  strip_tac >>
  ‘l0_rely w3’ by gvs[wown_def] >>
  drule_all l1_reap_so >> strip_tac >>
  qpat_x_assum ‘_ = evs’ (SUBST_ALL_TAC o SYM) >>
  fs[sr_open_APPEND]
QED

Theorem pround_so:
  pround lfd hw hs (w, ps) acts = SOME (sn, (w', ps'), log, evs) ∧
  wown lfd w ps ∧ own_ok lfd (k, opn) ps ∧ LENGTH ps.acq ≤ 1 ∧ okb ps.b ∧
  ps.b.nxt + naccepts acts < dimword (:64) ⇒
  sr_open (k, opn) evs
Proof
  strip_tac >> qpat_x_assum ‘pround _ _ _ _ _ = _’ mp_tac >>
  simp[pround_def, AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
  rename1 ‘pacts _ _ _ = SOME (rs, evs1, ws1)’ >> PairCases_on ‘ws1’ >>
  rename1 ‘pf_tail _ _ _ _ = SOME (rdy, _, log2, tevs)’ >>
  ‘l0_rely w’ by gvs[wown_def] >>
  ‘sr_open (k, opn) evs1’
    by (qspecl_then [‘acts’, ‘w’, ‘ps’, ‘rs’, ‘evs1’, ‘ws10’, ‘ws11’, ‘opn’] mp_tac pacts_so >>
        impl_tac >- fs[] >> simp[]) >>
  drule_all pacts_in >> strip_tac >>
  drule_all pacts_wown >> strip_tac >>
  drule_all pacts_okb >> strip_tac >>
  drule pacts_nxt_acc >> strip_tac >>
  drule pacts_nxt >> strip_tac >>
  Cases_on ‘l0_ep_st (k, opn) evs1’ >> gvs[] >>
  rename1 ‘own_ok lfd (k, opn1) ws11’ >>
  ‘LENGTH ws11.acq ≤ 1’ by (Cases_on ‘acts’ >> gvs[own_ok_def]) >>
  ‘ws11.b.nxt < dimword (:64)’ by fs[] >>
  ‘sr_open (k, opn1) tevs’
    by (mp_tac (Q.INST [‘w’ |-> ‘ws10’, ‘ps’ |-> ‘ws11’, ‘opn’ |-> ‘opn1’, ‘evs’ |-> ‘tevs’,
                        ‘log’ |-> ‘log2’] pf_tail_so) >>
        impl_tac >- fs[] >> simp[]) >>
  fs[sr_open_APPEND]
QED

(* MAIN (b): every send or recv call of round k is on a fd open in the
   episode map of the trace before it *)
Theorem call_open:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ MEM lfd (l0_used w0) ∧
  rrev lfd pol ifds m w0 k = pre ++ [ev] ++ post ∧
  (ev_on «sys_send» f ev ∨ ev_on «sys_recv» f ev) ⇒
  ∃j. ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 k ++ pre))) f = SOME j
Proof
  strip_tac >>
  drule_all run_own >> disch_then (qspec_then ‘k’ strip_assume_tac) >>
  drule prun_round' >> disch_then (qspecl_then [‘f’, ‘k’] strip_assume_tac) >>
  drule prun_some >> disch_then (qspec_then ‘k’ assume_tac) >>
  ‘(rstate lfd pol ifds m w0 k).b.nxt +
   naccepts (new_actions (log_of m) (rhist lfd pol ifds m w0 k)) < dimword (:64)’
    by (Cases_on ‘prun lfd pol ifds m w0 k’ >> rename1 ‘_ = (hh, r)’ >> PairCases_on ‘r’ >>
        gvs[rstate_def, rhist_def, run_ok_def, pl2_ok_def] >>
        first_x_assum drule >> simp[]) >>
  Cases_on ‘l0_ep_st (0, []) (revs lfd pol ifds m w0 k)’ >>
  ‘sr_open (q, r) (rrev lfd pol ifds m w0 k)’
    by (qpat_x_assum ‘pround _ _ _ _ _ = _’
          (fn th => mp_tac (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
             (INST [“k:num” |-> “q:num”, “opn:(word64 # num) list” |-> “r:(word64 # num) list”]
                pround_so)) th)) >>
        rpt (impl_tac >- fs[]) >> simp[]) >>
  gvs[] >> metis_tac[sr_open_at]
QED
