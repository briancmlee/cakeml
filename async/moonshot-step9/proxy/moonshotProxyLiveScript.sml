(*
  The proxy's pairing liveness (proxyHLStmts.proxy_guar_hl, its last
  clause): every accepted front gets a backend that comes up or is
  refused, unless connects return no socket infinitely often.

  The world-level frame (cfix): while a round does not read backend c,
  c keeps its fd f and channel j, and j's status is unchanged; so the
  round's first read of c answers ERefused exactly when j was Refused at
  the round's start, and otherwise c was Up then (READ).  Across polls,
  Up and Refused are final.
*)
Theory moonshotProxyLive
Ancestors
  moonshotProxySafe moonshotProxyRel moonshotProxy moonshotClient proxyHLStmts
  moonshotClientSpec endpointHLModel endpointWorld asyncHLModel asyncLevel1 asyncCore
  socketV2FFI
Libs
  preamble

Overload PH[local] = “λlfd b hw lv W0. ehhist lfd lv (pifds lfd b hw) (pprog lfd b hw) W0”
Overload PS[local] = “λlfd b hw lv W0 n. pstate lfd b hw (ehhist lfd lv (pifds lfd b hw) (pprog lfd b hw) W0 n)”

(* ------------------------------------------------------------------------
   The frame: backend c at fd f, channel j
   ------------------------------------------------------------------------ *)

Definition cfix_def:
  cfix lfd c f j (w : eworld) (hs : ehstate) ⇔
    ALOOKUP hs.tbl c = SOME f ∧ ALOOKUP w.open_fds f = SOME j ∧ j < LENGTH w.chans ∧
    (∀h. MEM (h, f) hs.tbl ⇒ h = c) ∧ (∀f'. MEM (f', j) w.open_fds ⇒ f' = f) ∧
    (∃a q. w.listening = [(lfd, a, q)] ∧ ¬MEM j q) ∧ alloc_ok w.alloc ∧
    (∀k. hs.nxt ≤ k ∧ hdln (w2n lfd) k < dimword (:64) ⇒ hdl lfd k ≠ c)
End

Theorem alloc_not_f:
  alloc_ok w.alloc ∧ ALOOKUP w.open_fds f = SOME j ∧ LENGTH (ep_used w) < dimword (:64) ⇒
  w.alloc j' (ep_used w) ≠ f
Proof
  rw[alloc_ok_def] >> first_x_assum (qspecl_then [‘j'’, ‘ep_used w’] mp_tac) >>
  simp[] >> simp[ep_used_def, MEM_MAP] >> rpt strip_tac >>
  imp_res_tac ALOOKUP_MEM >> first_x_assum (qspec_then ‘(f, j)’ mp_tac) >> simp[]
QED

Theorem hdln_mono:
  k0 < k ⇒ hdln n k0 < hdln n k
Proof
  rw[hdln_def]
QED

(* A fresh handle (issued later, and in range) is not c *)
Theorem cfix_new_handle:
  cfix lfd c f j w hs ∧ hdln (w2n lfd) hs.nxt < dimword (:64) ⇒
  hdl lfd hs.nxt ≠ c ∧
  ∀k. hs.nxt + 1 ≤ k ∧ hdln (w2n lfd) k < dimword (:64) ⇒ hdl lfd k ≠ c
Proof
  rw[cfix_def]
QED

(* Another handle's fd and channel are not c's *)
Theorem cfix_other:
  cfix lfd c f j w hs ∧ ALOOKUP hs.tbl h = SOME f' ∧ h ≠ c ∧ ALOOKUP w.open_fds f' = SOME j' ⇒
  f' ≠ f ∧ j' ≠ j
Proof
  rw[cfix_def] >> imp_res_tac ALOOKUP_MEM >> strip_tac >> gvs[] >> res_tac >> gvs[]
QED

(* A channel update keeps the frame, and j's status unless it is j's own
   update and changes the status *)
Theorem cfix_upd:
  cfix lfd c f j w hs ∧ (j' = j ⇒ ∀x. (g x).status = x.status) ⇒
  cfix lfd c f j (upd_chan j' g w) hs ∧
  (EL j (upd_chan j' g w).chans).status = (EL j w.chans).status
Proof
  rw[cfix_def, upd_chan_def, EL_LUPDATE] >> rw[] >> gvs[]
QED

Theorem cfix_upd_other:
  cfix lfd c f j w hs ∧ j' ≠ j ⇒ cfix lfd c f j (upd_chan j' g w) hs
Proof
  strip_tac >> irule (cj 1 cfix_upd) >> simp[]
QED

Theorem upd_chan_open_fds:
  (upd_chan j g w with open_fds := x) = upd_chan j g (w with open_fds := x)
Proof
  simp[upd_chan_def]
QED

Theorem cfix_close:
  cfix lfd c f j w hs ∧ h ≠ c ∧ f' ≠ f ⇒
  cfix lfd c f j (w with open_fds := ADELKEY f' w.open_fds) (eh_del h hs)
Proof
  rw[cfix_def, eh_del_def, ALOOKUP_ADELKEY] >> fs[ADELKEY_def, MEM_FILTER] >> metis_tac[]
QED

Theorem ehdo_cfix:
  cfix lfd c f j w hs ∧ ehdo lfd v (w, hs) x = SOME (r, (w1, hs1)) ∧ (∀k. x ≠ ERead c k) ⇒
  cfix lfd c f j w1 hs1 ∧ (EL j w1.chans).status = (EL j w.chans).status
Proof
  strip_tac >> Cases_on ‘x’ >> fs[ehdo_def]
  >- (‘∃a q. w.listening = [(lfd, a, q)]’ by fs[cfix_def] >>
      gvs[ep_accept_def, AllCaseEqs(), ep_alloc_def] >>
      ‘ALOOKUP w.open_fds f = SOME j ∧ alloc_ok w.alloc’ by fs[cfix_def] >>
      ‘w.alloc j' (ep_used w) ≠ f’ by (match_mp_tac alloc_not_f >> fs[wordsTheory.dimword_64]) >>
      ‘hdln (w2n c') hs.nxt < dimword (:64)’ by fs[wordsTheory.dimword_64] >>
      drule_all cfix_new_handle >> strip_tac >>
      fs[cfix_def, eh_new_def, AFUPDKEY_def] >> rw[] >> gvs[])
  >- (Cases_on ‘ALOOKUP hs.tbl c'’ >> gvs[] >> rename1 ‘ALOOKUP hs.tbl c' = SOME f'’ >>
      gvs[ep_conn_err_def, ep_chan_of_def, ep_read_def, ep_close_def, AllCaseEqs()] >>
      drule_all cfix_other >> strip_tac >>
      (conj_tac >- simp[upd_chan_open_fds, cfix_upd_other, cfix_close]) >>
      simp[upd_chan_def, EL_LUPDATE])
  >- (Cases_on ‘ALOOKUP hs.tbl c'’ >> gvs[] >>
      gvs[ep_send_def, ep_chan_of_def, AllCaseEqs()] >>
      irule cfix_upd >> simp[])
  >- (gvs[ep_connect_def, AllCaseEqs(), ep_alloc_def] >>
      TRY (fs[cfix_def] >> NO_TAC) >>
      fs[ep_used_def] >>
      ‘w.alloc (LENGTH w.chans) (ep_used w) ≠ f’
        by (irule alloc_not_f >> fs[cfix_def] >> gvs[ep_used_def]) >>
      ‘hdln (w2n lfd) hs.nxt < dimword (:64)’ by fs[wordsTheory.dimword_64] >>
      drule_all cfix_new_handle >> strip_tac >>
      fs[ep_used_def, cfix_def, eh_new_def, EL_APPEND1] >> rw[] >> gvs[])
  >> gvs[]
QED

(* A round's actions that do not read c keep the frame and j's status *)
Theorem ehacts_cfix:
  ∀acts k w hs rs w1 hs1.
    cfix lfd c f j w hs ∧ ehacts lfd lv n k (w, hs) acts = SOME (rs, (w1, hs1)) ∧
    (∀k'. ¬MEM (ERead c k') acts) ⇒
    cfix lfd c f j w1 hs1 ∧ (EL j w1.chans).status = (EL j w.chans).status
Proof
  Induct >- simp[ehacts_def] >>
  rpt gen_tac >> strip_tac >> qpat_x_assum ‘ehacts _ _ _ _ _ _ = _’ mp_tac >>
  simp[Once ehacts_def] >> rpt (CASE_TAC >> simp[]) >> strip_tac >> gvs[] >>
  rename1 ‘ehdo _ _ _ h = SOME (q, r)’ >> PairCases_on ‘r’ >>
  ‘cfix lfd c f j r0 r1 ∧ (EL j r0.chans).status = (EL j w.chans).status’
    by (irule ehdo_cfix >> qexistsl_tac [‘hs’, ‘q’, ‘lv n k’, ‘h’] >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED
