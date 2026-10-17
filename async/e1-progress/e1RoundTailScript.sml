(*
  The PF round tail's steps on ewinv (close-v2, shared E1 progress layer,
  post-R3): honest-l1's tail lemmas (honestL1PFRound's *_winv,
  honestL1PFFlush's *_cflow, *_live, sys_poll_on, sys_poll_out) with
  ewinv for winv, so that they hold while connects are pending.  Their
  proofs are honest-l1's; sys_poll_out needs only f's own channel up (nc).
  Also: every step keeps a channel up (nc).

  MAIN: l1_flush_elive, l1_reap_elive, sys_poll_eout.
*)
Theory e1RoundTail
Ancestors
  honestL0 e1RoundConn e1RoundCflow e1RoundInv honestL1EPModel honestL1PFClose honestL1PFFlush
  honestL1PFOut honestL0WorldProps honestL1PFConnRun honestL1PFConn honestL1PFClient
  honestL1PFLive honestL1PFRound honestL1PFRefine honestL1PFInv honestL1PFModel
  honestL1Steps honestL1Inv honestL1Props honestL1Model honestL0WorldInv honestL0Rely
  honestL0World
Libs
  preamble

(* ------------------------------------------------------------------------
   Channels kept up: L1's calls
   ------------------------------------------------------------------------ *)

Theorem sys_nc:
  (nc c w ∧ sys_close g w = SOME (out, w', ev) ⇒ nc c w') ∧
  (nc c w ∧ sys_send g bs w = SOME (out, w', ev) ⇒ nc c w') ∧
  (nc c w ∧ sys_recv g k w = SOME (out, w', ev) ⇒ nc c w') ∧
  (nc c w ∧ sys_accept g w = SOME (out, w', ev) ⇒ nc c w') ∧
  (nc c w ∧ sys_poll fes w = SOME (out, w', ev) ⇒ nc c w') ∧
  (nc c w ∧ sys_connerr g w = SOME (out, w', ev) ⇒ nc c w') ∧
  (nc c w ∧ sys_shutdown g w = SOME (out, w', ev) ⇒ nc c w') ∧
  (nc c w ∧ sys_connect p w = SOME (out, w', ev) ⇒ nc c w')
Proof
  rpt conj_tac >> strip_tac >>
  gvs[sys_close_def, sys_send_def, sys_recv_def, sys_accept_def, sys_poll_def,
      sys_connerr_def, sys_shutdown_def, sys_connect_def] >>
  FIRST [drule_all nc_do_buf >> simp[] >> NO_TAC, drule_all nc_do >> simp[]]
QED

(* ------------------------------------------------------------------------
   ewinv along the tail
   ------------------------------------------------------------------------ *)

Theorem l1_close_ewinv:
  l1_close g (w, st) = SOME ((w', st'), evs) ∧ ewinv w ⇒ ewinv w' ∧ (nc c w ⇒ nc c w')
Proof
  rw[l1_close_def, AllCaseEqs()] >> gvs[] >> metis_tac[sys_ewinv, sys_nc]
QED

Theorem l1_polls_ewinv:
  ∀chs w rv w' evs.
    l1_polls chs w = SOME (rv, w', evs) ∧ ewinv w ⇒ ewinv w' ∧ (nc c w ⇒ nc c w')
Proof
  Induct >> simp[l1_polls_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[sys_ewinv, sys_nc]
QED

Theorem l1_flush_ewinv:
  ∀fs w st w' st' evs.
    l1_flush fs (w, st) = SOME ((w', st'), evs) ∧ ewinv w ⇒ ewinv w' ∧ (nc c w ⇒ nc c w')
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> rename1 ‘sys_send _ _ _ = SOME (out, w1, ev)’ >>
  ‘ewinv w1 ∧ (nc c w ⇒ nc c w1)’ by metis_tac[sys_ewinv, sys_nc] >>
  first_x_assum drule_all >> metis_tac[]
QED

Theorem l1_reap_ewinv:
  ∀fs w st w' st' evs.
    l1_reap fs (w, st) = SOME ((w', st'), evs) ∧ ewinv w ⇒ ewinv w' ∧ (nc c w ⇒ nc c w')
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> Cases_on ‘ws’ >> drule_all l1_close_ewinv >>
  disch_then (qspec_then ‘c’ strip_assume_tac) >>
  first_x_assum drule_all >> metis_tac[]
QED

Theorem pf_fetch_ewinv:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ ewinv w ⇒
    ewinv w' ∧ (nc c w ⇒ nc c w')
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘SOME (out, w1, ev)’ >>
  ‘ewinv w1 ∧ (nc c w ⇒ nc c w1)’ by metis_tac[sys_ewinv, sys_nc] >>
  first_x_assum drule_all >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Channel flow along the tail
   ------------------------------------------------------------------------ *)

Theorem l1_close_ecflow:
  l1_close g (w, st) = SOME ((w', st'), evs) ∧ ewinv w ∧ l0_chan_of w f = SOME c ∧ g ≠ f ⇒
  l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c
Proof
  rw[l1_close_def, AllCaseEqs()] >> drule_all (cj 5 sys_ecflow) >> simp[]
QED

Theorem l1_polls_ecflow:
  ∀chs w rv w' evs.
    l1_polls chs w = SOME (rv, w', evs) ∧ ewinv w ∧ l0_chan_of w f = SOME c ⇒
    l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c
Proof
  Induct >> simp[l1_polls_def] >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘sys_poll _ w = SOME (out, w1, ev)’ >>
  ‘ewinv w1’ by metis_tac[sys_ewinv] >>
  drule_all (cj 3 sys_ecflow) >> strip_tac >>
  first_x_assum drule_all >> metis_tac[cflow_trans]
QED

Theorem l1_flush_ecflow:
  ∀fs w st w' st' evs.
    l1_flush fs (w, st) = SOME ((w', st'), evs) ∧ ewinv w ∧ l0_chan_of w f = SOME c ⇒
    l0_chan_of w' f = SOME c ∧ cflow w w' c
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> rename1 ‘sys_send _ _ w = SOME (out, w1, ev)’ >>
  ‘ewinv w1’ by metis_tac[sys_ewinv] >>
  drule_all (cj 4 sys_ecflow) >> strip_tac >>
  first_x_assum drule_all >> metis_tac[cflow_trans]
QED

Theorem pf_fetch_ecflow:
  ∀fs w ps w' ps' log evs.
    pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ∧ ewinv w ∧
    l0_chan_of w f = SOME c ⇒
    l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c
Proof
  Induct >> simp[pf_fetch_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> pairarg_tac >> gvs[AllCaseEqs()] >>
  rename1 ‘SOME (out, w1, ev)’ >>
  ‘ewinv w1’ by metis_tac[sys_ewinv] >>
  TRY (drule_all (cj 2 sys_ecflow) >> strip_tac) >>
  TRY (drule_all (cj 1 sys_ecflow) >> strip_tac) >>
  first_x_assum drule_all >> metis_tac[cflow_trans]
QED

Theorem l1_reap_ecflow:
  ∀fs w st w' st' evs.
    l1_reap fs (w, st) = SOME ((w', st'), evs) ∧ ewinv w ∧ l0_chan_of w f = SOME c ∧
    ¬MEM f fs ⇒
    l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> Cases_on ‘ws’ >> rename1 ‘l1_close h' _ = SOME ((w1, st1), _)’ >>
  ‘ewinv w1’ by metis_tac[l1_close_ewinv] >>
  ‘h' ≠ f’ by (strip_tac >> gvs[]) >>
  drule_all l1_close_ecflow >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  irule cflow_trans >> qexists_tac ‘w1’ >> simp[]
QED

(* ------------------------------------------------------------------------
   f's output along the tail
   ------------------------------------------------------------------------ *)

Theorem retried_esend:
  sys_send g bs w = SOME (out, w', ev) ∧ ewinv w ⇒
  (retried ev ⇔ ∃e x. l0_res_of out = Fail e x ∧ l1_transient e)
Proof
  rw[sys_send_def] >>
  ‘LENGTH out = 13’
    by (gvs[l0_do_def, AllCaseEqs(), ewinv_def] >> drule_all l0_ffi_fn_length >> simp[]) >>
  drule l0_do_cases >> strip_tac >> gvs[] >>
  simp[retried_def, MAP_SND_ZIP_REPLICATE] >> every_case_tac >> simp[]
QED

Theorem sys_send_fail_ecsent:
  sys_send g bs w = SOME (out, w', ev) ∧ ewinv w ∧ l0_chan_of w f = SOME c ∧
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
  ‘l0wf (l0_tick «sys_send» w)’ by gvs[ewinv_def, l0wf_tick] >>
  drule_all csent_send >> strip_tac >>
  Cases_on ‘r’ >> gvs[csent_def] >>
  qspec_then ‘n’ strip_assume_tac (Q.GEN ‘v’ res_of_enc_ok) >> gvs[]
QED

Theorem l1_flush_elive:
  ∀fs w b w' b' evs.
    l1_flush fs (w, b) = SOME ((w', b'), evs) ∧ ewinv w ∧ l0_chan_of w f = SOME c ⇒
    (¬(∃ev. MEM ev evs ∧ ev_on «sys_send» f ev ∧ ¬retried ev) ⇒
     outbox_of b' f = outbox_of b f ∧ csent w' c = csent w c ∧
     (MEM f b'.gone ⇔ MEM f b.gone)) ∧
    (MEM f fs ∧ outbox_of b f ≠ [] ∧ ¬MEM f b.gone ⇒ EXISTS (ev_on «sys_send» f) evs)
Proof
  Induct >> simp[l1_flush_def] >> rpt gen_tac >> strip_tac >>
  Cases_on ‘outbox_of b h = [] ∨ MEM h b.gone’
  >- (gvs[] >> first_x_assum drule_all >> strip_tac >> simp[] >> rw[] >> gvs[]) >>
  gvs[AllCaseEqs()] >> rename1 ‘sys_send g _ w = SOME (out, w1, ev)’ >>
  ‘ewinv w1’ by metis_tac[sys_ewinv] >>
  drule_all (cj 4 sys_ecflow) >> strip_tac >>
  drule ev_on_send >> disch_then (qspec_then ‘f’ assume_tac) >>
  drule_all retried_esend >> strip_tac >>
  Cases_on ‘g = f’
  >- (gvs[] >> Cases_on ‘retried ev’ >> gvs[]
      >- (‘csent w1 c = csent w c’ by metis_tac[sys_send_fail_ecsent] >>
          gvs[after_send_def] >> first_x_assum drule_all >> strip_tac >> simp[] >>
          metis_tac[]) >>
      rw[] >> metis_tac[]) >>
  ‘outbox_of (after_send g (l0_res_of out) b) f = outbox_of b f ∧
   (MEM f (after_send g (l0_res_of out) b).gone ⇔ MEM f b.gone)’
    by metis_tac[outbox_of_after_send_other] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem l1_reap_elive:
  ∀fs w b w' b' evs.
    l1_reap fs (w, b) = SOME ((w', b'), evs) ∧ ewinv w ∧ l0_chan_of w f = SOME c ∧
    outbox_of b f ≠ [] ∧ ¬MEM f b.gone ⇒
    l0_chan_of w' f = SOME c ∧ cflow w w' c ∧ csent w' c = csent w c ∧
    outbox_of b' f = outbox_of b f ∧ ¬MEM f b'.gone
Proof
  Induct >> simp[l1_reap_def] >> rpt gen_tac >> rw[] >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs()] >> Cases_on ‘ws’ >> rename1 ‘l1_close g _ = SOME ((w1, b1), _)’ >>
  ‘g ≠ f’ by (strip_tac >> gvs[]) >>
  ‘ewinv w1’ by metis_tac[l1_close_ewinv] >>
  drule_all l1_close_ecflow >> strip_tac >>
  ‘outbox_of b1 f = outbox_of b f ∧ ¬MEM f b1.gone’
    by (gvs[l1_close_def, AllCaseEqs(), forget_def, outbox_of_set_outbox, MEM_FILTER] >>
        gvs[outbox_of_def]) >>
  ‘outbox_of b1 f ≠ []’ by fs[] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  irule cflow_trans >> qexists_tac ‘w1’ >> simp[]
QED

(* ------------------------------------------------------------------------
   The poll, seen from f's output
   ------------------------------------------------------------------------ *)

Theorem out_erevents:
  nc c w ∧ l0_chan_of w f = SOME c ∧ ¬(EL c w.chans).broken ∧ ¬(EL c w.chans).shut ∧
  2 ≤ ev MOD 4 ∧ 0 < w.ch.takes c w.hist (EL c w.chans).inflight 1 ⇒
  (byte_revents (fd_revents w (f, ev))).rout
Proof
  rw[fd_revents_def] >> simp[byte_revents_revents_byte] >>
  gvs[nc_def, chan_revents_def]
QED

Theorem sys_poll_eon:
  sys_poll fes w = SOME (out, w', ev) ∧ ewinv w ∧ EVERY (λ(g, e). small g ∧ e < 4) fes ⇒
  ∀nm g. ev_on nm g ev ⇔ nm = «sys_poll» ∧ MEM g (MAP FST fes)
Proof
  strip_tac >> ‘l0_rely w’ by gvs[ewinv_def] >>
  qpat_x_assum ‘sys_poll _ _ = _’ mp_tac >> simp[sys_poll_def] >> strip_tac >>
  drule_all ev_do_buf >> strip_tac >> simp[] >> rpt gen_tac >>
  eq_tac >> rw[] >> gvs[call_fds_poll]
QED

Theorem sys_poll_eout:
  sys_poll fes w = SOME (out, w', ev) ∧ ewinv w ∧ nc c w ∧ l0_chan_of w f = SOME c ∧
  EVERY (λ(g, e). small g ∧ e < 4) fes ∧ MEM (f, e) fes ∧ 2 ≤ e ∧
  ¬(EL c w'.chans).broken ∧ ¬(EL c w'.chans).shut ∧ (EL c w'.chans).inflight = 0 ∧
  (∀h. 0 < w.ch.takes c h 0 1) ∧ ¬retried ev ⇒
  MEM f (writable_fds (poll_revents fes out))
Proof
  strip_tac >> ‘l0_rely w’ by gvs[ewinv_def] >>
  qpat_x_assum ‘sys_poll _ _ = _’ mp_tac >> simp[sys_poll_def] >> strip_tac >>
  ‘LENGTH out = LENGTH (poll_buf fes)’
    by (gvs[l0_do_buf_def, AllCaseEqs()] >> drule_all l0_ffi_fn_length >> simp[]) >>
  drule_all ev_do_buf >> strip_tac >>
  drule l0_do_buf_cases >> strip_tac >> gvs[ev_name_def] >>
  qabbrev_tac ‘wt = l0_tick «sys_poll» w’ >>
  ‘nc c wt ∧ LENGTH (wt.ch.errno_of wt.hist) = 4 ∧ wt.ch = w.ch’
    by gvs[Abbr ‘wt’, nc_tick, l0_rely_def] >>
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
      irule out_erevents >> simp[] >>
      ‘e = 2 ∨ e = 3’ by (gvs[EVERY_MEM] >> first_x_assum drule >> simp[]) >>
      gvs[]) >>
  gvs[retried_def, MAP_ZIP]
QED
