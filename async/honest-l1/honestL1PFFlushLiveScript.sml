(*
  The output side of R1-live, as clients need it (moonshot step 8):
  flush_live, everything the server wrote to a client by round n
  eventually reaches the kernel (is in its channel's sent), unless the
  channel breaks or L1 drops f's output (a hard error, D19).

  First a generic tool: a world predicate kept by every L0 call L1 makes
  (none is a shutdown or a connect) is kept along the run.  With it,
  nshut: L1 never shuts a channel down, so the channels of open and queued
  fds are never shut.
*)
Theory honestL1PFFlushLive
Ancestors
  honestL1PFFlush honestL1PFOut honestL0WorldProps honestL1PFConnRun honestL1PFConn
  honestL1PFClient honestL1PFLive honestL1PFRound honestL1PFRefine honestL1PFInv
  honestL1PFModel honestL1Steps honestL1Inv honestL1Props honestL1Model honestL0WorldInv
  honestL0Rely honestL0World honestL0 socketV2FFI asyncHLModel asyncCore Marshalling
Libs
  preamble

(* ------------------------------------------------------------------------
   World predicates kept along the run
   ------------------------------------------------------------------------ *)

Definition wpres_def:
  wpres P ⇔
    (∀w nm. P w ∧ winv w ⇒ P (l0_tick nm w)) ∧
    (∀w h. P w ⇒ P (w with hist := h)) ∧
    (∀n conf bytes w bytes' w'.
       P w ∧ l0wf w ∧ fds_lt w ∧ l0_rely w ∧ n ≠ «sys_shutdown» ∧ n ≠ «sys_connect» ∧
       l0_call n conf bytes w = SOME (FFIreturn bytes' w') ⇒ P w')
End

Theorem wpres_do:
  wpres P ∧ P w ∧ winv w ∧ n ≠ «sys_shutdown» ∧ n ≠ «sys_connect» ∧
  l0_do n conf alen w = SOME (out, w', ev) ⇒ P w'
Proof
  rw[wpres_def] >> drule l0_do_cases >> strip_tac >> gvs[] >>
  qabbrev_tac ‘wt = l0_tick n w’ >>
  ‘P wt’ by (qunabbrev_tac ‘wt’ >> metis_tac[]) >>
  ‘l0wf wt ∧ fds_lt wt ∧ l0_rely wt’
    by (gvs[Abbr ‘wt’, winv_def, l0wf_tick] >>
        ‘fds_lt (l0_tick n w)’ by simp[] >> simp[] >>
        irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  metis_tac[]
QED

Theorem wpres_do_buf:
  wpres P ∧ P w ∧ winv w ∧ n ≠ «sys_shutdown» ∧ n ≠ «sys_connect» ∧
  l0_do_buf n conf bs w = SOME (out, w', ev) ⇒ P w'
Proof
  rw[wpres_def] >> drule l0_do_buf_cases >> strip_tac >> gvs[] >>
  qabbrev_tac ‘wt = l0_tick n w’ >>
  ‘P wt’ by (qunabbrev_tac ‘wt’ >> metis_tac[]) >>
  ‘l0wf wt ∧ fds_lt wt ∧ l0_rely wt’
    by (gvs[Abbr ‘wt’, winv_def, l0wf_tick] >>
        ‘fds_lt (l0_tick n w)’ by simp[] >> simp[] >>
        irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]) >>
  metis_tac[]
QED

Theorem sys_wpres:
  wpres P ∧ P w ∧ winv w ⇒
  (sys_recv g k w = SOME (out, w', ev) ⇒ P w') ∧
  (sys_accept g w = SOME (out, w', ev) ⇒ P w') ∧
  (sys_poll fes w = SOME (out, w', ev) ⇒ P w') ∧
  (sys_send g bs w = SOME (out, w', ev) ⇒ P w') ∧
  (sys_close g w = SOME (out, w', ev) ⇒ P w')
Proof
  rw[sys_recv_def, sys_accept_def, sys_poll_def, sys_send_def, sys_close_def] >>
  TRY (drule_at (Pos last) wpres_do_buf >> simp[] >> NO_TAC) >>
  drule_at (Pos last) wpres_do >> simp[]
QED

Theorem l1_close_wpres:
  wpres P ∧ P w ∧ winv w ∧ l1_close g (w, st) = SOME ((w', st'), evs) ⇒ P w'
Proof
  rw[l1_close_def, AllCaseEqs()] >> metis_tac[sys_wpres]
QED

Theorem pdo_wpres:
  wpres P ∧ P w ∧ winv w ∧ pdo lfd (w, ps) a = SOME (r, (w', ps'), evs) ⇒ P w'
Proof
  Cases_on ‘a’ >> simp[pdo_def] >> rw[AllCaseEqs()] >> gvs[] >>
  TRY (PairCases_on ‘z’) >> gvs[l1do_def, AllCaseEqs()] >>
  metis_tac[l1_close_wpres, sys_wpres]
QED

Theorem pacts_wpres:
  ∀acts w ps rs evs w' ps'.
    wpres P ∧ P w ∧ winv w ∧ pacts lfd (w, ps) acts = SOME (rs, evs, (w', ps')) ⇒ P w'
Proof
  Induct >> simp[pacts_def] >> rw[AllCaseEqs()] >> PairCases_on ‘ws1’ >>
  ‘winv ws10’ by metis_tac[pdo_winv] >> metis_tac[pdo_wpres]
QED

Theorem l1_polls_wpres:
  ∀chs w rv w' evs. wpres P ∧ P w ∧ winv w ∧ l1_polls chs w = SOME (rv, w', evs) ⇒ P w'
Proof
  Induct >> simp[l1_polls_def] >> rw[AllCaseEqs()] >> metis_tac[sys_wpres, sys_winv]
QED

Theorem l1_flush_wpres:
  ∀fs w st w' st' evs.
    wpres P ∧ P w ∧ winv w ∧ l1_flush fs (w, st) = SOME ((w', st'), evs) ⇒ P w'
Proof
  Induct >> simp[l1_flush_def] >> rw[AllCaseEqs()] >> metis_tac[sys_wpres, sys_winv]
QED

Theorem pf_fetch_wpres:
  ∀fs w ps w' ps' log evs.
    wpres P ∧ P w ∧ winv w ∧ pf_fetch lfd pol fs (w, ps) = SOME ((w', ps'), log, evs) ⇒ P w'
Proof
  Induct >> simp[pf_fetch_def] >> rw[AllCaseEqs()] >>
  TRY (pairarg_tac >> gvs[AllCaseEqs()]) >> metis_tac[sys_wpres, sys_winv]
QED

Theorem l1_reap_wpres:
  ∀fs w st w' st' evs.
    wpres P ∧ P w ∧ winv w ∧ l1_reap fs (w, st) = SOME ((w', st'), evs) ⇒ P w'
Proof
  Induct >> simp[l1_reap_def] >> rw[AllCaseEqs()] >>
  TRY (Cases_on ‘ws’) >> metis_tac[l1_close_wpres, l1_close_winv]
QED

Theorem pround_wpres:
  wpres P ∧ P w ∧ winv w ∧ pround lfd pol hs (w, ps) acts = SOME (snap, (w', ps'), log, evs) ⇒
  P w'
Proof
  simp[pround_def, AllCaseEqs()] >> strip_tac >> PairCases_on ‘ws1’ >>
  gvs[pf_tail_def, AllCaseEqs()] >>
  ‘winv ws10’ by metis_tac[pacts_winv] >>
  ‘P ws10’ by metis_tac[pacts_wpres] >>
  rename1 ‘l1_polls _ _ = SOME (rv, w1, pevs)’ >>
  ‘winv w1 ∧ P w1’ by metis_tac[l1_polls_winv, l1_polls_wpres] >>
  rename1 ‘l1_flush _ _ = SOME ((w2, b2), fevs)’ >>
  ‘winv w2 ∧ P w2’ by metis_tac[l1_flush_winv, l1_flush_wpres] >>
  rename1 ‘pf_fetch _ _ _ _ = SOME ((w3, _), _, _)’ >>
  ‘winv w3 ∧ P w3’ by metis_tac[pf_fetch_winv, pf_fetch_wpres] >>
  metis_tac[l1_reap_wpres]
QED

Theorem run_wpres:
  wpres P ∧ run_ok lfd pol ifds m w0 ∧ winv w0 ∧ P w0 ⇒ ∀n. P (rworld lfd pol ifds m w0 n)
Proof
  strip_tac >> Induct
  >- simp[rworld_def, prun_0] >>
  drule prun_round' >> disch_then (qspecl_then [‘ARB’, ‘n’] strip_assume_tac) >>
  irule pround_wpres >> goal_assum drule >> simp[] >> metis_tac[winv_run]
QED

(* ------------------------------------------------------------------------
   nshut: the channels of open and queued fds are not shut down
   ------------------------------------------------------------------------ *)

Definition nshut_def:
  nshut w ⇔ ∀j. MEM j (used_chans w) ⇒ ¬(EL j w.chans).shut
End

Theorem nshut_upd:
  nshut w ∧ (∀c. (g c).shut = c.shut) ⇒ nshut (upd_lchan j g w)
Proof
  rw[nshut_def, used_chans_def, upd_lchan_def] >> res_tac >> simp[EL_LUPDATE] >>
  rw[] >> gvs[]
QED

Theorem nshut_deliver:
  nshut w ∧ l0wf w ⇒ nshut (l0_deliver w a)
Proof
  strip_tac >> Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >> gvs[] >>
  TRY (irule nshut_upd >> rw[break_lchan_def] >> NO_TAC) >>
  (* a new connection: a fresh channel, queued *)
  gvs[nshut_def, used_chans_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >> rw[] >>
  TRY (res_tac >> gvs[EL_APPEND1, l0wf_def, used_chans_def, EVERY_MEM, MEM_FLAT, MEM_MAP] >>
       metis_tac[EL_APPEND1]) >>
  rename1 ‘MEM y (AFUPDKEY _ _ _)’ >> PairCases_on ‘y’ >>
  drule MEM_AFUPDKEY_imp >> strip_tac >> gvs[]
  >- (‘j < LENGTH w.chans’
        by (gvs[l0wf_def, used_chans_def, EVERY_MEM, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
            metis_tac[SND]) >>
      simp[EL_APPEND1] >> first_x_assum irule >> metis_tac[SND])
  >> pairarg_tac >> gvs[] >>
  TRY (simp[EL_APPEND2, fresh_lchan_def] >> NO_TAC) >>
  rename1 ‘MEM j qq’ >>
  ‘j < LENGTH w.chans’
    by (gvs[l0wf_def, used_chans_def, EVERY_MEM, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
        metis_tac[SND]) >>
  simp[EL_APPEND1] >> first_x_assum irule >> metis_tac[SND]
QED

Theorem nshut_tick:
  nshut w ∧ l0wf w ⇒ nshut (l0_tick nm w)
Proof
  simp[l0_tick_def] >>
  ‘∀as w. nshut w ∧ l0wf w ⇒ nshut (FOLDL l0_deliver w as) ∧ l0wf (FOLDL l0_deliver w as)’
    by (Induct >> simp[] >> rpt gen_tac >> strip_tac >> first_x_assum irule >>
        metis_tac[nshut_deliver, l0wf_deliver]) >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [‘w.env w.clock w.hist nm’, ‘w with clock := w.clock + 1’] mp_tac) >>
  impl_tac >- (fs[nshut_def, l0wf_def, used_chans_def] >> metis_tac[]) >> simp[]
QED

Theorem nshut_sub:
  nshut w ∧ w'.chans = w.chans ∧ (∀j. MEM j (used_chans w') ⇒ MEM j (used_chans w)) ⇒
  nshut w'
Proof
  rw[nshut_def] >> metis_tac[]
QED

Theorem nshut_FOLDL_break:
  ∀q w. nshut w ⇒ nshut (FOLDL (λw j. upd_lchan j (break_lchan e F) w) w q)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  irule nshut_upd >> simp[break_lchan_def] >> rw[]
QED

Theorem nshut_pop:
  nshut w ∧ FILTER (λ(l', p, q). l' = l) w.listeners = (x, p, j :: q') :: t ⇒
  nshut (w with listeners := AFUPDKEY l (K (p, q')) w.listeners) ∧
  nshut (w with <| listeners := AFUPDKEY l (K (p, q')) w.listeners;
                   open_fds := (f, j) :: w.open_fds |>)
Proof
  strip_tac >>
  ‘MEM (x, p, j :: q') w.listeners ∧ x = l’
    by (qpat_x_assum ‘FILTER _ _ = _’ (mp_tac o Q.AP_TERM ‘MEM (x, p, j :: q')’) >>
        simp[MEM_FILTER]) >>
  ‘∀y. MEM y (AFUPDKEY l (K (p, q')) w.listeners) ⇒
       ∀k. MEM k (SND (SND y)) ⇒ MEM k (used_chans w)’
    by (rpt strip_tac >> PairCases_on ‘y’ >> drule MEM_AFUPDKEY_imp >> strip_tac >>
        gvs[used_chans_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[SND, MEM]) >>
  ‘MEM j (used_chans w)’
    by (simp[used_chans_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[SND, MEM]) >>
  conj_tac >> irule nshut_sub >> qexists_tac ‘w’ >> simp[] >>
  rw[used_chans_def, MEM_FLAT, MEM_MAP] >> gvs[used_chans_def, MEM_FLAT, MEM_MAP] >>
  metis_tac[]
QED

Theorem distinct_snd:
  ∀l. ALL_DISTINCT (MAP SND l) ∧ MEM (a, j) l ∧ MEM (b, j) l ⇒ a = b
Proof
  Induct >> simp[FORALL_PROD] >> rw[] >> gvs[MEM_MAP] >> metis_tac[SND]
QED

Theorem nshut_call:
  l0_call n conf bytes w = SOME (FFIreturn bytes' w') ∧ n ≠ «sys_shutdown» ∧
  n ≠ «sys_connect» ∧ nshut w ∧ l0wf w ⇒ nshut w'
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  (* listen *)
  TRY (gvs[l0_listen_def, AllCaseEqs()] >> irule nshut_sub >> qexists_tac ‘w’ >>
       simp[used_chans_def] >> NO_TAC) >>
  (* poll *)
  TRY (qmatch_goalsub_abbrev_tac ‘l0_ticks _ kk w’ >>
       ‘∀k w. nshut w ∧ l0wf w ⇒ nshut (l0_ticks «sys_poll» k w)’
         by (Induct >> simp[l0_ticks_def] >> metis_tac[nshut_tick, l0wf_tick]) >>
       simp[] >> NO_TAC) >>
  (* recv, send, connerr: channel fields other than shut *)
  TRY (gvs[l0_recv_def, l0_send_def, l0_connerr_def, AllCaseEqs(), fail_def] >>
       irule nshut_upd >> simp[] >> NO_TAC) >>
  TRY (gvs[l0_recv_def, l0_send_def, l0_connerr_def, AllCaseEqs(), fail_def] >> NO_TAC) >>
  (* accept *)
  TRY (gvs[l0_accept_def, AllCaseEqs(), fail_def] >>
       drule_all nshut_pop >> strip_tac >> simp[] >>
       irule nshut_upd >> simp[break_lchan_def] >> rw[] >> NO_TAC) >>
  (* close *)
  gvs[l0_close_def, AllCaseEqs()] >> simp[close_fd_def] >> every_case_tac >> gvs[] >>
  TRY (irule nshut_FOLDL_break >> irule nshut_sub >> qexists_tac ‘w’ >>
       simp[used_chans_def, MEM_FLAT, MEM_MAP, MEM_FILTER] >> metis_tac[] >> NO_TAC) >>
  TRY (irule nshut_sub >> qexists_tac ‘w’ >> simp[used_chans_def] >> NO_TAC) >>
  rename1 ‘l0_chan_of w g = SOME j’ >>
  gvs[nshut_def, used_chans_def, upd_lchan_def, EL_LUPDATE, l0_chan_of_def, AllCaseEqs()] >>
  ‘MEM (g, j) w.open_fds’ by metis_tac[ALOOKUP_MEM] >>
  ‘ALL_DISTINCT (MAP SND w.open_fds) ∧
   ∀x. MEM x (MAP SND w.open_fds) ⇒ ¬MEM x (FLAT (MAP (SND o SND) w.listeners))’
    by gvs[l0wf_def, used_chans_def, ALL_DISTINCT_APPEND] >>
  rw[] >>
  gvs[MEM_MAP, MEM_FLAT, ALOOKUP_ADELKEY, PULL_EXISTS, FORALL_PROD] >>
  TRY (qpat_x_assum ‘∀y. MEM y w.open_fds ⇒ _’ (qspec_then ‘(g, j)’ mp_tac) >>
       simp[] >> NO_TAC) >>
  TRY (rpt strip_tac >> gvs[] >> metis_tac[distinct_snd] >> NO_TAC) >>
  rename1 ‘MEM yy (ADELKEY g _)’ >>
  qpat_x_assum ‘∀j''. _ ⇒ ¬_’ irule >> disj1_tac >> qexists_tac ‘yy’ >>
  PairCases_on ‘yy’ >> gvs[]
QED

Theorem wpres_nshut:
  wpres nshut
Proof
  rw[wpres_def]
  >- (irule nshut_tick >> gvs[winv_def])
  >- (qpat_x_assum ‘nshut _’ mp_tac >> simp[nshut_def, used_chans_def])
  >- (drule_all nshut_call >> simp[])
QED

Theorem run_nshut:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ nshut w0 ⇒
  ∀n. nshut (rworld lfd pol ifds m w0 n)
Proof
  strip_tac >> irule run_wpres >> simp[wpres_nshut]
QED

Theorem chan_of_used:
  l0_chan_of w f = SOME c ⇒ MEM c (used_chans w)
Proof
  rw[l0_chan_of_def, AllCaseEqs(), used_chans_def, MEM_MAP] >> disj1_tac >>
  qexists_tac ‘(f, c)’ >> simp[] >> imp_res_tac ALOOKUP_MEM
QED

(* flush_progress with ¬shut discharged: L1 never shuts a channel. *)
Theorem flush_progress_nshut:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ nshut w0 ∧ MEM lfd (l0_used w0) ∧
  (∀n. SND (pcm lfd pol ifds m w0 n) + 1 < dimword (:64)) ∧
  F1 lfd pol ifds m w0 ∧ F2 w0 ∧ drains lfd pol ifds m w0 c ∧
  olive lfd f (rstate lfd pol ifds m w0 n) ∧
  l0_chan_of (rworld lfd pol ifds m w0 n) f = SOME c ⇒
  ∃k. n ≤ k ∧
      ((∃ev. MEM ev (rrev lfd pol ifds m w0 k) ∧ ev_on «sys_send» f ev ∧ ¬retried ev) ∨
       outbox_of (rstate lfd pol ifds m w0 (SUC k)).b f = [] ∨
       (EL c (rworld lfd pol ifds m w0 (SUC k)).chans).broken)
Proof
  strip_tac >> irule flush_progress >> simp[] >>
  drule_all run_nshut >> disch_then (qspec_then ‘n’ mp_tac) >>
  simp[nshut_def] >> disch_then irule >> metis_tac[chan_of_used]
QED
