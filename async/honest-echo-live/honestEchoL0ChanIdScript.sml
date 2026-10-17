(*
  An fd's channel is fixed while its episode lasts (design/47 D, trace
  assembly): along L1's calls, an fd only gets a channel from an accept that
  returns it (an episode end), so a channel f has after events with no end
  of f's episode it already had before.  A close may take the channel away
  (an interrupted close that frees the fd), but cannot give another one.

  MAIN: world_at_chan_back, chan_same.
*)
Theory honestEchoL0ChanId
Ancestors
  honestEchoL0Excuse honestL1PFConnTrace honestL1PFLive honestEchoL0KSent honestEchoL0Sent honestEchoL0Spec honestL1BFaith honestL1BStmts honestL0Part
  honestL1PFOut honestL1PFRound honestL1Steps honestL1Inv honestL1Model honestL0WorldProps
  honestL0WorldInv honestL0Rely honestL0World honestL0
Libs
  preamble


Theorem ticks_open_fds[simp]:
  ∀k w. (l0_ticks nm k w).open_fds = w.open_fds
Proof
  Induct >> simp[l0_ticks_def]
QED

Theorem FOLDL_chans_open_fds[local]:
  ∀q w. (FOLDL (λw' j. w' with chans := g w' j) w q).open_fds = w.open_fds
Proof
  Induct >> simp[]
QED

(* A call other than an accept gives no fd a new entry *)
Theorem l0_call_fds_back:
  l0_call n conf bytes w = SOME (FFIreturn out w') ∧ n ≠ «sys_connect» ∧
  n ≠ «sys_accept» ∧ ALOOKUP w'.open_fds f = SOME j ⇒
  ALOOKUP w.open_fds f = SOME j
Proof
  rw[l0_call_def] >> gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  gvs[l0_listen_def, l0_recv_def, l0_send_def, l0_shutdown_def,
      l0_connerr_def, l0_close_def, close_fd_def, l0_alloc_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[AllCaseEqs()]) >>
  gvs[ALOOKUP_ADELKEY, upd_lchan_def, FOLDL_chans_open_fds]
QED

Theorem l0_accept_fds_back[local]:
  l0_accept l w = (r, w') ∧ ALOOKUP w'.open_fds f = SOME j ⇒
  ALOOKUP w.open_fds f = SOME j ∨ r = Ok (w2n f)
Proof
  rw[l0_accept_def] >> gvs[AllCaseEqs(), fail_def, upd_lchan_def] >>
  rw[] >> gvs[]
QED

Theorem chan_hist[local,simp]:
  l0_chan_of (w with hist := h) f = l0_chan_of w f
Proof
  simp[l0_chan_of_def]
QED

(* One of L1's calls that is not an end of f's episode gives f no new
   channel *)
Theorem faithful_step_chan_back:
  faithful w (ev :: evs) ∧ winv w ∧ ¬ep_ends f ev ⇒
  ∃u. l0_step (SOME w) (ev_lcall ev) = SOME u ∧ faithful u evs ∧ winv u ∧
      ∀c. l0_chan_of u f = SOME c ⇒ l0_chan_of w f = SOME c
Proof
  strip_tac >> drule faithful_CONS_buf >> strip_tac >> gvs[] >>
  ‘n ≠ «sys_connect»’ by (strip_tac >> gvs[l1_names_def]) >>
  conj_tac >- metis_tac[winv_do_buf] >>
  rpt strip_tac >>
  drule l0_do_buf_cases >> strip_tac >> gvs[] >>
  qpat_x_assum ‘l0_chan_of _ f = SOME c’ mp_tac >> simp[l0_chan_of_def, AllCaseEqs()] >>
  strip_tac >>
  ‘ALOOKUP w.open_fds f = SOME c’
    suffices_by (strip_tac >> simp[] >> imp_res_tac ALOOKUP_MEM >>
                 ‘l0wf w’ by fs[winv_def] >>
                 fs[l0wf_def, used_chans_def, EVERY_MEM, MEM_MAP, EXISTS_PROD] >>
                 metis_tac[]) >>
  Cases_on ‘n = «sys_accept»’
  >- (gvs[l0_call_def, AllCaseEqs()] >> pairarg_tac >> gvs[] >>
      drule_all l0_accept_fds_back >> strip_tac >> gvs[] >>
      ‘l0_rely (l0_tick «sys_accept» w)’
        by (irule l0_rely_ch >> qexists_tac ‘w’ >> gvs[winv_def]) >>
      drule_all l0_accept_res >> strip_tac >>
      ‘dec_res (MAP SND bs) = SOME (Ok (w2n f))’
        by (qpat_x_assum ‘enc_res _ = MAP SND bs’ (SUBST1_TAC o SYM) >>
            drule dec_enc_res >> disch_then (qspec_then ‘[]’ mp_tac) >> simp[]) >>
      qpat_x_assum ‘¬ep_ends f _’ mp_tac >>
      simp[ep_ends_def, l0_event_accepted_def, l0_ev_res_def, MAP_ZIP]) >>
  drule l0_call_fds_back >> simp[]
QED

Theorem faithful_chan_back:
  ∀evs w. faithful w evs ∧ winv w ∧ EVERY (λe. ¬ep_ends f e) evs ⇒
          ∃u. FOLDL l0_step (SOME w) (MAP ev_lcall evs) = SOME u ∧
              ∀c. l0_chan_of u f = SOME c ⇒ l0_chan_of w f = SOME c
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >> fs[] >>
  drule_all faithful_step_chan_back >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> simp[] >> metis_tac[]
QED

(* MAIN: while f is in the same episode, a channel f has at a later round
   it had at an earlier one *)
Theorem run_chan_same:
  run_ok lfd pol ifds m w0 ∧ winv w0 ∧ qfresh w0 ∧ n ≤ k ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 n))) f = SOME j ∧
  ALOOKUP (SND (l0_ep_st (0, []) (revs lfd pol ifds m w0 k))) f = SOME j ∧
  l0_chan_of (rworld lfd pol ifds m w0 k) f = SOME c ⇒
  l0_chan_of (rworld lfd pol ifds m w0 n) f = SOME c
Proof
  strip_tac >>
  ‘revs lfd pol ifds m w0 k = revs lfd pol ifds m w0 n ++ rrounds lfd pol ifds m w0 n (k − n)’
    by (drule revs_rrounds >> disch_then (qspecl_then [‘n’, ‘k − n’] mp_tac) >>
        ‘n + (k − n) = k’ by decide_tac >> simp[]) >>
  ‘ALOOKUP (SND (l0_ep_st (0, [])
     (revs lfd pol ifds m w0 n ++ rrounds lfd pol ifds m w0 n (k − n)))) f = SOME j’
    by metis_tac[] >>
  ‘¬EXISTS (ep_ends f) (rrounds lfd pol ifds m w0 n (k − n))’
    by (qspecl_then [‘revs lfd pol ifds m w0 n’, ‘f’, ‘j’, ‘rrounds lfd pol ifds m w0 n (k − n)’]
          mp_tac (Q.GENL [‘evs’, ‘f’, ‘j’, ‘mid’] idx_stable) >> simp[]) >>
  drule run_world_at >> strip_tac >>
  ‘faithful w0 (revs lfd pol ifds m w0 n ++ rrounds lfd pol ifds m w0 n (k − n))’
    by metis_tac[run_world_at] >>
  drule faithful_APPEND_inv >> simp[] >> strip_tac >>
  ‘u = rworld lfd pol ifds m w0 n’
    by (qpat_x_assum ‘∀n. world_at _ _ = _ ∧ _’ (qspec_then ‘n’ mp_tac) >>
        simp[world_at_def, l0_replay_def]) >>
  rveq >>
  qspecl_then [‘rrounds lfd pol ifds m w0 n (k − n)’, ‘rworld lfd pol ifds m w0 n’]
    mp_tac faithful_chan_back >>
  impl_tac >- (simp[] >> fs[EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  strip_tac >> first_x_assum irule >>
  qpat_x_assum ‘∀n. world_at _ _ = _ ∧ _’ (qspec_then ‘k’ mp_tac) >>
  simp[world_at_def, l0_replay_def, FOLDL_APPEND]
QED
