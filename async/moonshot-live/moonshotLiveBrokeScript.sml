(*
  Moonshot liveness, the excuse transfer for BROKEN channels (D28's
  flushed excuse, echo_live_l0's flushed_open): a channel of a live
  process that is still in use (queued at a listener, or held by an fd),
  that is not a connect's (no target), and that is broken, was broken by
  the kernel (a Break or ConnFail label on it) or by a hard accept failure
  of the process (EMFILE, D17 emfile_drops): kern_broke ∨ hard_fail
  «sys_accept», both in sys_excuse (irun_broke).

  Why "in use": closing a listener (or exiting) resets its queued
  connections with no kernel label, but those channels are then neither
  queued nor held, and never will be (only fresh channels are queued, and
  only queued or fresh ones get an fd).  Why "no target": a connect that
  fails at once leaves a broken channel with no label; its end has a
  target.
*)
Theory moonshotLiveBroke
Ancestors
  moonshotLiveInfl moonshotLiveDrains moonshotLiveStmts l0sysFair l0sys l0sysStep l0sysInv
  l0sysInvCall l0sysMono honestL0World honestL0 honestL0Rely honestL1Model alist
Libs
  preamble

(* Channel c is in use in w: queued at a listener or held by an fd *)
Definition live_def:
  live (w : l0world) c ⇔ queued w c ∨ ∃f. l0_chan_of w f = SOME c
End

(*---------------------------------------------------------------------------*)
(* World facts *)

Theorem l0_chan_of_upd[simp]:
  l0_chan_of (upd_lchan j g w) f = l0_chan_of w f
Proof
  simp[l0_chan_of_def, upd_lchan_def]
QED

Theorem live_upd[simp]:
  live (upd_lchan j g w) c ⇔ live w c
Proof
  simp[live_def]
QED

Theorem breaks_facts:
  ∀q (w : l0world).
    LENGTH (FOLDL (λw j. upd_lchan j (break_lchan e k) w) w q).chans = LENGTH w.chans ∧
    (FOLDL (λw j. upd_lchan j (break_lchan e k) w) w q).open_fds = w.open_fds ∧
    (FOLDL (λw j. upd_lchan j (break_lchan e k) w) w q).listeners = w.listeners ∧
    ∀c. c < LENGTH w.chans ∧
        (EL c (FOLDL (λw j. upd_lchan j (break_lchan e k) w) w q).chans).broken ⇒
        (EL c w.chans).broken ∨ MEM c q
Proof
  Induct >> simp[] >> rpt gen_tac >>
  first_x_assum (qspec_then ‘upd_lchan h (break_lchan e k) w’ strip_assume_tac) >>
  fs[upd_lchan_def] >> rpt strip_tac >>
  first_x_assum (qspec_then ‘c’ mp_tac) >> simp[EL_LUPDATE] >>
  rw[] >> fs[break_lchan_def] >> rw[] >> fs[]
QED

Theorem l0_chan_of_breaks:
  l0_chan_of (FOLDL (λw j. upd_lchan j (break_lchan e k) w) w q) f = l0_chan_of w f
Proof
  simp[l0_chan_of_def, breaks_facts]
QED

(* A channel sits in at most one listener's queue *)
Theorem queue_unique:
  ∀L. ALL_DISTINCT (FLAT (MAP (SND o SND) L)) ∧ MEM (a, b, q) L ∧ MEM (a', b', q') L ∧
      MEM c q ∧ MEM c q' ⇒ a = a'
Proof
  Induct >> simp[] >> PairCases >>
  simp[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >> gvs[] >>
  metis_tac[pairTheory.SND]
QED

(* close_fd: no channel newly held; a newly broken channel is no longer in use *)
Theorem close_fd_broke:
  pinv evs w cs ⇒
  LENGTH (close_fd f w).chans = LENGTH w.chans ∧
  (∀g c. l0_chan_of (close_fd f w) g = SOME c ⇒ l0_chan_of w g = SOME c) ∧
  (∀c. queued (close_fd f w) c ⇒ queued w c) ∧
  ∀c. c < LENGTH w.chans ∧ live (close_fd f w) c ∧ (EL c (close_fd f w).chans).broken ⇒
      (EL c w.chans).broken
Proof
  strip_tac >> simp[close_fd_infl] >>
  conj_tac >- (simp[close_fd_def] >> every_case_tac >>
               simp[l0_chan_of_breaks, l0_chan_of_ADELKEY] >> simp[l0_chan_of_def] >> rw[]) >>
  conj_tac >- metis_tac[queued_close_fd] >>
  Cases_on ‘l0_chan_of w f’ >> simp[close_fd_def]
  >- (Cases_on ‘FILTER (λ(l, p, q). l = f) w.listeners’ >> simp[] >>
      PairCases_on ‘h’ >> simp[] >>
      rpt strip_tac >>
      qmatch_asmsub_abbrev_tac ‘FOLDL _ w1 h2’ >>
      ‘c < LENGTH w1.chans’ by simp[Abbr ‘w1’] >>
      drule (cj 4 (SPEC_ALL breaks_facts)) >> simp[Abbr ‘w1’] >>
      disch_then (qspecl_then [‘h2’, ‘F’, ‘E_CONNRESET’] mp_tac) >> fs[] >> strip_tac >>
      ‘MEM (h0, h1, h2) w.listeners ∧ h0 = f’ by
        (‘MEM (h0, h1, h2) (FILTER (λ(l, p, q). l = f) w.listeners)’ by simp[] >>
         fs[MEM_FILTER]) >>
      qpat_x_assum ‘live _ _’ mp_tac >> simp[live_def, l0_chan_of_breaks] >>
      simp[queued_def, breaks_facts, MEM_FILTER] >> rpt strip_tac
      >- (rename1 ‘MEM (l', p', q') w.listeners’ >>
          ‘ALL_DISTINCT (FLAT (MAP (SND o SND) w.listeners))’ by fs[pinv_def] >>
          ‘l' = h0’ by metis_tac[queue_unique] >> gvs[]) >>
      qpat_x_assum ‘pinv _ _ _’ mp_tac >> rewrite_tac[pinv_def] >> strip_tac >>
      first_x_assum (qspecl_then [‘h0’, ‘h1’, ‘h2’] mp_tac) >> simp[] >> strip_tac >>
      first_x_assum (qspec_then ‘c’ mp_tac) >> simp[] >>
      strip_tac >> first_x_assum (qspec_then ‘f'’ mp_tac) >>
      qpat_x_assum ‘l0_chan_of _ f' = _’ mp_tac >> simp[l0_chan_of_def]) >>
  simp[l0_chan_of_ADELKEY] >> rw[] >> fs[upd_lchan_def, EL_LUPDATE] >> pop_assum mp_tac >> rw[]
QED

(*---------------------------------------------------------------------------*)
(* Calls *)

Theorem call_new_chans:
  l0_call nm (unblock nm conf) bts w = SOME (FFIreturn out w1) ∧ pinv evs w cs ∧
  LENGTH w.chans < LENGTH w1.chans ⇒
  nm = «sys_connect» ∧ LENGTH w1.chans = LENGTH w.chans + 1
Proof
  strip_tac >>
  Cases_on ‘nm = «sys_poll»’ >- (gvs[] >> drule l0_call_poll_unblock >> strip_tac >> gvs[]) >>
  gvs[unblock_other] >>
  Cases_on ‘nm = «sys_connect»’
  >- (gvs[l0_call_def, AllCaseEqs()] >> drule l0_connect_cases >> simp[LET_THM] >>
      strip_tac >> gvs[upd_lchan_def]) >>
  Cases_on ‘nm = «sys_listen»’ >- gvs[l0_call_def, l0_listen_def, AllCaseEqs()] >>
  Cases_on ‘nm = «sys_accept»’
  >- (gvs[l0_call_def] >> pairarg_tac >> gvs[] >>
      drule l0_accept_cases >> strip_tac >> gvs[upd_lchan_def]) >>
  Cases_on ‘nm = «sys_recv»’
  >- (gvs[l0_call_def] >> pairarg_tac >> gvs[] >>
      drule l0_recv_cases >> strip_tac >> gvs[upd_lchan_def]) >>
  Cases_on ‘nm = «sys_send»’
  >- (gvs[l0_call_def] >> pairarg_tac >> gvs[] >>
      drule l0_send_cases >> strip_tac >> gvs[upd_lchan_def]) >>
  Cases_on ‘nm = «sys_shutdown»’
  >- (gvs[l0_call_def] >> pairarg_tac >> gvs[l0_shutdown_def, AllCaseEqs(), upd_lchan_def]) >>
  Cases_on ‘nm = «sys_connerr»’
  >- gvs[l0_call_def, l0_connerr_def, AllCaseEqs(), upd_lchan_def] >>
  Cases_on ‘nm = «sys_close»’
  >- (gvs[l0_call_def] >> pairarg_tac >> gvs[l0_close_def, AllCaseEqs()] >>
      fs[close_fd_infl]) >>
  gvs[l0_call_def]
QED

Theorem call_fd:
  l0_call nm (unblock nm conf) bts w = SOME (FFIreturn out w1) ∧ pinv evs w cs ∧
  l0_chan_of w1 f = SOME c ∧ c < LENGTH w.chans ⇒
  (∃f'. l0_chan_of w f' = SOME c) ∨ queued w c
Proof
  strip_tac >>
  Cases_on ‘nm = «sys_poll»’ >- (gvs[] >> drule l0_call_poll_unblock >> strip_tac >> gvs[] >>
                                metis_tac[]) >>
  gvs[unblock_other, l0_call_def, AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  FIRST [
    gvs[l0_listen_def, AllCaseEqs()] >> fs[l0_chan_of_def] >> metis_tac[],
    drule l0_accept_cases >> strip_tac >> gvs[] >> fs[l0_chan_of_def] >>
    TRY (metis_tac[]) >>
    gvs[AllCaseEqs()] >> TRY (metis_tac[]) >>
    disj2_tac >> simp[queued_def] >>
    ‘MEM (l1, p, c :: q') (FILTER (λ(l', p, q). l' = bytes_fd conf) w.listeners)’ by simp[] >>
    fs[MEM_FILTER] >> metis_tac[MEM],
    drule l0_recv_cases >> strip_tac >> gvs[] >> metis_tac[],
    drule l0_send_cases >> strip_tac >> gvs[] >> metis_tac[],
    gvs[l0_shutdown_def, AllCaseEqs()] >> metis_tac[],
    drule l0_connect_cases >> simp[LET_THM] >> strip_tac >> gvs[] >> fs[l0_chan_of_def] >>
    TRY (metis_tac[]) >> gvs[AllCaseEqs(), upd_lchan_def] >> metis_tac[],
    gvs[l0_connerr_def, AllCaseEqs()] >> metis_tac[],
    gvs[l0_close_def, AllCaseEqs()] >> drule close_fd_broke >> metis_tac[]]
QED

Theorem call_live:
  l0_call nm (unblock nm conf) bts w = SOME (FFIreturn out w1) ∧ pinv evs w cs ∧
  live w1 c ∧ c < LENGTH w.chans ⇒ live w c
Proof
  rw[live_def] >- (disj1_tac >> metis_tac[queued_call]) >>
  drule_all call_fd >> metis_tac[]
QED

(* accept breaks a channel only on EMFILE (emfile_drops) *)
Theorem accept_broke:
  l0_accept l w = (r, w') ∧ c < LENGTH w.chans ∧ (EL c w'.chans).broken ⇒
  (EL c w.chans).broken ∨ r = fail w E_MFILE
Proof
  rw[l0_accept_def, AllCaseEqs()] >> gvs[upd_lchan_def, EL_LUPDATE] >>
  every_case_tac >> gvs[break_lchan_def] >> every_case_tac >> gvs[]
QED

Theorem call_broke:
  l0_rely w ∧ l0_call nm (unblock nm conf) bts w = SOME (FFIreturn out w1) ∧ pinv evs w cs ∧
  c < LENGTH w.chans ∧ live w1 c ∧ (EL c w1.chans).broken ⇒
  (EL c w.chans).broken ∨ nm = «sys_accept» ∧ ∃v. dec_res out = SOME (Fail E_MFILE v)
Proof
  strip_tac >>
  Cases_on ‘nm = «sys_poll»’ >- (gvs[] >> drule l0_call_poll_unblock >> strip_tac >> gvs[]) >>
  gvs[unblock_other] >>
  Cases_on ‘nm = «sys_accept»’
  >- (gvs[l0_call_def] >> pairarg_tac >> gvs[] >>
      drule accept_broke >> disch_then drule >> simp[] >> strip_tac >> simp[] >>
      ‘LENGTH (w.ch.errno_of w.hist) = 4’ by fs[l0_rely_def] >>
      ‘dec_res (enc_res (Fail E_MFILE (w.ch.errno_of w.hist)) ++ []) =
       SOME (Fail E_MFILE (w.ch.errno_of w.hist))’ by (irule dec_enc_res >> simp[l0_res_ok_def]) >>
      fs[fail_def]) >>
  Cases_on ‘nm = «sys_connect»’
  >- (gvs[l0_call_def, AllCaseEqs()] >> drule l0_connect_cases >> simp[LET_THM] >>
      strip_tac >> gvs[upd_lchan_def, EL_LUPDATE, EL_APPEND1] >>
      qpat_x_assum ‘(EL _ (LUPDATE _ _ _)).broken’ mp_tac >> rw[EL_LUPDATE, EL_APPEND1] >> fs[EL_APPEND1]) >>
  Cases_on ‘nm = «sys_listen»’ >- gvs[l0_call_def, l0_listen_def, AllCaseEqs()] >>
  Cases_on ‘nm = «sys_recv»’
  >- (gvs[l0_call_def] >> pairarg_tac >> gvs[] >>
      drule l0_recv_cases >> strip_tac >> gvs[upd_lchan_def] >>
      qpat_x_assum ‘(EL _ (LUPDATE _ _ _)).broken’ mp_tac >> rw[EL_LUPDATE] >> fs[]) >>
  Cases_on ‘nm = «sys_send»’
  >- (gvs[l0_call_def] >> pairarg_tac >> gvs[] >>
      drule l0_send_cases >> strip_tac >> gvs[upd_lchan_def] >>
      qpat_x_assum ‘(EL _ (LUPDATE _ _ _)).broken’ mp_tac >> rw[EL_LUPDATE] >> fs[]) >>
  Cases_on ‘nm = «sys_shutdown»’
  >- (gvs[l0_call_def] >> pairarg_tac >> gvs[l0_shutdown_def, AllCaseEqs(), upd_lchan_def] >>
      qpat_x_assum ‘(EL _ (LUPDATE _ _ _)).broken’ mp_tac >> rw[EL_LUPDATE] >> fs[]) >>
  Cases_on ‘nm = «sys_connerr»’
  >- (gvs[l0_call_def, l0_connerr_def, AllCaseEqs(), upd_lchan_def] >>
      qpat_x_assum ‘(EL _ (LUPDATE _ _ _)).broken’ mp_tac >> rw[EL_LUPDATE] >> fs[]) >>
  Cases_on ‘nm = «sys_close»’
  >- (gvs[l0_call_def] >> pairarg_tac >> gvs[l0_close_def, AllCaseEqs()] >>
      drule close_fd_broke >> disch_then (qspec_then ‘bytes_fd conf’ strip_assume_tac) >>
      first_x_assum irule >> simp[]) >>
  gvs[l0_call_def]
QED

(*---------------------------------------------------------------------------*)
(* Arrivals *)

Theorem deliver_broke:
  c < LENGTH w.chans ∧ live (l0_deliver w a) c ∧ (EL c (l0_deliver w a).chans).broken ⇒
  live w c ∧ ((EL c w.chans).broken ∨ (∃e keep. a = LBreak c e keep) ∨ ∃e. a = LConnFail c e)
Proof
  strip_tac >>
  ‘∀f. l0_chan_of (l0_deliver w a) f = SOME c ⇒ l0_chan_of w f = SOME c’ by
    (Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >> gvs[] >>
     fs[l0_chan_of_def, AllCaseEqs()] >> rw[] >> fs[]) >>
  conj_tac
  >- (fs[live_def] >- (drule queued_deliver >> simp[]) >> metis_tac[]) >>
  qpat_x_assum ‘(EL _ _).broken’ mp_tac >>
  Cases_on ‘a’ >> simp[l0_deliver_def] >> every_case_tac >>
  simp[upd_lchan_def, EL_LUPDATE, EL_APPEND1] >> rw[] >> fs[break_lchan_def] >> rw[] >> fs[]
QED

Theorem deliver_new_chans:
  LENGTH w.chans ≤ LENGTH (l0_deliver w a).chans ∧
  ∀c. LENGTH w.chans ≤ c ∧ c < LENGTH (l0_deliver w a).chans ⇒
      ¬(EL c (l0_deliver w a).chans).broken
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >> gvs[upd_lchan_def] >>
  ‘c = LENGTH w.chans’ by simp[] >> gvs[EL_APPEND2, fresh_lchan_def]
QED

(*---------------------------------------------------------------------------*)
(* Back: a live broken channel of w' is a live broken channel of w, or X *)

Definition back_def:
  back (w : l0world) (w' : l0world) X ⇔
    ∀c. c < LENGTH w'.chans ∧ live w' c ∧ (EL c w'.chans).broken ⇒
        (c < LENGTH w.chans ∧ live w c ∧ (EL c w.chans).broken) ∨ X c
End

Theorem back_refl[simp]:
  back w w X
Proof
  simp[back_def]
QED

Theorem back_trans:
  back w1 w2 X ∧ back w2 w3 X ⇒ back w1 w3 X
Proof
  rw[back_def] >> metis_tac[]
QED

Theorem back_mono:
  back w w' X ∧ (∀c. X c ⇒ Y c) ⇒ back w w' Y
Proof
  rw[back_def] >> metis_tac[]
QED

Theorem back_any:
  (∀c. X c) ⇒ back w w' X
Proof
  simp[back_def]
QED

Definition nb_def:
  nb a ⇔ (∀j e keep. a ≠ LBreak j e keep) ∧ ∀j e. a ≠ LConnFail j e
End

Theorem back_deliver:
  nb a ⇒ back w (l0_deliver w a) X
Proof
  rw[back_def, nb_def] >>
  Cases_on ‘c < LENGTH w.chans’
  >- (drule_all deliver_broke >> simp[]) >>
  metis_tac[deliver_new_chans, arithmeticTheory.NOT_LESS]
QED

Theorem live_clock_hist[simp]:
  live (w with <| clock := a; hist := b |>) c ⇔ live w c
Proof
  simp[live_def, queued_def, l0_chan_of_def]
QED

Theorem back_call:
  l0_rely w ∧ pinv evs w cs ∧ l0_call nm (unblock nm conf) bts w = SOME (FFIreturn out w1) ⇒
  back w (w1 with <| clock := a; hist := b |>)
    (λc. nm = «sys_connect» ∧ c = LENGTH w.chans ∧ LENGTH w1.chans = LENGTH w.chans + 1 ∨
         nm = «sys_accept» ∧ ∃v. dec_res out = SOME (Fail E_MFILE v))
Proof
  rw[back_def] >>
  Cases_on ‘c < LENGTH w.chans’
  >- (‘live w c’ by metis_tac[call_live] >>
      drule_all call_broke >> rw[] >> simp[]) >>
  ‘LENGTH w.chans < LENGTH w1.chans’ by simp[] >>
  drule_all call_new_chans >> rw[] >> simp[]
QED

(*---------------------------------------------------------------------------*)
(* The invariant *)

(* Process k saw, before step n, a kernel break of one of its channels or
   a hard accept failure *)
Definition broke_by_def:
  broke_by (rs : num -> syslabel) n k ⇔
    ∃m. m < n ∧
        ((∃j e keep. rs m = Kern (Break k j e keep)) ∨ (∃j e. rs m = Kern (ConnFail k j e)) ∨
         ∃conf bts out v. rs m = Call k «sys_accept» conf bts out ∧
                          dec_res out = SOME (Fail E_MFILE v))
End

Definition broke_inv_def:
  broke_inv rs n (s : sysstate) ⇔
    ∀k c. is_end s (k, c) ∧ s.alive k ∧ (sys_chan s (k, c)).broken ∧ s.target (k, c) = NONE ∧
          live (EL k s.procs) c ⇒ broke_by rs n k
End

Theorem broke_by_SUC:
  broke_by rs n k ⇒ broke_by rs (SUC n) k
Proof
  rw[broke_by_def] >> qexists_tac ‘m’ >> simp[]
QED

Theorem broke_inv_gen:
  broke_inv rs n s ∧ LENGTH s'.procs = LENGTH s.procs ∧ (∀k. s'.alive k ⇒ s.alive k) ∧
  (∀e. is_end s e ∧ s'.target e = NONE ⇒ s.target e = NONE) ∧
  (∀k. k < LENGTH s.procs ∧ s'.alive k ⇒
       back (EL k s.procs) (EL k s'.procs)
            (λc. s'.target (k, c) ≠ NONE ∨ broke_by rs (SUC n) k)) ⇒
  broke_inv rs (SUC n) s'
Proof
  rw[broke_inv_def] >>
  ‘k < LENGTH s.procs’ by fs[is_end_def] >>
  first_x_assum (qspec_then ‘k’ mp_tac) >> simp[back_def] >>
  disch_then (qspec_then ‘c’ mp_tac) >> fs[is_end_def, sys_chan_def] >> strip_tac >>
  irule broke_by_SUC >> first_x_assum irule >> simp[is_end_def, sys_chan_def] >>
  qexists_tac ‘c’ >> simp[] >> first_x_assum irule >> simp[is_end_def]
QED

Theorem sys_deliver_EL:
  EL k' (sys_deliver k a s).procs =
  if k' = k ∧ k < LENGTH s.procs then l0_deliver (EL k s.procs) a else EL k' s.procs
Proof
  simp[sys_deliver_def, EL_LUPDATE] >> rw[] >> fs[]
QED

Theorem sys_deliver_fields[simp]:
  LENGTH (sys_deliver k a s).procs = LENGTH s.procs ∧
  (sys_deliver k a s).alive = s.alive ∧ (sys_deliver k a s).target = s.target
Proof
  simp[sys_deliver_def]
QED

Theorem sys_pair_fields[simp]:
  LENGTH (sys_pair e k p s).procs = LENGTH s.procs ∧
  (sys_pair e k p s).alive = s.alive ∧ (sys_pair e k p s).target = s.target ∧
  (sys_pair e k p s).procs = (sys_deliver k (LIncoming p) s).procs
Proof
  simp[sys_pair_def, LET_THM]
QED

Theorem back_sys_deliver:
  back w (EL k' s.procs) X ∧ nb a ⇒ back w (EL k' (sys_deliver k a s).procs) X
Proof
  rw[sys_deliver_EL] >> irule back_trans >> metis_tac[back_deliver]
QED

Theorem nb_incoming[simp]:
  nb (LIncoming p) ∧ nb (LConnUp j) ∧ nb (LData j bs) ∧ nb (LEof j) ∧ nb (LDrain j n)
Proof
  simp[nb_def]
QED

(* What broke_inv_gen needs of a step *)
Definition broke_ok_def:
  broke_ok rs n s s' ⇔
    LENGTH s'.procs = LENGTH s.procs ∧ (∀k. s'.alive k ⇒ s.alive k) ∧
    (∀e. is_end s e ∧ s'.target e = NONE ⇒ s.target e = NONE) ∧
    ∀k. k < LENGTH s.procs ∧ s'.alive k ⇒
        back (EL k s.procs) (EL k s'.procs) (λc. s'.target (k, c) ≠ NONE ∨ broke_by rs (SUC n) k)
End

Theorem broke_ok_call:
  sinv rsl s css ∧ rs n = Call k nm conf bts out ∧ sys_step s (Call k nm conf bts out) s' ⇒
  broke_ok rs n s s'
Proof
  simp[sys_step_def, LET_THM] >> strip_tac >>
  qabbrev_tac ‘w = EL k s.procs’ >>
  ‘l0_rely w ∧ pinv (proc_events k rsl) w (css k)’ by fs[sinv_def, pk_def, LET_THM, Abbr ‘w’] >>
  drule_all (Q.INST [‘a’ |-> ‘w.clock + 1’, ‘b’ |-> ‘w.hist ++ [(nm, conf, bts)]’] back_call) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac ‘back w w1' _’ >>
  ‘∀k'. k' < LENGTH s.procs ⇒
        back (EL k' s.procs) (EL k' (LUPDATE w1' k s.procs))
          (λc. k' = k ∧ nm = «sys_connect» ∧ c = LENGTH w.chans ∧
               LENGTH w1.chans = LENGTH w.chans + 1 ∨ broke_by rs (SUC n) k')’ by
    (rw[EL_LUPDATE] >> irule back_mono >> first_x_assum (irule_at Any) >> rw[] >>
     simp[broke_by_def] >> qexists_tac ‘n’ >> simp[]) >>
  ‘∀e. is_end s e ⇒ e ≠ (k, LENGTH w.chans)’ by (simp[FORALL_PROD, is_end_def, Abbr ‘w’] >> rpt strip_tac >> gvs[]) >>
  Cases_on ‘nm = «sys_connect» ∧ LENGTH w1.chans = LENGTH w.chans + 1’ >> fs[]
  >- (‘∀s''. s''.target = ((k, LENGTH w.chans) =+ SOME (w22n conf)) s.target ∧
             (∀k'. k' < LENGTH s.procs ⇒
                   back (EL k' s.procs) (EL k' s''.procs)
                     (λc. k' = k ∧ c = LENGTH w.chans ∨ broke_by rs (SUC n) k')) ∧
             LENGTH s''.procs = LENGTH s.procs ∧ s''.alive = s.alive ⇒ broke_ok rs n s s''’ by
        (rw[broke_ok_def] >>
         TRY (gvs[combinTheory.APPLY_UPDATE_THM, AllCaseEqs()] >> NO_TAC) >>
         irule back_mono >>
         qexists_tac ‘λc. k' = k ∧ c = LENGTH w.chans ∨ broke_by rs (SUC n) k'’ >>
         conj_tac >- (rw[combinTheory.APPLY_UPDATE_THM] >> fs[]) >>
         first_x_assum irule >> simp[]) >>
      every_case_tac >> fs[] >> qpat_x_assum ‘∀s''. _’ irule >> simp[] >> rpt strip_tac >>
      TRY (irule back_sys_deliver >> simp[]) >> first_x_assum irule >> simp[]) >>
  ‘¬(nm = «sys_connect» ∧ LENGTH w1.chans = LENGTH w.chans + 1)’ by fs[] >>
  qpat_x_assum ‘if _ then _ else _’ mp_tac >> pop_assum (fn th => rewrite_tac[th]) >>
  strip_tac >> gvs[] >>
  rw[broke_ok_def] >> irule back_mono >>
  qexists_tac ‘λc. k' = k ∧ nm = «sys_connect» ∧ c = LENGTH w.chans ∧
                   LENGTH w1.chans = LENGTH w.chans + 1 ∨ broke_by rs (SUC n) k'’ >>
  conj_tac >- (rw[] >> fs[]) >>
  first_x_assum irule >> simp[]
QED

Theorem broke_ok_of:
  LENGTH s'.procs = LENGTH s.procs ∧ (∀k. s'.alive k ⇒ s.alive k) ∧ s'.target = s.target ∧
  (∀k. k < LENGTH s.procs ∧ s'.alive k ⇒
       back (EL k s.procs) (EL k s'.procs) (λc. broke_by rs (SUC n) k)) ⇒
  broke_ok rs n s s'
Proof
  rw[broke_ok_def] >> irule back_mono >> qexists_tac ‘λc. broke_by rs (SUC n) k’ >> simp[]
QED

Theorem back_deliver2:
  nb a ∧ nb b ∧ k < LENGTH s.procs ⇒
  back (EL k s.procs) (EL k (sys_deliver k2 b (sys_deliver k1 a s)).procs) X
Proof
  strip_tac >> irule back_sys_deliver >> simp[] >> irule back_sys_deliver >> simp[]
QED

Theorem back_deliver1:
  nb a ∧ k < LENGTH s.procs ⇒ back (EL k s.procs) (EL k (sys_deliver k1 a s).procs) X
Proof
  strip_tac >> irule back_sys_deliver >> simp[]
QED

Theorem broke_ok_kern:
  rs n = Kern kk ∧ sys_step s (Kern kk) s' ⇒ broke_ok rs n s s'
Proof
  Cases_on ‘kk’ >> simp[sys_step_def] >> strip_tac >> irule broke_ok_of >> gvs[]
  >- simp[back_deliver2]
  >- simp[back_deliver1]
  >- simp[back_deliver1]
  >- simp[back_deliver1]
  >> rw[sys_deliver_EL] >> irule back_any >> simp[broke_by_def] >> qexists_tac ‘n’ >> simp[]
QED

Theorem broke_ok_env:
  sys_step s (Env ee) s' ⇒ broke_ok rs n s s'
Proof
  Cases_on ‘ee’ >> simp[sys_step_def] >> strip_tac >> irule broke_ok_of >> gvs[]
  >- simp[back_deliver1]
  >- simp[back_deliver1] >>
  rename1 ‘env_arrival_chan a = SOME j’ >>
  ‘nb a’ by (Cases_on ‘a’ >> fs[env_arrival_chan_def, nb_def]) >>
  simp[back_deliver1]
QED

Theorem broke_ok_exit:
  sys_step s (Exit k) s' ⇒ broke_ok rs n s s'
Proof
  simp[sys_step_def] >> strip_tac >> irule broke_ok_of >>
  gvs[combinTheory.APPLY_UPDATE_THM, EL_LUPDATE] >> rw[]
QED

Theorem broke_inv_ok:
  broke_inv rs n s ∧ broke_ok rs n s s' ⇒ broke_inv rs (SUC n) s'
Proof
  rw[broke_ok_def] >> irule broke_inv_gen >> qexists_tac ‘s’ >> simp[]
QED

Theorem broke_inv_step:
  sinv rsl s css ∧ broke_inv rs n s ∧ sys_step s (rs n) s' ⇒ broke_inv rs (SUC n) s'
Proof
  strip_tac >> irule broke_inv_ok >> qexists_tac ‘s’ >> simp[] >> Cases_on ‘rs n’ >> fs[]
  >- (irule broke_ok_call >> metis_tac[])
  >- (irule broke_ok_kern >> metis_tac[])
  >- (irule broke_ok_env >> metis_tac[])
  >> irule broke_ok_exit >> metis_tac[]
QED

Theorem irun_broke_inv:
  l0sys_irun ps ss rs ⇒ ∀n. broke_inv rs n (ss n)
Proof
  strip_tac >> Induct
  >- (fs[l0sys_irun_def, sys_init_def, LET_THM, broke_inv_def, is_end_def] >>
      rpt strip_tac >> res_tac >> fs[]) >>
  drule irun_sinv >> disch_then (qspec_then ‘n’ strip_assume_tac) >>
  irule broke_inv_step >> fs[l0sys_irun_def] >> metis_tac[]
QED

(* MAIN: a live broken channel of an alive process, not a connect's, is
   excused (kern_broke or a hard accept failure, both in sys_excuse) *)
Theorem irun_broke:
  l0sys_irun ps ss rs ∧ is_end (ss n) (k, c) ∧ (ss n).alive k ∧
  (sys_chan (ss n) (k, c)).broken ∧ (ss n).target (k, c) = NONE ∧
  live (EL k (ss n).procs) c ⇒
  kern_broke rs k ∨ hard_fail rs k «sys_accept»
Proof
  strip_tac >> drule irun_broke_inv >> disch_then (qspec_then ‘n’ mp_tac) >>
  rewrite_tac[broke_inv_def] >> disch_then drule_all >> rw[broke_by_def]
  >- (disj1_tac >> simp[kern_broke_def] >> metis_tac[])
  >- (disj1_tac >> simp[kern_broke_def] >> metis_tac[]) >>
  disj2_tac >> simp[hard_fail_def, l1_transient_def] >>
  qexistsl_tac [‘m’, ‘conf’, ‘bts’, ‘out’, ‘E_MFILE’, ‘v’] >> simp[]
QED
