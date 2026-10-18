(*
  The KV lift, never-accepted ends: a channel queued at a listener of k
  stays queued, gets an fd (accept) or breaks (accept abort, EMFILE drop,
  listener close).
*)
Theory moonshotLiveKvQueue
Ancestors
  moonshotLiveKvLift moonshotLiveF1 moonshotLiveExcuse moonshotLiveClaimRun moonshotLiveWorldDrains moonshotLiveProjInf moonshotLiveAccepts l0sysFair l0sys
  l0sysInvCall l0sysMono l0sysStep l0sysProj moonshotLiveDrains honestL0World honestL0Rely llist
Libs
  preamble

(* ------------------------------------------------------------------------
   Leaving the queue: a queued channel stays queued, gets an fd, or breaks
   ------------------------------------------------------------------------ *)

Theorem pop_queued:
  ∀L. MEM c (FLAT (MAP (SND o SND) L)) ∧ FILTER (λ(l', p, q). l' = l) L = (l1, p1, j :: q1) :: t1 ⇒
      c = j ∨ MEM c (FLAT (MAP (SND o SND) (AFUPDKEY l (K (p1, q1)) L)))
Proof
  Induct >> simp[] >> PairCases >> rpt gen_tac >> strip_tac >> Cases_on ‘h0 = l’ >> fs[AFUPDKEY_def] >> gvs[]
QED

Theorem breaks_broken:
  ∀q w. c < LENGTH w.chans ∧ (MEM c q ∨ (EL c w.chans).broken) ⇒
        c < LENGTH (FOLDL (λw j. upd_lchan j (break_lchan e kp) w) w q).chans ∧
        (EL c (FOLDL (λw j. upd_lchan j (break_lchan e kp) w) w q).chans).broken
Proof
  Induct >> simp[] >> rpt gen_tac >> disch_tac >>
  first_x_assum (qspec_then ‘upd_lchan h (break_lchan e kp) w’ mp_tac) >>
  impl_tac >- (fs[upd_lchan_def, EL_LUPDATE] >> rw[break_lchan_def] >> fs[]) >>
  simp[]
QED

Theorem filter_head_distinct:
  ∀L. ALL_DISTINCT (MAP FST L) ∧ MEM (f, b, qq) L ∧
      FILTER (λ(l, p, q). l = f) L = (x, y, q) :: t ⇒ qq = q
Proof
  Induct >> simp[] >> PairCases >> rw[] >> gvs[MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

Theorem breaks_listeners[simp]:
  ∀q w. (FOLDL (λw j. upd_lchan j g w) w q).listeners = w.listeners
Proof
  Induct >> simp[] >> simp[upd_lchan_def]
QED

Theorem breaks_len[simp]:
  ∀q w. LENGTH (FOLDL (λw j. upd_lchan j g w) w q).chans = LENGTH w.chans
Proof
  Induct >> simp[upd_lchan_def]
QED

Theorem close_fd_queued:
  MEM c (FLAT (MAP (SND o SND) w.listeners)) ∧ ALL_DISTINCT (MAP FST w.listeners) ∧ c < LENGTH w.chans ⇒
  MEM c (FLAT (MAP (SND o SND) (close_fd f w).listeners)) ∨
  c < LENGTH (close_fd f w).chans ∧ (EL c (close_fd f w).chans).broken
Proof
  strip_tac >> simp[close_fd_def] >> Cases_on ‘l0_chan_of w f’ >> simp[] >>
  Cases_on ‘FILTER (λ(l,p,q). l = f) w.listeners’ >> simp[] >>
  PairCases_on ‘h’ >> simp[] >>
  qpat_x_assum ‘MEM c _’ mp_tac >> simp[MEM_FLAT, MEM_MAP, EXISTS_PROD] >> strip_tac >>
  Cases_on ‘p_1 = f’
  >- (‘l = h2’ by metis_tac[filter_head_distinct] >> disj2_tac >>
      mp_tac (Q.INST [‘e’ |-> ‘E_CONNRESET’, ‘kp’ |-> ‘F’] breaks_broken) >>
      disch_then (qspecl_then [‘h2’, ‘w with listeners := FILTER (λ(l,p,q). l ≠ f) w.listeners’] mp_tac) >>
      gvs[]) >>
  disj1_tac >> qexists_tac ‘l’ >> simp[MEM_FILTER] >> qexistsl_tac [‘p_1’, ‘p_1'’] >> simp[]
QED

Theorem accept_queued:
  l0_accept l w = (r, w') ∧ MEM c (FLAT (MAP (SND o SND) w.listeners)) ∧ c < LENGTH w.chans ⇒
  MEM c (FLAT (MAP (SND o SND) w'.listeners)) ∨
  c < LENGTH w'.chans ∧ (EL c w'.chans).broken ∨ ∃f. l0_chan_of w' f = SOME c
Proof
  rw[l0_accept_def, AllCaseEqs()] >> simp[] >>
  drule_all pop_queued >> strip_tac >> gvs[] >>
  TRY (disj2_tac >> qexists_tac ‘f’ >> simp[l0_chan_of_def] >> NO_TAC) >>
  disj2_tac >> disj1_tac >> simp[upd_lchan_def, EL_LUPDATE, break_lchan_def] >> rw[]
QED

Theorem close_queued:
  l0_close g w = (r, w') ∧
  MEM c (FLAT (MAP (SND o SND) w.listeners)) ∧ ALL_DISTINCT (MAP FST w.listeners) ∧ c < LENGTH w.chans ⇒
  MEM c (FLAT (MAP (SND o SND) w'.listeners)) ∨ c < LENGTH w'.chans ∧ (EL c w'.chans).broken
Proof
  rw[l0_close_def] >> every_case_tac >> gvs[] >> irule close_fd_queued >> simp[]
QED

Theorem call_queued:
  l0_call nm (unblock nm conf) bts w = SOME (FFIreturn out w1) ∧
  MEM c (FLAT (MAP (SND o SND) w.listeners)) ∧ ALL_DISTINCT (MAP FST w.listeners) ∧ c < LENGTH w.chans ⇒
  MEM c (FLAT (MAP (SND o SND) w1.listeners)) ∨
  c < LENGTH w1.chans ∧ (EL c w1.chans).broken ∨ ∃f. l0_chan_of w1 f = SOME c
Proof
  strip_tac >>
  Cases_on ‘nm = «sys_poll»’ >- (gvs[] >> drule l0_call_poll_unblock >> simp[]) >>
  gvs[unblock_other, l0_call_def, AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  TRY (gvs[l0_listen_def, l0_recv_def, l0_send_def, l0_shutdown_def, l0_connerr_def, AllCaseEqs()] >>
       gvs[upd_lchan_def] >> NO_TAC) >>
  TRY (drule_all accept_queued >> simp[] >> NO_TAC) >>
  TRY (qpat_x_assum ‘l0_close _ _ = _’ assume_tac >> drule close_queued >>
       disch_then (qspec_then ‘c’ mp_tac) >> impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
       metis_tac[]) >>
  drule l0_connect_cases >> simp[LET_THM] >> strip_tac >> gvs[upd_lchan_def]
QED

Theorem irun_queued_ok:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ∧
  MEM j (FLAT (MAP (SND o SND) (EL k (ss t).procs).listeners)) ⇒
  ALL_DISTINCT (MAP FST (EL k (ss t).procs).listeners) ∧ j < LENGTH (EL k (ss t).procs).chans
Proof
  strip_tac >> ‘k < LENGTH (ss t).procs’ by metis_tac[irun_procs_length] >>
  drule irun_sinv >> disch_then (qspec_then ‘t’ strip_assume_tac) >>
  fs[sinv_def] >> first_x_assum drule >>
  simp[pk_def, LET_THM, l0sysInvTheory.pinv_def] >> strip_tac >>
  gvs[MEM_FLAT, MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

(* The three outcomes survive deliveries *)
Theorem FOLDL_deliver_qout:
  MEM j (FLAT (MAP (SND o SND) w.listeners)) ∨ (∃f. l0_chan_of w f = SOME j) ∨
  j < LENGTH w.chans ∧ frozen (EL j w.chans) ⇒
  MEM j (FLAT (MAP (SND o SND) (FOLDL l0_deliver w as).listeners)) ∨
  (∃f. l0_chan_of (FOLDL l0_deliver w as) f = SOME j) ∨
  j < LENGTH (FOLDL l0_deliver w as).chans ∧ frozen (EL j (FOLDL l0_deliver w as).chans)
Proof
  strip_tac
  >- (disj1_tac >> irule FOLDL_deliver_queued >> first_assum ACCEPT_TAC)
  >- (disj2_tac >> disj1_tac >> qexists_tac ‘f’ >> irule FOLDL_deliver_chan_of >> first_assum ACCEPT_TAC) >>
  disj2_tac >> disj2_tac >> irule FOLDL_deliver_frozen >> simp[]
QED

(* One step: a queued channel of k stays queued, gets an fd, or ends *)
Theorem queued_step:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ∧ kstep k (ss t) (rs t) (ss (SUC t)) as ∧ (ss (SUC t)).alive k ∧
  MEM j (FLAT (MAP (SND o SND) (EL k (ss t).procs).listeners)) ⇒
  MEM j (FLAT (MAP (SND o SND) (EL k (ss (SUC t)).procs).listeners)) ∨
  (∃f. fd_at ss k j f (SUC t)) ∨ ended ss (k, j) (SUC t)
Proof
  strip_tac >> drule_all irun_queued_ok >> strip_tac >>
  ‘k < LENGTH (ss (SUC t)).procs’ by metis_tac[irun_procs_length] >>
  qpat_x_assum ‘kstep _ _ _ _ _’ mp_tac >> rewrite_tac[kstep_def] >> strip_tac >>
  simp[fd_at_def, moonshotLiveObsTheory.ended_def, is_end_def, sys_chan_def] >>
  Cases_on ‘rs t’ >> fs[] >>
  TRY (rename1 ‘Exit k0’ >> Cases_on ‘k0 = k’ >> gvs[]) >>
  TRY (rename1 ‘Call k0 nm conf bts out’ >> Cases_on ‘k0 = k’ >> gvs[]) >>
  irule FOLDL_deliver_qout >>
  TRY (disj1_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
  drule_all call_queued >> simp[frozen_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The world on k's trace right after k's call: the call's result
   ------------------------------------------------------------------------ *)

Theorem agrees_to_det:
  ∀evs st a b. agrees_to orc st evs a ∧ agrees_to orc st evs b ⇒ a = b
Proof
  Induct >> simp[agrees_to_def] >> Cases >> simp[agrees_to_def] >> rpt strip_tac >>
  gvs[] >> first_x_assum irule >> metis_tac[]
QED

Theorem world_after_call:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ∧ (∀t. kstep k (ss t) (rs t) (ss (SUC t)) (AS t)) ∧
  w0 = (EL k (ss 0).procs) with env := (λn h nm. fenv k ss AS n) ∧
  (∀t. ∃V. agrees_to l0_oracle w0 (ptr rs k t) V ∧
           ((ss t).alive k ⇒
            V.env = w0.env ∧ V.clock = fclk k ss t ∧
            (EL k (ss t).procs) with env := w0.env = FOLDL l0_deliver V (fseg k ss AS t))) ∧
  rs t = Call k nm conf bts out ⇒
  ∃w1. l0_call nm (unblock nm conf) bts (EL k (ss t).procs) = SOME (FFIreturn out w1) ∧
       EL k (ss (SUC t)).procs =
         FOLDL l0_deliver (w1 with <| clock := (EL k (ss t).procs).clock + 1;
                                      hist := (EL k (ss t).procs).hist ++ [(nm, conf, bts)] |>) (AS t) ∧
       moonshotLiveCopy$world_at w0 (ptr rs k (SUC t)) =
         SOME ((w1 with <| clock := (EL k (ss t).procs).clock + 1;
                           hist := (EL k (ss t).procs).hist ++ [(nm, conf, bts)] |>) with env := w0.env)
Proof
  strip_tac >>
  qpat_assum ‘∀t. kstep _ _ _ _ _’ (qspec_then ‘t’ mp_tac) >> rewrite_tac[kstep_def] >>
  simp[] >> strip_tac >>
  qexists_tac ‘w1’ >> simp[] >>
  qabbrev_tac ‘wk = EL k (ss t).procs’ >>
  qpat_assum ‘∀t. ∃V. _’ (qspec_then ‘t’ strip_assume_tac) >> gvs[] >>
  ‘fenv k ss AS (fclk k ss t) = fseg k ss AS t’
    by (irule fenv_call >> qexists_tac ‘rs’ >> conj_tac >- first_assum ACCEPT_TAC >>
        qpat_assum ‘rs t = _’ (fn th => simp[th, is_kcall_def])) >>
  ‘fclk k ss t = wk.clock’ by simp[fclk_def, Abbr ‘wk’] >>
  ‘l0_oracle (ExtCall nm) V conf bts =
   Oracle_return ((w1 with <| clock := wk.clock + 1; hist := wk.hist ++ [(nm, conf, bts)] |>)
                    with env := V.env) out’
    by (irule l0_oracle_call >> simp[] >>
        qexists_tac ‘λn. fenv k ss AS n’ >> gvs[]) >>
  irule agrees_world_at >>
  simp[ptr_SUC, agrees_to_SNOC] >> qexists_tac ‘V’ >> simp[] >>
  ‘l0_rely wk’ by (simp[Abbr ‘wk’] >> drule_all irun_fds >> simp[]) >>
  ‘LENGTH out = LENGTH bts’ by metis_tac[honestL0WorldPropsTheory.l0_call_length] >>
  gvs[MAP_ZIP]
QED

(* ------------------------------------------------------------------------
   From the world on k's trace back to the run: an fd, a break
   ------------------------------------------------------------------------ *)

Theorem run_of_world:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ∧ (ss t).alive k ∧
  (∀t. ∃V. agrees_to l0_oracle w0 (ptr rs k t) V ∧
           ((ss t).alive k ⇒
            V.env = w0.env ∧ V.clock = fclk k ss t ∧
            (EL k (ss t).procs) with env := w0.env = FOLDL l0_deliver V (fseg k ss AS t))) ∧
  moonshotLiveCopy$world_at w0 (ptr rs k t) = SOME w ⇒
  (EL k (ss t).procs).open_fds = w.open_fds ∧
  (∀j. j < LENGTH w.chans ∧ frozen (EL j w.chans) ⇒
       j < LENGTH (EL k (ss t).procs).chans ∧ frozen (EL j (EL k (ss t).procs).chans))
Proof
  strip_tac >>
  qpat_x_assum ‘∀t. ∃V. _’ (qspec_then ‘t’ strip_assume_tac) >>
  ‘V = w’ by (drule agrees_world_at >> simp[]) >> gvs[] >>
  ‘(EL k (ss t).procs).open_fds = V.open_fds ∧
   (EL k (ss t).procs).chans = (FOLDL l0_deliver V (fseg k ss AS t)).chans’
    by (qpat_x_assum ‘_ with env := _ = FOLDL _ _ _’ (mp_tac o Q.AP_TERM ‘λx. (x.open_fds, x.chans)’) >>
        simp[]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  qspecl_then [‘fseg k ss AS t’, ‘V’] mp_tac FOLDL_deliver_frozen >> simp[]
QED

Theorem fd_at_of_world_fds:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ∧ (ss t).alive k ∧
  (∀t. ∃V. agrees_to l0_oracle w0 (ptr rs k t) V ∧
           ((ss t).alive k ⇒
            V.env = w0.env ∧ V.clock = fclk k ss t ∧
            (EL k (ss t).procs) with env := w0.env = FOLDL l0_deliver V (fseg k ss AS t))) ∧
  moonshotLiveCopy$world_at w0 (ptr rs k t) = SOME w ∧ ALOOKUP w.open_fds f = SOME j ⇒
  fd_at ss k j f t
Proof
  strip_tac >> drule_all run_of_world >> strip_tac >>
  ‘ALOOKUP (EL k (ss t).procs).open_fds f = SOME j’ by gvs[] >>
  drule_all irun_open_lt >> strip_tac >>
  simp[fd_at_def, l0_chan_of_def]
QED

Theorem ended_of_world:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ∧ (ss t).alive k ∧
  (∀t. ∃V. agrees_to l0_oracle w0 (ptr rs k t) V ∧
           ((ss t).alive k ⇒
            V.env = w0.env ∧ V.clock = fclk k ss t ∧
            (EL k (ss t).procs) with env := w0.env = FOLDL l0_deliver V (fseg k ss AS t))) ∧
  moonshotLiveCopy$world_at w0 (ptr rs k t) = SOME w ∧ j < LENGTH w.chans ∧ (EL j w.chans).broken ⇒
  ended ss (k, j) t
Proof
  strip_tac >> drule_all run_of_world >> strip_tac >>
  ‘k < LENGTH (ss t).procs’ by metis_tac[irun_procs_length] >>
  first_x_assum (qspec_then ‘j’ mp_tac) >> simp[frozen_def] >> strip_tac >>
  simp[moonshotLiveObsTheory.ended_def, is_end_def, sys_chan_def, frozen_def]
QED

(* ------------------------------------------------------------------------
   conn_live_l0 at the run.  TEMPORARY COPIES of honestL1BStmts' broke and
   conn_live_unless (spike/kv-live-l0 @bbf45dfe8; not an ancestor here);
   remove when the lines merge.
   ------------------------------------------------------------------------ *)

Definition kv_broke_def:
  kv_broke w0 io c ⇔
    ∃evs w. LPREFIX (fromList evs) io ∧ moonshotLiveCopy$world_at w0 evs = SOME w ∧
            c < LENGTH w.chans ∧ (EL c w.chans).broken
End

Definition kv_conn_live_unless_def:
  kv_conn_live_unless X w0 io ⇔
    ∀evs w l p q j0.
      LPREFIX (fromList evs) io ∧ moonshotLiveCopy$world_at w0 evs = SOME w ∧
      MEM (l, p, q) w.listeners ∧ MEM j0 q ⇒
      X ∨
      (∃evs' w' f. LPREFIX (fromList evs') io ∧ moonshotLiveCopy$world_at w0 evs' = SOME w' ∧
                   ALOOKUP w'.open_fds f = SOME j0 ∧
                   MEM f (honestEchoL0SpecCopy$l0_accepted evs')) ∨
      kv_broke w0 io j0
End

(* Queued from t0 on: at k's next call, the world on k's trace has it queued *)
Theorem kv_queued_held:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ∧ (∀t. kstep k (ss t) (rs t) (ss (SUC t)) (AS t)) ∧
  (∀t. ∃t'. t ≤ t' ∧ is_kcall k (rs t')) ∧
  w0 = (EL k (ss 0).procs) with env := (λn h nm. fenv k ss AS n) ∧
  (∀t. ∃V. agrees_to l0_oracle w0 (ptr rs k t) V ∧
           ((ss t).alive k ⇒
            V.env = w0.env ∧ V.clock = fclk k ss t ∧
            (EL k (ss t).procs) with env := w0.env = FOLDL l0_deliver V (fseg k ss AS t))) ∧
  (∀t. LPREFIX (fromList (ptr rs k t)) tr) ∧ kv_conn_live_unless X w0 tr ∧
  (∀u. t0 ≤ u ⇒ MEM j (FLAT (MAP (SND o SND) (EL k (ss u).procs).listeners))) ⇒
  X ∨ (∃f t. fd_at ss k j f t) ∨ ∃n. ended ss (k, j) n
Proof
  strip_tac >>
  ‘∀t. (ss t).alive k’ by (irule kstep_alive_all >> metis_tac[]) >>
  qpat_assum ‘∀t. ∃t'. t ≤ t' ∧ _’ (qspec_then ‘t0’ strip_assume_tac) >>
  ‘∃nm conf bts out. rs t' = Call k nm conf bts out’
    by (Cases_on ‘rs t'’ >> fs[is_kcall_def]) >>
  ‘MEM j (FLAT (MAP (SND o SND) (EL k (ss t').procs).listeners))’ by (first_x_assum irule >> simp[]) >>
  drule_all irun_queued_ok >> strip_tac >>
  ‘∃w1. l0_call nm (unblock nm conf) bts (EL k (ss t').procs) = SOME (FFIreturn out w1) ∧
        EL k (ss (SUC t')).procs =
          FOLDL l0_deliver (w1 with <| clock := (EL k (ss t').procs).clock + 1;
                                       hist := (EL k (ss t').procs).hist ++ [(nm, conf, bts)] |>) (AS t') ∧
        moonshotLiveCopy$world_at w0 (ptr rs k (SUC t')) =
          SOME ((w1 with <| clock := (EL k (ss t').procs).clock + 1;
                            hist := (EL k (ss t').procs).hist ++ [(nm, conf, bts)] |>) with env := w0.env)’
    by (irule world_after_call >> rpt conj_tac >>
        FIRST [first_assum ACCEPT_TAC, qexists_tac ‘ps’ >> conj_tac >> first_assum ACCEPT_TAC]) >>
  qabbrev_tac ‘W1 = w1 with <| clock := (EL k (ss t').procs).clock + 1;
                               hist := (EL k (ss t').procs).hist ++ [(nm, conf, bts)] |>’ >>
  ‘k < LENGTH (ss (SUC t')).procs’ by metis_tac[irun_procs_length] >>
  drule_all call_queued >> strip_tac
  >- (‘∃l p q. MEM (l, p, q) w1.listeners ∧ MEM j q’
        by (gvs[MEM_FLAT, MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
      qpat_x_assum ‘kv_conn_live_unless _ _ _’ (mp_tac o REWRITE_RULE [kv_conn_live_unless_def]) >>
      disch_then (qspecl_then [‘ptr rs k (SUC t')’, ‘W1 with env := w0.env’, ‘l’, ‘p’, ‘q’, ‘j’] mp_tac) >>
      impl_tac >- simp[Abbr ‘W1’] >>
      strip_tac >- simp[]
      >- (disj2_tac >> disj1_tac >>
          ‘∃t''. ptr rs k t'' = evs'’ by (irule ptr_of_prefix >> metis_tac[]) >>
          qexistsl_tac [‘f’, ‘t''’] >> irule fd_at_of_world_fds >>
          conj_tac >- (qpat_assum ‘∀t. (ss t).alive k’ (qspec_then ‘t''’ ACCEPT_TAC)) >>
          qexistsl_tac [‘AS’, ‘ps’, ‘rs’, ‘w'’, ‘w0’] >>
          qpat_x_assum ‘ptr _ _ _ = _’ (fn th => rewrite_tac[th]) >>
          rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disj2_tac >> disj2_tac >>
      qpat_x_assum ‘kv_broke _ _ _’ (strip_assume_tac o REWRITE_RULE [kv_broke_def]) >>
      ‘∃t3. ptr rs k t3 = evs’ by (irule ptr_of_prefix >> metis_tac[]) >>
      qexists_tac ‘t3’ >> irule ended_of_world >>
      conj_tac >- (qpat_assum ‘∀t. (ss t).alive k’ (qspec_then ‘t3’ ACCEPT_TAC)) >>
      qexistsl_tac [‘AS’, ‘ps’, ‘rs’, ‘w’, ‘w0’] >>
      qpat_x_assum ‘ptr _ _ _ = _’ (fn th => rewrite_tac[th]) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (disj2_tac >> disj2_tac >> qexists_tac ‘SUC t'’ >>
      simp[moonshotLiveObsTheory.ended_def, is_end_def, sys_chan_def] >>
      qspecl_then [‘AS t'’, ‘W1’] mp_tac (Q.INST [‘j’ |-> ‘j’] FOLDL_deliver_frozen) >>
      simp[Abbr ‘W1’, frozen_def]) >>
  disj2_tac >> disj1_tac >> qexistsl_tac [‘f’, ‘SUC t'’] >>
  simp[fd_at_def] >> irule FOLDL_deliver_chan_of >> simp[Abbr ‘W1’]
QED

(* A channel queued at k: eventually it has an fd, or it ended, unless X *)
Theorem kv_queued_lift:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ∧ (∀t. kstep k (ss t) (rs t) (ss (SUC t)) (AS t)) ∧
  (∀t. ∃t'. t ≤ t' ∧ is_kcall k (rs t')) ∧
  w0 = (EL k (ss 0).procs) with env := (λn h nm. fenv k ss AS n) ∧
  (∀t. ∃V. agrees_to l0_oracle w0 (ptr rs k t) V ∧
           ((ss t).alive k ⇒
            V.env = w0.env ∧ V.clock = fclk k ss t ∧
            (EL k (ss t).procs) with env := w0.env = FOLDL l0_deliver V (fseg k ss AS t))) ∧
  (∀t. LPREFIX (fromList (ptr rs k t)) tr) ∧ kv_conn_live_unless X w0 tr ∧
  MEM j (FLAT (MAP (SND o SND) (EL k (ss t0).procs).listeners)) ⇒
  X ∨ (∃f t. fd_at ss k j f t) ∨ ∃n. ended ss (k, j) n
Proof
  strip_tac >>
  ‘∀t. (ss t).alive k’ by (irule kstep_alive_all >> metis_tac[]) >>
  mp_tac (Q.INST [‘P’ |-> ‘λu. MEM j (FLAT (MAP (SND o SND) (EL k (ss u).procs).listeners))’]
                 held_or_lost) >>
  impl_tac >- simp[] >> strip_tac
  >- (irule kv_queued_held >> conj_tac >- (qexists_tac ‘t0’ >> fs[]) >>
      qexistsl_tac [‘AS’, ‘ps’, ‘rs’, ‘tr’, ‘w0’] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  ‘MEM j (FLAT (MAP (SND o SND) (EL k (ss (SUC u)).procs).listeners)) ∨
   (∃f. fd_at ss k j f (SUC u)) ∨ ended ss (k, j) (SUC u)’
    by (irule queued_step >> rpt conj_tac >>
        FIRST [qexistsl_tac [‘AS u’, ‘ps’, ‘rs’] >> asm_rewrite_tac[] >> NO_TAC, fs[]]) >>
  metis_tac[]
QED
