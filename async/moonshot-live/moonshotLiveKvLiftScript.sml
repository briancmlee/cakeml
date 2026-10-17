(*
  The KV lift (README §6): kv_live_claim's trace clauses (kv_live_l0,
  conn_live_l0) at the run give kv_ob.  This file starts with the fd
  bridge: an fd that the world on k's trace prefix maps to channel j is
  fd_at j in the run (deliveries keep open_fds and only add channels).
*)
Theory moonshotLiveKvLift
Ancestors
  moonshotLiveF1 moonshotLiveExcuse moonshotLiveClaimRun moonshotLiveWorldDrains moonshotLiveProjInf moonshotLiveAccepts l0sysFair l0sys
  l0sysInvCall l0sysMono l0sysStep l0sysProj moonshotLiveDrains honestL0World honestL0Rely llist
Libs
  preamble

Theorem deliver_chan_of:
  l0_chan_of w f = SOME j ⇒ l0_chan_of (l0_deliver w a) f = SOME j
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def, l0_chan_of_def, upd_lchan_def] >>
  every_case_tac >> gvs[]
QED

Theorem FOLDL_deliver_chan_of:
  ∀as w. l0_chan_of w f = SOME j ⇒ l0_chan_of (FOLDL l0_deliver w as) f = SOME j
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >> irule deliver_chan_of >>
  first_assum ACCEPT_TAC
QED

Theorem chan_of_env:
  l0_chan_of (w with env := e) f = l0_chan_of w f
Proof
  simp[l0_chan_of_def]
QED

(* The fd bridge *)
Theorem fd_at_of_world:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ∧ (∀t. ∃t'. t ≤ t' ∧ is_kcall k (rs t')) ∧
  (∀t. kstep k (ss t) (rs t) (ss (SUC t)) (AS t)) ∧
  w0 = (EL k (ss 0).procs) with env := (λn h nm. fenv k ss AS n) ∧
  (∀t. ∃V. agrees_to l0_oracle w0 (ptr rs k t) V ∧
           ((ss t).alive k ⇒
            V.clock = fclk k ss t ∧
            (EL k (ss t).procs) with env := w0.env = FOLDL l0_deliver V (fseg k ss AS t))) ∧
  moonshotLiveCopy$world_at w0 (ptr rs k t) = SOME wt ∧ l0_chan_of wt f = SOME j ⇒
  fd_at ss k j f t
Proof
  strip_tac >>
  ‘(ss t).alive k’ by metis_tac[kstep_alive_all] >>
  qpat_x_assum ‘∀t. ∃V. _’ (qspec_then ‘t’ strip_assume_tac) >>
  drule agrees_world_at >> strip_tac >>
  ‘wt = V’ by metis_tac[optionTheory.SOME_11] >>
  gvs[] >>
  simp[fd_at_def] >>
  ‘l0_chan_of (EL k (ss t).procs) f =
   l0_chan_of ((EL k (ss t).procs) with env := (λn h nm. fenv k ss AS n)) f’ by simp[chan_of_env] >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum ‘_ with env := _ = FOLDL _ _ _’ SUBST1_TAC >>
  irule FOLDL_deliver_chan_of >> first_assum ACCEPT_TAC
QED

Theorem chan_of_upds:
  ∀q w. l0_chan_of (FOLDL (λw j. upd_lchan j g w) w q) f = l0_chan_of w f
Proof
  Induct >> simp[]
QED

Theorem close_chan_of:
  g ≠ f ∧ l0_close g w = (r, w') ⇒ l0_chan_of w' f = l0_chan_of w f
Proof
  rw[l0_close_def, close_fd_def] >> every_case_tac >> gvs[] >>
  simp[l0sysInvTheory.l0_chan_of_ADELKEY, chan_of_upds] >> simp[l0_chan_of_def]
QED

(* A call other than a close of f keeps f's channel (a new fd is the
   lowest free one, so not f) *)
Theorem chan_of_call:
  l0_call nm (unblock nm conf) bts w = SOME (FFIreturn out w1) ∧
  (∀x. MEM x (l0_used w) ⇒ w2n x < w.fd_limit) ∧ w.fd_limit ≤ 2 ** 31 ∧
  l0_chan_of w f = SOME j ∧ ¬(nm = «sys_close» ∧ bytes_fd conf = f) ⇒
  l0_chan_of w1 f = SOME j
Proof
  strip_tac >>
  ‘¬MEM (lowest_fd w) (l0_used w)’ by (irule lowest_fd_free >> simp[]) >>
  ‘MEM f (l0_used w)’
    by (qpat_x_assum ‘l0_chan_of _ _ = _’ mp_tac >> simp[l0_chan_of_def, AllCaseEqs(), l0_used_def] >>
        strip_tac >> imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  ‘f ≠ lowest_fd w’ by (strip_tac >> fs[]) >>
  Cases_on ‘nm = «sys_poll»’ >- (gvs[] >> drule l0_call_poll_unblock >> simp[]) >>
  gvs[unblock_other, l0_call_def, AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  TRY (gvs[l0_listen_def, l0_recv_def, l0_send_def, l0_shutdown_def, l0_connerr_def, AllCaseEqs()] >>
       gvs[l0_chan_of_def, upd_lchan_def, AllCaseEqs()] >> NO_TAC) >>
  TRY (drule_all close_chan_of >> simp[] >> NO_TAC) >>
  TRY (drule l0_accept_cases >> strip_tac >> gvs[l0_alloc_def, AllCaseEqs()] >>
       gvs[l0_chan_of_def, AllCaseEqs()] >> NO_TAC) >>
  drule l0_connect_cases >> strip_tac >> gvs[l0_alloc_def, LET_THM, AllCaseEqs()] >>
  gvs[l0_chan_of_def, upd_lchan_def, AllCaseEqs()]
QED

Theorem irun_fds:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ⇒
  l0_rely (EL k (ss t).procs) ∧
  ∀x. MEM x (l0_used (EL k (ss t).procs)) ⇒ w2n x < (EL k (ss t).procs).fd_limit
Proof
  strip_tac >> ‘k < LENGTH (ss t).procs’ by metis_tac[irun_procs_length] >>
  drule irun_sinv >> disch_then (qspec_then ‘t’ strip_assume_tac) >>
  fs[sinv_def] >> first_x_assum drule >>
  simp[pk_def, LET_THM, l0sysInvTheory.pinv_def, l0sysInvTheory.fds_lt_def] >> metis_tac[]
QED

Theorem chan_of_clock_hist[simp]:
  l0_chan_of (w with <| clock := c; hist := h |>) f = l0_chan_of w f
Proof
  simp[l0_chan_of_def]
QED

(* One step: f keeps its channel unless k closes f *)
Theorem fd_at_step:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ∧ kstep k (ss t) (rs t) (ss (SUC t)) as ∧ (ss (SUC t)).alive k ∧
  fd_at ss k j f t ∧ (∀conf bts out. rs t = Call k «sys_close» conf bts out ⇒ bytes_fd conf ≠ f) ⇒
  fd_at ss k j f (SUC t)
Proof
  strip_tac >>
  ‘l0_rely (EL k (ss t).procs) ∧
   ∀x. MEM x (l0_used (EL k (ss t).procs)) ⇒ w2n x < (EL k (ss t).procs).fd_limit’
    by (drule_all irun_fds >> simp[]) >>
  qpat_x_assum ‘kstep _ _ _ _ _’ mp_tac >> rewrite_tac[kstep_def] >> strip_tac >>
  fs[fd_at_def] >> Cases_on ‘rs t’ >> gvs[]
  >- (rename1 ‘Call k0 nm conf bts out’ >> Cases_on ‘k0 = k’ >> gvs[]
      >- (irule FOLDL_deliver_chan_of >> simp[] >> irule chan_of_call >>
          qexistsl_tac [‘bts’, ‘conf’, ‘nm’, ‘out’] >>
          fs[l0_rely_def] >> rw[] >> fs[unblock_def] >> metis_tac[]) >>
      irule FOLDL_deliver_chan_of >> first_assum ACCEPT_TAC) >>
  TRY (rename1 ‘Exit k0’ >> Cases_on ‘k0 = k’ >> gvs[]) >>
  irule FOLDL_deliver_chan_of >> first_assum ACCEPT_TAC
QED

(* Over an interval: f keeps its channel while k doesn't close f *)
Theorem fd_at_persist:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ∧ (∀t. kstep k (ss t) (rs t) (ss (SUC t)) (AS t)) ∧
  (∀t. (ss t).alive k) ∧ fd_at ss k j f t0 ∧
  (∀t conf bts out. t0 ≤ t ∧ t < t0 + d ∧ rs t = Call k «sys_close» conf bts out ⇒ bytes_fd conf ≠ f) ⇒
  fd_at ss k j f (t0 + d)
Proof
  strip_tac >> Induct_on ‘d’ >- simp[] >>
  strip_tac >> rewrite_tac[ADD_CLAUSES] >> irule fd_at_step >>
  simp[] >>
  conj_tac >- (qpat_x_assum ‘_ ⇒ fd_at _ _ _ _ _’ mp_tac >> impl_tac >> simp[] >>
               rpt strip_tac >> qpat_x_assum ‘∀t conf bts out. _’ drule >> simp[]) >>
  qexistsl_tac [‘AS (t0 + d)’, ‘ps’, ‘rs’] >> simp[] >>
  rpt strip_tac >> first_x_assum (qspecl_then [‘t0 + d’, ‘conf’, ‘bts’, ‘out’] mp_tac) >> simp[]
QED

(* ------------------------------------------------------------------------
   K-asks transfer.  TEMPORARY COPIES of honestKvL0LiveStmts' asks_ev and
   asks_io_on (spike/kv-live-l0 @bbf45dfe8; not an ancestor here); remove
   when the lines merge.
   ------------------------------------------------------------------------ *)

Definition kv_asks_ev_def:
  kv_asks_ev f ev ⇔
    (∃conf bs. ev = IO_event (ExtCall «sys_recv») conf bs ∧ LENGTH conf = 8 ∧
               bytes_fd conf = f) ∨
    (∃conf bs. ev = IO_event (ExtCall «sys_poll») conf bs ∧
               ∃e. MEM (f, e) (MAP pe_fe (pollfd_entries (DROP 16 (MAP FST bs)))) ∧ ODD e)
End

Definition kv_asks_io_on_def:
  kv_asks_io_on f (tr : io_event llist) ⇔ ∀i. ∃i' ev. i ≤ i' ∧ LNTH i' tr = SOME ev ∧ kv_asks_ev f ev
End

Theorem asks_ev_lab:
  rs n = Call k nm conf bts out ∧ LENGTH out = LENGTH bts ∧
  kv_asks_ev f (IO_event (ExtCall nm) conf (ZIP (bts, out))) ∧ fd_at ss k j f n ⇒
  asks_in ss rs k j n
Proof
  rw[kv_asks_ev_def, asks_in_def] >> gvs[MAP_ZIP] >> metis_tac[]
QED

(* K-asks on the trace, with f k's fd of j from t0 on and never closed by
   k, is asks_in on the run *)
Theorem asks_transfer:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ∧ (∀t. kstep k (ss t) (rs t) (ss (SUC t)) (AS t)) ∧
  (∀t. ∃t'. t ≤ t' ∧ is_kcall k (rs t')) ∧ (∀t. LPREFIX (fromList (ptr rs k t)) tr) ∧
  kv_asks_io_on f tr ∧ fd_at ss k j f t0 ∧
  (∀t conf bts out. t0 ≤ t ∧ rs t = Call k «sys_close» conf bts out ⇒ bytes_fd conf ≠ f) ⇒
  io (asks_in ss rs k j)
Proof
  strip_tac >>
  ‘∀t. (ss t).alive k’ by (irule kstep_alive_all >> metis_tac[]) >>
  ‘io (λn. ∃nm conf bts out. rs n = Call k nm conf bts out ∧
                             kv_asks_ev f (IO_event (ExtCall nm) conf (ZIP (bts, out))))’
    by (mp_tac (Q.INST [‘P’ |-> ‘kv_asks_ev f’] io_tr_lab) >>
        impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
        disch_then (SUBST1_TAC o GSYM) >>
        qpat_x_assum ‘kv_asks_io_on _ _’ mp_tac >> rewrite_tac[kv_asks_io_on_def]) >>
  rewrite_tac[io_def] >> strip_tac >>
  qpat_x_assum ‘io (λn. _)’ mp_tac >> rewrite_tac[io_def] >>
  disch_then (qspec_then ‘MAX n0 t0’ strip_assume_tac) >> fs[MAX_LE] >>
  qexists_tac ‘n’ >> simp[] >>
  irule asks_ev_lab >> qexistsl_tac [‘bts’, ‘conf’, ‘f’, ‘nm’, ‘out’] >> simp[] >>
  conj_tac >- (irule irun_call_len >> metis_tac[]) >>
  ‘n = t0 + (n - t0)’ by simp[] >> pop_assum SUBST1_TAC >>
  irule fd_at_persist >> rpt conj_tac >- first_assum ACCEPT_TAC
  >- (qexistsl_tac [‘AS’, ‘ps’, ‘rs’] >> simp[] >>
      rpt strip_tac >> rename1 ‘rs t = Call k «sys_close» cf bs ot’ >>
      qpat_x_assum ‘∀t conf bts out. t0 ≤ t ∧ _ ⇒ _’ (qspecl_then [‘t’, ‘cf’, ‘bs’, ‘ot’] mp_tac) >>
      simp[]) >>
  first_assum ACCEPT_TAC
QED

(* ------------------------------------------------------------------------
   The converse bridge: an fd of k's channel j in the run is j's fd in the
   world of k's trace.  Deliveries keep open_fds; a channel they add is
   queued at a listener, and queued channels have no fd (pinv)
   ------------------------------------------------------------------------ *)

Theorem queued_AFUPDKEY:
  ∀L. MEM x (FLAT (MAP (SND o SND) L)) ⇒
      MEM x (FLAT (MAP (SND o SND) (AFUPDKEY l (λ(p, q). (p, q ++ [c])) L)))
Proof
  Induct >> simp[AFUPDKEY_def] >> PairCases >> rw[AFUPDKEY_def] >> gvs[]
QED

Theorem queued_AFUPDKEY_new:
  ∀L. MEM l (MAP FST L) ⇒
      MEM c (FLAT (MAP (SND o SND) (AFUPDKEY l (λ(p, q). (p, q ++ [c])) L)))
Proof
  Induct >> simp[AFUPDKEY_def] >> PairCases >> rw[AFUPDKEY_def] >> gvs[]
QED

Theorem deliver_open_fds[simp]:
  (l0_deliver w a).open_fds = w.open_fds
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def, upd_lchan_def] >> every_case_tac >> simp[]
QED

Theorem FOLDL_deliver_open_fds[simp]:
  ∀as w. (FOLDL l0_deliver w as).open_fds = w.open_fds
Proof
  Induct >> simp[]
QED

Theorem deliver_queued:
  MEM j (FLAT (MAP (SND o SND) w.listeners)) ⇒
  MEM j (FLAT (MAP (SND o SND) (l0_deliver w a).listeners))
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def, upd_lchan_def] >> every_case_tac >> simp[] >>
  irule queued_AFUPDKEY >> first_assum ACCEPT_TAC
QED

Theorem FOLDL_deliver_queued:
  ∀as w. MEM j (FLAT (MAP (SND o SND) w.listeners)) ⇒
         MEM j (FLAT (MAP (SND o SND) (FOLDL l0_deliver w as).listeners))
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >> irule deliver_queued >>
  first_assum ACCEPT_TAC
QED

Theorem deliver_len:
  LENGTH (l0_deliver w a).chans = LENGTH w.chans ∨
  LENGTH (l0_deliver w a).chans = LENGTH w.chans + 1 ∧
  MEM (LENGTH w.chans) (FLAT (MAP (SND o SND) (l0_deliver w a).listeners))
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def, upd_lchan_def] >> every_case_tac >> simp[] >>
  irule queued_AFUPDKEY_new >>
  rename1 ‘FILTER _ w.listeners = (l, r) :: _’ >>
  ‘MEM (l, r) w.listeners’
    by (qpat_x_assum ‘FILTER _ _ = _’ (mp_tac o Q.AP_TERM ‘MEM (l, r)’) >>
        simp[MEM_FILTER]) >>
  simp[MEM_MAP, EXISTS_PROD] >> PairCases_on ‘r’ >> metis_tac[]
QED

(* A channel that deliveries added is queued at a listener *)
Theorem FOLDL_deliver_new_queued:
  ∀as w. j < LENGTH (FOLDL l0_deliver w as).chans ∧ LENGTH w.chans ≤ j ⇒
         MEM j (FLAT (MAP (SND o SND) (FOLDL l0_deliver w as).listeners))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  qspecl_then [‘w’, ‘h’] strip_assume_tac (GEN_ALL deliver_len)
  >- (first_x_assum irule >> simp[]) >>
  Cases_on ‘j = LENGTH w.chans’
  >- (irule FOLDL_deliver_queued >> gvs[]) >>
  first_x_assum irule >> simp[]
QED

(* Queued channels have no fd *)
Theorem irun_queued_no_fd:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ∧
  MEM j (FLAT (MAP (SND o SND) (EL k (ss t).procs).listeners)) ⇒
  l0_chan_of (EL k (ss t).procs) f ≠ SOME j
Proof
  strip_tac >> ‘k < LENGTH (ss t).procs’ by metis_tac[irun_procs_length] >>
  drule irun_sinv >> disch_then (qspec_then ‘t’ strip_assume_tac) >>
  fs[sinv_def] >> first_x_assum drule >>
  simp[pk_def, LET_THM, l0sysInvTheory.pinv_def] >> strip_tac >>
  gvs[MEM_FLAT, MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

Theorem world_of_fd_at:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ∧ (ss t).alive k ∧
  w0 = (EL k (ss 0).procs) with env := (λn h nm. fenv k ss AS n) ∧
  (∀t. ∃V. agrees_to l0_oracle w0 (ptr rs k t) V ∧
           ((ss t).alive k ⇒
            V.clock = fclk k ss t ∧
            (EL k (ss t).procs) with env := w0.env = FOLDL l0_deliver V (fseg k ss AS t))) ∧
  fd_at ss k j f t ⇒
  ∃V. moonshotLiveCopy$world_at w0 (ptr rs k t) = SOME V ∧ l0_chan_of V f = SOME j
Proof
  strip_tac >>
  qpat_x_assum ‘∀t. ∃V. _’ (qspec_then ‘t’ strip_assume_tac) >>
  qexists_tac ‘V’ >> conj_tac >- (irule agrees_world_at >> first_assum ACCEPT_TAC) >>
  ‘(ss t).alive k ⇒ V.clock = fclk k ss t ∧
     (EL k (ss t).procs) with env := w0.env = FOLDL l0_deliver V (fseg k ss AS t)’
    by first_assum ACCEPT_TAC >>
  pop_assum mp_tac >> impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qabbrev_tac ‘P = EL k (ss t).procs’ >>
  ‘l0_chan_of P f = SOME j’ by fs[fd_at_def, Abbr ‘P’] >>
  ‘(P with env := w0.env).open_fds = V.open_fds ∧
   (P with env := w0.env).chans = (FOLDL l0_deliver V (fseg k ss AS t)).chans ∧
   (P with env := w0.env).listeners = (FOLDL l0_deliver V (fseg k ss AS t)).listeners’
    by (qpat_x_assum ‘_ with env := _ = _’ SUBST1_TAC >> simp[]) >>
  fs[] >>
  ‘ALOOKUP V.open_fds f = SOME j ∧ j < LENGTH P.chans’
    by (qpat_x_assum ‘l0_chan_of P f = _’ mp_tac >> simp[l0_chan_of_def, AllCaseEqs()]) >>
  simp[l0_chan_of_def] >> CCONTR_TAC >> fs[NOT_LESS] >>
  ‘MEM j (FLAT (MAP (SND o SND) P.listeners))’
    by (qpat_x_assum ‘P.listeners = _’ SUBST1_TAC >> irule FOLDL_deliver_new_queued >>
        conj_tac >- (qpat_x_assum ‘P.chans = _’ (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
        first_assum ACCEPT_TAC) >>
  ‘l0_chan_of P f ≠ SOME j’ by (qunabbrev_tac ‘P’ >> irule irun_queued_no_fd >>
                                      conj_tac >- first_assum ACCEPT_TAC >>
                                      qexistsl_tac [‘ps’, ‘rs’] >> asm_rewrite_tac[]) >>
  fs[]
QED

(* ------------------------------------------------------------------------
   Episodes.  TEMPORARY COPIES of honestL1BStmts' ep_ends and ep_open
   (spike/kv-live-l0 @bbf45dfe8); remove when the lines merge.
   ------------------------------------------------------------------------ *)

Definition kv_ep_ends_def:
  kv_ep_ends f e ⇔ l0_event_closed e = SOME f ∨ l0_event_accepted e = SOME f
End

Definition kv_ep_open_def:
  kv_ep_open j evs ⇔
    ∃pre ev post f.
      evs = pre ++ [ev] ++ post ∧ LENGTH (l0_accepted pre) = j ∧
      l0_event_accepted ev = SOME f ∧ EVERY (λe. ¬kv_ep_ends f e) post
End

(* A successful accept by k at t opens episode j = #accepts before t, on
   the fd it returned *)
Theorem ep_open_accept:
  rs t = Call k nm conf bts out ∧
  l0_event_accepted (IO_event (ExtCall nm) conf (ZIP (bts, out))) = SOME f ⇒
  kv_ep_open (LENGTH (l0_accepted (ptr rs k t))) (ptr rs k (SUC t)) ∧
  EL (LENGTH (l0_accepted (ptr rs k t))) (l0_accepted (ptr rs k (SUC t))) = f
Proof
  strip_tac >> simp[ptr_SUC, l0_accepted_append] >>
  conj_tac >- (simp[kv_ep_open_def] >>
               qexistsl_tac [‘ptr rs k t’, ‘IO_event (ExtCall nm) conf (ZIP (bts, out))’, ‘[]’] >>
               simp[]) >>
  simp[honestEchoL0SpecCopyTheory.l0_accepted_def, EL_APPEND2]
QED
