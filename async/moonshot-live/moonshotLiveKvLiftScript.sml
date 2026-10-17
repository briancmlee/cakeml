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
