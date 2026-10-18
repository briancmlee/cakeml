(*
  The KV lift, the excuses (README §6): kv_live_l0's K-asks excuses, read
  on KV's own trace tr, in the system forms kv_ob reads:
   - ep_hard_err j tr ⇒ hard_io rs k (in sys_excuse);
   - ep_timed_out K j tr ⇒ timed_out_sys K rs k (in sys_excuse);
   - ch_frozen w0 tr c ⇒ ended ss (k, c) n for some n;
   - ep_ended j tr, for the episode j of an end (k, c) accepted at t on
     fd f ⇒ ended ss (k, c) n for some n: an episode ends at a successful
     close of f or an accept returning f, and neither can happen while k
     still holds f on c, so k loses f (fd_lost_ended).
  kv_ep_closed, kv_ep_ended, kv_hard_err_on, kv_ep_hard_err,
  kv_ep_timed_out, kv_ch_frozen and kv_peer_valid are TEMPORARY COPIES of
  honestL1BStmts' ep_closed, ep_ended, hard_err_on, ep_hard_err,
  ep_timed_out and honestKvL0LiveStmts' ch_frozen, peer_valid @bbf45dfe8 (with l0_ev_res bs written
  dec_res (MAP SND bs), and moonshotLiveStmts' poll_ev / out_poll /
  n_out_polls / send_took, qualified: proxyL0StmtsCopy has its own); unify at the merge.
*)
Theory moonshotLiveKvExcuse
Ancestors
  moonshotLiveKvQueue moonshotLiveKvLift moonshotLiveF1 moonshotLiveExcuse moonshotLiveClaimRun
  moonshotLiveWorldDrains moonshotLiveProjInf moonshotLiveAccepts l0sysFair l0sys
  l0sysInvCall l0sysMono l0sysStep l0sysProj moonshotLiveDrains honestL0World honestL0Rely llist
Libs
  preamble

(* ------------------------------------------------------------------------
   TEMPORARY COPIES (honestL1BStmts / honestKvL0LiveStmts @bbf45dfe8)
   ------------------------------------------------------------------------ *)

Definition kv_ep_closed_def:
  kv_ep_closed j evs ⇔
    ∃pre ev post f.
      evs = pre ++ [ev] ++ post ∧ LENGTH (l0_accepted pre) = j ∧
      l0_event_accepted ev = SOME f ∧ EXISTS (kv_ep_ends f) post
End

Definition kv_ep_ended_def:
  kv_ep_ended j io ⇔ ∃evs. LPREFIX (fromList evs) io ∧ kv_ep_closed j evs
End

Definition kv_hard_err_on_def:
  kv_hard_err_on f (IO_event nm conf bs) ⇔
    (nm = ExtCall «sys_recv» ∨ nm = ExtCall «sys_send») ∧ 8 ≤ LENGTH conf ∧
    bytes_fd (TAKE 8 conf) = f ∧
    ∃e x. dec_res (MAP SND bs) = SOME (Fail e x) ∧ ¬l1_transient e
End

Definition kv_ep_hard_err_def:
  kv_ep_hard_err j io ⇔
    ∃evs ev. LPREFIX (fromList (evs ++ [ev])) io ∧ kv_ep_open j evs ∧
             kv_hard_err_on (EL j (l0_accepted evs)) ev
End

Definition kv_ep_timed_out_def:
  kv_ep_timed_out bnd j io ⇔
    ∃evs span.
      LPREFIX (fromList (evs ++ span)) io ∧ kv_ep_open j evs ∧
      bnd ≤ moonshotLiveStmts$n_out_polls (EL j (l0_accepted evs)) span ∧
      EVERY (λe. moonshotLiveStmts$poll_ev e ⇒ moonshotLiveStmts$out_poll (EL j (l0_accepted evs)) e) span ∧
      ¬EXISTS (moonshotLiveStmts$send_took (EL j (l0_accepted evs))) span ∧
      ¬EXISTS (kv_ep_ends (EL j (l0_accepted evs))) span
End

Definition kv_ch_frozen_def:
  kv_ch_frozen w0 io c ⇔
    ∃evs w. LPREFIX (fromList evs) io ∧ moonshotLiveCopy$world_at w0 evs = SOME w ∧
            c < LENGTH w.chans ∧
            ((EL c w.chans).peer_eof ∨ (EL c w.chans).broken ∨ (EL c w.chans).closed)
End

Definition kv_peer_valid_def:
  kv_peer_valid w0 io c ⇔
    ∀evs w. LPREFIX (fromList evs) io ∧ moonshotLiveCopy$world_at w0 evs = SOME w ∧ c < LENGTH w.chans ⇒
            ∃rqs. EVERY valid_brequest rqs ∧ (EL c w.chans).peer_sent ≼ brequests rqs
End

(* ------------------------------------------------------------------------
   D16, D23: events of the run
   ------------------------------------------------------------------------ *)

Theorem kv_hard_err_sys:
  l0sys_irun ps ss rs ∧ (∀t. ∃t'. t ≤ t' ∧ is_kcall k (rs t')) ∧
  (∀t. LPREFIX (fromList (ptr rs k t)) tr) ∧ kv_ep_hard_err j tr ⇒
  hard_io rs k
Proof
  rewrite_tac[kv_ep_hard_err_def] >> strip_tac >>
  ‘∃t. MEM ev (ptr rs k t)’ by (irule io_mem_ptr >> conj_tac >- first_assum ACCEPT_TAC >> qexistsl_tac [‘evs ++ [ev]’, ‘tr’] >> simp[]) >>
  Cases_on ‘ev’ >> rename1 ‘IO_event nm conf bs’ >> Cases_on ‘nm’ >>
  fs[kv_hard_err_on_def] >> metis_tac[hard_io_of_event]
QED

Theorem kv_timed_out_sys:
  (∀t. ∃t'. t ≤ t' ∧ is_kcall k (rs t')) ∧
  (∀t. LPREFIX (fromList (ptr rs k t)) tr) ∧ kv_ep_timed_out bnd j tr ⇒
  timed_out_sys bnd rs k
Proof
  rewrite_tac[kv_ep_timed_out_def] >> strip_tac >>
  irule timed_out_of_prefix >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [‘EL j (l0_accepted evs)’, ‘evs’, ‘span’, ‘tr’] >> asm_rewrite_tac[]
QED

(* ------------------------------------------------------------------------
   A frozen channel on the trace: ended
   ------------------------------------------------------------------------ *)

Theorem kv_frozen_sys:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ∧ (∀t. (ss t).alive k) ∧
  (∀t. ∃t'. t ≤ t' ∧ is_kcall k (rs t')) ∧
  (∀t. ∃V. agrees_to l0_oracle w0 (ptr rs k t) V ∧
           ((ss t).alive k ⇒
            V.env = w0.env ∧ V.clock = fclk k ss t ∧
            (EL k (ss t).procs) with env := w0.env = FOLDL l0_deliver V (fseg k ss AS t))) ∧
  (∀t. LPREFIX (fromList (ptr rs k t)) tr) ∧ kv_ch_frozen w0 tr c ⇒
  ∃n. ended ss (k, c) n
Proof
  rewrite_tac[kv_ch_frozen_def] >> strip_tac >>
  ‘∃t. ptr rs k t = evs’
    by (irule ptr_of_prefix >> conj_tac >- first_assum ACCEPT_TAC >> qexists_tac ‘tr’ >> asm_rewrite_tac[]) >>
  qpat_x_assum ‘ptr rs k t = evs’ (SUBST_ALL_TAC o SYM) >>
  qexists_tac ‘t’ >>
  ‘(ss t).alive k’ by (qpat_assum ‘∀t. (ss t).alive k’ (qspec_then ‘t’ ACCEPT_TAC)) >>
  drule_all run_of_world >> strip_tac >>
  ‘k < LENGTH (ss t).procs’ by metis_tac[irun_procs_length] >>
  first_x_assum (qspec_then ‘c’ mp_tac) >> simp[frozen_def] >>
  strip_tac >> simp[moonshotLiveObsTheory.ended_def, is_end_def, sys_chan_def, frozen_def]
QED

(* ------------------------------------------------------------------------
   An ended episode: k lost the fd
   ------------------------------------------------------------------------ *)

Theorem close_ok_gone:
  l0_rely w ∧ l0_call «sys_close» conf bts w = SOME (FFIreturn out w1) ∧
  l0_event_closed (IO_event (ExtCall «sys_close») conf (ZIP (bts, out))) = SOME f ∧
  l0_chan_of w f = SOME j ⇒
  ALOOKUP w1.open_fds f = NONE
Proof
  strip_tac >> ‘LENGTH out = LENGTH bts’ by metis_tac[honestL0WorldPropsTheory.l0_call_length] >>
  gvs[l0_call_def] >> pairarg_tac >> gvs[] >>
  gvs[honestEchoL0SpecCopyTheory.l0_event_closed_def, honestEchoL0SpecCopyTheory.l0_ev_res_def,
      MAP_ZIP, AllCaseEqs()] >>
  gvs[l0_close_def, AllCaseEqs()] >>
  TRY (metis_tac[dec_res_fail0]) >>
  gvs[close_fd_def] >> simp[upd_lchan_def, ALOOKUP_ADELKEY]
QED

Theorem accept_ok_fresh:
  l0_rely w ∧ (∀x. MEM x (l0_used w) ⇒ w2n x < w.fd_limit) ∧
  l0_call «sys_accept» conf bts w = SOME (FFIreturn out w1) ∧
  l0_event_accepted (IO_event (ExtCall «sys_accept») conf (ZIP (bts, out))) = SOME f ⇒
  l0_chan_of w f = NONE
Proof
  strip_tac >> ‘LENGTH out = LENGTH bts’ by metis_tac[honestL0WorldPropsTheory.l0_call_length] >>
  gvs[l0_call_def] >> pairarg_tac >> gvs[] >>
  drule l0_accept_cases >> strip_tac >>
  gvs[honestEchoL0SpecCopyTheory.l0_event_accepted_def, honestEchoL0SpecCopyTheory.l0_ev_res_def,
      MAP_ZIP, AllCaseEqs()] >>
  TRY (metis_tac[dec_res_fail0]) >>
  ‘dec_res (enc_res (Ok (w2n f')) ++ []) = SOME (Ok (w2n f'))’
    by (irule dec_res_ok >> assume_tac (w2n_lt |> INST_TYPE [alpha |-> “:64”]) >> gvs[]) >>
  gvs[] >>
  ‘w.fd_limit ≤ 2 ** 31’ by fs[l0_rely_def] >>
  ‘¬MEM f' (l0_used w)’
    by (drule_at (Pos last) l0sysInvTheory.l0_alloc_fresh >>
        simp[l0sysInvTheory.fds_lt_def]) >>
  gvs[l0_used_def, l0_chan_of_def, AllCaseEqs()] >>
  disj1_tac >> simp[ALOOKUP_NONE]
QED

(* An event ending f's episode is not a step that keeps k's fd f on j *)
Theorem ends_step_lost:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ∧ kstep k (ss u) (rs u) (ss (SUC u)) as ∧ (ss (SUC u)).alive k ∧
  rs u = Call k nm conf bts out ∧ kv_ep_ends f (IO_event (ExtCall nm) conf (ZIP (bts, out))) ∧
  fd_at ss k j f u ⇒
  ¬fd_at ss k j f (SUC u)
Proof
  strip_tac >>
  ‘l0_rely (EL k (ss u).procs) ∧
   ∀x. MEM x (l0_used (EL k (ss u).procs)) ⇒ w2n x < (EL k (ss u).procs).fd_limit’
    by (drule_all irun_fds >> simp[]) >>
  qpat_x_assum ‘kstep _ _ _ _ _’ mp_tac >> rewrite_tac[kstep_def] >> simp[] >> strip_tac >>
  qpat_x_assum ‘kv_ep_ends _ _’ mp_tac >> rewrite_tac[kv_ep_ends_def] >> strip_tac
  >- (‘nm = «sys_close»’
        by (qpat_x_assum ‘l0_event_closed _ = _’ mp_tac >>
            simp[honestEchoL0SpecCopyTheory.l0_event_closed_def, AllCaseEqs()]) >>
      gvs[unblock_other] >>
      ‘l0_chan_of (EL k (ss u).procs) f = SOME j’ by fs[fd_at_def] >>
      drule_all close_ok_gone >> strip_tac >>
      simp[fd_at_def, l0_chan_of_def]) >>
  ‘nm = «sys_accept»’
    by (qpat_x_assum ‘l0_event_accepted _ = _’ mp_tac >>
        simp[honestEchoL0SpecCopyTheory.l0_event_accepted_def, AllCaseEqs()]) >>
  gvs[unblock_other] >>
  drule_all accept_ok_fresh >> strip_tac >>
  qpat_x_assum ‘fd_at _ _ _ _ u’ mp_tac >> simp[fd_at_def]
QED

Theorem accepted_unique:
  a ++ [x] ++ c = b ++ [y] ++ d ∧ IS_SOME (l0_event_accepted x) ∧ IS_SOME (l0_event_accepted y) ∧
  LENGTH (l0_accepted a) = LENGTH (l0_accepted b) ⇒
  a = b ∧ x = y ∧ c = d
Proof
  rewrite_tac[GSYM APPEND_ASSOC, APPEND_EQ_APPEND] >> strip_tac >> gvs[] >>
  gvs[l0_accepted_append, APPEND_EQ_SING, APPEND_EQ_CONS, IS_SOME_EXISTS] >>
  gvs[honestEchoL0SpecCopyTheory.l0_accepted_def]
QED

Theorem ptr_index:
  ∀n p. p < LENGTH (ptr rs k n) ⇒
        ∃u. u < n ∧ LENGTH (ptr rs k u) = p ∧ ptr rs k (SUC u) = ptr rs k u ++ [EL p (ptr rs k n)]
Proof
  Induct >- simp[moonshotLiveStmtsTheory.ptr_def, proc_events_def] >>
  rpt strip_tac >>
  ‘∃X. ptr rs k (SUC n) = ptr rs k n ++ X’ by (irule ptr_mono >> simp[]) >>
  assume_tac (Q.INST [‘t’ |-> ‘n’] ptr_len_SUC) >>
  qpat_x_assum ‘ptr rs k (SUC n) = _’ (fn th => FULL_SIMP_TAC std_ss [th] >> assume_tac th) >>
  Cases_on ‘p < LENGTH (ptr rs k n)’
  >- (first_x_assum drule >> strip_tac >> qexists_tac ‘u’ >> simp[EL_APPEND1]) >>
  ‘p = LENGTH (ptr rs k n) ∧ LENGTH X = 1’ by (fs[] >> every_case_tac >> fs[]) >>
  qexists_tac ‘n’ >> Cases_on ‘X’ >> fs[] >> rename1 ‘h :: tl’ >> Cases_on ‘tl’ >> fs[EL_APPEND2]
QED

(* The episode of an end (k, j) accepted at t on fd f has ended on tr:
   k lost f on j, so the end is ended *)
Theorem kv_ended_lift:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ∧ (∀t. kstep k (ss t) (rs t) (ss (SUC t)) (AS t)) ∧
  (∀t. (ss t).alive k) ∧ (∀t. ∃t'. t ≤ t' ∧ is_kcall k (rs t')) ∧
  (∀t. LPREFIX (fromList (ptr rs k t)) tr) ∧
  rs t = Call k «sys_accept» conf bts out ∧
  l0_event_accepted (IO_event (ExtCall «sys_accept») conf (ZIP (bts, out))) = SOME f ∧
  fd_at ss k j f (SUC t) ∧ kv_ep_ended (LENGTH (l0_accepted (ptr rs k t))) tr ⇒
  ∃n. ended ss (k, j) n
Proof
  strip_tac >>
  mp_tac (Q.INST [‘P’ |-> ‘λu. fd_at ss k j f u’, ‘t0’ |-> ‘SUC t’] held_or_lost) >> simp[] >>
  strip_tac
  >- (CCONTR_TAC >> qpat_x_assum ‘¬_’ kall_tac >>
      qpat_x_assum ‘kv_ep_ended _ _’ mp_tac >> rewrite_tac[kv_ep_ended_def, kv_ep_closed_def] >>
      strip_tac >>
      ‘∃n. ptr rs k n = evs’
        by (irule ptr_of_prefix >> conj_tac >- first_assum ACCEPT_TAC >>
            qexists_tac ‘tr’ >> asm_rewrite_tac[]) >>
      qabbrev_tac ‘acc = IO_event (ExtCall «sys_accept») conf (ZIP (bts, out))’ >>
      ‘ptr rs k (SUC t) = ptr rs k t ++ [acc]’ by simp[ptr_SUC, Abbr ‘acc’] >>
      ‘∃d. ptr rs k n = ptr rs k (SUC t) ++ d’
        by (Cases_on ‘SUC t ≤ n’ >- (irule ptr_mono >> simp[]) >>
            ‘∃d. ptr rs k (SUC t) = ptr rs k n ++ d’ by (irule ptr_mono >> simp[]) >>
            ‘ptr rs k t ++ [acc] ++ [] = pre ++ [ev] ++ (post ++ d)’ by gvs[] >>
            drule accepted_unique >> simp[Abbr ‘acc’] >> strip_tac >> gvs[]) >>
      ‘ptr rs k t ++ [acc] ++ d = pre ++ [ev] ++ post’ by gvs[] >>
      drule accepted_unique >> simp[Abbr ‘acc’] >> strip_tac >> gvs[] >>
      qpat_x_assum ‘EXISTS _ d’ (strip_assume_tac o REWRITE_RULE [EXISTS_MEM, MEM_EL]) >>
      rename1 ‘i < LENGTH d’ >>
      qspecl_then [‘n’, ‘LENGTH (ptr rs k (SUC t)) + i’] mp_tac ptr_index >>
      impl_tac >- simp[] >> strip_tac >>
      ‘EL (LENGTH (ptr rs k (SUC t)) + i) (ptr rs k n) = EL i d’ by simp[EL_APPEND2] >>
      ‘SUC t ≤ u’
        by (CCONTR_TAC >>
            ‘∃x. ptr rs k t = ptr rs k u ++ x’ by (irule ptr_mono >> simp[]) >>
            ‘LENGTH (ptr rs k u) ≤ LENGTH (ptr rs k t)’ by (pop_assum SUBST1_TAC >> simp[]) >>
            qpat_x_assum ‘LENGTH (ptr rs k u) = _’ mp_tac >>
            qpat_x_assum ‘ptr rs k (SUC t) = _’ (fn th => rewrite_tac[th]) >> simp[] >>
            qpat_x_assum ‘LENGTH (ptr rs k u) ≤ _’ mp_tac >> simp[]) >>
      qpat_x_assum ‘ptr rs k (SUC u) = _’ mp_tac >> simp[ptr_SUC] >>
      Cases_on ‘rs u’ >> simp[] >> rename1 ‘Call k0 nm c0 b0 o0’ >> Cases_on ‘k0 = k’ >> simp[] >>
      strip_tac >>
      ‘kv_ep_ends f (IO_event (ExtCall nm) c0 (ZIP (b0, o0)))’
        by (qpat_x_assum ‘IO_event _ _ _ = _’ SUBST1_TAC >>
            qpat_x_assum ‘e = _’ (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
      qpat_x_assum ‘k0 = k’ SUBST_ALL_TAC >>
      mp_tac (Q.INST [‘as’ |-> ‘AS u’, ‘conf’ |-> ‘c0’, ‘bts’ |-> ‘b0’, ‘out’ |-> ‘o0’] ends_step_lost) >>
      impl_tac
      >- (rpt conj_tac >>
          FIRST [first_assum ACCEPT_TAC >> NO_TAC,
                 qpat_assum ‘∀t. kstep _ _ _ _ _’ (qspec_then ‘u’ ACCEPT_TAC) >> NO_TAC,
                 qpat_assum ‘∀t. (ss t).alive k’ (qspec_then ‘SUC u’ ACCEPT_TAC) >> NO_TAC,
                 qpat_assum ‘∀u. SUC t ≤ u ⇒ _’ irule >> first_assum ACCEPT_TAC]) >>
      simp[] >> qpat_assum ‘∀u. SUC t ≤ u ⇒ _’ irule >>
      qpat_x_assum ‘SUC t ≤ u’ mp_tac >> simp[]) >>
  qexists_tac ‘SUC u’ >>
  irule fd_lost_ended >> rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC >> NO_TAC,
         qpat_assum ‘∀t. (ss t).alive k’ (qspec_then ‘SUC u’ ACCEPT_TAC) >> NO_TAC,
         qexists_tac ‘f’ >> conj_tac >> first_assum ACCEPT_TAC >> NO_TAC,
         qexistsl_tac [‘AS u’, ‘ps’, ‘rs’] >> asm_rewrite_tac[]]
QED

(* ------------------------------------------------------------------------
   K-asks per end, with kv_live_l0's excuses in system form.  The
   hypothesis on tr is kv_live_l0's K-asks clause (drains and peer_valid
   as its premises); peer_valid is still in world form here
   ------------------------------------------------------------------------ *)

Theorem kv_asks_sys:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ∧ (∀t. kstep k (ss t) (rs t) (ss (SUC t)) (AS t)) ∧
  (∀t. ∃t'. t ≤ t' ∧ is_kcall k (rs t')) ∧
  w0 = (EL k (ss 0).procs) with env := (λn h nm. fenv k ss AS n) ∧
  (∀t. ∃V. agrees_to l0_oracle w0 (ptr rs k t) V ∧
           ((ss t).alive k ⇒
            V.env = w0.env ∧ V.clock = fclk k ss t ∧
            (EL k (ss t).procs) with env := w0.env = FOLDL l0_deliver V (fseg k ss AS t))) ∧
  (∀t. LPREFIX (fromList (ptr rs k t)) tr) ∧
  (∀t conf bts out. rs t ≠ Call k «sys_connect» conf bts out) ∧
  (∀evs i c w. LPREFIX (fromList evs) tr ∧ kv_ep_open i evs ∧
               moonshotLiveCopy$world_at w0 evs = SOME w ∧
               l0_chan_of w (EL i (l0_accepted evs)) = SOME c ∧ moonshotLiveCopy$drains w0 tr c ⇒
               (kv_peer_valid w0 tr c ⇒
                kv_ep_hard_err i tr ∨ kv_ep_timed_out bnd i tr ∨ kv_ch_frozen w0 tr c ∨
                kv_ep_ended i tr ∨ kv_asks_io_on (EL i (l0_accepted evs)) tr)) ∧
  kv_conn_live_unless X w0 tr ∧ is_end (ss n) (k, j) ∧
  sys_drains ss (k, j) ∧ kv_peer_valid w0 tr j ⇒
  X ∨ hard_io rs k ∨ timed_out_sys bnd rs k ∨ (∃n. ended ss (k, j) n) ∨ io (asks_in ss rs k j)
Proof
  strip_tac >>
  ‘∀t. (ss t).alive k’ by (irule kstep_alive_all >> metis_tac[]) >>
  mp_tac (BETA_RULE
            (Q.INST [‘Q’ |-> ‘λi c. moonshotLiveCopy$drains w0 tr c ⇒ kv_peer_valid w0 tr c ⇒
                                    kv_ep_hard_err i tr ∨ kv_ep_timed_out bnd i tr ∨
                                    kv_ch_frozen w0 tr c ∨ kv_ep_ended i tr’] kv_end_lift)) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      rpt strip_tac >> qpat_x_assum ‘w0 = _’ kall_tac >>
      qpat_x_assum ‘∀evs i c w. _’ (qspecl_then [‘evs’, ‘i’, ‘c’, ‘w’] mp_tac) >>
      asm_rewrite_tac[] >> rpt (pop_assum kall_tac) >>
      metis_tac[]) >>
  strip_tac
  >- (disj1_tac >> first_assum ACCEPT_TAC)
  >- (‘moonshotLiveCopy$drains w0 tr j’
        by (irule world_drains >> qexistsl_tac [‘AS’, ‘k’, ‘ps’, ‘rs’, ‘ss’] >>
            rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
            gen_tac >> qpat_assum ‘∀t. ∃V. agrees_to _ _ _ V ∧ _’ (qspec_then ‘t'’ strip_assume_tac) >>
            qexists_tac ‘V’ >> simp[]) >>
      qpat_x_assum ‘moonshotLiveCopy$drains w0 tr j ⇒ _’ mp_tac >>
      impl_tac >- first_assum ACCEPT_TAC >>
      impl_tac >- first_assum ACCEPT_TAC >> strip_tac
      >- (disj2_tac >> disj1_tac >> drule_all kv_hard_err_sys >> disch_then ACCEPT_TAC)
      >- (disj2_tac >> disj2_tac >> disj1_tac >> drule_all kv_timed_out_sys >> disch_then ACCEPT_TAC)
      >- (disj2_tac >> disj2_tac >> disj2_tac >> disj1_tac >> drule_all kv_frozen_sys >>
          disch_then ACCEPT_TAC) >>
      disj2_tac >> disj2_tac >> disj2_tac >> disj1_tac >> drule_all kv_ended_lift >>
      disch_then ACCEPT_TAC)
  >- (disj2_tac >> disj2_tac >> disj2_tac >> disj1_tac >>
      first_assum (fn th => exists_tac (rand (concl th)) >> ACCEPT_TAC th)) >>
  disj2_tac >> disj2_tac >> disj2_tac >> disj2_tac >> first_assum ACCEPT_TAC
QED
