(*
  G2 (lift scoping): KV's peer_valid at system level, from the relay
  chain (safety).  For KV's end (2, c) paired with the proxy's backend
  (1, c1):
    KV's peer_sent at (2, c)  ≼  the backend's sent           (kernel, kinv)
    the backend's sent        =  the proxy's episode sent      (pinv)
                              ≼  the paired front's read       (proxy_safe_l0)
                              ≼  the client episode's sent     (causal_at)
                              ≼  brequests (rqs i)             (client safety)
  MAIN: kv_peer_valid_sys: at every instant, KV's end paired with a
    connect to b (kv_ob's ends) has received a prefix of valid requests,
    given the proxy's relay (relay_ok), the client's sending (csend_ok),
    W2 for client and proxy (no_fd0), neither closes fd 0, and only the
    client connects to a and only the proxy to b.  The links:
    irun_peer_sent, irun_ep_sent, irun_causal (with acc_peer), and
    irun_peer_or_empty (before its pairing an end has received nothing:
    a queued end is paired at birth, a connect end is empty while
    connecting).
  Also: orig_inv / irun_orig (an unpaired end is a connect's or an
    outside connection's; not needed by the MAIN, kept for the
    world-level lift).
*)
Theory moonshotLiveRelay
Ancestors
  moonshotLiveBroke moonshotLiveAccepts moonshotLiveCompose moonshotLiveDrains moonshotLiveProjInf moonshotLiveObs honestL0World
  moonshotLiveStmts l0sysStep l0sysInv l0sysCausal l0sysEpisodes l0sysRun l0sys
Libs
  preamble

(* What an end has received is a prefix of what its peer sent *)
Theorem irun_peer_sent:
  l0sys_irun ps ss rs ∧ (ss n).peer e = SOME e' ⇒
  (sys_chan (ss n) e).peer_sent ≼ (sys_chan (ss n) e').sent
Proof
  strip_tac >> ‘kinv (ss n)’ by metis_tac[irun_kinv] >>
  ‘(ss n).peer e' = SOME e’ by (fs[kinv_def] >> metis_tac[]) >>
  ‘(sys_chan (ss n) e).peer_sent ≼ TAKE ((ss n).moved e') (sys_chan (ss n) e').sent’
    by (qpat_x_assum ‘kinv _’ mp_tac >> rewrite_tac[kinv_def] >> strip_tac >>
        first_x_assum drule >> simp[]) >>
  metis_tac[IS_PREFIX_TRANS, TAKE_prefix_self]
QED

(* An episode with a socket sends what its channel holds *)
Theorem irun_ep_sent:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ∧ j < LENGTH (run_css ss rs n k) ∧
  EL j (ep_fds (ptr rs k n)) ≠ 0w ⇒
  l0_ep_sent j (ptr rs k n) = (sys_chan (ss n) (k, EL j (run_css ss rs n k))).sent
Proof
  strip_tac >>
  ‘sinv (GENLIST rs n) (ss n) (run_css ss rs n)’ by metis_tac[irun_sinv_css] >>
  ‘k < LENGTH (ss n).procs’ by metis_tac[irun_procs_length] >>
  ‘pk (GENLIST rs n) (ss n) (run_css ss rs n) k’ by fs[sinv_def] >>
  ‘pinv (ptr rs k n) (EL k (ss n).procs) (run_css ss rs n k)’ by fs[pk_def, ptr_def] >>
  qpat_x_assum ‘pinv _ _ _’ mp_tac >> rewrite_tac[pinv_def] >> strip_tac >>
  first_x_assum (qspec_then ‘j’ mp_tac) >> simp[l0_ep_sent_def, sys_chan_def]
QED

(* causal_at along the run: of a paired episode, what one end has read
   the other end's episode has sent *)
Theorem irun_causal:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ∧ k' < LENGTH ps ∧
  j < LENGTH (run_css ss rs n k) ∧ j' < LENGTH (run_css ss rs n k') ∧
  (ss n).peer (k', EL j' (run_css ss rs n k')) = SOME (k, EL j (run_css ss rs n k)) ∧
  EL j (ep_fds (ptr rs k n)) ≠ 0w ∧ EL j' (ep_fds (ptr rs k' n)) ≠ 0w ⇒
  l0_ep_recvd j' (ptr rs k' n) ≼ l0_ep_sent j (ptr rs k n)
Proof
  strip_tac >>
  ‘sinv (GENLIST rs n) (ss n) (run_css ss rs n)’ by metis_tac[irun_sinv_css] >>
  ‘kinv (ss n)’ by fs[sinv_def] >>
  ‘LENGTH (ss n).procs = LENGTH ps’ by metis_tac[irun_procs_length] >>
  ‘pinv (ptr rs k n) (EL k (ss n).procs) (run_css ss rs n k)’
    by (‘pk (GENLIST rs n) (ss n) (run_css ss rs n) k’ by fs[sinv_def] >> fs[pk_def, ptr_def]) >>
  ‘ALL_DISTINCT (run_css ss rs n k)’ by fs[pinv_def] >>
  rewrite_tac[ptr_def] >> irule causal_at >>
  qexistsl_tac [‘run_css ss rs n’, ‘run_css ss rs n’, ‘ss n’, ‘ss n’] >>
  fs[hist_refl, ptr_def]
QED

(* ------------------------------------------------------------------------
   Provenance of unpaired ends: a connect's (it has a target) or an
   outside connection's (an EIncoming label)
   ------------------------------------------------------------------------ *)

Definition orig_inv_def:
  orig_inv (labels : syslabel list) (s : sysstate) ⇔
    ∀k c. is_end s (k, c) ∧ s.peer (k, c) = NONE ⇒
          s.target (k, c) ≠ NONE ∨ ∃p. MEM (Env (EIncoming k p)) labels
End

Theorem deliver_chans_len:
  (∀p. a ≠ LIncoming p) ⇒ LENGTH (l0_deliver w a).chans = LENGTH w.chans
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >> gvs[upd_lchan_def]
QED

Theorem deliver_ends:
  (∀p. a ≠ LIncoming p) ⇒ (is_end (sys_deliver k a s) e ⇔ is_end s e)
Proof
  strip_tac >> PairCases_on ‘e’ >> rw[is_end_def, sys_deliver_def, EL_LUPDATE] >>
  rw[deliver_chans_len]
QED

Theorem deliver_peer_target[simp]:
  (sys_deliver k a s).peer = s.peer ∧ (sys_deliver k a s).target = s.target
Proof
  simp[sys_deliver_def]
QED

(* An old end keeps its target *)
Theorem target_old:
  sys_step s r s' ∧ is_end s e ⇒ s'.target e = s.target e
Proof
  Cases_on ‘∃k nm conf bts out. r = Call k nm conf bts out’
  >- (fs[] >> rveq >> strip_tac >> drule call_target_eq >> strip_tac >>
      qpat_x_assum ‘s'.target = _’ (fn th => rewrite_tac[th]) >>
      PairCases_on ‘e’ >> rw[call_target_def, APPLY_UPDATE_THM] >> fs[is_end_def] >>
      rw[] >> fs[]) >>
  strip_tac >> drule target_step >> metis_tac[]
QED

Theorem incoming_len:
  LENGTH (l0_deliver w (LIncoming p)).chans ≤ LENGTH w.chans + 1
Proof
  rw[l0_deliver_def] >> every_case_tac >> simp[]
QED

(* A pairing's new end has a peer *)
Theorem pair_new_end:
  is_end (sys_pair e k' p s0) x ∧ ¬is_end s0 x ⇒ (sys_pair e k' p s0).peer x ≠ NONE
Proof
  PairCases_on ‘x’ >> simp[sys_pair_def, LET_THM, is_end_def, sys_deliver_def, EL_LUPDATE] >>
  Cases_on ‘x0 = k'’ >> simp[] >> strip_tac >>
  ‘x1 = LENGTH (EL k' s0.procs).chans’
    by (‘LENGTH (l0_deliver (EL k' s0.procs) (LIncoming p)).chans ≤
         LENGTH (EL k' s0.procs).chans + 1’ by simp[incoming_len] >>
        gvs[]) >>
  rw[APPLY_UPDATE_THM]
QED

Theorem pair_ends:
  is_end s0 x ⇒ is_end (sys_pair e k' p s0) x
Proof
  PairCases_on ‘x’ >> simp[sys_pair_def, LET_THM, is_end_def, sys_deliver_def, EL_LUPDATE] >>
  rw[] >> rw[l0_deliver_def] >> every_case_tac >> simp[]
QED

(* A new end without peer or target is an outside connection's *)
Theorem new_end_step:
  sinv rs s css ∧ sys_step s r s' ∧ ¬is_end s (k, c) ∧ is_end s' (k, c) ∧
  s'.peer (k, c) = NONE ∧ s'.target (k, c) = NONE ⇒
  ∃p. r = Env (EIncoming k p)
Proof
  strip_tac >> Cases_on ‘r’
  >- ((* Call *)
      rename1 ‘Call k0 nm conf bts out’ >>
      simp[] >>
      qpat_x_assum ‘sys_step _ _ _’ (strip_assume_tac o SIMP_RULE (srw_ss()) [sys_step_def, LET_THM]) >>
      qabbrev_tac ‘w = EL k0 s.procs’ >>
      ‘pinv (proc_events k0 rs) w (css k0)’
        by (‘pk rs s css k0’ by fs[sinv_def] >> fs[pk_def, Abbr ‘w’]) >>
      ‘LENGTH w.chans < LENGTH w1.chans ⇒ nm = «sys_connect» ∧ LENGTH w1.chans = LENGTH w.chans + 1’
        by metis_tac[call_new_chans] >>
      qabbrev_tac ‘s1 = s with procs := LUPDATE (w1 with <| clock := w.clock + 1;
                                                     hist := w.hist ++ [(nm, conf, bts)] |>)
                                              k0 s.procs’ >>
      ‘∀x. is_end s1 x ∧ ¬is_end s x ⇒
           x = (k0, LENGTH w.chans) ∧ nm = «sys_connect» ∧ LENGTH w1.chans = LENGTH w.chans + 1’
        by (‘∀r. is_end s (k0, r) ⇔ r < LENGTH w.chans’ by simp[is_end_def, Abbr ‘w’] >>
            Cases >> simp[Abbr ‘s1’, is_end_LUPDATE] >> Cases_on ‘q = k0’ >> simp[] >>
            strip_tac >>
            qpat_x_assum ‘LENGTH w.chans < _ ⇒ _’ mp_tac >> impl_tac >- simp[] >> simp[]) >>
      qabbrev_tac ‘s2 = s1 with target := ((k0, LENGTH w.chans) =+ SOME (w22n conf)) s.target’ >>
      ‘¬(nm = «sys_connect» ∧ LENGTH w1.chans = LENGTH w.chans + 1) ∧ s' = s1 ∨ s' = s2 ∨
       ∃k' p. s' = sys_pair (k0, LENGTH w.chans) k' p s2’
        by (qpat_x_assum ‘if _ then _ else _’ mp_tac >>
            rw[Abbr ‘s1’, Abbr ‘s2’] >> metis_tac[])
      >- (qpat_x_assum ‘∀x. is_end s1 x ∧ _ ⇒ _’ (qspec_then ‘(k, c)’ mp_tac) >> fs[])
      >- (‘(k, c) = (k0, LENGTH w.chans)’
            by (qpat_x_assum ‘∀x. is_end s1 x ∧ _ ⇒ _’ (qspec_then ‘(k, c)’ mp_tac) >>
                fs[Abbr ‘s2’, is_end_def]) >>
          qpat_x_assum ‘s'.target _ = NONE’ mp_tac >> simp[Abbr ‘s2’, APPLY_UPDATE_THM]) >>
      Cases_on ‘is_end s2 (k, c)’
      >- (‘(k, c) = (k0, LENGTH w.chans)’
            by (qpat_x_assum ‘∀x. is_end s1 x ∧ _ ⇒ _’ (qspec_then ‘(k, c)’ mp_tac) >>
                fs[Abbr ‘s2’, is_end_def]) >>
          qpat_x_assum ‘s'.peer _ = NONE’ mp_tac >>
          simp[sys_pair_def, LET_THM, APPLY_UPDATE_THM] >> rw[]) >>
      ‘s'.peer (k, c) ≠ NONE’ suffices_by simp[] >>
      qpat_x_assum ‘s' = _’ SUBST_ALL_TAC >> irule pair_new_end >> simp[])
  >- ((* Kern *)
      Cases_on ‘k'’ >> simp[] >> qpat_x_assum ‘sys_step _ _ _’ (strip_assume_tac o SIMP_RULE (srw_ss()) [sys_step_def]) >>
      rveq >> TRY (gvs[deliver_ends] >> NO_TAC) >>
      Cases_on ‘is_end (sys_deliver n (LConnUp n0) s) (k, c)’
      >- (qpat_x_assum ‘is_end (sys_deliver _ _ _) _’ mp_tac >> simp[deliver_ends]) >>
      drule_all pair_new_end >> simp[])
  >- ((* Env *)
      Cases_on ‘e’ >> simp[] >> qpat_x_assum ‘sys_step _ _ _’ (strip_assume_tac o SIMP_RULE (srw_ss()) [sys_step_def]) >>
      rveq
      >- (Cases_on ‘k = n’ >> simp[] >>
          qpat_x_assum ‘is_end (sys_deliver _ _ _) _’ mp_tac >>
          simp[is_end_def, sys_deliver_def, EL_LUPDATE] >> fs[is_end_def])
      >- (qpat_x_assum ‘is_end (sys_deliver _ _ _) _’ mp_tac >> simp[deliver_ends]) >>
      Cases_on ‘l’ >> fs[env_arrival_chan_def] >>
      qpat_x_assum ‘is_end (sys_deliver _ _ _) _’ mp_tac >> simp[deliver_ends]) >>
  (* Exit *)
  simp[] >> qpat_x_assum ‘sys_step _ _ _’ (strip_assume_tac o SIMP_RULE (srw_ss()) [sys_step_def]) >> rveq >>
  qpat_x_assum ‘is_end _ _’ mp_tac >>
  simp[is_end_def, EL_LUPDATE] >> rw[moonshotLiveInflTheory.close_all_infl] >> fs[is_end_def]
QED

Theorem orig_step:
  sinv rs s css ∧ orig_inv lbls s ∧ sys_step s r s' ⇒ orig_inv (lbls ++ [r]) s'
Proof
  strip_tac >> rewrite_tac[orig_inv_def] >> rpt gen_tac >> strip_tac >>
  Cases_on ‘is_end s (k, c)’
  >- (‘s.peer (k, c) = NONE’
        by (‘sys_ext s s'’ by metis_tac[sys_ext_step] >>
            Cases_on ‘s.peer (k, c)’ >> simp[] >>
            qpat_x_assum ‘sys_ext _ _’ mp_tac >> rewrite_tac[sys_ext_def] >> strip_tac >>
            first_x_assum drule >> simp[]) >>
      ‘s'.target (k, c) = s.target (k, c)’ by metis_tac[target_old] >>
      qpat_x_assum ‘orig_inv _ _’ mp_tac >> rewrite_tac[orig_inv_def] >>
      disch_then (qspecl_then [‘k’, ‘c’] mp_tac) >> simp[] >> metis_tac[]) >>
  Cases_on ‘s'.target (k, c)’ >> simp[] >>
  ‘∃p. r = Env (EIncoming k p)’ by metis_tac[new_end_step] >>
  qexists_tac ‘p’ >> simp[]
QED

Theorem irun_orig:
  l0sys_irun ps ss rs ⇒ ∀n. orig_inv (GENLIST rs n) (ss n)
Proof
  strip_tac >> Induct
  >- (‘sys_init ps (ss 0)’ by fs[l0sysFairTheory.l0sys_irun_def] >>
      fs[sys_init_def, orig_inv_def, is_end_def, LET_THM] >> rpt gen_tac >>
      Cases_on ‘k < LENGTH ps’ >> simp[] >>
      qpat_x_assum ‘∀k. k < LENGTH ps ⇒ _’ drule >> simp[]) >>
  rewrite_tac[GENLIST, SNOC_APPEND] >> irule orig_step >>
  qexistsl_tac [‘run_css ss rs n’, ‘GENLIST rs n’, ‘ss n’] >>
  ‘sys_step (ss n) (rs n) (ss (SUC n))’ by fs[l0sysFairTheory.l0sys_irun_def] >>
  metis_tac[irun_sinv_css]
QED

(* ------------------------------------------------------------------------
   An end paired at some point: before that it was paired with the same
   end, or unpaired and connecting (so nothing had arrived on it)
   ------------------------------------------------------------------------ *)

Theorem ext_peer_back:
  sys_ext s s' ∧ is_end s x ∧ s'.peer x = SOME e ⇒
  s.peer x = SOME e ∨ s.peer x = NONE ∧ (sys_chan s x).connecting
Proof
  rewrite_tac[sys_ext_def] >> strip_tac >> Cases_on ‘s.peer x’
  >- (‘new_pair s x e ∨ new_pair s e x’
        by (qpat_x_assum ‘∀e e'. s'.peer e = SOME e' ∧ _ ⇒ _’ irule >> simp[]) >>
      gvs[new_pair_def]) >>
  qpat_x_assum ‘∀e e'. s.peer e = SOME e' ⇒ _’ drule >> simp[]
QED

Theorem irun_peer_fwd:
  l0sys_irun ps ss rs ⇒ ∀d m. (ss m).peer x = SOME e ⇒ (ss (m + d)).peer x = SOME e
Proof
  strip_tac >> Induct >> simp[] >> rpt strip_tac >>
  ‘sys_ext (ss (m + d)) (ss (SUC (m + d)))’ by metis_tac[irun_ext] >>
  ‘m + SUC d = SUC (m + d)’ by simp[] >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum ‘sys_ext _ _’ mp_tac >> rewrite_tac[sys_ext_def] >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem irun_peer_back:
  l0sys_irun ps ss rs ⇒
  ∀d n. is_end (ss n) x ∧ (ss (n + d)).peer x = SOME e ⇒
        (ss n).peer x = SOME e ∨ (ss n).peer x = NONE ∧ (sys_chan (ss n) x).connecting
Proof
  strip_tac >> Induct >> simp[] >> rpt strip_tac >>
  ‘sys_ext (ss n) (ss (SUC n))’ by metis_tac[irun_ext] >>
  ‘is_end (ss (SUC n)) x’ by metis_tac[is_end_ext] >>
  ‘(ss (SUC n + d)).peer x = SOME e’
    by (‘SUC n + d = n + SUC d’ by decide_tac >> pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  qpat_x_assum ‘∀n. is_end _ _ ∧ _ ⇒ _’ (qspec_then ‘SUC n’ mp_tac) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac
  >- (drule_all ext_peer_back >> simp[]) >>
  Cases_on ‘(ss n).peer x’
  >- (simp[] >> metis_tac[connecting_ext]) >>
  qpat_x_assum ‘sys_ext _ _’ mp_tac >> rewrite_tac[sys_ext_def] >> strip_tac >>
  first_x_assum drule >> simp[]
QED

(* So at any time it is paired with that end, or has received nothing *)
Theorem irun_peer_or_empty:
  l0sys_irun ps ss rs ∧ is_end (ss n) x ∧ (ss m).peer x = SOME e ⇒
  (ss n).peer x = SOME e ∨ (sys_chan (ss n) x).peer_sent = []
Proof
  strip_tac >> Cases_on ‘n ≤ m’
  >- (‘m = n + (m - n)’ by simp[] >>
      ‘(ss n).peer x = SOME e ∨ (ss n).peer x = NONE ∧ (sys_chan (ss n) x).connecting’
        by (drule irun_peer_back >> disch_then irule >> metis_tac[]) >>
      pop_assum strip_assume_tac >> simp[] >>
      ‘kinv (ss n)’ by metis_tac[irun_kinv] >>
      qpat_x_assum ‘kinv _’ mp_tac >> rewrite_tac[kinv_def] >> strip_tac >>
      first_x_assum (qspec_then ‘x’ mp_tac) >> simp[]) >>
  ‘n = m + (n - m)’ by simp[] >>
  disj1_tac >> pop_assum SUBST1_TAC >> drule irun_peer_fwd >> disch_then irule >> simp[]
QED

(* ------------------------------------------------------------------------
   G2 at system level: what KV's end paired with a connect to b has
   received is a prefix of valid requests.  The proxy's relay and the
   client's sending are hypotheses at the instant (the lift discharges
   relay_ok from close-v2's proxy_safe_ep via proxy_safe_bridge at
   ft = ptr rs 1 n, and csend_ok from the client's claim); no_fd0 is W2
   (moonshot_sys_safe's hypothesis on the proxy), here for the client too
   ------------------------------------------------------------------------ *)

Definition relay_ok_def:
  relay_ok a b rs n ⇔
    ∀i. l0_ep_role i (ptr rs 1 n) = SOME (Connected b) ⇒
        ∃f. l0_ep_role f (ptr rs 1 n) = SOME (Accepted a) ∧
            l0_ep_sent i (ptr rs 1 n) ≼ l0_ep_recvd f (ptr rs 1 n)
End

Definition csend_ok_def:
  csend_ok a rs n ⇔
    ∀i. l0_ep_role i (ptr rs 0 n) = SOME (Connected a) ⇒
        ∃rqs. EVERY valid_brequest rqs ∧ l0_ep_sent i (ptr rs 0 n) ≼ brequests rqs
End

Definition no_fd0_def:
  no_fd0 evs ⇔ EVERY (λev. ∀r. ev_new ev ≠ SOME (0w, r)) evs
End

Theorem no_fd0_ep:
  no_fd0 evs ∧ j < LENGTH (ep_fds evs) ⇒ EL j (ep_fds evs) ≠ 0w
Proof
  rw[no_fd0_def] >> strip_tac >>
  ‘MEM 0w (ep_fds evs)’ by metis_tac[MEM_EL] >>
  fs[ep_fds_def, MEM_FLAT, MEM_MAP, EVERY_MEM] >> rveq >>
  first_x_assum drule >> Cases_on ‘ev_new ev’ >> gvs[] >>
  rename1 ‘SOME x’ >> PairCases_on ‘x’ >> gvs[]
QED

Theorem irun_css_len:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ⇒
  LENGTH (run_css ss rs n k) = LENGTH (ep_fds (ptr rs k n)) ∧
  LENGTH (ep_roles [] (ptr rs k n)) = LENGTH (ep_fds (ptr rs k n))
Proof
  strip_tac >> simp[LENGTH_ep_roles] >>
  ‘sinv (GENLIST rs n) (ss n) (run_css ss rs n)’ by metis_tac[irun_sinv_css] >>
  ‘k < LENGTH (ss n).procs’ by metis_tac[irun_procs_length] >>
  ‘pk (GENLIST rs n) (ss n) (run_css ss rs n) k’ by fs[sinv_def] >>
  ‘pinv (ptr rs k n) (EL k (ss n).procs) (run_css ss rs n k)’ by fs[pk_def, ptr_def] >>
  fs[pinv_def]
QED

Theorem irun_target_fwd:
  l0sys_irun ps ss rs ⇒
  ∀d n. is_end (ss n) e ⇒ is_end (ss (n + d)) e ∧ (ss (n + d)).target e = (ss n).target e
Proof
  strip_tac >> Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  ‘n + SUC d = SUC (n + d)’ by simp[] >> pop_assum SUBST1_TAC >>
  ‘sys_ext (ss (n + d)) (ss (SUC (n + d)))’ by metis_tac[irun_ext] >>
  ‘sys_step (ss (n + d)) (rs (n + d)) (ss (SUC (n + d)))’ by fs[l0sysFairTheory.l0sys_irun_def] >>
  conj_tac >- metis_tac[is_end_ext] >>
  metis_tac[target_old]
QED

Theorem irun_target_at:
  l0sys_irun ps ss rs ∧ is_end (ss n) e ∧ is_end (ss m) e ⇒ (ss n).target e = (ss m).target e
Proof
  strip_tac >> Cases_on ‘n ≤ m’
  >- (‘m = n + (m - n)’ by simp[] >> pop_assum SUBST1_TAC >>
      metis_tac[irun_target_fwd]) >>
  ‘n = m + (n - m)’ by simp[] >> pop_assum SUBST1_TAC >>
  metis_tac[irun_target_fwd]
QED

(* An end with target b, where only the proxy connects to b, is a proxy
   Connected b episode *)
Theorem peer_backend:
  l0sys_irun ps ss rs ∧ LENGTH ps = 3 ∧ (ss n).peer x = SOME e ∧ (ss n).target e = SOME b ∧
  ¬free0 (ptr rs 1 n) ∧ (∀k. k < 3 ∧ k ≠ 1 ⇒ no_conn_to b (ptr rs k n)) ⇒
  ∃i. i < LENGTH (run_css ss rs n 1) ∧ e = (1, EL i (run_css ss rs n 1)) ∧
      EL i (ep_roles [] (ptr rs 1 n)) = Connected b
Proof
  strip_tac >>
  ‘kinv (ss n)’ by metis_tac[irun_kinv] >>
  ‘is_end (ss n) e’ by metis_tac[moonshotLiveDeliverTheory.kinv_peer_end] >>
  PairCases_on ‘e’ >>
  ‘LENGTH (ss n).procs = 3’ by metis_tac[irun_procs_length] >>
  ‘e0 < 3’ by fs[is_end_def] >>
  ‘tinv (GENLIST rs n) (ss n) (run_css ss rs n)’ by metis_tac[irun_tinv] >>
  qpat_x_assum ‘tinv _ _ _’ mp_tac >> rewrite_tac[tinv_def] >>
  disch_then drule >> rewrite_tac[GSYM ptr_def] >> strip_tac
  >- (‘e0 = 1’
        by (CCONTR_TAC >>
            ‘MEM (Connected b) (ep_roles [] (ptr rs e0 n))’
              by (rewrite_tac[MEM_EL] >> qexists_tac ‘i’ >> simp[] >>
                  mp_tac (Q.INST [‘k’ |-> ‘e0’] (SPEC_ALL irun_css_len)) >> simp[]) >>
            qpat_x_assum ‘∀k. k < 3 ∧ k ≠ 1 ⇒ _’ (qspec_then ‘e0’ mp_tac) >>
            asm_simp_tac (srw_ss()) [no_conn_to_def]) >>
      rveq >> qexists_tac ‘i’ >> simp[]) >>
  ‘e0 = 1’
    by (CCONTR_TAC >> qpat_x_assum ‘∀k. k < 3 ∧ k ≠ 1 ⇒ _’ (qspec_then ‘e0’ mp_tac) >>
        asm_simp_tac (srw_ss()) [no_conn_to_def]) >>
  rveq >> fs[]
QED

(* What a proxy Connected b episode's channel has sent is a prefix of
   valid requests: relay, the front's peer (the client's connect), causal,
   the client's sending *)
Theorem backend_valid:
  l0sys_irun ps ss rs ∧ LENGTH ps = 3 ∧ isolated [a; b] ss rs ∧
  i < LENGTH (run_css ss rs n 1) ∧ EL i (ep_roles [] (ptr rs 1 n)) = Connected b ∧
  ¬free0 (ptr rs 0 n) ∧ (∀k. k < 3 ∧ k ≠ 0 ⇒ no_conn_to a (ptr rs k n)) ∧
  no_fd0 (ptr rs 0 n) ∧ no_fd0 (ptr rs 1 n) ∧ relay_ok a b rs n ∧ csend_ok a rs n ⇒
  ∃rqs. EVERY valid_brequest rqs ∧
        (sys_chan (ss n) (1, EL i (run_css ss rs n 1))).sent ≼ brequests rqs
Proof
  strip_tac >>
  ‘LENGTH (ss n).procs = 3’ by metis_tac[irun_procs_length] >>
  mp_tac (Q.INST [‘k’ |-> ‘1’] (SPEC_ALL irun_css_len)) >> simp[] >> strip_tac >>
  mp_tac (Q.INST [‘k’ |-> ‘0’] (SPEC_ALL irun_css_len)) >> simp[] >> strip_tac >>
  ‘EL i (ep_fds (ptr rs 1 n)) ≠ 0w’ by (irule no_fd0_ep >> simp[]) >>
  ‘l0_ep_sent i (ptr rs 1 n) = (sys_chan (ss n) (1, EL i (run_css ss rs n 1))).sent’
    by (irule irun_ep_sent >> simp[] >> TRY (qexists_tac ‘ps’) >> simp[]) >>
  pop_assum (SUBST1_TAC o SYM) >>
  ‘l0_ep_role i (ptr rs 1 n) = SOME (Connected b)’ by simp[l0_ep_role_def] >>
  ‘∃f. l0_ep_role f (ptr rs 1 n) = SOME (Accepted a) ∧
       l0_ep_sent i (ptr rs 1 n) ≼ l0_ep_recvd f (ptr rs 1 n)’
    by (qpat_x_assum ‘relay_ok _ _ _ _’ mp_tac >> rewrite_tac[relay_ok_def] >>
        disch_then drule >> simp[]) >>
  ‘f < LENGTH (ep_roles [] (ptr rs 1 n)) ∧ EL f (ep_roles [] (ptr rs 1 n)) = Accepted a’
    by (qpat_x_assum ‘l0_ep_role f _ = _’ mp_tac >> rw[l0_ep_role_def]) >>
  ‘sinv (GENLIST rs n) (ss n) (run_css ss rs n)’ by metis_tac[irun_sinv_css] >>
  ‘tinv (GENLIST rs n) (ss n) (run_css ss rs n)’ by metis_tac[irun_tinv] >>
  ‘acc_inv [a; b] (GENLIST rs n) (ss n) (run_css ss rs n)’ by metis_tac[irun_acc_inv] >>
  ‘∃i0. i0 < LENGTH (run_css ss rs n 0) ∧
        EL i0 (ep_roles [] (proc_events 0 (GENLIST rs n))) = Connected a ∧
        (ss n).peer (1, EL f (run_css ss rs n 1)) = SOME (0, EL i0 (run_css ss rs n 0))’
    by (irule acc_peer >> rewrite_tac[GSYM ptr_def] >> rpt conj_tac
        >> TRY (qexists_tac ‘[a; b]’ >> simp[] >> NO_TAC) >> fs[]) >>
  ‘EL f (ep_fds (ptr rs 1 n)) ≠ 0w’ by (irule no_fd0_ep >> simp[]) >>
  ‘EL i0 (ep_fds (ptr rs 0 n)) ≠ 0w’ by (irule no_fd0_ep >> simp[]) >>
  ‘l0_ep_recvd f (ptr rs 1 n) ≼ l0_ep_sent i0 (ptr rs 0 n)’
    by (irule irun_causal >> simp[] >> qexistsl_tac [‘ps’, ‘ss’] >> simp[]) >>
  ‘l0_ep_role i0 (ptr rs 0 n) = SOME (Connected a)’ by fs[l0_ep_role_def, GSYM ptr_def] >>
  ‘∃rqs. EVERY valid_brequest rqs ∧ l0_ep_sent i0 (ptr rs 0 n) ≼ brequests rqs’
    by (qpat_x_assum ‘csend_ok _ _ _’ mp_tac >> rewrite_tac[csend_ok_def] >>
        disch_then drule >> simp[]) >>
  qexists_tac ‘rqs’ >> simp[] >>
  irule IS_PREFIX_TRANS >> qexists_tac ‘l0_ep_recvd f (ptr rs 1 n)’ >> simp[] >>
  irule IS_PREFIX_TRANS >> qexists_tac ‘l0_ep_sent i0 (ptr rs 0 n)’ >> simp[]
QED

(* G2 at system level, for kv_ob's ends: at every instant, what KV's end
   paired with a connect to b has received is a prefix of valid requests *)
Theorem kv_peer_valid_sys:
  l0sys_irun ps ss rs ∧ LENGTH ps = 3 ∧ isolated [a; b] ss rs ∧
  (ss m).peer (2, jk) = SOME e ∧ (ss m).target e = SOME b ∧ is_end (ss n) (2, jk) ∧
  ¬free0 (ptr rs 0 n) ∧ ¬free0 (ptr rs 1 n) ∧
  (∀k. k < 3 ∧ k ≠ 0 ⇒ no_conn_to a (ptr rs k n)) ∧ (∀k. k < 3 ∧ k ≠ 1 ⇒ no_conn_to b (ptr rs k n)) ∧
  no_fd0 (ptr rs 0 n) ∧ no_fd0 (ptr rs 1 n) ∧ relay_ok a b rs n ∧ csend_ok a rs n ⇒
  ∃rqs. EVERY valid_brequest rqs ∧ (sys_chan (ss n) (2, jk)).peer_sent ≼ brequests rqs
Proof
  strip_tac >>
  ‘(ss n).peer (2, jk) = SOME e ∨ (sys_chan (ss n) (2, jk)).peer_sent = []’
    by (mp_tac (Q.INST [‘x’ |-> ‘(2, jk)’] (SPEC_ALL irun_peer_or_empty)) >> simp[]) >>
  pop_assum strip_assume_tac
  >- (‘kinv (ss m) ∧ kinv (ss n)’ by metis_tac[irun_kinv] >>
      ‘is_end (ss m) e’ by metis_tac[moonshotLiveDeliverTheory.kinv_peer_end] >>
      ‘is_end (ss n) e’ by metis_tac[moonshotLiveDeliverTheory.kinv_peer_end] >>
      ‘(ss n).target e = SOME b’
        by (mp_tac (SPEC_ALL irun_target_at) >> simp[]) >>
      mp_tac (Q.INST [‘x’ |-> ‘(2, jk)’] (SPEC_ALL peer_backend)) >> simp[] >> strip_tac >>
      ‘(sys_chan (ss n) (2, jk)).peer_sent ≼ (sys_chan (ss n) e).sent’
        by (irule irun_peer_sent >> simp[] >> TRY (qexistsl_tac [‘ps’, ‘rs’]) >> simp[]) >>
      mp_tac (SPEC_ALL backend_valid) >> simp[] >> strip_tac >>
      qexists_tac ‘rqs’ >> simp[] >>
      irule IS_PREFIX_TRANS >> qexists_tac ‘(sys_chan (ss n) e).sent’ >> gvs[]) >>
  qexists_tac ‘[]’ >> simp[]
QED
