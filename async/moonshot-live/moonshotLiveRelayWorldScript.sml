(*
  G2, world level: KV's claim's premise peer_valid w0 io c (K-asks) from
  the system's fact about end (k, c) at every instant (for KV's ends
  paired with a connect to b: moonshotLiveRelay's kv_peer_valid_sys).

  MAIN: world_peer_valid, for process k of an infinite run calling
    infinitely often, with the world w0 of l0sys_proj_inf (as N2's
    world_drains): every finite prefix of tr is k's calls up to some
    instant t0 (ptr_of_prefix); the world after them is iksim's V; the
    system's state is V after pending arrivals, and arrivals only extend
    what a channel's peer has sent.

  TEMPORARY COPY (remove at merge): peer_valid (honestKvL0LiveStmts,
  spike/kv-live-l0 @ bbf45dfe8).
*)
Theory moonshotLiveRelayWorld
Ancestors
  moonshotLiveRelay moonshotLiveWorldDrains moonshotLiveCopy moonshotLiveProjInf moonshotLiveStmts
  l0sysFair l0sys l0sysProj honestL0World
Libs
  preamble

Definition peer_valid_def:
  peer_valid w0 io c ⇔
    ∀evs w. LPREFIX (fromList evs) io ∧ world_at w0 evs = SOME w ∧ c < LENGTH w.chans ⇒
            ∃rqs. EVERY valid_brequest rqs ∧ (EL c w.chans).peer_sent ≼ brequests rqs
End

(* Arrivals only extend what a channel's peer has sent *)
Theorem deliver_peer_sent:
  c < LENGTH w.chans ⇒
  c < LENGTH (l0_deliver w a).chans ∧
  (EL c w.chans).peer_sent ≼ (EL c (l0_deliver w a).chans).peer_sent
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >>
  rw[upd_lchan_def, EL_LUPDATE, EL_APPEND1, break_lchan_def] >> rw[]
QED

Theorem FOLDL_deliver_peer_sent:
  ∀as w. c < LENGTH w.chans ⇒
         c < LENGTH (FOLDL l0_deliver w as).chans ∧
         (EL c w.chans).peer_sent ≼ (EL c (FOLDL l0_deliver w as).chans).peer_sent
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  drule deliver_peer_sent >> disch_then (qspec_then ‘h’ strip_assume_tac) >>
  first_x_assum drule >> strip_tac >> simp[] >> metis_tac[IS_PREFIX_TRANS]
QED

Theorem world_peer_valid:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ∧
  (∀t. kstep k (ss t) (rs t) (ss (SUC t)) (AS t)) ∧
  (∀t. ∃V. agrees_to l0_oracle w0 (ptr rs k t) V ∧
           ((ss t).alive k ⇒
            V.clock = fclk k ss t ∧
            (EL k (ss t).procs) with env := w0.env = FOLDL l0_deliver V (fseg k ss AS t))) ∧
  (∀t. ∃t'. t ≤ t' ∧ is_kcall k (rs t')) ∧
  (∀t. LPREFIX (fromList (ptr rs k t)) tr) ∧
  (∀n. is_end (ss n) (k, c) ⇒
       ∃rqs. EVERY valid_brequest rqs ∧ (sys_chan (ss n) (k, c)).peer_sent ≼ brequests rqs) ⇒
  peer_valid w0 tr c
Proof
  strip_tac >> rewrite_tac[peer_valid_def] >> rpt gen_tac >> strip_tac >>
  ‘∀t. (ss t).alive k’ by metis_tac[kstep_alive_all] >>
  ‘∃t0. ptr rs k t0 = evs’ by metis_tac[ptr_of_prefix] >>
  qpat_x_assum ‘∀t. ∃V. agrees_to _ _ _ _ ∧ _’ (qspec_then ‘t0’ strip_assume_tac) >>
  ‘world_at w0 (ptr rs k t0) = SOME V’ by metis_tac[agrees_world_at] >>
  ‘V = w’ by gvs[] >> pop_assum SUBST_ALL_TAC >>
  ‘(EL k (ss t0).procs) with env := w0.env = FOLDL l0_deliver w (fseg k ss AS t0)’
    by metis_tac[] >>
  qspecl_then [‘fseg k ss AS t0’, ‘w’] mp_tac FOLDL_deliver_peer_sent >> simp[] >>
  qpat_x_assum ‘_ with env := _ = _’ (SUBST1_TAC o SYM) >> simp[] >> strip_tac >>
  ‘k < LENGTH (ss t0).procs’ by metis_tac[irun_procs_length] >>
  ‘is_end (ss t0) (k, c)’ by simp[is_end_def] >>
  qpat_x_assum ‘∀n. is_end _ _ ⇒ _’ drule >> strip_tac >>
  qexists_tac ‘rqs’ >> simp[] >>
  irule IS_PREFIX_TRANS >> qexists_tac ‘(sys_chan (ss t0) (k, c)).peer_sent’ >>
  simp[sys_chan_def]
QED

(*---------------------------------------------------------------------------*)
(* kv_peer_valid_sys's hypotheses from the proxy's and the client's claims,
   stated on the clauses used, so the statements' parameters (proxy_safe_l0's
   Bnd or kt hw) don't matter here *)

(* relay_ok from proxy_safe_ep's cover and relay clauses (moonshotPairGlue),
   at instant t with tr px t = ptr rs 1 n and rl px the roles at ptr rs 1 n
   (proxy_safe_bridge with ft = ptr rs 1 n, tr px t = ptr rs 1 (MIN t n)) *)
Theorem relay_ok_of_ep:
  (∀c. rl c = SOME (Connected b) ⇒ ∃f. prx f = SOME c ∧ rl f = SOME (Accepted a)) ∧
  (∀f c. prx f = SOME c ⇒ l0_ep_sent c evs ≼ l0_ep_recvd f evs) ∧
  (∀j. rl j = l0_ep_role j (ptr rs 1 n)) ∧ evs = ptr rs 1 n ⇒
  relay_ok a b rs n
Proof
  strip_tac >> rewrite_tac[relay_ok_def] >> rpt strip_tac >>
  ‘rl i = SOME (Connected b)’ by metis_tac[] >>
  first_x_assum drule >> strip_tac >>
  qexists_tac ‘f’ >> conj_tac >- metis_tac[] >>
  first_x_assum drule >> rw[]
QED

(* csend_ok from client_safe_l0's connect clause (moonshotClientL0Stmts) at
   evs = ptr rs 0 n *)
Theorem csend_ok_of_client:
  (∀i. EVERY valid_brequest (rqs i)) ∧
  (∀j p. l0_ep_role j (ptr rs 0 n) = SOME (Connected p) ⇒
         lc j < N ∧ l0_ep_sent j (ptr rs 0 n) ≼ brequests (rqs (lc j))) ⇒
  csend_ok a rs n
Proof
  strip_tac >> rewrite_tac[csend_ok_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexists_tac ‘rqs (lc i)’ >> simp[]
QED
