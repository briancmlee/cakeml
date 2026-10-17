(*
  Moonshot step 12 glue, G2 and the B2 wiring (design/45 §4.1): the
  composition moonshot_view_safe instantiated at an l0sys run.

  G2, one io per process.
   - Each per-process claim gives SOME behaviour.  B1 (l0sys_proj) puts the
     process's whole trace in the run below EVERY behaviour that is not
     Fail.  So it is below the claim's behaviour, and every instant is
     below that one io too (g2_one_io).
   - A step of the system adds at most one event to a process's trace.  So
     every prefix of a process's whole trace is its trace at some instant
     (proc_events_instant).

  The world class of the claims is B1's (l0_rely ∧ l0_fresh ∧ fds_lt), as
  the user's stdio decision (D33 (ii)) restates the per-process claims.

  B2 → b2_conn (b2_wire): l0sys_causal's three facts are b2_conn's first
  three.  The fourth ("an episode conn leaves unpaired reads nothing") is
  the hypothesis b2_quiet.  It is what `isolated` must give, together with
  B2's own pairing: a B2 variant, m4-server's note (3).

  moonshot_sys_safe: in an l0sys run of the client cl, the proxy px and KV
  kv, the client's whole trace is linearizable against KV
  (kv_client_safe), from:
   - the three processes' claims, each in its safe form;
   - B2 with b2_quiet;
   - the ports (topology);
   - W2 for the proxy.
*)
Theory moonshotSysGlue
Ancestors
  moonshotSafeGlue moonshotPairGlue moonshotProxyGlue moonshotWorldFacts l0sysBridges
  l0sysRun l0sys
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* G2 *)

Theorem proc_events_mono:
  t ≤ t' ⇒ proc_events k (TAKE t rs) ≼ proc_events k (TAKE t' rs)
Proof
  strip_tac >>
  ‘TAKE t rs = TAKE t (TAKE t' rs)’ by simp[TAKE_TAKE_T] >>
  pop_assum SUBST1_TAC >> simp[proc_events_TAKE]
QED

(* A step adds at most one event to k's trace *)
Theorem proc_events_one:
  proc_events k [r] = [] ∨ ∃e. proc_events k [r] = [e]
Proof
  Cases_on ‘r’ >> rw[proc_events_def]
QED

Theorem prefix_SNOC_cases:
  evs ≼ a ++ [e] ⇒ evs ≼ a ∨ evs = a ++ [e]
Proof
  rw[IS_PREFIX_APPEND] >> Cases_on ‘l’ using SNOC_CASES >> gvs[SNOC_APPEND] >>
  metis_tac[APPEND_ASSOC, APPEND_11]
QED

Theorem proc_events_instant:
  ∀rs evs. evs ≼ proc_events k rs ⇒ ∃t. proc_events k (TAKE t rs) = evs
Proof
  ho_match_mp_tac SNOC_INDUCT >> rw[]
  >- gvs[proc_events_def] >>
  gvs[SNOC_APPEND, proc_events_APPEND] >>
  Cases_on ‘evs ≼ proc_events k rs’
  >- (first_x_assum drule >> strip_tac >>
      qexists_tac ‘MIN t (LENGTH rs)’ >>
      ‘TAKE (MIN t (LENGTH rs)) (rs ++ [x]) = TAKE t rs’
        by (rw[MIN_DEF, TAKE_APPEND1] >> simp[TAKE_LENGTH_TOO_LONG]) >>
      simp[]) >>
  qexists_tac ‘SUC (LENGTH rs)’ >>
  ‘TAKE (SUC (LENGTH rs)) (rs ++ [x]) = rs ++ [x]’ by simp[TAKE_LENGTH_TOO_LONG] >>
  simp[proc_events_APPEND] >>
  qspecl_then [‘k’, ‘x’] strip_assume_tac (Q.GENL [‘k’, ‘r’] proc_events_one) >>
  gvs[] >> drule prefix_SNOC_cases >> simp[]
QED

(* One io per process: the claim's behaviour is above the whole trace *)
Theorem g2_one_io:
  l0sys_run ps rs ∧ k < LENGTH ps ∧
  (∀w0. l0_rely w0 ∧ l0_fresh w0 ∧ fds_lt w0 ⇒
        ∃b. semantics_prog (init_state (l0_ffi w0)) init_env (EL k ps) b ∧ b ≠ Fail ∧ Q b) ⇒
  ∃b. Q b ∧ LPREFIX (fromList (proc_events k rs)) (beh_io b)
Proof
  rpt strip_tac >> drule_all l0sys_proj >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* B2 → b2_conn *)

Definition sys_rl_def:
  sys_rl rs k j = l0_ep_role j (proc_events k rs)
End

Definition sys_tr_def:
  sys_tr rs k t = proc_events k (TAKE t rs)
End

(* What isolation must add to B2: an episode conn leaves unpaired reads
   nothing, at every instant *)
Definition b2_quiet_def:
  b2_quiet rs cn ⇔
    ∀k j t. cn (k, j) = NONE ⇒ l0_ep_recvd j (proc_events k (TAKE t rs)) = []
End

Theorem b2_wire:
  (∀e e'. cn e = SOME e' ⇔ cn e' = SOME e) ∧
  (∀k j k' j'. cn (k, j) = SOME (k', j') ⇒
     (∃p. l0_ep_role j (proc_events k rs) = SOME (Connected p) ∧
          l0_ep_role j' (proc_events k' rs) = SOME (Accepted p) ∨
          l0_ep_role j (proc_events k rs) = SOME (Accepted p) ∧
          l0_ep_role j' (proc_events k' rs) = SOME (Connected p)) ∧
     ∀t. l0_ep_recvd j' (proc_events k' (TAKE t rs)) ≼ l0_ep_sent j (proc_events k (TAKE t rs))) ∧
  b2_quiet rs cn ⇒
  b2_conn cn (sys_rl rs) (sys_tr rs)
Proof
  rw[b2_conn_def, sys_rl_def, sys_tr_def, b2_quiet_def] >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* The system *)

Theorem moonshot_sys_safe:
  l0sys_run ps rs ∧ cl < LENGTH ps ∧ px < LENGTH ps ∧ kv < LENGTH ps ∧
  (* B2, with isolation's b2_quiet *)
  (∀e e'. cn e = SOME e' ⇔ cn e' = SOME e) ∧
  (∀k j k' j'. cn (k, j) = SOME (k', j') ⇒
     (∃p. l0_ep_role j (proc_events k rs) = SOME (Connected p) ∧
          l0_ep_role j' (proc_events k' rs) = SOME (Accepted p) ∨
          l0_ep_role j (proc_events k rs) = SOME (Accepted p) ∧
          l0_ep_role j' (proc_events k' rs) = SOME (Connected p)) ∧
     ∀t. l0_ep_recvd j' (proc_events k' (TAKE t rs)) ≼ l0_ep_sent j (proc_events k (TAKE t rs))) ∧
  b2_quiet rs cn ∧
  (* the ports *)
  topology (sys_rl rs) cl px kv pa pb ∧ pa < 65536 ∧ pb < 65536 ∧
  (* the proxy's claim, safe form, and W2 *)
  (∀w0. l0_rely w0 ∧ l0_fresh w0 ∧ fds_lt w0 ⇒
        ∃b. semantics_prog (init_state (l0_ffi w0)) init_env (EL px ps) b ∧ b ≠ Fail ∧
            ∃pr. proxy_safe_l0 Bnd pa pb pr (beh_io b)) ∧
  EVERY (λev. ∀r. ev_new ev ≠ SOME (0w, r)) (proc_events px rs) ∧
  (* KV's claim, safe form *)
  (∀w0. l0_rely w0 ∧ l0_fresh w0 ∧ fds_lt w0 ⇒
        ∃b. semantics_prog (init_state (l0_ffi w0)) init_env (EL kv ps) b ∧ b ≠ Fail ∧
            kv_safe_g l0_ep_recvd l0_ep_sent (beh_io b)) ⇒
  kv_client_safe l0_ep_sent l0_ep_recvd (fromList (proc_events cl rs))
Proof
  strip_tac >>
  ‘b2_conn cn (sys_rl rs) (sys_tr rs)’
    by (irule b2_wire >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  (* the proxy: B1's world for px, and its claim's behaviour there *)
  qspecl_then [‘ps’, ‘rs’, ‘px’] mp_tac (Q.GENL [‘ps’, ‘rs’, ‘k’] l0sys_proj) >>
  simp[] >> strip_tac >> rename1 ‘l0_fresh wp’ >>
  qpat_x_assum ‘∀w0. _ ⇒ ∃b. semantics_prog _ _ (EL px ps) _ ∧ _’
    (qspec_then ‘wp’ mp_tac) >> simp[] >> strip_tac >>
  rename1 ‘proxy_safe_l0 Bnd pa pb pr (beh_io bp)’ >>
  ‘LPREFIX (fromList (proc_events px rs)) (beh_io bp)’ by (first_x_assum irule >> simp[]) >>
  ‘ep_ok (proc_events px rs)’
    by (qpat_x_assum ‘l0sys_run _ _’ (strip_assume_tac o REWRITE_RULE [l0sys_run_def]) >>
        irule l0sys_ep_ok >> simp[] >> metis_tac[]) >>
  (* KV *)
  qspecl_then [‘ps’, ‘rs’, ‘kv’] mp_tac (Q.GENL [‘ps’, ‘rs’, ‘k’] l0sys_proj) >>
  simp[] >> strip_tac >> rename1 ‘l0_fresh wk’ >>
  qpat_x_assum ‘∀w0. _ ⇒ ∃b. semantics_prog _ _ (EL kv ps) _ ∧ _’
    (qspec_then ‘wk’ mp_tac) >> simp[] >> strip_tac >>
  rename1 ‘kv_safe_g _ _ (beh_io bk)’ >>
  ‘LPREFIX (fromList (proc_events kv rs)) (beh_io bk)’ by (first_x_assum irule >> simp[]) >>
  irule moonshot_view_safe >>
  qexistsl_tac [‘Bnd’, ‘cl’, ‘cn’, ‘proc_events px rs’, ‘beh_io bk’, ‘beh_io bp’, ‘kv’,
                ‘pa’, ‘pb’, ‘pr’, ‘px’, ‘sys_rl rs’, ‘sys_tr rs’] >>
  simp[sys_tr_def, sys_rl_def, proc_events_mono, proc_events_TAKE] >> rpt conj_tac
  >- (rpt strip_tac >> irule proc_events_instant >> gvs[LPREFIX_fromList, from_toList])
  >- (gen_tac >> irule LPREFIX_TRANS >> qexists_tac ‘fromList (proc_events kv rs)’ >>
      simp[LPREFIX_fromList, from_toList, proc_events_TAKE]) >>
  fs[sys_rl_def, sys_tr_def, ETA_THM]
QED
