(*
  Moonshot liveness, N2 (README §4): each process's `drains` premise
  (honestL1BStmts.drains, copied in moonshotLiveCopy) from the system's
  drain of its end (sys_drains).

  For process k of an infinite run, calling infinitely often, with the
  world w0 of l0sys_proj_inf (N1): if the system drains k's end (k, c),
  then in w0, along any trace tr that has every finite prefix of k's calls
  as a prefix (in particular the program's behaviour), channel c drains.
  The argument:
   - every finite prefix of tr is k's calls up to some instant t0
     (ptr_of_prefix); the world after them is iksim's V (agrees_world_at);
   - the world's sent on c is the system's (deliveries keep sent), so if
     the world sends nothing more on c, nor does the system (from t0);
   - then the system drains (k, c): from some n2 on, all it sent is moved
     and acknowledged, so its inflight is 0 (infl_inv);
   - at k's next call t4 ≥ n2 the world's state after the call is the
     call's result on k's system state; it sends nothing on c, so its
     inflight on c is the system's, 0.
*)
Theory moonshotLiveWorldDrains
Ancestors
  moonshotLiveCopy moonshotLiveInfl moonshotLiveProjInf moonshotLiveChain moonshotLiveDrains
  moonshotLiveDeliver moonshotLiveStmts l0sysFair l0sys l0sysProj l0sysStep l0sysMono
  l0sysInvCall l0sysCausal l0sysRun l0sysBridges honestL0World honestL0WorldProps llist
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* The oracle's states are the replayed worlds *)

Theorem agrees_world_at:
  ∀evs w V. agrees_to l0_oracle w evs V ⇒ world_at w evs = SOME V
Proof
  simp[world_at_def, l0_replay_def] >>
  Induct >> simp[agrees_to_def] >> Cases >> rename1 ‘IO_event nm conf bl’ >>
  Cases_on ‘nm’ >> simp[agrees_to_def, l0_oracle_def, ev_lcall_def] >>
  rw[AllCaseEqs()] >> simp[l0_step_def] >> first_x_assum irule >> simp[]
QED

(*---------------------------------------------------------------------------*)
(* Arrivals keep a channel and what it sent; worlds only gain channels *)

Theorem deliver_sent:
  c < LENGTH w.chans ⇒
  c < LENGTH (l0_deliver w a).chans ∧ (EL c (l0_deliver w a).chans).sent = (EL c w.chans).sent
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def] >> every_case_tac >>
  rw[upd_lchan_def, EL_LUPDATE, EL_APPEND1, break_lchan_def] >> rw[]
QED

Theorem FOLDL_deliver_sent:
  ∀as w. c < LENGTH w.chans ⇒
         c < LENGTH (FOLDL l0_deliver w as).chans ∧
         (EL c (FOLDL l0_deliver w as).chans).sent = (EL c w.chans).sent
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  drule deliver_sent >> disch_then (qspec_then ‘h’ strip_assume_tac) >>
  first_x_assum drule >> simp[]
QED

Theorem FOLDL_deliver_len:
  ∀as w. LENGTH w.chans ≤ LENGTH (FOLDL l0_deliver w as).chans
Proof
  Induct >> simp[] >> rpt gen_tac >>
  irule LESS_EQ_TRANS >> qexists_tac ‘LENGTH (l0_deliver w h).chans’ >> simp[] >>
  Cases_on ‘LENGTH w.chans’ >> simp[] >>
  ‘n < LENGTH w.chans’ by simp[] >> drule deliver_sent >>
  disch_then (qspec_then ‘h’ strip_assume_tac) >> simp[]
QED

Theorem tick_chans_len:
  LENGTH w.chans ≤ LENGTH (l0_tick nm w).chans
Proof
  simp[l0_tick_def] >>
  qspecl_then [‘w.env w.clock w.hist nm’, ‘w with clock := w.clock + 1’] mp_tac FOLDL_deliver_len >>
  simp[]
QED

Theorem ticks_chans_len:
  ∀n w. LENGTH w.chans ≤ LENGTH (l0_ticks nm n w).chans
Proof
  Induct >> rw[l0_ticks_def] >>
  irule LESS_EQ_TRANS >> qexists_tac ‘LENGTH (l0_tick nm w).chans’ >> simp[tick_chans_len]
QED

Theorem l0_call_chans_len:
  l0_call nm conf bs w = SOME (FFIreturn out w1) ⇒ LENGTH w.chans ≤ LENGTH w1.chans
Proof
  Cases_on ‘nm = «sys_poll»’
  >- (rw[l0_call_def] >> gvs[AllCaseEqs(), ticks_chans_len]) >>
  strip_tac >> ‘unblock nm conf = conf’ by simp[unblock_other] >>
  ‘wmono w w1’ by (irule wmono_call >> metis_tac[]) >> fs[wmono_def]
QED

Theorem l0_ffi_fn_chans_len:
  l0_ffi_fn n conf bs w = SOME (FFIreturn out w') ⇒ LENGTH w.chans ≤ LENGTH w'.chans
Proof
  rw[l0_ffi_fn_def, AllCaseEqs()] >> drule l0_call_chans_len >>
  ‘LENGTH w.chans ≤ LENGTH (l0_tick n w).chans’ by simp[tick_chans_len] >> simp[]
QED

Theorem replay_chans_len:
  ∀h w w'. FOLDL l0_step (SOME w) h = SOME w' ⇒ LENGTH w.chans ≤ LENGTH w'.chans
Proof
  ‘∀h. FOLDL l0_step NONE h = NONE’ by (Induct >> simp[l0_step_def]) >>
  Induct >> simp[] >> rpt gen_tac >> PairCases_on ‘h'’ >> simp[l0_step_def] >>
  every_case_tac >> simp[] >> strip_tac >> first_x_assum drule >>
  drule l0_ffi_fn_chans_len >> simp[]
QED

Theorem world_at_chans_len:
  world_at w0 evs = SOME w ∧ world_at w0 (evs ++ evs') = SOME w' ⇒
  LENGTH w.chans ≤ LENGTH w'.chans
Proof
  rw[world_at_def, l0_replay_def, FOLDL_APPEND] >> gvs[] >> metis_tac[replay_chans_len]
QED

(*---------------------------------------------------------------------------*)
(* A process calling infinitely often is alive throughout *)

Theorem kstep_alive_all:
  (∀t. kstep k (ss t) (rs t) (ss (SUC t)) (AS t)) ∧ (∀t. ∃t'. t ≤ t' ∧ is_kcall k (rs t')) ⇒
  ∀t. (ss t).alive k
Proof
  rpt strip_tac >>
  ‘∀d t. (ss (t + d)).alive k ⇒ (ss t).alive k’ by
    (Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
     qpat_x_assum ‘∀t. kstep _ _ _ _ _’ (qspec_then ‘t + d’ mp_tac) >>
     rw[kstep_def, ADD_CLAUSES] >> fs[ADD_CLAUSES]) >>
  qpat_x_assum ‘∀t. ∃t'. _’ (qspec_then ‘t’ strip_assume_tac) >>
  ‘(ss t').alive k’ by
    (qpat_x_assum ‘∀t. kstep _ _ _ _ _’ (qspec_then ‘t'’ mp_tac) >>
     fs[is_kcall_def] >> rw[kstep_def]) >>
  first_x_assum (qspecl_then [‘t' − t’, ‘t’] mp_tac) >> simp[]
QED

(*---------------------------------------------------------------------------*)
(* k's calls so far *)

Theorem ptr_SUC:
  ptr rs k (SUC t) =
  ptr rs k t ++
  (case rs t of
   | Call k' nm conf bts out => if k' = k then [IO_event (ExtCall nm) conf (ZIP (bts, out))] else []
   | _ => [])
Proof
  simp[ptr_def, GENLIST, SNOC_APPEND, proc_events_SNOC]
QED

Theorem ptr_mono:
  t ≤ t' ⇒ ∃evs'. ptr rs k t' = ptr rs k t ++ evs'
Proof
  ‘∀d. ∃evs'. ptr rs k (t + d) = ptr rs k t ++ evs'’ suffices_by
    (rpt strip_tac >> first_x_assum (qspec_then ‘t' − t’ mp_tac) >> simp[]) >>
  Induct >> simp[] >> fs[ADD_CLAUSES, ptr_SUC] >> metis_tac[APPEND_ASSOC]
QED

Theorem ptr_len_SUC:
  LENGTH (ptr rs k (SUC t)) = LENGTH (ptr rs k t) + if is_kcall k (rs t) then 1 else 0
Proof
  simp[ptr_SUC, is_kcall_def] >> Cases_on ‘rs t’ >> simp[] >> rw[]
QED

Theorem ptr_len_hits:
  (∀t. ∃t'. t ≤ t' ∧ is_kcall k (rs t')) ⇒ ∀m. ∃t. LENGTH (ptr rs k t) = m
Proof
  strip_tac >>
  ‘∀t t'. t ≤ t' ⇒ LENGTH (ptr rs k t) ≤ LENGTH (ptr rs k t')’ by
    (rpt strip_tac >> drule ptr_mono >> disch_then (qspecl_then [‘rs’, ‘k’] strip_assume_tac) >>
     simp[]) >>
  ‘∀m. ∃t. m ≤ LENGTH (ptr rs k t)’ by
    (Induct >> simp[] >> pop_assum strip_assume_tac >>
     qpat_x_assum ‘∀t. ∃t'. _’ (qspec_then ‘t’ strip_assume_tac) >>
     qexists_tac ‘SUC t'’ >> simp[ptr_len_SUC] >>
     ‘LENGTH (ptr rs k t) ≤ LENGTH (ptr rs k t')’ by simp[] >> simp[]) >>
  gen_tac >> first_x_assum (qspec_then ‘m’ assume_tac) >>
  qspec_then ‘λt. m ≤ LENGTH (ptr rs k t)’ mp_tac WOP >> simp[] >>
  strip_tac >>
  Cases_on ‘n’
  >- (‘ptr rs k 0 = []’ by simp[ptr_def, proc_events_def] >> fs[] >> qexists_tac ‘0’ >> simp[]) >>
  ‘¬(m ≤ LENGTH (ptr rs k n'))’ by simp[] >>
  qexists_tac ‘SUC n'’ >> fs[ptr_len_SUC] >> rw[] >> fs[]
QED

Theorem prefix_unique:
  LPREFIX (fromList a) l ∧ LPREFIX (fromList b) l ∧ LENGTH a = LENGTH b ⇒ a = b
Proof
  rw[LPREFIX_fromList] >> every_case_tac >> fs[] >- rfs[] >>
  ‘a ≼ b ∨ b ≼ a’ by metis_tac[prefixes_is_prefix_total] >>
  metis_tac[IS_PREFIX_LENGTH_ANTI]
QED

Theorem ptr_of_prefix:
  (∀t. ∃t'. t ≤ t' ∧ is_kcall k (rs t')) ∧ (∀t. LPREFIX (fromList (ptr rs k t)) tr) ∧
  LPREFIX (fromList evs) tr ⇒
  ∃t. ptr rs k t = evs
Proof
  strip_tac >> drule ptr_len_hits >> disch_then (qspec_then ‘LENGTH evs’ strip_assume_tac) >>
  qexists_tac ‘t’ >> irule prefix_unique >> simp[] >> qexists_tac ‘tr’ >> simp[]
QED

(*---------------------------------------------------------------------------*)
(* The system's end and the world's channel *)

Theorem sys_world_sent:
  (EL k (ss t).procs) with env := E = FOLDL l0_deliver V as ∧ c < LENGTH V.chans ∧
  k < LENGTH (ss t).procs ⇒
  is_end (ss t) (k, c) ∧ (sys_chan (ss t) (k, c)).sent = (EL c V.chans).sent
Proof
  strip_tac >>
  ‘(EL k (ss t).procs).chans = (FOLDL l0_deliver V as).chans’ by
    (qpat_x_assum ‘_ with env := _ = _’ (mp_tac o Q.AP_TERM ‘λw. w.chans’) >> simp[]) >>
  drule (Q.SPEC ‘as’ FOLDL_deliver_sent) >> strip_tac >>
  simp[is_end_def, sys_chan_def]
QED

(* A drained end has nothing in flight *)
Theorem infl_zero:
  infl_inv s ∧ kinv s ∧ is_end s e ∧ s.moved e = LENGTH (sys_chan s e).sent ∧
  s.acked e = LENGTH (sys_chan s e).sent ⇒
  (sys_chan s e).inflight = 0
Proof
  strip_tac >>
  ‘(sys_chan s e).inflight ≤ LENGTH (sys_chan s e).sent ∧
   (s.peer e ≠ NONE ⇒ (sys_chan s e).inflight + s.acked e = LENGTH (sys_chan s e).sent)’ by
    fs[infl_inv_def] >>
  Cases_on ‘s.peer e’ >> fs[] >>
  ‘s.moved e = 0’ by
    (qpat_x_assum ‘kinv s’ mp_tac >> rewrite_tac[kinv_def] >> strip_tac >>
     first_x_assum (qspec_then ‘e’ mp_tac) >> simp[]) >>
  fs[] >> qpat_x_assum ‘_.inflight ≤ _’ mp_tac >>
  qpat_x_assum ‘_.sent = []’ (fn th => rewrite_tac[th]) >> simp[]
QED

(*---------------------------------------------------------------------------*)
(* N2 *)

Theorem world_drains:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ∧
  (∀t. kstep k (ss t) (rs t) (ss (SUC t)) (AS t)) ∧
  w0 = (EL k (ss 0).procs) with env := (λn h nm. fenv k ss AS n) ∧
  (∀t. ∃V. agrees_to l0_oracle w0 (ptr rs k t) V ∧
           ((ss t).alive k ⇒
            V.clock = fclk k ss t ∧
            (EL k (ss t).procs) with env := w0.env = FOLDL l0_deliver V (fseg k ss AS t))) ∧
  (∀t. ∃t'. t ≤ t' ∧ is_kcall k (rs t')) ∧
  (∀t. LPREFIX (fromList (ptr rs k t)) tr) ∧
  sys_drains ss (k, c) ⇒
  drains w0 tr c
Proof
  strip_tac >> rewrite_tac[drains_def] >> rpt gen_tac >> strip_tac >>
  ‘∀t. (ss t).alive k’ by metis_tac[kstep_alive_all] >>
  ‘∀t. k < LENGTH (ss t).procs’ by metis_tac[irun_procs_length] >>
  ‘∀t. l0_rely (EL k (ss t).procs)’ by
    (gen_tac >> drule irun_sinv >> disch_then (qspec_then ‘t’ strip_assume_tac) >>
     fs[sinv_def, pk_def, LET_THM]) >>
  ‘∃t0. ptr rs k t0 = evs’ by metis_tac[ptr_of_prefix] >>
  (* the world at each instant *)
  ‘∀t. ∃V. agrees_to l0_oracle w0 (ptr rs k t) V ∧ world_at w0 (ptr rs k t) = SOME V ∧
           V.clock = fclk k ss t ∧
           (EL k (ss t).procs) with env := w0.env = FOLDL l0_deliver V (fseg k ss AS t)’ by
    (gen_tac >> qpat_x_assum ‘∀t. ∃V. agrees_to _ _ _ _ ∧ _’ (qspec_then ‘t’ strip_assume_tac) >>
     qexists_tac ‘V’ >> simp[] >> metis_tac[agrees_world_at]) >>
  (* from t0 on, the system's end sends what the world's channel sent *)
  ‘∀n. t0 ≤ n ⇒ is_end (ss n) (k, c) ∧ (sys_chan (ss n) (k, c)).sent = (EL c w.chans).sent’ by
    (rpt gen_tac >> strip_tac >>
     drule ptr_mono >> disch_then (qspecl_then [‘rs’, ‘k’] strip_assume_tac) >>
     qpat_x_assum ‘∀t. ∃V. agrees_to _ _ _ _ ∧ world_at _ _ = _ ∧ _’ (qspec_then ‘n’ strip_assume_tac) >>
     ‘LENGTH w.chans ≤ LENGTH V.chans’ by metis_tac[world_at_chans_len] >>
     ‘(EL c V.chans).sent = (EL c w.chans).sent’ by
       (qpat_x_assum ‘∀evs' w'. _ ⇒ _’ irule >> qexists_tac ‘evs'’ >> gvs[] >>
        qpat_x_assum ‘∀t. LPREFIX _ tr’ (qspec_then ‘n’ mp_tac) >>
        qpat_x_assum ‘ptr rs k n = _’ (fn th => rewrite_tac[th])) >>
     qspecl_then [‘k’, ‘ss’, ‘n’, ‘w0.env’, ‘V’, ‘fseg k ss AS n’, ‘c’] mp_tac
       (Q.GENL [‘k’, ‘ss’, ‘t’, ‘E’, ‘V’, ‘as’, ‘c’] sys_world_sent) >>
     simp[]) >>
  (* so the system drains it from t0 *)
  ‘∃n2. t0 ≤ n2 ∧ ∀n. n2 ≤ n ⇒
          (ss n).moved (k, c) = LENGTH (sys_chan (ss t0) (k, c)).sent ∧
          (ss n).acked (k, c) = LENGTH (sys_chan (ss t0) (k, c)).sent’ by
    (qpat_x_assum ‘sys_drains _ _’ mp_tac >> rewrite_tac[sys_drains_def] >>
     disch_then irule >> rpt strip_tac >>
     ‘t0 ≤ t0’ by simp[] >> metis_tac[]) >>
  (* k's next call t4 *)
  qpat_x_assum ‘∀t. ∃t'. t ≤ t' ∧ _’ (qspec_then ‘n2’ strip_assume_tac) >>
  rename1 ‘is_kcall k (rs t4)’ >>
  ‘∃nm conf bts out. rs t4 = Call k nm conf bts out’ by fs[is_kcall_def] >>
  ‘is_end (ss t4) (k, c) ∧ (sys_chan (ss t4) (k, c)).sent = (EL c w.chans).sent’ by simp[] >>
  ‘(sys_chan (ss (SUC t4)) (k, c)).sent = (EL c w.chans).sent’ by simp[] >>
  ‘(sys_chan (ss t4) (k, c)).inflight = 0’ by
    (irule infl_zero >> rpt conj_tac
     >- metis_tac[irun_infl_inv]
     >- metis_tac[irun_kinv]
     >- simp[]
     >> ‘(sys_chan (ss t4) (k, c)).sent = (sys_chan (ss t0) (k, c)).sent’ by simp[] >>
     simp[]) >>
  (* the call at t4, in the system and in the world *)
  qabbrev_tac ‘wk = EL k (ss t4).procs’ >>
  ‘poll_may_return nm conf bts wk ∧
   ∃w1. l0_call nm (unblock nm conf) bts wk = SOME (FFIreturn out w1) ∧
        EL k (ss (SUC t4)).procs =
        FOLDL l0_deliver (w1 with <| clock := wk.clock + 1; hist := wk.hist ++ [(nm, conf, bts)] |>)
          (AS t4)’ by
    (qpat_x_assum ‘∀t. kstep _ _ _ _ _’ (qspec_then ‘t4’ mp_tac) >>
     simp[kstep_def, Abbr ‘wk’] >> metis_tac[]) >>
  qpat_x_assum ‘∀t. ∃V. agrees_to _ _ _ _ ∧ world_at _ _ = _ ∧ _’ (qspec_then ‘t4’ strip_assume_tac) >>
  ‘V.env = w0.env’ by
    (qpat_x_assum ‘_ with env := _ = FOLDL _ _ _’ (mp_tac o Q.AP_TERM ‘λw. w.env’) >> simp[]) >>
  ‘fenv k ss AS (fclk k ss t4) = fseg k ss AS t4’ by (irule fenv_call >> qexists_tac ‘rs’ >> simp[]) >>
  ‘l0_oracle (ExtCall nm) V conf bts =
   Oracle_return ((w1 with <| clock := wk.clock + 1; hist := wk.hist ++ [(nm, conf, bts)] |>)
                    with env := V.env) out’ by
    (irule l0_oracle_call >> simp[] >>
     ‘fclk k ss t4 = wk.clock’ by simp[fclk_def, Abbr ‘wk’] >> simp[] >>
     qexists_tac ‘fenv k ss AS’ >> simp[] >> rfs[Abbr ‘wk’] >>
     qpat_x_assum ‘fenv _ _ _ _ = _’ mp_tac >> simp[fclk_def]) >>
  qabbrev_tac ‘V' = (w1 with <| clock := wk.clock + 1; hist := wk.hist ++ [(nm, conf, bts)] |>)
                      with env := V.env’ >>
  ‘LENGTH out = LENGTH bts’ by (irule l0_call_length >> simp[Abbr ‘wk’] >> metis_tac[]) >>
  ‘world_at w0 (ptr rs k (SUC t4)) = SOME V'’ by
    (irule agrees_world_at >> simp[ptr_SUC, agrees_to_SNOC] >> qexists_tac ‘V’ >> simp[MAP_ZIP] >>
     qpat_x_assum ‘agrees_to _ _ (ptr rs k t4) V’ mp_tac >>
     qpat_x_assum ‘w0 = _’ (fn th => rewrite_tac[th])) >>
  (* the call sends nothing on c: its inflight there is the system's, 0 *)
  ‘t0 ≤ SUC t4’ by (qpat_x_assum ‘t0 ≤ n2’ mp_tac >> qpat_x_assum ‘n2 ≤ t4’ mp_tac >> simp[]) >>
  ‘c < LENGTH wk.chans’ by fs[is_end_def, Abbr ‘wk’] >>
  ‘ikeep (EL c wk.chans) (EL c w1.chans) ∧ c < LENGTH w1.chans’ by
    (drule wikeep_call >> rw[wikeep_def]) >>
  ‘(EL c w1.chans).sent = (EL c w.chans).sent’ by
    (qspecl_then [‘AS t4’, ‘w1 with <| clock := wk.clock + 1; hist := wk.hist ++ [(nm, conf, bts)] |>’]
       mp_tac (Q.GEN ‘c’ FOLDL_deliver_sent |> Q.SPEC ‘c’) >>
     simp[] >> strip_tac >>
     qpat_x_assum ‘(sys_chan (ss (SUC t4)) (k,c)).sent = _’ (SUBST1_TAC o SYM) >>
     rewrite_tac[sys_chan_def] >>
     qpat_x_assum ‘EL k (ss (SUC t4)).procs = _’ SUBST1_TAC >>
     qpat_x_assum ‘(EL c (FOLDL _ _ _).chans).sent = _’ (ACCEPT_TAC o SYM)) >>
  ‘(EL c wk.chans).sent = (EL c w.chans).sent ∧ (EL c wk.chans).inflight = 0’ by
    fs[sys_chan_def, Abbr ‘wk’] >>
  ‘(EL c w1.chans).inflight = 0’ by fs[ikeep_alt] >>
  (* the prefix *)
  qpat_x_assum ‘t0 ≤ SUC t4’ assume_tac >> drule ptr_mono >>
  disch_then (qspecl_then [‘rs’, ‘k’] strip_assume_tac) >>
  qexistsl_tac [‘evs'’, ‘V'’] >>
  qpat_x_assum ‘ptr rs k t0 = evs’ (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum ‘ptr rs k (SUC t4) = _’ (SUBST1_TAC o SYM) >>
  rpt conj_tac
  >- (qpat_x_assum ‘∀t. LPREFIX _ tr’ (qspec_then ‘SUC t4’ ACCEPT_TAC))
  >- (qpat_x_assum ‘world_at w0 (ptr rs k (SUC t4)) = _’ ACCEPT_TAC) >>
  qpat_x_assum ‘c < LENGTH w1.chans’ mp_tac >>
  qpat_x_assum ‘(EL c w1.chans).inflight = 0’ mp_tac >>
  simp[Abbr ‘V'’]
QED

(* N2, with N1's world: for process k calling infinitely often *)
Theorem l0sys_proj_drains:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ∧ (∀t. ∃t'. t ≤ t' ∧ is_kcall k (rs t')) ⇒
  ∃w0. l0_rely w0 ∧ l0_fresh w0 ∧ fds_lt w0 ∧
       (∀b. semantics_prog (init_state (l0_ffi w0)) init_env (EL k ps) b ∧ b ≠ Fail ⇒
            ∀t. LPREFIX (fromList (ptr rs k t)) (beh_io b)) ∧
       ∀tr c. (∀t. LPREFIX (fromList (ptr rs k t)) tr) ∧ sys_drains ss (k, c) ⇒ drains w0 tr c
Proof
  strip_tac >> drule_all l0sys_proj_inf >> strip_tac >> fs[LET_THM] >>
  qexists_tac ‘(EL k (ss 0).procs) with env := (λn h nm. fenv k ss AS n)’ >> simp[] >>
  rpt strip_tac >> irule world_drains >> simp[] >> metis_tac[]
QED
