(*
  Moonshot liveness, N1 (README §4): B1 for an INFINITE l0sys run.

  m4-server's B1 (l0sysBridges.l0sys_proj) gives each process of a finite
  run an L0 world answering its calls as recorded; the world's environment
  is built from the run's arrivals up to the run's length.  For an infinite
  run there is no last step, so the environment at clock n collects the
  arrivals of every step after which the process's clock is n (fenv; the
  set is finite once the process calls again, and only the clocks of calls
  are ever used).  With one world for the whole run:
   - every finite prefix of the process's calls is a prefix of the
     program's behaviour in that world (l0sys_proj_inf);
   - at every instant at which the process is alive, its system state is
     the world's state after its calls so far, plus the arrivals since its
     last call (iksim): the bridge N2 uses to read `drains` off the system.
  The proofs follow l0sysProj's ksim, kenv_call and kseg_call/other, over a
  run given as functions instead of lists.
*)
Theory moonshotLiveProjInf
Ancestors
  moonshotLiveStmts moonshotLiveDrains l0sysFair honestL0Rely itree_semantics itree_semanticsProps
  itree_semanticsEquiv l0sys l0sysProj l0sysReplay l0sysBridges l0sysStep l0sysRun
  l0sysInvCall honestL0World honestL0WorldProps semantics alt_semantics
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* Process k's clock along an infinite run *)

Definition fclk_def:
  fclk k (ss : num -> sysstate) t = (EL k (ss t).procs).clock
End

(* the arrivals since k's last call, at t *)
Definition fseg_def:
  fseg k ss (AS : num -> l0_arrival list) t =
    FLAT (MAP AS (FILTER (λu. fclk k ss (u + 1) = fclk k ss t) (COUNT_LIST t)))
End

(* the environment at clock n: the arrivals of the steps after which k's
   clock is n (before k's clock passes n) *)
Definition fenv_def:
  fenv k ss (AS : num -> l0_arrival list) n =
    if ∃u. n < fclk k ss u then
      FLAT (MAP AS (FILTER (λu. fclk k ss (u + 1) = n)
                     (COUNT_LIST (LEAST u. n < fclk k ss u))))
    else []
End

Theorem fclk_step:
  (∀t. kstep k (ss t) (rs t) (ss (SUC t)) (AS t)) ⇒
  ∀t. fclk k ss (t + 1) = fclk k ss t + if is_kcall k (rs t) then 1 else 0
Proof
  rw[fclk_def, GSYM ADD1] >> first_x_assum (qspec_then ‘t’ assume_tac) >>
  drule kstep_clock >> simp[]
QED

Theorem fclk_mono:
  (∀t. kstep k (ss t) (rs t) (ss (SUC t)) (AS t)) ⇒
  ∀u v. u ≤ v ⇒ fclk k ss u ≤ fclk k ss v
Proof
  strip_tac >> drule fclk_step >> strip_tac >>
  ‘∀d u. fclk k ss u ≤ fclk k ss (u + d)’ suffices_by
    (rpt strip_tac >> first_x_assum (qspecl_then [‘v - u’, ‘u’] mp_tac) >> simp[]) >>
  Induct >> simp[] >> gen_tac >>
  first_x_assum (qspec_then ‘u’ assume_tac) >>
  ‘fclk k ss (u + SUC d) = fclk k ss (u + d) + if is_kcall k (rs (u + d)) then 1 else 0’ by
    (‘u + SUC d = (u + d) + 1’ by simp[] >> pop_assum SUBST1_TAC >>
     qpat_x_assum ‘∀t. fclk _ _ (t + 1) = _’ (qspec_then ‘u + d’ ACCEPT_TAC)) >>
  pop_assum SUBST1_TAC >>
  irule LESS_EQ_TRANS >> qexists_tac ‘fclk k ss (u + d)’ >> conj_tac
  >- first_assum ACCEPT_TAC >> simp[]
QED

Theorem fenv_call:
  (∀t. kstep k (ss t) (rs t) (ss (SUC t)) (AS t)) ∧ is_kcall k (rs t) ⇒
  fenv k ss AS (fclk k ss t) = fseg k ss AS t
Proof
  strip_tac >> drule fclk_mono >> strip_tac >> drule fclk_step >> strip_tac >>
  ‘fclk k ss (t + 1) = fclk k ss t + 1’ by (first_x_assum (qspec_then ‘t’ mp_tac) >> simp[]) >>
  ‘(LEAST u. fclk k ss t < fclk k ss u) = t + 1’ by
    (numLib.LEAST_ELIM_TAC >> conj_tac >- (qexists_tac ‘t + 1’ >> simp[]) >>
     rw[] >> CCONTR_TAC >>
     Cases_on ‘n < t + 1’
     >- (‘fclk k ss n ≤ fclk k ss t’ by (first_x_assum irule >> simp[]) >> fs[]) >>
     ‘t + 1 < n’ by simp[] >> res_tac >> fs[]) >>
  simp[fenv_def] >> IF_CASES_TAC >- simp[fseg_def, GSYM ADD1, COUNT_LIST_SNOC, FILTER_APPEND,
                                        SNOC_APPEND] >>
  fs[] >> first_x_assum (qspec_then ‘t + 1’ mp_tac) >> simp[]
QED

Theorem fseg_call:
  (∀t. kstep k (ss t) (rs t) (ss (SUC t)) (AS t)) ∧ is_kcall k (rs t) ⇒
  fseg k ss AS (t + 1) = AS t
Proof
  strip_tac >> drule fclk_mono >> strip_tac >> drule fclk_step >> strip_tac >>
  ‘fclk k ss (t + 1) = fclk k ss t + 1’ by (first_x_assum (qspec_then ‘t’ mp_tac) >> simp[]) >>
  qpat_x_assum ‘∀t. fclk _ _ (t + 1) = _’ kall_tac >>
  simp[fseg_def, GSYM ADD1, COUNT_LIST_SNOC, FILTER_APPEND, SNOC_APPEND] >> simp[ADD1] >>
  ‘FILTER (λu. fclk k ss (u + 1) = fclk k ss t + 1) (COUNT_LIST t) = []’ suffices_by simp[] >>
  simp[FILTER_EQ_NIL, EVERY_MEM, MEM_COUNT_LIST] >> rpt strip_tac >>
  rename1 ‘u < t’ >>
  ‘fclk k ss (u + 1) ≤ fclk k ss t’ by (qpat_x_assum ‘∀u v. _’ irule >> simp[]) >>
  fs[]
QED

Theorem fseg_other:
  (∀t. kstep k (ss t) (rs t) (ss (SUC t)) (AS t)) ∧ ¬is_kcall k (rs t) ⇒
  fseg k ss AS (t + 1) = fseg k ss AS t ++ AS t
Proof
  strip_tac >> drule fclk_step >> strip_tac >>
  ‘fclk k ss (t + 1) = fclk k ss t’ by (first_x_assum (qspec_then ‘t’ mp_tac) >> simp[]) >>
  simp[fseg_def, GSYM ADD1, COUNT_LIST_SNOC, FILTER_APPEND, SNOC_APPEND] >> simp[ADD1]
QED

(*---------------------------------------------------------------------------*)
(* The run, seen by k, against one world for the whole run (ksim, infinite) *)

Theorem iksim:
  (∀t. kstep k (ss t) (rs t) (ss (SUC t)) (AS t) ∧ l0_rely (EL k (ss t).procs)) ∧
  E = (λn h nm. fenv k ss AS n) ∧ (ss 0).alive k ⇒
  ∀t. ∃V. agrees_to l0_oracle ((EL k (ss 0).procs) with env := E)
                    (proc_events k (GENLIST rs t)) V ∧
          ((ss t).alive k ⇒
           V.env = E ∧ V.clock = fclk k ss t ∧
           (EL k (ss t).procs) with env := E = FOLDL l0_deliver V (fseg k ss AS t))
Proof
  strip_tac >>
  ‘∀t. kstep k (ss t) (rs t) (ss (SUC t)) (AS t)’ by metis_tac[] >>
  Induct
  >- (rw[proc_events_def, agrees_to_def, fseg_def, fclk_def, COUNT_LIST_def]) >>
  fs[] >>
  ‘kstep k (ss t) (rs t) (ss (SUC t)) (AS t) ∧ l0_rely (EL k (ss t).procs)’ by metis_tac[] >>
  simp[GENLIST, SNOC_APPEND, proc_events_SNOC] >>
  Cases_on ‘is_kcall k (rs t)’
  >- (‘∃nm conf bts out. rs t = Call k nm conf bts out’ by fs[is_kcall_def] >>
      fs[] >>
      qpat_x_assum ‘kstep _ _ (Call _ _ _ _ _) _ _’ mp_tac >> rewrite_tac[kstep_def] >>
      simp[] >> strip_tac >> fs[] >>
      qabbrev_tac ‘wk = EL k (ss t).procs’ >>
      ‘fenv k ss AS (fclk k ss t) = fseg k ss AS t’ by
        (irule fenv_call >> simp[is_kcall_def] >> metis_tac[]) >>
      ‘l0_oracle (ExtCall nm) V conf bts =
       Oracle_return ((w1 with <| clock := wk.clock + 1; hist := wk.hist ++ [(nm, conf, bts)] |>)
                        with env := V.env) out’
        by (irule l0_oracle_call >> simp[] >>
            ‘fclk k ss t = wk.clock’ by simp[fclk_def, Abbr ‘wk’] >>
            rfs[] >> qexists_tac ‘λn. fenv k ss AS n’ >> rfs[] >> fs[]) >>
      ‘LENGTH out = LENGTH bts’ by metis_tac[l0_call_length] >>
      qexists_tac ‘(w1 with <| clock := wk.clock + 1; hist := wk.hist ++ [(nm, conf, bts)] |>)
                     with env := V.env’ >>
      conj_tac
      >- (simp[agrees_to_SNOC] >> qexists_tac ‘V’ >> rfs[MAP_ZIP]) >>
      strip_tac >>
      ‘fseg k ss AS (t + 1) = AS t’ by (irule fseg_call >> simp[is_kcall_def] >> metis_tac[]) >>
      fs[GSYM ADD1] >> rfs[fclk_def, FOLDL_deliver_env]) >>
  ‘(case rs t of
      Call k' nm conf bts out =>
        if k' = k then [IO_event (ExtCall nm) conf (ZIP (bts, out))] else []
    | Kern v13 => [] | Env v14 => [] | Exit v15 => []) = []’
    by (Cases_on ‘rs t’ >> fs[is_kcall_def]) >>
  pop_assum SUBST1_TAC >> qexists_tac ‘V’ >> rfs[] >> strip_tac >>
  ‘(ss t).alive k’ by fs[kstep_def] >> fs[] >>
  ‘fclk k ss (t + 1) = fclk k ss t’ by
    (drule fclk_step >> disch_then (qspec_then ‘t’ mp_tac) >> simp[]) >>
  ‘fseg k ss AS (t + 1) = fseg k ss AS t ++ AS t’ by (irule fseg_other >> simp[] >> metis_tac[]) >>
  fs[ADD1] >> simp[FOLDL_APPEND] >>
  qpat_x_assum ‘_ with env := _ = FOLDL _ _ _’ (SUBST1_TAC o SYM) >>
  simp[FOLDL_deliver_env] >>
  ‘kstep k (ss t) (rs t) (ss (t + 1)) (AS t)’ by fs[] >>
  Cases_on ‘rs t’ >> fs[is_kcall_def] >>
  qpat_x_assum ‘kstep _ _ _ _ _’ (strip_assume_tac o SIMP_RULE (srw_ss()) [kstep_def]) >>
  rfs[ADD1] >> Cases_on ‘n = k’ >> fs[ADD1]
QED

(*---------------------------------------------------------------------------*)
(* Replaying a prefix: a program that makes evs ++ more, answered by an
   oracle that agrees on evs, makes at least evs (l0sysReplay's
   replay_trace / replay_prefix, for a prefix of what the program makes) *)

Theorem replay_trace_ext:
  ∀n evs evs' seed (orc : 'b oracle) (st : 'b).
    agrees orc st evs ∧ evs ≼ evs' ⇒
    TAKE (LENGTH evs) (FST (trace_prefix n (replay_oracle, evs') (cml_itree_unfold_err f seed))) ≼
    FST (trace_prefix n (orc, st) (cml_itree_unfold_err f seed))
Proof
  Induct >> simp[trace_prefix_def] >> rpt gen_tac >> strip_tac >>
  once_rewrite_tac[cml_unfold] >>
  Cases_on ‘f seed’ >> simp[trace_prefix_def] >>
  rename1 ‘Vis' ev g’ >> PairCases_on ‘ev’ >> simp[trace_prefix_def] >>
  Cases_on ‘evs’ >- simp[] >>
  rename1 ‘agrees orc st (h :: rest)’ >>
  ‘∃rest'. evs' = h :: rest'’ by (Cases_on ‘evs'’ >> fs[]) >> rveq >> fs[] >>
  Cases_on ‘h’ >> rename1 ‘IO_event nm conf bl’ >>
  Cases_on ‘ev0’ >> simp[replay_oracle_def] >> Cases_on ‘nm’ >> simp[replay_oracle_def] >>
  IF_CASES_TAC >> simp[] >> fs[agrees_def] >> rveq >>
  first_x_assum (qspecl_then [‘rest’, ‘rest'’, ‘g (MAP SND bl)’, ‘orc’, ‘st'’] mp_tac) >>
  simp[] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[ZIP_MAP_FST_SND]
QED

Theorem replay_prefix_ext:
  prog_makes prog (evs ++ more) ∧ agrees f.oracle f.ffi_state evs ∧ f.io_events = [] ∧
  semantics_prog (init_state f) init_env prog b ⇒
  (∀out io. b = Terminate out io ⇒ evs ≼ io) ∧
  (∀io. b = Diverge io ⇒ LPREFIX (fromList evs) io)
Proof
  strip_tac >>
  qabbrev_tac ‘T0 = itree_of (init_state f) init_env prog’ >>
  ‘itree_of (init_state (replay_ffi (evs ++ more))) init_env prog = T0’
    by simp[Abbr ‘T0’, itree_of_init_state] >>
  drule prog_makes_trace >> simp[] >> strip_tac >>
  ‘evs ≼ FST (trace_prefix n (f.oracle, f.ffi_state) T0)’
    by (‘∃G (seed : dstep_result). T0 = cml_itree_unfold_err G seed’
          by simp[Abbr ‘T0’, itree_of_unfold] >>
        ‘TAKE (LENGTH evs) (FST (trace_prefix n (replay_oracle, evs ++ more)
                                   (cml_itree_unfold_err G seed))) ≼
         FST (trace_prefix n (f.oracle, f.ffi_state) (cml_itree_unfold_err G seed))’ by
          (irule replay_trace_ext >> fs[]) >>
        qpat_x_assum ‘T0 = _’ SUBST_ALL_TAC >> rfs[TAKE_APPEND1]) >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> rveq >>
  qpat_x_assum ‘semantics_prog _ _ _ _’ mp_tac >>
  asm_simp_tac std_ss [alt_semanticsTheory.itree_semantics, init_state_fields] >>
  strip_tac
  >- (rveq >> asm_rewrite_tac[APPEND] >> metis_tac[prefix_end]) >>
  metis_tac[prefix_div]
QED

(*---------------------------------------------------------------------------*)
(* N1: B1 for an infinite run *)

Theorem irun_procs_length:
  l0sys_irun ps ss rs ⇒ ∀t. LENGTH (ss t).procs = LENGTH ps
Proof
  strip_tac >> Induct
  >- fs[l0sys_irun_def, sys_init_def] >>
  ‘sys_ext (ss t) (ss (SUC t))’ by metis_tac[irun_ext] >> fs[sys_ext_def]
QED

Theorem l0sys_proj_inf:
  l0sys_irun ps ss rs ∧ k < LENGTH ps ⇒
  ∃AS. (∀t. kstep k (ss t) (rs t) (ss (SUC t)) (AS t)) ∧
       let w0 = (EL k (ss 0).procs) with env := (λn h nm. fenv k ss AS n) in
         l0_rely w0 ∧ l0_fresh w0 ∧ fds_lt w0 ∧
         (∀b. semantics_prog (init_state (l0_ffi w0)) init_env (EL k ps) b ∧ b ≠ Fail ⇒
              ∀t. LPREFIX (fromList (ptr rs k t)) (beh_io b)) ∧
         ∀t. ∃V. agrees_to l0_oracle w0 (ptr rs k t) V ∧
                 ((ss t).alive k ⇒
                  V.clock = fclk k ss t ∧
                  (EL k (ss t).procs) with env := w0.env = FOLDL l0_deliver V (fseg k ss AS t))
Proof
  strip_tac >>
  ‘∀t. k < LENGTH (ss t).procs’ by metis_tac[irun_procs_length] >>
  ‘∀t. sys_step (ss t) (rs t) (ss (SUC t))’ by fs[l0sys_irun_def] >>
  qexists_tac ‘λt. @as. kstep k (ss t) (rs t) (ss (SUC t)) as’ >>
  ‘∀t. kstep k (ss t) (rs t) (ss (SUC t)) (@as. kstep k (ss t) (rs t) (ss (SUC t)) as)’ by
    (gen_tac >> SELECT_ELIM_TAC >> simp[] >> irule kstep_exists >> simp[]) >>
  simp[] >> qmatch_goalsub_abbrev_tac ‘fenv k ss AS’ >>
  ‘∀t. l0_rely (EL k (ss t).procs)’ by
    (gen_tac >> drule irun_sinv >> disch_then (qspec_then ‘t’ strip_assume_tac) >>
     fs[sinv_def, pk_def, LET_THM]) >>
  ‘(ss 0).alive k ∧ l0_fresh (EL k (ss 0).procs) ∧ fds_lt (EL k (ss 0).procs)’ by
    (fs[l0sys_irun_def, sys_init_def, LET_THM, l0_fresh_def, l0sysInvTheory.fds_lt_def,
        honestL0WorldPropsTheory.fds_lt_def]) >>
  qspecl_then [‘k’, ‘ss’, ‘rs’, ‘AS’, ‘λn h nm. fenv k ss AS n’] mp_tac
    (Q.GENL [‘k’, ‘ss’, ‘rs’, ‘AS’, ‘E’] iksim) >>
  impl_tac >- simp[Abbr ‘AS’] >> strip_tac >>
  rpt conj_tac
  >- (irule l0_rely_ch >> qexists_tac ‘EL k (ss 0).procs’ >> simp[])
  >- fs[l0_fresh_def]
  >- (qpat_x_assum ‘fds_lt _’ mp_tac >>
      simp[l0sysInvTheory.fds_lt_def, honestL0WorldPropsTheory.fds_lt_def, l0_used_def])
  >- (rpt strip_tac >>
      first_x_assum (qspec_then ‘t’ strip_assume_tac) >>
      ‘∃more. prog_makes (EL k ps) (proc_events k (GENLIST rs t) ++ more)’ by
        fs[l0sys_irun_def] >>
      qspecl_then [‘EL k ps’, ‘ptr rs k t’, ‘more’,
                   ‘l0_ffi ((EL k (ss 0).procs) with env := (λn h nm. fenv k ss AS n))’, ‘b’]
        mp_tac (Q.GENL [‘prog’, ‘evs’, ‘more’, ‘f’, ‘b’] replay_prefix_ext) >>
      impl_tac
      >- (simp[l0_ffi_def, ptr_def] >> irule agrees_to_agrees >> metis_tac[]) >>
      Cases_on ‘b’ >> fs[beh_io_def, LPREFIX_fromList, from_toList]) >>
  gen_tac >> first_x_assum (qspec_then ‘t’ strip_assume_tac) >>
  qexists_tac ‘V’ >> fs[ptr_def]
QED
