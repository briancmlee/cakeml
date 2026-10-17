(*
  One program on the honest L0 world (l0_ffi w0), outside any l0sys run:
  every finite prefix of its trace is a sequence of calls the world
  answered (l0_replay_ok), and an induction over those calls with the same
  per-call obligations as moonshotWorldFacts' run_calls_induct_inv
  (lone_calls_induct_inv), so the l0sys facts' per-call lemmas apply.

  A blocking poll (conf 1) is, in the l0sys vocabulary, the unblocked poll
  (unblock: conf 0) on the world after its ticks.
*)
Theory moonshotLoneTrace
Ancestors
  moonshotW2 moonshotWorldFacts l0sysEpisodesEcho honestL0World honestL0WorldProps honestL0Rely
  l0sys l0sysEpisodes l0sysInv l0sysInvCall l0sysRun l0sysBridges
  llist ffi semantics evaluateProps ml_prog
Libs
  preamble

(*---------------------------------------------------------------------------*)
(* The trace replays in the world *)

Definition l0_replay_ok_def:
  l0_replay_ok w [] = T ∧
  l0_replay_ok w (IO_event (ExtCall n) conf bs :: evs) =
    (case l0_ffi_fn n conf (MAP FST bs) w of
     | SOME (FFIreturn out w') => out = MAP SND bs ∧ l0_replay_ok w' evs
     | _ => F) ∧
  l0_replay_ok w (_ :: evs) = F
End

Definition l0_replay_def:
  l0_replay w [] = w ∧
  l0_replay w (IO_event (ExtCall n) conf bs :: evs) =
    (case l0_ffi_fn n conf (MAP FST bs) w of
     | SOME (FFIreturn out w') => l0_replay w' evs
     | _ => w) ∧
  l0_replay w (_ :: evs) = w
End

Theorem l0_replay_ok_APPEND:
  ∀w a b. l0_replay_ok w (a ++ b) ⇔ l0_replay_ok w a ∧ l0_replay_ok (l0_replay w a) b
Proof
  ho_match_mp_tac l0_replay_ok_ind >> rw[l0_replay_ok_def, l0_replay_def] >>
  every_case_tac >> fs[] >> metis_tac[]
QED

Theorem l0_replay_APPEND:
  ∀w evs. l0_replay_ok w evs ⇒ ∀rest. l0_replay w (evs ++ rest) = l0_replay (l0_replay w evs) rest
Proof
  ho_match_mp_tac l0_replay_ok_ind >> rw[l0_replay_ok_def, l0_replay_def] >>
  every_case_tac >> fs[]
QED

Theorem call_FFI_rel_l0_replay:
  ∀f1 f2. RTC call_FFI_rel f1 f2 ⇒ f1.oracle = l0_oracle ⇒
          ∃new. f2.io_events = f1.io_events ++ new ∧ l0_replay_ok f1.ffi_state new ∧
                l0_replay f1.ffi_state new = f2.ffi_state
Proof
  ho_match_mp_tac RTC_INDUCT >> conj_tac
  >- (rw[] >> TRY (qexists_tac ‘[]’) >> simp[l0_replay_ok_def, l0_replay_def]) >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  imp_res_tac call_FFI_rel_consts >> fs[] >>
  ‘∃e. f1'.io_events = f1.io_events ++ e ∧ l0_replay_ok f1.ffi_state e ∧
       l0_replay f1.ffi_state e = f1'.ffi_state’
    by (qpat_x_assum ‘call_FFI_rel _ _’ mp_tac >>
        simp[call_FFI_rel_def, call_FFI_def] >> rpt strip_tac >>
        qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac >>
        IF_CASES_TAC >>
        TRY (rw[] >> TRY (qexists_tac ‘[]’) >> simp[l0_replay_ok_def, l0_replay_def] >> NO_TAC) >>
        Cases_on ‘n’ >> simp[l0_oracle_def] >>
        rename1 ‘l0_ffi_fn s conf bs f1.ffi_state’ >>
        Cases_on ‘l0_ffi_fn s conf bs f1.ffi_state’ >> simp[] >>
        rename1 ‘SOME r’ >> Cases_on ‘r’ >> simp[] >>
        IF_CASES_TAC >> simp[] >> strip_tac >> rveq >>
        rename1 ‘FFIreturn out w'’ >>
        qexists_tac ‘[IO_event (ExtCall s) conf (ZIP (bs, out))]’ >>
        simp[l0_replay_ok_def, l0_replay_def, MAP_ZIP]) >>
  qexists_tac ‘e ++ new’ >> simp[l0_replay_ok_APPEND, l0_replay_APPEND]
QED

Theorem prefix_FRONT[local]:
  a ≼ b ∧ a ≠ b ⇒ a ≼ FRONT b
Proof
  rw[IS_PREFIX_APPEND] >> gvs[] >> Cases_on ‘l’ using SNOC_CASES >> gvs[] >>
  qexists_tac ‘l'’ >> REWRITE_TAC[APPEND_ASSOC, GSYM SNOC_APPEND, FRONT_SNOC]
QED

(* endpointTrace's diverge_prefix, copied (its theory's ancestors are not
   wanted here) *)
Theorem diverge_prefix_l0[local]:
  semantics_prog st env prog (Diverge io) ∧ LPREFIX (fromList evs) io ⇒
  ∃k. evs ≼ (FST (evaluate_prog_with_clock st env k prog)).io_events
Proof
  rw[semanticsTheory.semantics_prog_def] >> CCONTR_TAC >> fs[] >>
  ‘evs ≠ []’ by (strip_tac >> fs[]) >>
  qmatch_asmsub_abbrev_tac ‘lprefix_lub (IMAGE g UNIV) io’ >>
  ‘∀k. LPREFIX (g k) (fromList (FRONT evs))’
    by (gen_tac >>
        ‘LPREFIX (g k) io’ by (fs[lprefix_lub_def] >> metis_tac[IN_IMAGE, IN_UNIV]) >>
        first_x_assum (qspec_then ‘k’ mp_tac) >> fs[Abbr ‘g’] >>
        qmatch_goalsub_abbrev_tac ‘evs ≼ ek’ >> rpt strip_tac >>
        ‘LPREFIX (fromList ek) (fromList evs) ∨ LPREFIX (fromList evs) (fromList ek)’
          by metis_tac[prefixes_lprefix_total] >>
        fs[LPREFIX_fromList, from_toList] >>
        irule prefix_FRONT >> rw[] >> strip_tac >> fs[]) >>
  ‘LPREFIX io (fromList (FRONT evs))’
    by (fs[lprefix_lub_def] >> first_x_assum irule >> rw[] >> simp[]) >>
  ‘LPREFIX (fromList evs) (fromList (FRONT evs))’ by metis_tac[LPREFIX_TRANS] >>
  fs[LPREFIX_fromList, from_toList] >>
  imp_res_tac IS_PREFIX_LENGTH >>
  Cases_on ‘evs’ using SNOC_CASES >> fs[FRONT_SNOC]
QED

(* Every finite prefix of a behaviour's trace replays *)
Theorem beh_l0_replay_ok:
  semantics_prog (init_state (l0_ffi w)) init_env prog beh ∧
  LPREFIX (fromList evs) (beh_io beh) ⇒ l0_replay_ok w evs
Proof
  strip_tac >>
  ‘∃k. evs ≼ (FST (evaluate_prog_with_clock (init_state (l0_ffi w)) init_env k prog)).io_events’
    by (Cases_on ‘beh’ >> fs[beh_io_def] >>
        TRY (drule_all diverge_prefix_l0 >> simp[] >> NO_TAC) >>
        TRY (qpat_x_assum ‘semantics_prog _ _ _ (Terminate _ _)’
               (strip_assume_tac o REWRITE_RULE [semanticsTheory.semantics_prog_def]) >>
             qexists_tac ‘k’ >> gvs[LPREFIX_fromList, from_toList] >> NO_TAC) >>
        fs[LPREFIX_fromList, from_toList]) >>
  fs[evaluate_prog_with_clock_def] >> pairarg_tac >> fs[] >>
  imp_res_tac evaluate_call_FFI_rel_imp >>
  ‘(init_state (l0_ffi w) with clock := k).ffi = l0_ffi w’
    by simp[ml_progTheory.init_state_def] >>
  fs[] >> drule call_FFI_rel_l0_replay >> simp[l0_ffi_def] >> strip_tac >>
  gvs[IS_PREFIX_APPEND] >> fs[l0_ffi_def] >> gvs[l0_replay_ok_APPEND]
QED

(*---------------------------------------------------------------------------*)
(* One lone call, in the l0sys vocabulary *)

Theorem deliver_hist[simp]:
  (l0_deliver w a).hist = w.hist
Proof
  Cases_on ‘a’ >> rw[l0_deliver_def, upd_lchan_def] >> every_case_tac >> simp[]
QED

Theorem FOLDL_deliver_hist[simp]:
  ∀as w. (FOLDL l0_deliver w as).hist = w.hist
Proof
  Induct >> simp[]
QED

Theorem ticks_hist[simp]:
  ∀k w. (l0_ticks nm k w).hist = w.hist
Proof
  Induct >> simp[l0_ticks_def, l0_tick_def]
QED

Theorem lone_step:
  l0_ffi_fn nm conf bytes w = SOME (FFIreturn out w') ⇒
  ∃wc w1. (∃k nm0. wc = l0_ticks nm0 k (l0_tick nm w)) ∧
          l0_call nm (unblock nm conf) bytes wc = SOME (FFIreturn out w1) ∧
          w' = w1 with <| clock := w1.clock; hist := w.hist ++ [(nm, conf, bytes)] |>
Proof
  rw[l0_ffi_fn_def, AllCaseEqs()] >>
  Cases_on ‘nm = «sys_poll» ∧ conf ≠ [] ∧ HD conf = 1w’
  >- (gvs[] >> qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >>
      simp[l0_call_def] >> rw[AllCaseEqs()] >>
      TRY (qexistsl_tac [‘l0_tick «sys_poll» w’, ‘l0_tick «sys_poll» w’] >>
           conj_tac >- (qexistsl_tac [‘0’, ‘«sys_poll»’] >> simp[l0_ticks_def]) >>
           Cases_on ‘conf’ >>
           gvs[l0_call_def, unblock_def, honestL0WorldTheory.l0world_component_equality] >>
           NO_TAC) >>
      qexistsl_tac [‘l0_ticks «sys_poll» k (l0_tick «sys_poll» w)’,
                    ‘l0_ticks «sys_poll» k (l0_tick «sys_poll» w)’] >>
      conj_tac >- (qexistsl_tac [‘k’, ‘«sys_poll»’] >> simp[]) >>
      Cases_on ‘conf’ >>
      gvs[l0_call_def, unblock_def, honestL0WorldTheory.l0world_component_equality]) >>
  qexistsl_tac [‘l0_tick nm w’, ‘w''’] >>
  ‘unblock nm conf = conf’ by (rw[unblock_def] >> fs[]) >>
  simp[] >> conj_tac >- (qexistsl_tac [‘0’, ‘nm’] >> simp[l0_ticks_def]) >>
  simp[honestL0WorldTheory.l0world_component_equality]
QED

Theorem pinv_clock[simp]:
  pinv evs (w with clock := c) cs ⇔ pinv evs w cs
Proof
  simp[pinv_def, l0_chan_of_def, fds_lt_def, l0_used_def]
QED

Theorem pinv_FOLDL_deliver:
  ∀as w. pinv evs w cs ⇒ pinv evs (FOLDL l0_deliver w as) cs
Proof
  Induct >> rw[] >> first_x_assum irule >> irule pinv_deliver >> simp[]
QED

Theorem pinv_tick:
  pinv evs w cs ⇒ pinv evs (l0_tick nm w) cs
Proof
  rw[l0_tick_def] >> irule pinv_FOLDL_deliver >> simp[pinv_clock]
QED

Theorem rely_tick:
  l0_rely w ⇒ l0_rely (l0_tick nm w)
Proof
  strip_tac >> irule l0_rely_ch >> qexists_tac ‘w’ >> simp[]
QED

(*---------------------------------------------------------------------------*)
(* The induction over a lone program's calls *)

Theorem lone_calls_induct_inv:
  (∀evs w c. Inv evs w ⇒ Inv evs (w with clock := c)) ∧
  (∀evs w as. Inv evs w ⇒ Inv evs (FOLDL l0_deliver w as)) ∧
  (∀evs w cs nm conf bytes out w1 n h.
     Inv evs w ∧ pinv evs w cs ∧ l0_rely w ∧ small_ch w.ch ∧
     l0_call nm (unblock nm conf) bytes w = SOME (FFIreturn out w1) ⇒
     Inv (evs ++ [IO_event (ExtCall nm) conf (ZIP (bytes, out))])
       (w1 with <| clock := n; hist := h |>)) ∧
  (∀evs w cs nm conf bytes out w1.
     Q evs ∧ Inv evs w ∧ pinv evs w cs ∧ l0_rely w ∧ small_ch w.ch ∧
     l0_call nm (unblock nm conf) bytes w = SOME (FFIreturn out w1) ⇒
     Q (evs ++ [IO_event (ExtCall nm) conf (ZIP (bytes, out))])) ⇒
  ∀evs w evs0 cs. l0_replay_ok w evs ∧ pinv evs0 w cs ∧ l0_rely w ∧ Q evs0 ∧ Inv evs0 w ⇒
                  Q (evs0 ++ evs)
Proof
  strip_tac >>
  ‘∀evs0 w cs nm k. pinv evs0 w cs ∧ l0_rely w ∧ Inv evs0 w ⇒
                    pinv evs0 (l0_tick nm w) cs ∧ l0_rely (l0_tick nm w) ∧ Inv evs0 (l0_tick nm w)’
    by (rpt gen_tac >> strip_tac >> simp[pinv_tick, rely_tick] >> simp[l0_tick_def] >>
        qpat_x_assum ‘∀evs w as. Inv _ _ ⇒ Inv _ (FOLDL _ _ _)’ irule >>
        qpat_x_assum ‘∀evs w c. Inv _ _ ⇒ Inv _ (_ with clock := _)’ irule >> simp[]) >>
  ‘∀k evs0 w cs nm. pinv evs0 w cs ∧ l0_rely w ∧ Inv evs0 w ⇒
                    pinv evs0 (l0_ticks nm k w) cs ∧ l0_rely (l0_ticks nm k w) ∧
                    Inv evs0 (l0_ticks nm k w)’
    by (Induct >> simp[l0_ticks_def] >> rpt gen_tac >> strip_tac >>
        first_x_assum irule >> metis_tac[]) >>
  Induct >- simp[] >>
  Cases >> rename1 ‘IO_event nm0 conf bs’ >> Cases_on ‘nm0’ >> simp[l0_replay_ok_def] >>
  rpt gen_tac >> rename1 ‘l0_ffi_fn nm conf (MAP FST bs) w’ >>
  Cases_on ‘l0_ffi_fn nm conf (MAP FST bs) w’ >> simp[] >>
  rename1 ‘SOME r’ >> Cases_on ‘r’ >> simp[] >> strip_tac >>
  rename1 ‘FFIreturn out w'’ >>
  drule lone_step >> strip_tac >>
  ‘pinv evs0 wc cs ∧ l0_rely wc ∧ Inv evs0 wc’ by metis_tac[] >>
  ‘small_ch wc.ch’ by metis_tac[l0_rely_small_ch] >>
  ‘ZIP (MAP FST bs, MAP SND bs) = bs’ by (rpt (pop_assum kall_tac) >> Induct_on ‘bs’ >> simp[]) >>
  qabbrev_tac ‘e = IO_event (ExtCall nm) conf (ZIP (MAP FST bs, out))’ >>
  ‘evs0 ++ IO_event (ExtCall nm) conf bs :: evs = (evs0 ++ [e]) ++ evs’
    by (simp[Abbr ‘e’] >> metis_tac[]) >>
  pop_assum SUBST1_TAC >>
  first_x_assum irule >> conj_tac
  >- (qunabbrev_tac ‘e’ >>
      qpat_x_assum ‘∀evs w cs nm conf bytes out w1. _ ⇒ Q _’ irule >>
      simp[] >> qexistsl_tac [‘cs’, ‘wc’, ‘w1’] >> fs[]) >>
  qexistsl_tac [‘cs ++ new_chans wc e’, ‘w'’] >> simp[] >> rpt conj_tac
  >- (irule l0_rely_ch >> qexists_tac ‘wc’ >> imp_res_tac l0_call_ch >> simp[])
  >- (qunabbrev_tac ‘e’ >>
      qpat_x_assum ‘∀evs w cs nm conf bytes out w1 n h. _ ⇒ Inv _ _’ irule >>
      qexistsl_tac [‘cs’, ‘wc’] >> fs[]) >>
  qunabbrev_tac ‘e’ >> irule pinv_call >> qpat_x_assum ‘wc = _’ (fn th => fs[GSYM th]) >>
  irule l0_rely_small_ch >> first_assum ACCEPT_TAC
QED

(*---------------------------------------------------------------------------*)
(* A lone run from a fresh world: the trace facts the bridges need *)

Theorem lone_induct:
  w0.listeners = [] ∧ w0.chans = [] ∧ w0.open_fds = [] ∧ fds_lt w0 ∧ l0_rely w0 ∧
  semantics_prog (init_state (l0_ffi w0)) init_env prog beh ∧
  LPREFIX (fromList evs) (beh_io beh) ∧ Q [] ∧ Inv [] w0 ∧
  (∀evs w c. Inv evs w ⇒ Inv evs (w with clock := c)) ∧
  (∀evs w as. Inv evs w ⇒ Inv evs (FOLDL l0_deliver w as)) ∧
  (∀evs w cs nm conf bytes out w1 n h.
     Inv evs w ∧ pinv evs w cs ∧ l0_rely w ∧ small_ch w.ch ∧
     l0_call nm (unblock nm conf) bytes w = SOME (FFIreturn out w1) ⇒
     Inv (evs ++ [IO_event (ExtCall nm) conf (ZIP (bytes, out))])
       (w1 with <| clock := n; hist := h |>)) ∧
  (∀evs w cs nm conf bytes out w1.
     Q evs ∧ Inv evs w ∧ pinv evs w cs ∧ l0_rely w ∧ small_ch w.ch ∧
     l0_call nm (unblock nm conf) bytes w = SOME (FFIreturn out w1) ⇒
     Q (evs ++ [IO_event (ExtCall nm) conf (ZIP (bytes, out))])) ⇒
  Q evs
Proof
  strip_tac >> drule_all beh_l0_replay_ok >> strip_tac >>
  qspecl_then [‘Inv’, ‘Q’] mp_tac (Q.GENL [‘Inv’, ‘Q’] lone_calls_induct_inv) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [‘evs’, ‘w0’, ‘[]’, ‘[]’] mp_tac) >> simp[] >>
  disch_then irule >> irule pinv_init >> simp[]
QED

(* W3 for a lone run *)
Theorem lone_ops_live:
  w0.listeners = [] ∧ w0.chans = [] ∧ w0.open_fds = [] ∧ fds_lt w0 ∧ l0_rely w0 ∧
  semantics_prog (init_state (l0_ffi w0)) init_env prog beh ∧
  LPREFIX (fromList evs) (beh_io beh) ⇒ ops_live evs
Proof
  strip_tac >>
  qspecl_then [‘ops_live’, ‘fds_live’] mp_tac (Q.GENL [‘Q’, ‘Inv’] lone_induct) >>
  disch_then irule >> simp[] >> rpt conj_tac >>
  FIRST [
    simp[fds_live_def] >> NO_TAC,
    simp[ops_live_def] >> NO_TAC,
    metis_tac[fds_live_deliver] >> NO_TAC,
    rpt strip_tac >> irule fds_live_call >> metis_tac[] >> NO_TAC,
    rpt strip_tac >> simp[ops_live_SNOC] >> rpt strip_tac >>
    ‘∃c. ALOOKUP w.open_fds f = SOME c’ by (irule call_op_open >> metis_tac[]) >>
    fs[fds_live_def] >> metis_tac[] >> NO_TAC,
    metis_tac[]]
QED

(* W2 for a lone run that checks fd 0 and never closes it *)
Theorem lone_no_fd0:
  w0.listeners = [] ∧ w0.chans = [] ∧ w0.open_fds = [] ∧ fds_lt w0 ∧ l0_rely w0 ∧
  semantics_prog (init_state (l0_ffi w0)) init_env prog beh ∧
  LPREFIX (fromList evs) (beh_io beh) ∧ fd0_checked evs ∧ no_close0 evs ⇒
  EVERY (λev. ∀r. ev_new ev ≠ SOME (0w, r)) evs
Proof
  strip_tac >>
  qspecl_then [‘λevs. fd0_checked evs ∧ no_close0 evs ⇒
                      EVERY (λev. ∀r. ev_new ev ≠ SOME (0w, r)) evs’, ‘fd0_used’]
    mp_tac (Q.GENL [‘Q’, ‘Inv’] lone_induct) >>
  simp[] >> disch_then irule >> rpt conj_tac >>
  FIRST [
    rw[fd0_used_def] >> fs[] >> NO_TAC,
    rw[fd0_used_def] >> ‘l0_used (w with clock := c) = l0_used w’ by simp[l0_used_def] >>
    fs[] >> metis_tac[] >> NO_TAC,
    simp[fd0_used_def] >> NO_TAC,
    rpt strip_tac >> irule fd0_used_call >> metis_tac[] >> NO_TAC,
    rpt gen_tac >> strip_tac >> strip_tac >>
    imp_res_tac fd0_checked_prefix >> imp_res_tac no_close0_prefix >> fs[] >>
    rpt strip_tac >> drule_all fd0_checked_SNOC >> strip_tac >>
    ‘MEM 0w (l0_used w)’ by (fs[fd0_used_def] >> metis_tac[]) >>
    ‘fds_lt w’ by fs[pinv_def] >>
    ‘¬MEM 0w (l0_used w)’ suffices_by simp[] >>
    irule call_new_unused >> metis_tac[unblock_other]]
QED

(* A listen that got an answer had a 2-byte conf *)
Theorem lone_listen_conf:
  w0.listeners = [] ∧ w0.chans = [] ∧ w0.open_fds = [] ∧ fds_lt w0 ∧ l0_rely w0 ∧
  semantics_prog (init_state (l0_ffi w0)) init_env prog beh ∧
  LPREFIX (fromList evs) (beh_io beh) ⇒
  ∀conf bs. MEM (IO_event (ExtCall «sys_listen») conf bs) evs ⇒ LENGTH conf = 2
Proof
  strip_tac >>
  qspecl_then [‘λevs. ∀conf bs. MEM (IO_event (ExtCall «sys_listen») conf bs) evs ⇒
                                LENGTH conf = 2’, ‘K (K T)’]
    mp_tac (Q.GENL [‘Q’, ‘Inv’] lone_induct) >>
  simp[] >> impl_tac >> simp[] >>
  rpt strip_tac >> fs[] >- metis_tac[] >>
  qpat_x_assum ‘l0_call _ _ _ _ = _’ mp_tac >> simp[unblock_def, l0_call_def] >> rw[]
QED
