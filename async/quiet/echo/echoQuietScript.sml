(*
  The shipped blocking echo program meets QuietSpec (option C, echo).

     echo_blocking_quiet : ⊢ echo_quiet 3w (SNOC (main_call «main») echo_blocking_prog)

  #46's echo_blocking_semantics gives the program's two outcomes in #46's
  select world (ssel_ffi): it runs forever, or it ends blocked forever in
  select.  This file
  - moves both outcomes to QuietSpec's select world (select_ffi): the two
    worlds answer the same to every call the program makes, because it
    selects only on the listener and accepted connections (trace_good,
    answers_agree, semantics_prog_upto);
  - takes safety and liveness from #46 (echo_blocking_spec, with the polling
    loop's liveness echo_live_rounds);
  - shows that in a world where only finitely many things arrive the run
    ends asleep (echo_sleeps).

  The select set is #46's live list; that it is exactly what the echo
  server waits for is echo_blocking_list_covers (echoSleeps).

  MAIN: echo_blocking_quiet.
*)
Theory echoQuiet
Ancestors
  pair list rich_list arithmetic option llist alist words
  ffi semantics evaluate evaluateProps ml_prog
  socketWorld socketFair EchoSpec QuietSpec
  loopPollWorld loopRounds loopRoundsTrans echoSockModel loopPollDyn
  loopSelectWorld loopSelectTrace loopSelectSet echoSelectMain
  echoBlockingSet echoBlockingProg echoBlockingMain echoLiveReadSoon
  echoLive echoSafe echoBlockingInv echoSleeps echoQuietBridge
  echoQuietTrace ffiAgreeUpto
Libs
  preamble

(* ------------------------------------------------------------------------
   Clocked runs against a terminating one
   ------------------------------------------------------------------------ *)

(* Every clocked run either times out with a prefix of a terminating run's
   events, or is that run *)
Theorem clocked_vs_terminating:
  evaluate_prog_with_clock st env k0 prog = (ffi0, r0) ∧
  r0 ≠ Rerr (Rabort Rtimeout_error) ⇒
  ∀k. (SND (evaluate_prog_with_clock st env k prog) = Rerr (Rabort Rtimeout_error) ∧
       (FST (evaluate_prog_with_clock st env k prog)).io_events ≼ ffi0.io_events) ∨
      evaluate_prog_with_clock st env k prog = (ffi0, r0)
Proof
  rw[evaluate_prog_with_clock_def] >>
  Cases_on ‘evaluate_decs (st with clock := k0) env prog’ >> gvs[] >>
  Cases_on ‘evaluate_decs (st with clock := k) env prog’ >> gvs[] >>
  rename1 ‘evaluate_decs (st with clock := k) env prog = (s1, r1)’ >>
  rename1 ‘evaluate_decs (st with clock := k0) env prog = (s0', r0)’ >>
  Cases_on ‘k ≤ k0’
  >- (Cases_on ‘r1 = Rerr (Rabort Rtimeout_error)’
      >- (disj1_tac >> simp[] >>
          qspecl_then [‘k’, ‘k0’, ‘st’, ‘env’, ‘prog’] mp_tac evaluate_decs_ffi_mono_clock >>
          simp[io_events_mono_def])
      >> disj2_tac >>
      drule_all evaluate_decs_add_to_clock >>
      disch_then (qspec_then ‘k0 − k’ mp_tac) >> simp[])
  >> disj2_tac >>
  drule_all evaluate_decs_add_to_clock >>
  disch_then (qspec_then ‘k − k0’ mp_tac) >> simp[]
QED

(* ------------------------------------------------------------------------
   llist prefixes of the rounds (as loopSelectSet's local lemmas)
   ------------------------------------------------------------------------ *)

Theorem LFLATTEN_fromList_GENLIST[local]:
  ∀n. LFLATTEN (fromList (GENLIST (λi. fromList (f i)) n)) =
      fromList (FLAT (GENLIST f n))
Proof
  Induct >> simp[GENLIST, SNOC_APPEND, GSYM LAPPEND_fromList,
                 LFLATTEN_APPEND_FINITE1] >>
  simp[LAPPEND_fromList, FLAT_APPEND, LAPPEND_NIL_2ND]
QED

Theorem LFLATTEN_LGENLIST_chunk[local]:
  LFLATTEN (LGENLIST (λi. fromList (f i)) NONE) =
  LAPPEND (fromList (FLAT (GENLIST f n)))
          (LFLATTEN (LGENLIST (λi. fromList (f (n + i))) NONE))
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV
    [Q.SPEC ‘n’ (Q.GEN ‘n’ LGENLIST_CHUNK_GENLIST)])) >>
  simp[LFLATTEN_APPEND_FINITE1] >>
  simp[LFLATTEN_fromList_GENLIST, combinTheory.o_DEF] >>
  AP_TERM_TAC >> AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM]
QED

Theorem rounds_LPREFIX[local]:
  LPREFIX (fromList (FLAT (GENLIST f n)))
          (LFLATTEN (LGENLIST (λi. fromList (f i)) NONE))
Proof
  ONCE_REWRITE_TAC[LFLATTEN_LGENLIST_chunk] >> simp[LPREFIX_APPEND] >>
  metis_tac[]
QED

Theorem LPREFIX_LTAKE[local]:
  LPREFIX (fromList l) ll ⇒ LTAKE (LENGTH l) ll = SOME l
Proof
  rw[LPREFIX_APPEND] >>
  qspecl_then [‘ll'’, ‘l’, ‘0’] mp_tac LTAKE_LAPPEND_fromList >> simp[]
QED

Theorem LPREFIX_comparable[local]:
  LPREFIX (fromList a) ll ∧ LPREFIX (fromList b) ll ∧ LENGTH a ≤ LENGTH b ⇒
  a ≼ b
Proof
  rw[] >> imp_res_tac LPREFIX_LTAKE >>
  drule_all LTAKE_TAKE_LESS >> rw[] >> gvs[] >>
  ‘a = TAKE (LENGTH a) b’ by gvs[] >> pop_assum SUBST1_TAC >>
  simp[IS_PREFIX_APPEND] >> qexists_tac ‘DROP (LENGTH a) b’ >> simp[]
QED

Theorem LPREFIX_rounds[local]:
  (∀i. f i ≠ []) ∧
  LPREFIX (fromList evs) (LFLATTEN (LGENLIST (λi. fromList (f i)) NONE)) ⇒
  ∃n. evs ≼ FLAT (GENLIST f n)
Proof
  strip_tac >>
  ‘∀n. n ≤ LENGTH (FLAT (GENLIST f n))’
    by (Induct >> simp[GENLIST, SNOC_APPEND, FLAT_APPEND] >>
        first_x_assum (qspec_then ‘n’ mp_tac) >> Cases_on ‘f n’ >> simp[]) >>
  qexists_tac ‘LENGTH evs’ >> irule LPREFIX_comparable >>
  metis_tac[rounds_LPREFIX]
QED

(* ------------------------------------------------------------------------
   The program
   ------------------------------------------------------------------------ *)

Overload echo_blocking_main = “SNOC (main_call «main») echo_blocking_prog”

Theorem echo_blocking_syntax_ok:
  prog_syntax_ok echo_blocking_main
Proof
  REWRITE_TAC [echo_blocking_prog_def, prog_syntax_ok_def] >> EVAL_TAC
QED

Theorem echo_sel_eq[local]:
  echo_sel = sel_echo 3
Proof
  simp[FUN_EQ_THM, lsel_def, sel_echo_def, secho_run]
QED

Theorem final_call_len[local]:
  LENGTH (final_call r) ≤ 1
Proof
  rw[final_call_def, final_err_def] >> every_case_tac >> simp[] >>
  TRY (rename1 ‘final_ffi fe’ >> Cases_on ‘fe’ >> simp[final_ffi_def])
QED

(* The calls of a clocked run of the program are disciplined, given the
   program's behaviour in #46's world *)
Theorem clock_ok[local]:
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ∧
  (∀k. good 3w [] (FST (evaluate_prog_with_clock (init_state (ssel_ffi sk)) init_env k
                          echo_blocking_main)).io_events ∧
       ∀n c b. MEM (n, c, b) (final_call (SND (evaluate_prog_with_clock
                                (init_state (ssel_ffi sk)) init_env k echo_blocking_main))) ∧
               n = ExtCall «sock_select» ⇒
               EVERY (λfd. fd = 3w ∨
                           MEM fd (accs_of (FST (evaluate_prog_with_clock
                                     (init_state (ssel_ffi sk)) init_env k echo_blocking_main)).io_events))
                     (bytes_fds c)) ⇒
  ∀k. agree_upto (clock_calls (init_state (ssel_ffi sk)) init_env echo_blocking_main k)
                 (ssel_ffi sk) (select_ffi sk)
Proof
  rpt strip_tac >> simp[agree_upto_def] >> rpt strip_tac >>
  first_x_assum (qspec_then ‘k’ strip_assume_tac) >>
  Cases_on ‘evaluate_prog_with_clock (init_state (ssel_ffi sk)) init_env k echo_blocking_main’ >>
  rename1 ‘_ = (ffik, rk)’ >> gvs[] >>
  ‘RTC call_FFI_rel (ssel_ffi sk) ffik’
    by (gvs[evaluate_prog_with_clock_def] >> pairarg_tac >> gvs[] >>
        qspecl_then [‘init_state (ssel_ffi sk) with clock := k’, ‘init_env’, ‘echo_blocking_main’]
          mp_tac (CONJUNCT2 (CONJUNCT2 evaluate_call_FFI_rel)) >>
        simp[init_state_def]) >>
  drule call_FFI_rel_answers >> strip_tac >>
  gvs[ssel_ffi_def] >>
  qspecl_then [‘calls_of ffik.io_events ++ final_call rk’, ‘[]’, ‘sk’] mp_tac
    (Q.GEN ‘L’ answers_agree_prefix |> Q.SPEC ‘3w’) >>
  impl_tac
  >- (conj_tac
      >- simp[sock_inv_def, is_listener_def, is_conn_def] >>
      simp[GSYM ssel_ffi_def] >>
      ‘ffi_answers (ssel_ffi sk) (calls_of ffik.io_events ++ final_call rk) =
       answers_of ffik.io_events ++ ffi_answers ffik (final_call rk)’
        by gvs[ssel_ffi_def] >>
      simp[] >> irule ok_of_good >> simp[final_call_len] >> gvs[ext_def] >>
      metis_tac[]) >>
  disch_then (qspec_then ‘cs’ mp_tac) >> gvs[ext_def, ssel_ffi_def]
QED

Theorem lbround_events_nonempty[local]:
  lbgrounds sel fds0 m s0 (SUC i) ≠ NONE ⇒ lbround_events sel fds0 m s0 i ≠ []
Proof
  Cases_on ‘lbgrounds sel fds0 m s0 (SUC i)’ >> simp[] >>
  rename1 ‘SOME x’ >> PairCases_on ‘x’ >> strip_tac >>
  drule lbgrounds_SUC_cases >> strip_tac >> every_case_tac >> gvs[]
QED

(* The select of a stuck round names only the listener and accepted fds *)
Theorem stuck_select_ok[local]:
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ∧
  lbgrounds echo_sel [3w] echo_c.run sk n = SOME (kept, N, s) ⇒
  EVERY (λfd. fd = 3w ∨
              MEM fd (accs_of (FLAT (GENLIST (lbround_events echo_sel [3w] echo_c.run sk) n))))
        (echo_sel kept)
Proof
  strip_tac >> gvs[echo_sel_eq, secho_run] >>
  ‘(3w : word64) = n2w 3’ by simp[] >> pop_assum SUBST_ALL_TAC >>
  qspecl_then [‘sk’, ‘3’] mp_tac (Q.GENL [‘s0’, ‘lfdn’] trace_good) >>
  simp[] >> disch_then drule >> strip_tac >> simp[] >>
  qspecl_then [‘sk’, ‘3’] mp_tac (Q.GENL [‘s0’, ‘lfdn’] kept_live) >>
  simp[] >> disch_then drule >> strip_tac >> simp[EVERY_MEM] >>
  rpt strip_tac >>
  qspecl_then [‘sk’, ‘3’] mp_tac (Q.GENL [‘s0’, ‘lfdn’] live_inv) >> simp[] >>
  disch_then (qspec_then ‘N’ (drule o CONJUNCT2)) >> rw[] >> simp[]
QED

(* The trace up to any round is good *)
Theorem rounds_good[local]:
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ∧
  lbgrounds echo_sel [3w] echo_c.run sk n = SOME (kept, N, s) ⇒
  good 3w [] (FLAT (GENLIST (lbround_events echo_sel [3w] echo_c.run sk) n))
Proof
  strip_tac >> gvs[echo_sel_eq, secho_run] >>
  ‘(3w : word64) = n2w 3’ by simp[] >> pop_assum SUBST_ALL_TAC >>
  qspecl_then [‘sk’, ‘3’] mp_tac (Q.GENL [‘s0’, ‘lfdn’] trace_good) >>
  simp[] >> disch_then drule >> simp[]
QED

(* ------------------------------------------------------------------------
   The theorem
   ------------------------------------------------------------------------ *)

(* MAIN: the shipped blocking echo program meets QuietSpec *)
Theorem echo_blocking_quiet:
  echo_quiet 3w echo_blocking_main
Proof
  rw[echo_quiet_def, server_world_def] >>
  ‘echo_safe (poll_io [3w] echo_c.run sk)’
    by (simp[secho_run] >> irule echo_comp_safe >> simp[]) >>
  ‘wf echo_c.run ∧ quiet echo_c ∧ sel_covers echo_c echo_sel’
    by simp[wf_secho, quiet_secho, echo_sel_covers] >>
  ‘echo_live sk (poll_io [3w] echo_c.run sk)’
    by (qspecl_then [‘sk’, ‘3’] mp_tac (Q.GENL [‘s0’, ‘lfdn’] echo_live_rounds) >>
        simp[secho_run]) >>
  ‘semantics_dec_list (init_state (ssel_ffi sk)) init_env echo_blocking_main =
   semantics_prog (init_state (ssel_ffi sk)) init_env echo_blocking_main’
    by simp[MATCH_MP prog_syntax_ok_semantics echo_blocking_syntax_ok] >>
  ‘init_state (ssel_ffi sk) with ffi := select_ffi sk = init_state (select_ffi sk)’
    by simp[init_state_def, semanticPrimitivesTheory.state_component_equality] >>
  ‘(init_state (ssel_ffi sk)).ffi.io_events = [] ∧ (select_ffi sk).io_events = [] ∧
   (init_state (ssel_ffi sk)).ffi = ssel_ffi sk’
    by simp[init_state_def, ssel_ffi_def, select_ffi_def] >>
  qspec_then ‘sk’ mp_tac (Q.GEN ‘sk’ echo_blocking_semantics) >> simp[] >> strip_tac
  (* outcome 1: it runs forever *)
  >- (gvs[] >> qexists_tac ‘Diverge (lblock_io echo_sel [3w] echo_c.run sk)’ >>
      ‘∀i. lbround_events echo_sel [3w] echo_c.run sk i ≠ []’
        by (gen_tac >> irule lbround_events_nonempty >> simp[]) >>
      rpt conj_tac
      >- (qpat_x_assum ‘init_state _ with ffi := _ = _’ (SUBST1_TAC o SYM) >>
          irule semantics_prog_upto >> simp[] >>
          irule clock_ok >> simp[] >> gen_tac >>
          qpat_x_assum ‘semantics_prog _ _ _ (Diverge _)’ mp_tac >>
          simp[semanticsTheory.semantics_prog_def,
               lprefix_lubTheory.lprefix_lub_def, PULL_EXISTS] >>
          strip_tac >>
          qpat_x_assum ‘∀k. ∃ffi. _’ (qspec_then ‘k’ strip_assume_tac) >>
          qpat_x_assum ‘∀k. LPREFIX _ _’ (qspec_then ‘k’ mp_tac) >>
          qpat_assum ‘evaluate_prog_with_clock _ _ k _ = _’ (fn th => REWRITE_TAC[th]) >>
          simp[final_call_def, final_err_def] >> strip_tac >>
          drule_at Any LPREFIX_rounds >> simp[] >> strip_tac >>
          ‘∃kept N s. lbgrounds echo_sel [3w] echo_c.run sk n = SOME (kept, N, s)’
            by (qpat_x_assum ‘∀n. lbgrounds _ _ _ _ n ≠ NONE’ (qspec_then ‘n’ mp_tac) >>
                Cases_on ‘lbgrounds echo_sel [3w] echo_c.run sk n’ >> simp[] >>
                rename1 ‘SOME x’ >> PairCases_on ‘x’ >> simp[]) >>
          drule_all rounds_good >> strip_tac >>
          irule good_prefix >> first_assum (irule_at Any) >> simp[])
      >- (disj1_tac >> drule_all lblocking_echo_div >> simp[secho_run] >>
          disch_then (qspec_then ‘sk’ strip_assume_tac) >> gvs[secho_run])
      >> strip_tac >>
      qspecl_then [‘sk’, ‘3’] mp_tac (Q.GENL [‘s0’, ‘lfdn’] echo_sleeps) >> simp[] >>
      strip_tac >> gvs[GSYM echo_sel_eq, GSYM secho_run] >>
      qpat_x_assum ‘∀n. lbgrounds _ _ _ _ n ≠ NONE’ (qspec_then ‘SUC n’ mp_tac) >>
      simp[lbgrounds_def])
  (* outcome 2: it ends blocked forever in select *)
  >> gvs[] >> qmatch_asmsub_abbrev_tac ‘Terminate out io’ >>
  qexists_tac ‘Terminate out io’ >>
  ‘asleep (Terminate out io) io’ by simp[asleep_def, Abbr ‘out’] >>
  rpt conj_tac
  >- (qpat_x_assum ‘init_state _ with ffi := _ = _’ (SUBST1_TAC o SYM) >>
      irule semantics_prog_upto >> simp[] >>
      irule clock_ok >> simp[] >> gen_tac >>
      qpat_x_assum ‘semantics_prog _ _ _ (Terminate _ _)’ mp_tac >>
      simp[semanticsTheory.semantics_prog_def, Abbr ‘out’] >> strip_tac >>
      ‘r = Rerr (Rabort (Rffi_error (Final_event (ExtCall «sock_select»)
                                       (fds_bytes (echo_sel kept)) [] FFI_diverged)))’
        by (every_case_tac >> gvs[]) >>
      ‘ffi.io_events = FLAT (GENLIST (lbround_events echo_sel [3w] echo_c.run sk) n)’
        by fs[markerTheory.Abbrev_def] >>
      drule_all rounds_good >> strip_tac >>
      qpat_x_assum ‘r = _’ SUBST_ALL_TAC >>
      drule clocked_vs_terminating >> impl_tac >- simp[] >>
      disch_then (qspec_then ‘k’ strip_assume_tac)
      >- (qpat_x_assum ‘SND _ = _’ (fn th => REWRITE_TAC[th, final_call_simps, MEM]) >>
          irule good_prefix >> qexists_tac ‘ffi.io_events’ >> ASM_REWRITE_TAC[]) >>
      qpat_x_assum ‘evaluate_prog_with_clock _ _ k _ = _’
        (fn th => REWRITE_TAC[th, FST, SND, final_call_simps, MEM]) >>
      qpat_x_assum ‘ffi.io_events = _’ (fn th => REWRITE_TAC[th]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      REWRITE_TAC[PAIR_EQ] >> rpt strip_tac >>
      qpat_x_assum ‘c = _’ SUBST1_TAC >> REWRITE_TAC[bytes_fds_fds_bytes] >>
      drule_all stuck_select_ok >> REWRITE_TAC[])
  >- (disj2_tac >> qexists_tac ‘io’ >> simp[] >>
      drule_all lblocking_echo_stuck >> simp[secho_run] >>
      disch_then (qspec_then ‘sk’ strip_assume_tac) >> gvs[markerTheory.Abbrev_def, secho_run])
  >> strip_tac >> qexists_tac ‘io’ >> simp[]
QED
