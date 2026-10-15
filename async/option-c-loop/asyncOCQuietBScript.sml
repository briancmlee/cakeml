(*
  Option C §2.5: the HTTP-bodies program on the select-on-interest loop
  meets QuietSpec's HTTP statement (assembly).

  - hb_acc: every fd the loop selects on is the listener or a connection
    the server has accepted (asyncOCAcc's proto_acc, through the socket
    relabelling and the polling run's transcript);
  - so its trace is good (trace_good_q), and QuietSpec's select world and
    #46's answer it alike (as for echo, asyncEchoQuiet);
  - safety and liveness are http_q_spec's; going to sleep is qsel_sleeps,
    given the server's stability after the last arrival (proto_stable,
    cf-actions, a hypothesis here until it lands).

  MAIN: hb_acc, http_q_quiet_b.
*)
Theory asyncOCQuietB
Ancestors
  pair list rich_list arithmetic option pred_set llist alist words
  ffi ffiSpikeSocketFFI ffiSpikeSocketFair asyncCore asyncLevel1 asyncLevel2
  asyncSched2 asyncTranscript asyncServer asyncM3World asyncM4Relabel
  asyncM4RelabelDist asyncM4SockModel asyncM4GRounds asyncM4GTrans
  asyncM4SockInv asyncM4Loop asyncM4BlkWorld asyncM4BlkTrace asyncM4BlkSelWorld
  asyncM4LiveServer asyncProto asyncProtoServer asyncProtoB asyncProtoV2
  asyncOCRelabel asyncOCProtoModel asyncOCFinite asyncOCSel asyncOCAcc
  asyncOCSleeps asyncOCTrace asyncOCSemB asyncOCTransfer asyncProtoViaB
  asyncStaticRounds HttpSpecBodies EchoSpec QuietSpec semantics evaluate
  evaluateProps ml_prog asyncM4BlkMain asyncEchoBridgeWorld asyncEchoQuietTrace
  asyncEchoQuiet ffiAgreeUpto
Libs
  preamble

Overload S2 = “proto_server_v2 idVu P_b (K (NONE : unit option))
                  (λr (k : unit option). resp_b r) 3”

Theorem MEM_wacc[local]:
  ∀ps. MEM (Accept l, Accepted (SOME c)) ps ⇒ MEM c (wacc ps)
Proof
  Induct >> simp[wacc_def, FORALL_PROD] >> rw[] >> simp[]
QED

Theorem waiting_on_srelabel2[local]:
  w ∈ waiting_on (srelabel2 c) h ⇔ Readable (w2n w) ∈ waiting_on c (MAP sfs h)
Proof
  simp[waiting_on_def, relabel2_def, relabel_def, sie_def] >> rw[]
QED

(* MAIN: the loop selects only on the listener and accepted connections *)
Theorem hb_acc:
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ∧
  lbgrounds hb_sel [3w] hb_c.run sk n = SOME (kept, N, s) ⇒
  ∀w. MEM w (hb_sel kept) ⇒
      w = 3w ∨ MEM w (wacc (gperf (interest [3w]) hb_c.run sk N))
Proof
  rpt strip_tac >>
  ‘wf hb_c.run ∧ quiet hb_c ∧ finite2 hb_c’ by simp[hb_ok] >>
  ‘lbinv hb_c [3w] sk kept N s’
    by (drule sel_covers_qsel >> strip_tac >> drule_all lbgrounds_inv >> simp[]) >>
  ‘FINITE (waiting_on hb_c kept)’ by gvs[finite2_def, waiting_on_def] >>
  ‘w ∈ waiting_on hb_c kept’ by metis_tac[set_qsel] >>
  ‘w ∈ waiting_on hb_c (ghist (interest [3w]) hb_c.run sk N)’
    by (gvs[lbinv_def] >>
        ‘waiting_on hb_c (ghist (interest [3w]) hb_c.run sk N) = waiting_on hb_c kept’
          suffices_by simp[] >>
        gvs[same_for_def, waiting_on_def] >>
        first_x_assum (qspec_then ‘[]’ mp_tac) >> simp[] >> rw[] >> gvs[]) >>
  qpat_x_assum ‘w ∈ waiting_on _ kept’ kall_tac >>
  gvs[waiting_on_srelabel2] >>
  qspecl_then [‘resp_b’, ‘3’] mp_tac
    (Q.GENL [‘resp’, ‘lfd’] (MATCH_MP proto_acc proto_ok_b)) >>
  simp[] >> disch_then drule >> strip_tac
  >- (disj1_tac >> ‘w = n2w (w2n w)’ by simp[] >> pop_assum SUBST1_TAC >> simp[])
  >> disj2_tac >>
  ‘∃l. MEM (Accept l, SOME (Accepted (w2n w)))
           (trans (proto_server P_b resp_b 3)
              (MAP sfs (ghist (interest [3w]) hb_c.run sk N)))’
    by (gvs[accs_def, LENGTH_NON_NIL, FILTER_NEQ_NIL] >>
        PairCases_on ‘x’ >> gvs[is_acc_def] >> metis_tac[]) >>
  qspecl_then [‘sfs’, ‘sfr’, ‘proto_server P_b resp_b 3’,
               ‘ghist (interest [3w]) hb_c.run sk N’, ‘sfa’]
    mp_tac (Q.GENL [‘fs’, ‘fr’, ‘m’, ‘h’, ‘fa’] trans_relabel) >>
  impl_tac >- simp[snap_map_def] >>
  strip_tac >>
  ‘MEM (sfa (Accept l), SOME (Accepted (w2n w)))
       (MAP (λ(a, r). (a, OPTION_MAP sfr r))
          (trans (srelabel (proto_server P_b resp_b 3))
             (ghist (interest [3w]) hb_c.run sk N)))’
    by (qpat_x_assum ‘MAP _ _ = MAP _ _’ (SUBST1_TAC o SYM) >>
        simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  gvs[MEM_MAP, EXISTS_PROD, sfa_def] >>
  qmatch_asmsub_rename_tac ‘Accepted _ = sfr z’ >>
  Cases_on ‘z’ >> gvs[sfr_def] >>
  TRY (rename1 ‘Got ro’ >> Cases_on ‘ro’ >> gvs[sfr_def] >> every_case_tac >>
       gvs[] >> NO_TAC) >>
  rename1 ‘Accepted ro’ >> Cases_on ‘ro’ >> gvs[sfr_def, w2n_11] >>
  ‘grun_ok (interest [3w]) hb_c.run sk’ by simp[hb_grun_ok] >>
  gvs[hb_run] >>
  drule trans_ghist >> disch_then (qspec_then ‘N’ assume_tac) >>
  gvs[MEM_MAP, EXISTS_PROD] >>
  irule MEM_wacc >> qexists_tac ‘n2w l’ >> gvs[w2n_11]
QED

(* ------------------------------------------------------------------------
   The server's stability after the last arrival (cf-actions' proto_stable,
   in the agreed shape; a hypothesis until it lands)
   ------------------------------------------------------------------------ *)

Definition PROTO_STABLE_def:
  PROTO_STABLE P resp ⇔
    ∀s0 lfdn.
      proto_ok P ∧ s0.listeners = [(n2w lfdn, [])] ∧ s0.conns = [] ∧
      lfdn < dimword (:64) ∧ sched_wf s0 ∧ arrivals_finite s0 ⇒
      ∃n1. ∀n. n1 ≤ n ⇒
        gacts (EI lfdn) (srelabel (proto_server P resp lfdn)) s0 n = [] ∧
        ∀x. Readable x ∈
              waiting_on (proto_server_v2 idVu P (K (NONE : unit option))
                            (λr (k : unit option). resp r) lfdn)
                (MAP sfs (ghist (EI lfdn) (srelabel (proto_server P resp lfdn)) s0 n)) ⇒
            ¬is_ready (gstate (EI lfdn) (srelabel (proto_server P resp lfdn)) s0 n)
                      (n2w x)
End

(* With it, the loop goes to sleep in a world where only finitely many
   things arrive *)
Theorem hb_sleeps:
  PROTO_STABLE P_b resp_b ∧
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ∧ sched_wf sk ∧ arrivals_finite sk ⇒
  ∃n kept N s. lbgrounds hb_sel [3w] hb_c.run sk n = SOME (kept, N, s) ∧
               new_actions (log_of hb_c.run) kept = [] ∧
               sock_wait (hb_sel kept) s = NONE
Proof
  rw[PROTO_STABLE_def] >>
  first_x_assum (qspecl_then [‘sk’, ‘3’] mp_tac) >> simp[proto_ok_b] >>
  strip_tac >>
  qspecl_then [‘sk’, ‘interest [3w]’, ‘hb_c.run’] mp_tac
    (Q.GENL [‘s0’, ‘ifds’, ‘m’] static_after) >>
  simp[] >> strip_tac >>
  irule qsel_sleeps >> simp[hb_ok] >>
  conj_tac >- metis_tac[] >>
  qexists_tac ‘n1’ >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> simp[hb_run] >> strip_tac >> simp[] >>
  rpt strip_tac >> gvs[waiting_on_srelabel2] >>
  first_x_assum drule >> simp[]
QED

(* ------------------------------------------------------------------------
   The program in QuietSpec's world
   ------------------------------------------------------------------------ *)

Overload http_q_main = “SNOC (main_call «main») http_q_prog”

Theorem http_q_syntax_ok:
  prog_syntax_ok http_q_main
Proof
  REWRITE_TAC [http_q_prog_def, prog_syntax_ok_def] >> EVAL_TAC
QED

Theorem final_call_len[local]:
  LENGTH (final_call r) ≤ 1
Proof
  rw[final_call_def, final_err_def] >> every_case_tac >> simp[] >>
  TRY (rename1 ‘final_ffi fe’ >> Cases_on ‘fe’ >> simp[final_ffi_def])
QED

Theorem clock_ok[local]:
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ∧
  (∀k. good 3w [] (FST (evaluate_prog_with_clock (init_state (ssel_ffi sk)) init_env k
                          http_q_main)).io_events ∧
       ∀n c b. MEM (n, c, b) (final_call (SND (evaluate_prog_with_clock
                                (init_state (ssel_ffi sk)) init_env k http_q_main))) ∧
               n = ExtCall «sock_select» ⇒
               EVERY (λfd. fd = 3w ∨
                           MEM fd (accs_of (FST (evaluate_prog_with_clock
                                     (init_state (ssel_ffi sk)) init_env k http_q_main)).io_events))
                     (bytes_fds c)) ⇒
  ∀k. agree_upto (clock_calls (init_state (ssel_ffi sk)) init_env http_q_main k)
                 (ssel_ffi sk) (select_ffi sk)
Proof
  rpt strip_tac >> simp[agree_upto_def] >> rpt strip_tac >>
  first_x_assum (qspec_then ‘k’ strip_assume_tac) >>
  Cases_on ‘evaluate_prog_with_clock (init_state (ssel_ffi sk)) init_env k http_q_main’ >>
  rename1 ‘_ = (ffik, rk)’ >> gvs[] >>
  ‘RTC call_FFI_rel (ssel_ffi sk) ffik’
    by (gvs[evaluate_prog_with_clock_def] >> pairarg_tac >> gvs[] >>
        qspecl_then [‘init_state (ssel_ffi sk) with clock := k’, ‘init_env’, ‘http_q_main’]
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

Theorem hb_trace[local]:
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ∧
  lbgrounds hb_sel [3w] hb_c.run sk n = SOME (kept, N, s) ⇒
  good 3w [] (FLAT (GENLIST (lbround_events hb_sel [3w] hb_c.run sk) n)) ∧
  accs_of (FLAT (GENLIST (lbround_events hb_sel [3w] hb_c.run sk) n)) =
  wacc (gperf (interest [3w]) hb_c.run sk N)
Proof
  strip_tac >>
  qspecl_then [‘hb_c’, ‘[3w]’, ‘sk’, ‘3w’] mp_tac
    (Q.GENL [‘c’, ‘fds0’, ‘s0’, ‘L’] trace_good_q) >>
  simp[hb_ok, hb_grun_ok] >>
  impl_tac >- (rpt strip_tac >> drule_all hb_acc >> simp[]) >>
  disch_then drule >> simp[]
QED

Theorem stuck_select_ok[local]:
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ∧
  lbgrounds hb_sel [3w] hb_c.run sk n = SOME (kept, N, s) ⇒
  EVERY (λfd. fd = 3w ∨
              MEM fd (accs_of (FLAT (GENLIST (lbround_events hb_sel [3w] hb_c.run sk) n))))
        (hb_sel kept)
Proof
  strip_tac >> drule_all hb_trace >> strip_tac >> simp[EVERY_MEM] >>
  rpt strip_tac >> drule_all hb_acc >> simp[]
QED

Theorem resp_b_o[local]:
  print_response o bhandle files = (λr. print_response (bhandle files r))
Proof
  simp[FUN_EQ_THM]
QED

Theorem LPREFIX_rounds_q[local]:
  (∀i. f i ≠ []) ∧
  LPREFIX (fromList evs) (LFLATTEN (LGENLIST (λi. fromList (f i)) NONE)) ⇒
  ∃n. evs ≼ FLAT (GENLIST f n)
Proof
  strip_tac >> drule_all LPREFIX_rounds_between >> metis_tac[]
QED

(* MAIN: the HTTP-bodies program on the select-on-interest loop meets
   QuietSpec, given the server's stability (PROTO_STABLE) *)
Theorem http_q_quiet_b:
  PROTO_STABLE P_b resp_b ⇒ http_quiet_b 3w demo_files http_q_main
Proof
  rw[http_quiet_b_def, server_world_def] >>
  ‘wf hb_c.run ∧ quiet hb_c ∧ sel_covers hb_c hb_sel’
    by simp[hb_ok, sel_covers_qsel] >>
  ‘proto_safe P_b resp_b (poll_io [3w] hb_c.run sk)’ by simp[hb_poll_safe] >>
  ‘proto_live P_b resp_b sk (poll_io [3w] hb_c.run sk)’ by simp[hb_poll_live] >>
  ‘semantics_dec_list (init_state (ssel_ffi sk)) init_env http_q_main =
   semantics_prog (init_state (ssel_ffi sk)) init_env http_q_main’
    by simp[MATCH_MP prog_syntax_ok_semantics http_q_syntax_ok] >>
  ‘init_state (ssel_ffi sk) with ffi := select_ffi sk = init_state (select_ffi sk)’
    by simp[init_state_def, semanticPrimitivesTheory.state_component_equality] >>
  ‘(init_state (ssel_ffi sk)).ffi.io_events = [] ∧ (select_ffi sk).io_events = [] ∧
   (init_state (ssel_ffi sk)).ffi = ssel_ffi sk’
    by simp[init_state_def, ssel_ffi_def, select_ffi_def] >>
  simp[http_safe_b_proto, http_live_b_proto, resp_b_o] >>
  qspec_then ‘sk’ mp_tac (Q.GEN ‘sk’ http_q_semantics) >> simp[] >> strip_tac
  (* outcome 1: it runs forever *)
  >- (gvs[] >> qexists_tac ‘Diverge (lblock_io hb_sel [3w] hb_c.run sk)’ >>
      ‘∀i. lbround_events hb_sel [3w] hb_c.run sk i ≠ []’
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
          drule_at Any LPREFIX_rounds_q >> simp[] >> strip_tac >>
          ‘∃kept N s. lbgrounds hb_sel [3w] hb_c.run sk n = SOME (kept, N, s)’
            by (qpat_x_assum ‘∀n. lbgrounds _ _ _ _ n ≠ NONE’ (qspec_then ‘n’ mp_tac) >>
                Cases_on ‘lbgrounds hb_sel [3w] hb_c.run sk n’ >> simp[] >>
                rename1 ‘SOME x’ >> PairCases_on ‘x’ >> simp[]) >>
          drule_all hb_trace >> strip_tac >>
          irule good_prefix >> first_assum (irule_at Any) >> simp[])
      >- (disj1_tac >> simp[] >> conj_tac
          >- (irule (cj 1 (SIMP_RULE bool_ss [IMP_CONJ_THM, AND_IMP_INTRO]
                             lblocking_proto_div)) >> simp[])
          >> irule (cj 2 (SIMP_RULE bool_ss [IMP_CONJ_THM, AND_IMP_INTRO]
                            lblocking_proto_div)) >> simp[])
      >> strip_tac >>
      drule_all hb_sleeps >> strip_tac >>
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
                                       (fds_bytes (hb_sel kept)) [] FFI_diverged)))’
        by (every_case_tac >> gvs[]) >>
      ‘ffi.io_events = FLAT (GENLIST (lbround_events hb_sel [3w] hb_c.run sk) n)’
        by fs[markerTheory.Abbrev_def] >>
      drule_all hb_trace >> strip_tac >>
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
  >- (disj2_tac >> qexists_tac ‘io’ >> gvs[markerTheory.Abbrev_def] >> conj_tac
      >- (irule (cj 1 (SIMP_RULE bool_ss [IMP_CONJ_THM, AND_IMP_INTRO]
                         lblocking_proto_stuck)) >> simp[] >> metis_tac[])
      >> irule (cj 2 (SIMP_RULE bool_ss [IMP_CONJ_THM, AND_IMP_INTRO]
                        lblocking_proto_stuck)) >> simp[] >> metis_tac[])
  >> strip_tac >> qexists_tac ‘io’ >> simp[]
QED
