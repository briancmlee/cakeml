(*
  The blocking HTTP program that selects on the live connections, end to
  end (as asyncM4LiveMain does for echo).

      fun main u = run_l ([3], [3], http_server_h demo_files 3)

  The world is asyncM4BlkMain's ssel_ffi (EchoSpec's socket world plus
  «sock_select»).

  MAIN:
  - http_blk_semantics: the program either diverges with the trace
    lblock_io, or ends in an FFI divergence of «sock_select» on the live
    fds after the finite trace of its first n rounds, having done
    everything the polling loop would ever do;
  - http_blk_spec: in both cases the trace is http_safe_h, and
    http_live_h whenever the polling loop's trace is (echo_live_spec's
    shape);
  - http_blk_spec_fair: in a fair world (sched_wf) the polling loop's
    trace is live (http_live_h_rounds), so both outcomes are safe and live.
  Caveat (design note 31 §4): a connection whose handler stopped on an
  invalid request stays in the live list; if its client then closes or
  sends more, select returns at once every round (busy polling).
  Correctness is unaffected.
*)
Theory asyncHttpBlkMain
Ancestors
  asyncCore asyncLevel1 asyncLevel2 asyncChoose asyncServer asyncCfActModel
  asyncCfActProg asyncM3World asyncM3Loop asyncM4GRounds asyncM4Loop
  asyncM4SockModel asyncM4SockServer asyncM4BlkWorld asyncM4BlkTrace
  asyncM4BlkLoop asyncM4BlkMain asyncM4BlkSelWorld asyncM4LiveEcho
  asyncM4LiveLoop asyncRunOkGen asyncHttpSafeH asyncHttpLiveH asyncHttpMain
  asyncHttpServerH asyncHttpServer2H asyncHttpLiveSel asyncHttpBlkTransfer
  asyncHttpBlkProg asyncHttpBlkSpec EchoSpec HttpSpec HttpSpecHeaders
  ffiSpikeSocketFFI ffiSpikeSocketFair ffiSpikeSocketWorld ffiSpikeDivMain
  ml_translator ml_prog cfMain cfDiv cfStore llist
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncHttpBlkProg"

Overload http_c = “shttp demo_files 3”
Overload http_sel = “lsel [3w] (shttp demo_files 3).run”

(* demo_files (asyncHttpMain's definition) is translated again in this program *)
val r = translate demo_files_def;

Quote add_cakeml:
  fun main u = run_l ([3], [3], http_server_h demo_files 3);
End

val st = get_ml_prog_state ();

Theorem http_sel_covers:
  sel_covers http_c http_sel
Proof
  ‘http_sel = sel_http demo_files 3’
    by simp[FUN_EQ_THM, lsel_def, sel_http_def, shttp_run] >>
  simp[] >> irule sel_covers_http >> simp[]
QED

Theorem http_grun_ok:
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ⇒
  grun_ok (interest [3w]) http_c.run sk
Proof
  strip_tac >> simp[shttp_run] >>
  irule gen_grun_ok >> simp[] >> qexists_tac ‘3’ >>
  simp[uses_ok_def, http_server_h_uses_accepted]
QED

Theorem main_lh_spec_div:
  limited_parts ssel_names p ∧
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ∧
  (∀n. lbgrounds http_sel [3w] http_c.run sk n ≠ NONE) ⇒
  app (p:'ffi ffi_proj) asyncHttpBlkMain$main_v [Conv NONE []] (SSEL sk [])
    (POSTd io. io = lblock_io http_sel [3w] http_c.run sk)
Proof
  strip_tac >>
  xcf_with_def (fetch "-" "main_v_def") >>
  xlet ‘POSTv cv. &COMP p SACT UNIT_TYPE SSNAP http_c.run cv * SSEL sk []’
  >- (xapp_spec shttp_server_h_spec >> xsimpl >> qexists_tac ‘demo_files’ >>
      simp[fetch "-" "demo_files_v_thm", shttp_run]) >>
  rpt (xlet_auto >- (xcon >> xsimpl)) >>
  rveq >> xapp_spec (run_l_spec |> Q.GEN ‘c’ |> Q.ISPEC ‘shttp demo_files 3’) >>
  simp[LIST_TYPE_def, NUM_def, INT_def, quiet_shttp, wf_shttp, http_sel_covers,
       http_grun_ok] >>
  metis_tac[]
QED

Theorem main_lh_spec_stuck:
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ∧
  lbgrounds http_sel [3w] http_c.run sk n = SOME (kept, N, s) ∧
  new_actions (log_of http_c.run) kept = [] ∧
  sock_wait (http_sel kept) s = NONE ⇒
  app (p:'ffi ffi_proj) asyncHttpBlkMain$main_v [Conv NONE []] (SSEL sk [])
    (POSTf nm. λcf b.
       &(nm = «sock_select» ∧ cf = fds_bytes (http_sel kept) ∧ b = []) *
       SSEL s (FLAT (GENLIST (lbround_events http_sel [3w] http_c.run sk) n)) *
       SEP_EXISTS av. W8ARRAY av [])
Proof
  strip_tac >>
  xcf_with_def (fetch "-" "main_v_def") >>
  xlet ‘POSTv cv. &COMP p SACT UNIT_TYPE SSNAP http_c.run cv * SSEL sk []’
  >- (xapp_spec shttp_server_h_spec >> xsimpl >> qexists_tac ‘demo_files’ >>
      simp[fetch "-" "demo_files_v_thm", shttp_run]) >>
  rpt (xlet_auto >- (xcon >> xsimpl)) >>
  rveq >> xapp_spec (run_l_stuck_spec |> Q.GEN ‘c’ |> Q.ISPEC ‘shttp demo_files 3’) >>
  simp[LIST_TYPE_def, NUM_def, INT_def, quiet_shttp, wf_shttp, http_sel_covers,
       http_grun_ok] >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------
   The whole program
   ------------------------------------------------------------------------ *)

val Decls_th =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> GEN_ALL |> ISPEC “ssel_ffi sk” |> SPEC_ALL;

val (_, decls_args) = strip_comb (concl Decls_th);
val decs_tm = List.nth (decls_args, 2);
val env2_tm = List.nth (decls_args, 3);
val st2_tm = List.nth (decls_args, 4);

val http_l_prog_def = new_definition ("http_l_prog_def",
  mk_eq (mk_var ("http_l_prog", type_of decs_tm), decs_tm));

val lookup_main = let
  val g = “nsLookup (^env2_tm).v (Short «main») = SOME asyncHttpBlkMain$main_v”
  in prove (g, REWRITE_TAC [fst (dest_eq g) |> nsLookup_conv]) end;

val st2_ffi = prove (“(^st2_tm).ffi = ssel_ffi sk”, EVAL_TAC);

(* MAIN: the program's two outcomes, in CakeML's semantics *)
Theorem http_blk_semantics:
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ⇒
  (∃io. semantics_dec_list (init_state (ssel_ffi sk)) init_env
          (SNOC (main_call «main») http_l_prog) (Diverge io) ∧
        (∀n. lbgrounds http_sel [3w] http_c.run sk n ≠ NONE) ∧
        io = lblock_io http_sel [3w] http_c.run sk) ∨
  (∃n kept N s.
     lbgrounds http_sel [3w] http_c.run sk n = SOME (kept, N, s) ∧
     new_actions (log_of http_c.run) kept = [] ∧
     sock_wait (http_sel kept) s = NONE ∧
     semantics_dec_list (init_state (ssel_ffi sk)) init_env
       (SNOC (main_call «main») http_l_prog)
       (Terminate (FFI_outcome (Final_event (ExtCall «sock_select»)
                                  (fds_bytes (http_sel kept)) []
                                  FFI_diverged))
                  (FLAT (GENLIST (lbround_events http_sel [3w] http_c.run sk) n))))
Proof
  strip_tac >>
  assume_tac (REWRITE_RULE [GSYM http_l_prog_def] Decls_th) >>
  assume_tac st2_ffi >>
  drule ssel_init_heap >> strip_tac >>
  Cases_on ‘∀n. lbgrounds http_sel [3w] http_c.run sk n ≠ NONE’
  >- (disj1_tac >> simp[] >>
      drule call_main_thm_div >>
      disch_then (qspecl_then [‘ssel_proj2’, ‘ssel_proj1’, ‘h2’, ‘h1’,
         ‘asyncHttpBlkMain$main_v’, ‘«main»’, ‘λio. io = lblock_io http_sel [3w] http_c.run sk’,
         ‘SSEL sk []’] mp_tac) >>
      impl_tac
      >- (simp [lookup_var_def, lookup_main] >>
          irule main_lh_spec_div >> simp [limited_parts_ssel]) >>
      simp [])
  >- (disj2_tac >>
      ‘∃n kept N s. lbgrounds http_sel [3w] http_c.run sk n = SOME (kept, N, s) ∧
                    new_actions (log_of http_c.run) kept = [] ∧
                    sock_wait (http_sel kept) s = NONE’
        by metis_tac[lbgrounds_two_outcomes] >>
      qexistsl [‘n’, ‘kept’, ‘N’, ‘s’] >> simp[] >>
      drule call_main_thm2_ffidiv >>
      disch_then (qspecl_then [‘ssel_proj2’, ‘ssel_proj1’, ‘h2’, ‘h1’,
         ‘asyncHttpBlkMain$main_v’, ‘«main»’,
         ‘λnm cf b. &(nm = «sock_select» ∧ cf = fds_bytes (http_sel kept) ∧
                      b = []) *
                    SSEL s (FLAT (GENLIST (lbround_events http_sel [3w] http_c.run sk) n)) *
                    SEP_EXISTS av. W8ARRAY av []’,
         ‘SSEL sk []’] mp_tac) >>
      impl_tac
      >- (simp [lookup_var_def, lookup_main] >>
          irule main_lh_spec_stuck >> simp [] >> metis_tac []) >>
      strip_tac >>
      fs [SEP_CLAUSES, SEP_EXISTS_THM, cond_STAR] >> rveq >>
      fs [GSYM STAR_ASSOC, cond_STAR] >> rveq >>
      qpat_x_assum ‘(_ * _) h3’ mp_tac >>
      simp [SSEL_def, STAR_def, one_def] >> strip_tac >>
      gvs [SPLIT_def, SPLIT3_def] >>
      ‘FFI_part (sockets_encode s) (mk_ffi_next ssel_ffi_part) ssel_names
         (FLAT (GENLIST (lbround_events http_sel [3w] http_c.run sk) n)) ∈
         st2heap (ssel_proj1, ssel_proj2) st3’
        by (qpat_x_assum ‘_ = st2heap _ st3’ (SUBST1_TAC o SYM) >> simp []) >>
      drule_at Any limited_FFI_part_IN_st2heap_IMP >>
      simp [limited_parts_ssel] >> strip_tac >>
      gvs [main_call_def])
QED

(* MAIN: in HttpSpecHeaders' terms (echo_live_spec's shape) *)
Theorem http_blk_spec:
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ⇒
  (∃io. semantics_dec_list (init_state (ssel_ffi sk)) init_env
          (SNOC (main_call «main») http_l_prog) (Diverge io) ∧
        http_safe_h demo_files io ∧
        (http_live_h demo_files sk (poll_io [3w] http_c.run sk) ⇒
         http_live_h demo_files sk io)) ∨
  (∃c io. semantics_dec_list (init_state (ssel_ffi sk)) init_env
            (SNOC (main_call «main») http_l_prog)
            (Terminate (FFI_outcome (Final_event (ExtCall «sock_select») c []
                                       FFI_diverged)) io) ∧
          http_safe_h demo_files (fromList io) ∧
          (http_live_h demo_files sk (poll_io [3w] http_c.run sk) ⇒
           http_live_h demo_files sk (fromList io)))
Proof
  strip_tac >>
  ‘http_safe_h demo_files (poll_io [3w] http_c.run sk)’
    by (simp[shttp_run] >>
        qspecl_then [‘sk’, ‘3’, ‘demo_files’, ‘interest [3w]’] mp_tac
          (Q.GENL [‘s0’, ‘lfdn’, ‘files’, ‘ifds’] http_comp_safe_h) >>
        simp[]) >>
  ‘wf http_c.run ∧ quiet http_c ∧ sel_covers http_c http_sel’
    by simp[wf_shttp, quiet_shttp, http_sel_covers] >>
  drule_all http_blk_semantics >> strip_tac
  >- (disj1_tac >> qexists_tac ‘io’ >> simp[] >>
      drule_all lblocking_http_div >> simp[])
  >- (disj2_tac >>
      qexistsl [‘fds_bytes (http_sel kept)’,
                ‘FLAT (GENLIST (lbround_events http_sel [3w] http_c.run sk) n)’] >>
      simp[] >> drule_all lblocking_http_stuck >> simp[])
QED

(* MAIN: in a fair world, both outcomes are safe and live *)
Theorem http_blk_spec_fair:
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ∧ sched_wf sk ⇒
  (∃io. semantics_dec_list (init_state (ssel_ffi sk)) init_env
          (SNOC (main_call «main») http_l_prog) (Diverge io) ∧
        http_safe_h demo_files io ∧ http_live_h demo_files sk io) ∨
  (∃c io. semantics_dec_list (init_state (ssel_ffi sk)) init_env
            (SNOC (main_call «main») http_l_prog)
            (Terminate (FFI_outcome (Final_event (ExtCall «sock_select») c []
                                       FFI_diverged)) io) ∧
          http_safe_h demo_files (fromList io) ∧
          http_live_h demo_files sk (fromList io))
Proof
  strip_tac >>
  ‘http_live_h demo_files sk (poll_io [3w] http_c.run sk)’
    by (simp[shttp_run] >>
        qspecl_then [‘sk’, ‘3’, ‘demo_files’] mp_tac
          (Q.GENL [‘s0’, ‘lfdn’, ‘files’] http_live_h_rounds) >>
        simp[]) >>
  drule_all http_blk_spec >> metis_tac[]
QED
