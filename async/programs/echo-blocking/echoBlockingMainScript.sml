(*
  The blocking echo program that selects on the live connections, end to
  end (as echoSelectMain, for run_l).

      fun main u = run_l ([3], [3], server 3)

  The loop's interest list starts as [3] (the listener), and so does its
  live list.  The world is echoSelectMain's ssel_ffi (EchoSpec's socket
  world plus «sock_select»).

  MAIN:
  - echo_blocking_semantics: the program either diverges with the trace
    lblock_io, or ends in an FFI divergence of «sock_select» on the live
    fds after the finite trace of its first n rounds, having done
    everything the polling loop would ever do;
  - echo_blocking_spec: in both cases the trace is echo_safe, and echo_live
    whenever the polling loop's trace is.
  No hypothesis beyond the initial world.
*)
Theory echoBlockingMain
Ancestors
  asyncCore asyncLevel1 asyncChoose echoServer libModel
  libProg loopPollWorld loopPoll loopRounds loopPollDyn
  echoSockModel echoSockServer echoRunOk echoSafe
  loopSelectWorld loopSelectTrace echoSelectIdle loopSelect
  echoSelectMain loopSelectSet echoBlockingSet echoBlockingProg EchoSpec
  socketWorld composedWorld divMain
  ml_translator ml_prog cfMain cfDiv cfStore llist
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "echoBlockingProg"

Overload echo_c = “secho 3”
Overload echo_sel = “lsel [3w] (secho 3).run”

Quote add_cakeml:
  fun main u = run_l ([3], [3], server 3);
End

val st = get_ml_prog_state ();

Theorem echo_sel_covers:
  sel_covers echo_c echo_sel
Proof
  ‘echo_sel = sel_echo 3’ by simp[FUN_EQ_THM, lsel_def, sel_echo_def, secho_run] >>
  simp[] >> irule sel_covers_echo >> simp[]
QED

Theorem main_l_spec_div:
  limited_parts ssel_names p ∧
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ∧
  (∀n. lbgrounds echo_sel [3w] echo_c.run sk n ≠ NONE) ⇒
  app (p:'ffi ffi_proj) main_v [Conv NONE []] (SSEL sk [])
    (POSTd io. io = lblock_io echo_sel [3w] echo_c.run sk)
Proof
  strip_tac >>
  xcf_with_def (fetch "-" "main_v_def") >>
  xlet ‘POSTv cv. &COMP p SACT UNIT_TYPE SSNAP echo_c.run cv * SSEL sk []’
  >- (xapp_spec sserver_spec >> xsimpl >> simp[NUM_def, INT_def, secho_run]) >>
  rpt (xlet_auto >- (xcon >> xsimpl)) >>
  rveq >> xapp_spec (run_l_spec |> Q.GEN ‘c’ |> Q.ISPEC ‘secho 3’) >>
  simp[LIST_TYPE_def, NUM_def, INT_def, quiet_secho, wf_secho, echo_sel_covers] >>
  TRY (conj_tac >- (simp[secho_run] >> irule echo_grun_ok >> simp[])) >>
  metis_tac[]
QED

Theorem main_l_spec_stuck:
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ∧
  lbgrounds echo_sel [3w] echo_c.run sk n = SOME (kept, N, s) ∧
  new_actions (log_of echo_c.run) kept = [] ∧
  sock_wait (echo_sel kept) s = NONE ⇒
  app (p:'ffi ffi_proj) main_v [Conv NONE []] (SSEL sk [])
    (POSTf nm. λcf b.
       &(nm = «sock_select» ∧ cf = fds_bytes (echo_sel kept) ∧ b = []) *
       SSEL s (FLAT (GENLIST (lbround_events echo_sel [3w] echo_c.run sk) n)) *
       SEP_EXISTS av. W8ARRAY av [])
Proof
  strip_tac >>
  xcf_with_def (fetch "-" "main_v_def") >>
  xlet ‘POSTv cv. &COMP p SACT UNIT_TYPE SSNAP echo_c.run cv * SSEL sk []’
  >- (xapp_spec sserver_spec >> xsimpl >> simp[NUM_def, INT_def, secho_run]) >>
  rpt (xlet_auto >- (xcon >> xsimpl)) >>
  rveq >> xapp_spec (run_l_stuck_spec |> Q.GEN ‘c’ |> Q.ISPEC ‘secho 3’) >>
  simp[LIST_TYPE_def, NUM_def, INT_def, quiet_secho, wf_secho, echo_sel_covers] >>
  TRY (conj_tac >- (simp[secho_run] >> irule echo_grun_ok >> simp[])) >>
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

val echo_blocking_prog_def = new_definition ("echo_blocking_prog_def",
  mk_eq (mk_var ("echo_blocking_prog", type_of decs_tm), decs_tm));

val lookup_main = let
  val g = “nsLookup (^env2_tm).v (Short «main») = SOME main_v”
  in prove (g, REWRITE_TAC [fst (dest_eq g) |> nsLookup_conv]) end;

val st2_ffi = prove (“(^st2_tm).ffi = ssel_ffi sk”, EVAL_TAC);

(* MAIN: the program's two outcomes, in CakeML's semantics *)
Theorem echo_blocking_semantics:
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ⇒
  (∃io. semantics_dec_list (init_state (ssel_ffi sk)) init_env
          (SNOC (main_call «main») echo_blocking_prog) (Diverge io) ∧
        (∀n. lbgrounds echo_sel [3w] echo_c.run sk n ≠ NONE) ∧
        io = lblock_io echo_sel [3w] echo_c.run sk) ∨
  (∃n kept N s.
     lbgrounds echo_sel [3w] echo_c.run sk n = SOME (kept, N, s) ∧
     new_actions (log_of echo_c.run) kept = [] ∧
     sock_wait (echo_sel kept) s = NONE ∧
     semantics_dec_list (init_state (ssel_ffi sk)) init_env
       (SNOC (main_call «main») echo_blocking_prog)
       (Terminate (FFI_outcome (Final_event (ExtCall «sock_select»)
                                  (fds_bytes (echo_sel kept)) []
                                  FFI_diverged))
                  (FLAT (GENLIST (lbround_events echo_sel [3w] echo_c.run sk) n))))
Proof
  strip_tac >>
  assume_tac (REWRITE_RULE [GSYM echo_blocking_prog_def] Decls_th) >>
  assume_tac st2_ffi >>
  drule ssel_init_heap >> strip_tac >>
  Cases_on ‘∀n. lbgrounds echo_sel [3w] echo_c.run sk n ≠ NONE’
  >- (disj1_tac >> simp[] >>
      drule call_main_thm_div >>
      disch_then (qspecl_then [‘ssel_proj2’, ‘ssel_proj1’, ‘h2’, ‘h1’,
         ‘main_v’, ‘«main»’, ‘λio. io = lblock_io echo_sel [3w] echo_c.run sk’,
         ‘SSEL sk []’] mp_tac) >>
      impl_tac
      >- (simp [lookup_var_def, lookup_main] >>
          irule main_l_spec_div >> simp [limited_parts_ssel]) >>
      simp [])
  >- (disj2_tac >>
      ‘∃n kept N s. lbgrounds echo_sel [3w] echo_c.run sk n = SOME (kept, N, s) ∧
                    new_actions (log_of echo_c.run) kept = [] ∧
                    sock_wait (echo_sel kept) s = NONE’
        by metis_tac[lbgrounds_two_outcomes] >>
      qexistsl [‘n’, ‘kept’, ‘N’, ‘s’] >> simp[] >>
      drule call_main_thm2_ffidiv >>
      disch_then (qspecl_then [‘ssel_proj2’, ‘ssel_proj1’, ‘h2’, ‘h1’,
         ‘main_v’, ‘«main»’,
         ‘λnm cf b. &(nm = «sock_select» ∧ cf = fds_bytes (echo_sel kept) ∧
                      b = []) *
                    SSEL s (FLAT (GENLIST (lbround_events echo_sel [3w] echo_c.run sk) n)) *
                    SEP_EXISTS av. W8ARRAY av []’,
         ‘SSEL sk []’] mp_tac) >>
      impl_tac
      >- (simp [lookup_var_def, lookup_main] >>
          irule main_l_spec_stuck >> simp [] >> metis_tac []) >>
      strip_tac >>
      fs [SEP_CLAUSES, SEP_EXISTS_THM, cond_STAR] >> rveq >>
      fs [GSYM STAR_ASSOC, cond_STAR] >> rveq >>
      qpat_x_assum ‘(_ * _) h3’ mp_tac >>
      simp [SSEL_def, STAR_def, one_def] >> strip_tac >>
      gvs [SPLIT_def, SPLIT3_def] >>
      ‘FFI_part (sockets_encode s) (mk_ffi_next ssel_ffi_part) ssel_names
         (FLAT (GENLIST (lbround_events echo_sel [3w] echo_c.run sk) n)) ∈
         st2heap (ssel_proj1, ssel_proj2) st3’
        by (qpat_x_assum ‘_ = st2heap _ st3’ (SUBST1_TAC o SYM) >> simp []) >>
      drule_at Any limited_FFI_part_IN_st2heap_IMP >>
      simp [limited_parts_ssel] >> strip_tac >>
      gvs [main_call_def])
QED

(* MAIN: in EchoSpec's terms *)
Theorem echo_blocking_spec:
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ⇒
  (∃io. semantics_dec_list (init_state (ssel_ffi sk)) init_env
          (SNOC (main_call «main») echo_blocking_prog) (Diverge io) ∧
        echo_safe io ∧
        (echo_live sk (poll_io [3w] echo_m sk) ⇒ echo_live sk io)) ∨
  (∃c io. semantics_dec_list (init_state (ssel_ffi sk)) init_env
            (SNOC (main_call «main») echo_blocking_prog)
            (Terminate (FFI_outcome (Final_event (ExtCall «sock_select») c []
                                       FFI_diverged)) io) ∧
          echo_safe (fromList io) ∧
          (echo_live sk (poll_io [3w] echo_m sk) ⇒ echo_live sk (fromList io)))
Proof
  strip_tac >>
  ‘echo_safe (poll_io [3w] echo_c.run sk)’
    by (simp[secho_run] >> irule echo_comp_safe >> simp[]) >>
  ‘wf echo_c.run ∧ quiet echo_c ∧ sel_covers echo_c echo_sel’
    by simp[wf_secho, quiet_secho, echo_sel_covers] >>
  drule_all echo_blocking_semantics >> strip_tac
  >- (disj1_tac >> qexists_tac ‘io’ >> simp[] >>
      drule_all lblocking_echo_div >> simp[secho_run])
  >- (disj2_tac >>
      qexistsl [‘fds_bytes (echo_sel kept)’,
                ‘FLAT (GENLIST (lbround_events echo_sel [3w] echo_c.run sk) n)’] >>
      simp[] >> drule_all lblocking_echo_stuck >> simp[secho_run])
QED
