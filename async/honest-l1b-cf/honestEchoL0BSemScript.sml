(*
  The blocking echo program's whole-program semantics on the honest L0
  world: from the startup world w0, listening on the port either fails
  (the program terminates after that one event), or succeeds, and then
  the blocking L1 loop either never sleeps (the program diverges with the
  listen event then the loop's rounds) or sleeps in round n (the program
  stops in the final blocking poll, FFI_diverged, after the listen event
  and the rounds' events before that poll).
  As honestEchoL0Sem, with the third outcome.

  MAIN: echo_l0b_semantics_prog.
*)
Theory honestEchoL0BSem
Ancestors
  ml_translator ml_prog cfMain cfDiv cfStore llist std_prelude
  honestL0 honestL0World honestL0Rely honestL1Model honestL0WorldProps honestL0Part honestL0Proof
  honestL1PFSpec honestEchoL0Prog honestEchoL0Main honestEchoL0Sem ffiSpikeDivMain
  honestL1Inv honestL1PFModel honestL1PFInv
  honestL1BModel honestL1BSpec honestEchoL0BProg honestEchoL0BMain
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "honestEchoL0BProg";

(* The program's declarations, and the whole program *)
val echo_l0b_decs_tm =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> concl |> strip_comb |> snd |> (fn args => List.nth (args, 2));

Definition echo_l0b_decs_def:
  echo_l0b_decs = ^echo_l0b_decs_tm
End

Definition echo_l0b_prog_def:
  echo_l0b_prog = SNOC (main_call «main») echo_l0b_decs
End

Theorem FFI_part_hprop_L0_EV[local]:
  FFI_part_hprop (L0_EV w0 w evs)
Proof
  simp[L0_EV_def] >> irule FFI_part_hprop_STAR >> disj1_tac >>
  simp[FFI_part_hprop_def, one_def]
QED

val Decls_th =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> GEN_ALL |> ISPEC “l0_ffi w0” |> SPEC_ALL
  |> REWRITE_RULE [GSYM echo_l0b_decs_def];

val (_, decls_args) = strip_comb (concl Decls_th);
val env2_tm = List.nth (decls_args, 3);
val st2_tm = List.nth (decls_args, 4);

val lookup_main = let
  val g = “nsLookup (^env2_tm).v (Short «main») = SOME main_v”
  in prove (g, REWRITE_TAC [fst (dest_eq g) |> nsLookup_conv]) end;

val st2_ffi = prove (“(^st2_tm).ffi = l0_ffi w0”, EVAL_TAC);

(* The listen fails: the program terminates after the one event *)
Theorem echo_l0b_fail_semantics:
  l0_rely w0 ∧ w0.hist = [] ∧
  sys_listen_echo w0 = SOME (out, w1, ev) ∧ listen_fd out = NONE ⇒
  semantics_dec_list (init_state (l0_ffi w0)) init_env echo_l0b_prog
    (Terminate Success [ev])
Proof
  strip_tac >> assume_tac Decls_th >>
  drule call_main_thm2 >>
  Cases_on ‘l0_proj w0’ >> rename1 ‘l0_proj w0 = (pj1, pj2)’ >>
  assume_tac st2_ffi >> drule l0_init_heap >> simp[] >> strip_tac >>
  disch_then (qspecl_then [‘pj2’, ‘pj1’, ‘h2’, ‘h1’, ‘main_v’, ‘«main»’,
                           ‘L0_EV w0 w1 [ev]’, ‘L0_EV w0 w0 []’] mp_tac) >>
  impl_tac
  >- (gvs[lookup_var_def, lookup_main, FFI_part_hprop_L0_EV] >>
      irule main_fail_spec >> simp[UNIT_TYPE_def] >> metis_tac[]) >>
  strip_tac >>
  ‘limited_parts l0_names (pj1,pj2)’ by metis_tac[limited_parts_l0] >>
  qpat_x_assum ‘L0_EV _ _ _ h3’ mp_tac >>
  simp[L0_EV_def, STAR_def, one_def, cond_def, SPLIT_def] >> strip_tac >>
  ‘FFI_part (l0_enc w0 w1) (l0_next w0) l0_names [ev] ∈ st2heap (pj1,pj2) st3’
    by (gvs[SPLIT3_def, EXTENSION] >> metis_tac[]) >>
  drule_all limited_FFI_part_IN_st2heap_IMP >> strip_tac >>
  gvs[echo_l0b_prog_def, main_call_def]
QED

(* The listen succeeds and the loop never sleeps: the program diverges *)
Theorem echo_l0b_div_semantics:
  l0_rely w0 ∧ w0.hist = [] ∧
  sys_listen_echo w0 = SOME (out, w1, ev) ∧ listen_fd out = SOME k ∧ k < 2147483648 ∧
  bt_awake (n2w k) echo_hw (asyncM4LiveInterest$live [n2w k] (log_of (srelabel (server k)))) (srelabel (server k)) (w1, pinit) ⇒
  semantics_dec_list (init_state (l0_ffi w0)) init_env echo_l0b_prog
    (Diverge (LCONS ev (echo_l0b_run k w1)))
Proof
  strip_tac >> assume_tac Decls_th >>
  drule call_main_thm_div >>
  Cases_on ‘l0_proj w0’ >> rename1 ‘l0_proj w0 = (pj1, pj2)’ >>
  assume_tac st2_ffi >> drule l0_init_heap >> simp[] >> strip_tac >>
  disch_then (qspecl_then [‘pj2’, ‘pj1’, ‘h2’, ‘h1’, ‘main_v’, ‘«main»’,
                           ‘λio. io = LCONS ev (echo_l0b_run k w1)’,
                           ‘L0_EV w0 w0 []’] mp_tac) >>
  impl_tac
  >- (gvs[lookup_var_def, lookup_main] >>
      irule (SIMP_RULE (srw_ss()) [] main_div_spec) >> simp[UNIT_TYPE_def, l0_reach_init] >>
      metis_tac[limited_parts_l0]) >>
  rw[echo_l0b_prog_def, main_call_def] >> gvs[]
QED

(* The listen succeeds and the loop sleeps in round n: the program stops in
   the final blocking poll *)
Theorem echo_l0b_sleep_semantics:
  l0_rely w0 ∧ w0.hist = [] ∧
  sys_listen_echo w0 = SOME (out, w1, ev) ∧ listen_fd out = SOME k ∧ k < 2147483648 ∧
  echo_b_rounds k w1 n = SOME (BSlept h evs cb) ⇒
  semantics_dec_list (init_state (l0_ffi w0)) init_env echo_l0b_prog
    (Terminate (FFI_outcome (Final_event (ExtCall «sys_poll») (FST cb) (SND cb) FFI_diverged))
               (ev :: evs))
Proof
  strip_tac >> assume_tac Decls_th >>
  drule call_main_thm2_ffidiv >>
  Cases_on ‘l0_proj w0’ >> rename1 ‘l0_proj w0 = (pj1, pj2)’ >>
  assume_tac st2_ffi >> drule l0_init_heap >> simp[] >> strip_tac >>
  disch_then (qspecl_then [‘pj2’, ‘pj1’, ‘h2’, ‘h1’, ‘main_v’, ‘«main»’,
                           ‘λnm c b. &(nm = «sys_poll» ∧ (c, b) = cb) *
                                     (SEP_EXISTS w2. L0_EV w0 w2 ([ev] ++ evs)) * GC’,
                           ‘L0_EV w0 w0 []’] mp_tac) >>
  impl_tac
  >- (gvs[lookup_var_def, lookup_main] >>
      irule (SIMP_RULE (srw_ss()) [] main_sleep_spec) >> simp[UNIT_TYPE_def, l0_reach_init] >>
      metis_tac[limited_parts_l0]) >>
  strip_tac >>
  ‘limited_parts l0_names (pj1,pj2)’ by metis_tac[limited_parts_l0] >>
  qpat_x_assum ‘_ h3’ mp_tac >>
  simp[L0_EV_def, STAR_def, one_def, cond_def, SPLIT_def, SEP_EXISTS_THM, GC_def] >>
  strip_tac >>
  ‘FFI_part (l0_enc w0 w2) (l0_next w0) l0_names ([ev] ++ evs) ∈ st2heap (pj1,pj2) st3’
    by (gvs[SPLIT3_def, EXTENSION] >> metis_tac[]) >>
  drule_all limited_FFI_part_IN_st2heap_IMP >> strip_tac >>
  Cases_on ‘cb’ >> gvs[echo_l0b_prog_def, main_call_def]
QED

Theorem echo_l0b_prog_eq =
  REWRITE_CONV [echo_l0b_prog_def, echo_l0b_decs_def, main_call_def,
                listTheory.SNOC_APPEND, listTheory.APPEND] “echo_l0b_prog”;

Theorem echo_l0b_prog_syntax_ok:
  prog_syntax_ok echo_l0b_prog
Proof
  REWRITE_TAC [echo_l0b_prog_eq, prog_syntax_ok_def] >> EVAL_TAC
QED

(* The blocking loop, from the world after the listen, either never
   sleeps or sleeps in some round *)
Theorem echo_b_awake_or_sleeps:
  l0_rely w0 ∧ w0.hist = [] ∧ sys_listen_echo w0 = SOME (out, w1, ev) ∧ k < 2147483648 ⇒
  bt_awake (n2w k) echo_hw (asyncM4LiveInterest$live [n2w k] (log_of (srelabel (server k)))) (srelabel (server k)) (w1, pinit) ∨
  ∃n h evs cb. echo_b_rounds k w1 n = SOME (BSlept h evs cb)
Proof
  strip_tac >>
  ‘l0_reach w0 w1’
    by (‘l0_reach w0 w0’ by simp[l0_reach_init] >>
        gvs[sys_listen_echo_def, l0_do_def, AllCaseEqs()] >> metis_tac[l0_reach_step]) >>
  ‘l0_rely w1’ by fs[l0_reach_def] >>
  ‘psmall (n2w k) pinit’
    by simp[psmall_def, pinit_def, l1init_def, small_fds_def, small_def] >>
  ‘∀n. ∃r. echo_b_rounds k w1 n = SOME r ∧
           ∀h w ps evs logs. r = BRun h (w, ps) evs logs ⇒ l0_rely w ∧ psmall (n2w k) ps’
    by (irule brounds_t_total >> simp[server_bt_ok]) >>
  Cases_on ‘∃n h evs cb. echo_b_rounds k w1 n = SOME (BSlept h evs cb)’ >> simp[] >>
  fs[bt_awake_def] >> gen_tac >>
  qpat_x_assum ‘∀n. ∃r. _’ (qspec_then ‘n’ strip_assume_tac) >>
  Cases_on ‘r’ >> fs[] >> metis_tac[]
QED

(* MAIN: from a startup world, the program listens; if that fails it
   terminates after the one event; else it runs the blocking L1 loop with
   the echo server on the returned listener fd k, and either diverges
   (the loop never sleeps) with the listen event then the loop's rounds,
   or stops in the final blocking poll (the loop sleeps in round n) after
   the listen event and the rounds' events before that poll *)
Theorem echo_l0b_semantics_prog:
  l0_rely w0 ∧ w0.hist = [] ⇒
  ∃out w1 ev.
    sys_listen_echo w0 = SOME (out, w1, ev) ∧
    ((listen_fd out = NONE ∧
      semantics_prog (init_state (l0_ffi w0)) init_env echo_l0b_prog (Terminate Success [ev])) ∨
     (∃k. listen_fd out = SOME k ∧
          ((bt_awake (n2w k) echo_hw (asyncM4LiveInterest$live [n2w k] (log_of (srelabel (server k)))) (srelabel (server k)) (w1, pinit) ∧
            semantics_prog (init_state (l0_ffi w0)) init_env echo_l0b_prog
              (Diverge (LCONS ev (echo_l0b_run k w1)))) ∨
           (∃n h evs cb.
              echo_b_rounds k w1 n = SOME (BSlept h evs cb) ∧
              semantics_prog (init_state (l0_ffi w0)) init_env echo_l0b_prog
                (Terminate (FFI_outcome (Final_event (ExtCall «sys_poll») (FST cb) (SND cb)
                                           FFI_diverged)) (ev :: evs))))))
Proof
  strip_tac >>
  qspec_then ‘w0’ strip_assume_tac (Q.GEN ‘w’ sys_listen_echo_SOME) >>
  simp[GSYM (MATCH_MP prog_syntax_ok_semantics echo_l0b_prog_syntax_ok)] >>
  Cases_on ‘listen_fd out’ >> simp[]
  >- (irule echo_l0b_fail_semantics >> simp[] >> metis_tac[]) >>
  rename1 ‘listen_fd out = SOME k’ >>
  ‘k < 2147483648’ by metis_tac[listen_fd_small] >>
  qspecl_then [‘w0’, ‘out’, ‘w1’, ‘ev’, ‘k’] mp_tac (Q.GENL [‘w0’, ‘out’, ‘w1’, ‘ev’, ‘k’] echo_b_awake_or_sleeps) >>
  simp[] >> strip_tac
  >- (disj1_tac >> simp[] >> irule echo_l0b_div_semantics >> simp[] >> metis_tac[]) >>
  disj2_tac >> qexistsl [‘n’, ‘h’, ‘evs’, ‘cb’] >> simp[] >>
  irule echo_l0b_sleep_semantics >> simp[] >> metis_tac[]
QED
