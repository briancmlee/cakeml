(*
  The proxy binary's whole-program semantics on the honest L0 world:
  proxy_prog a b hw is proxyMain's declarations, then

    val main = fn u => proxy_main a b hw

  then the call main ().  From a startup world w0, its behaviour is one of
  proxy_main's three outcomes (proxyMain): stdio closed (Terminate after the
  three fdok events), the listen on a failed (Terminate after it), or E1's
  rounds forever (Diverge).  This is the program of
  l0_proxy_claim pf_sendwait hw a b (proxy_prog a b hw).
*)
Theory proxySem
Ancestors
  ml_translator ml_prog cfMain cfDiv cfStore llist std_prelude
  honestL0 honestL0World honestL0Part honestL0Proof
  ffiSpikeDivMain e1DriverLoop e1DriverMain moonshotProxy proxyMain e1Lemmas
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "proxyMain";

(* ------------------------------------------------------------------------
   The program
   ------------------------------------------------------------------------ *)

val proxy_decs_tm =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> concl |> strip_comb |> snd |> (fn args => List.nth (args, 2));

Definition proxy_decs_def:
  proxy_decs = ^proxy_decs_tm
End

(* proxy_main a b hw, the arguments literals *)
Definition proxy_main_body_def:
  proxy_main_body (a : num) (b : num) (hw : num) =
    App Opapp [App Opapp [App Opapp [Var (Short «proxy_main»); Lit (IntLit (&a))];
                          Lit (IntLit (&b))];
               Lit (IntLit (&hw))]
End

Definition proxy_main_dec_def:
  proxy_main_dec a b hw = Dlet NoLocs (Pvar «main») (Fun «u» (proxy_main_body a b hw))
End

Definition proxy_prog_def:
  proxy_prog a b hw = SNOC (main_call «main») (proxy_decs ++ [proxy_main_dec a b hw])
End

(* ------------------------------------------------------------------------
   The declarations, then main
   ------------------------------------------------------------------------ *)

val Decls_th =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> GEN_ALL |> ISPEC “l0_ffi w0” |> SPEC_ALL
  |> REWRITE_RULE [GSYM proxy_decs_def];

val (_, decls_args) = strip_comb (concl Decls_th);
val env2_tm = List.nth (decls_args, 3);
val st2_tm = List.nth (decls_args, 4);

Overload PROXY_ENV = “^env2_tm”
Overload PROXY_ST = “λw0. ^st2_tm”
Overload MAIN_ENV = “merge_env PROXY_ENV init_env”
Overload MAIN_CLOS = “λa b hw. Closure MAIN_ENV «u» (proxy_main_body a b hw)”

val lookup_proxy_main = let
  val g = “nsLookup (^env2_tm).v (Short «proxy_main») = SOME proxy_main_v”
  in prove (g, REWRITE_TAC [fst (dest_eq g) |> nsLookup_conv]) end;

val st2_ffi = prove (“(^st2_tm).ffi = l0_ffi w0”, EVAL_TAC);

Theorem proxy_Decls:
  Decls init_env (init_state (l0_ffi w0)) (proxy_decs ++ [proxy_main_dec a b hw])
    (merge_env (write «main» (MAIN_CLOS a b hw) empty_env) PROXY_ENV) (PROXY_ST w0)
Proof
  simp[Decls_APPEND] >>
  qexistsl [‘PROXY_ENV’, ‘write «main» (MAIN_CLOS a b hw) empty_env’, ‘PROXY_ST w0’] >>
  simp[Decls_th, proxy_main_dec_def, Decls_Dlet, eval_rel_def, evaluateTheory.evaluate_def] >>
  qexists_tac ‘MAIN_CLOS a b hw’ >> simp[] >> qexistsl [‘0’, ‘0’] >> simp[]
QED

Theorem lookup_main:
  lookup_var «main» (merge_env (write «main» (MAIN_CLOS a b hw) empty_env) PROXY_ENV) =
    SOME (MAIN_CLOS a b hw)
Proof
  simp[lookup_var_def, merge_env_def, ml_progTheory.write_def, empty_env_def,
       namespacePropsTheory.nsLookup_nsAppend_some]
QED

Overload MAIN_ARGS = “λa b hw. [Litv (IntLit (&a)); Litv (IntLit (&b)); Litv (IntLit (&hw))]”

(* main () is proxy_main a b hw *)
Theorem main_app:
  app p proxy_main_v (MAIN_ARGS a b hw) H Q ⇒
  app (p:'ffi ffi_proj) (MAIN_CLOS a b hw) [Conv NONE []] H Q
Proof
  strip_tac >>
  ‘MAIN_CLOS a b hw = naryClosure MAIN_ENV [«u»] (proxy_main_body a b hw)’
    by simp[naryClosure_def, naryFun_def] >>
  pop_assum SUBST1_TAC >> irule app_of_cf >> simp[proxy_main_body_def] >>
  simp[Once cf_def, dest_opapp_def, cf_app_def] >> irule local_elim >> simp[] >>
  simp[exp2v_def, exp2v_list_def, extend_env_def, merge_env_def,
       namespacePropsTheory.nsLookup_nsAppend_some, lookup_proxy_main] >>
  qexists_tac ‘proxy_main_v’ >>
  simp[extend_env_v_def, namespacePropsTheory.nsLookup_nsAppend_some, lookup_proxy_main]
QED

Theorem proxy_prog_syntax_ok:
  prog_syntax_ok (proxy_prog a b hw)
Proof
  REWRITE_TAC [proxy_prog_def, proxy_decs_def, proxy_main_dec_def, proxy_main_body_def,
               main_call_def, prog_syntax_ok_def, listTheory.SNOC_APPEND, listTheory.APPEND] >>
  EVAL_TAC
QED

(* proxy_main returns: the program terminates with its events *)
Theorem proxy_term_semantics:
  l0_rely w0 ∧ w0.hist = [] ∧
  app (l0_proj w0) proxy_main_v (MAIN_ARGS a b hw) (L0_EV w0 w0 [])
    (POSTv v. &UNIT_TYPE () v * L0_EV w0 w' evs) ⇒
  semantics_prog (init_state (l0_ffi w0)) init_env (proxy_prog a b hw)
    (Terminate Success evs)
Proof
  strip_tac >>
  simp[GSYM (MATCH_MP prog_syntax_ok_semantics proxy_prog_syntax_ok)] >>
  assume_tac proxy_Decls >>
  drule call_main_thm2 >>
  Cases_on ‘l0_proj w0’ >> rename1 ‘l0_proj w0 = (pj1, pj2)’ >>
  assume_tac st2_ffi >> drule l0_init_heap >> simp[] >> strip_tac >>
  disch_then (qspecl_then [‘pj2’, ‘pj1’, ‘h2’, ‘h1’, ‘MAIN_CLOS a b hw’, ‘«main»’,
                           ‘L0_EV w0 w' evs’, ‘L0_EV w0 w0 []’] mp_tac) >>
  impl_tac
  >- (simp[lookup_main, FFI_part_hprop_L0_EV] >> irule main_app >> gvs[]) >>
  strip_tac >>
  ‘limited_parts l0_names (pj1,pj2)’ by metis_tac[limited_parts_l0] >>
  qpat_x_assum ‘L0_EV _ _ _ h3’ mp_tac >>
  simp[L0_EV_def, STAR_def, one_def, cond_def, SPLIT_def] >> strip_tac >>
  ‘FFI_part (l0_enc w0 w') (l0_next w0) l0_names evs ∈ st2heap (pj1,pj2) st3’
    by (gvs[SPLIT3_def, EXTENSION] >> metis_tac[]) >>
  drule_all limited_FFI_part_IN_st2heap_IMP >> strip_tac >>
  gvs[proxy_prog_def, main_call_def]
QED

(* proxy_main diverges: the program diverges with its events *)
Theorem proxy_div_semantics:
  l0_rely w0 ∧ w0.hist = [] ∧
  app (l0_proj w0) proxy_main_v (MAIN_ARGS a b hw) (L0_EV w0 w0 []) (POSTd io'. io' = io) ⇒
  semantics_prog (init_state (l0_ffi w0)) init_env (proxy_prog a b hw) (Diverge io)
Proof
  strip_tac >>
  simp[GSYM (MATCH_MP prog_syntax_ok_semantics proxy_prog_syntax_ok)] >>
  assume_tac proxy_Decls >>
  drule call_main_thm_div >>
  Cases_on ‘l0_proj w0’ >> rename1 ‘l0_proj w0 = (pj1, pj2)’ >>
  assume_tac st2_ffi >> drule l0_init_heap >> simp[] >> strip_tac >>
  disch_then (qspecl_then [‘pj2’, ‘pj1’, ‘h2’, ‘h1’, ‘MAIN_CLOS a b hw’, ‘«main»’,
                           ‘λio'. io' = io’, ‘L0_EV w0 w0 []’] mp_tac) >>
  impl_tac
  >- (simp[lookup_main] >> irule main_app >> gvs[]) >>
  rw[proxy_prog_def, main_call_def] >> gvs[]
QED

(* A proxy_main spec on the literal arguments *)
fun lit_args th =
  Q.INST [‘av’ |-> ‘Litv (IntLit (&a))’, ‘bv’ |-> ‘Litv (IntLit (&b))’,
          ‘hwv’ |-> ‘Litv (IntLit (&hw))’] th;

Theorem main_args_types[local]:
  NUM a (Litv (IntLit (&a)))
Proof
  simp[NUM_def, INT_def]
QED

(* ------------------------------------------------------------------------
   The program's three outcomes
   ------------------------------------------------------------------------ *)

(* stdin, stdout or stderr closed: the three fdok events, then stop *)
Theorem proxy_closed_semantics:
  l0_rely w0 ∧ w0.hist = [] ∧
  FDOK3 w0 w1 w2 w3 o0 o1 o2 e0 e1 e2 ∧ ¬fdok_all o0 o1 o2 ⇒
  semantics_prog (init_state (l0_ffi w0)) init_env (proxy_prog a b hw)
    (Terminate Success [e0; e1; e2])
Proof
  strip_tac >> irule proxy_term_semantics >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexists_tac ‘w3’ >> BETA_TAC >> irule (lit_args proxy_main_closed_spec) >> simp[main_args_types] >>
  qexistsl [‘o0’, ‘o1’, ‘o2’, ‘w1’, ‘w2’] >> simp[]
QED

(* The listen on a failed: the fdok events and the listen, then stop *)
Theorem proxy_nolisten_semantics:
  l0_rely w0 ∧ w0.hist = [] ∧
  FDOK3 w0 w1 w2 w3 o0 o1 o2 e0 e1 e2 ∧ fdok_all o0 o1 o2 ∧
  sys_listen_port a w3 = SOME (out, w4, ev) ∧ listen_fd out = NONE ⇒
  semantics_prog (init_state (l0_ffi w0)) init_env (proxy_prog a b hw)
    (Terminate Success [e0; e1; e2; ev])
Proof
  strip_tac >> irule proxy_term_semantics >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexists_tac ‘w4’ >> BETA_TAC >> irule (lit_args proxy_main_nolisten_spec) >> simp[main_args_types] >>
  qexistsl [‘o0’, ‘o1’, ‘o2’, ‘out’, ‘w1’, ‘w2’, ‘w3’] >> simp[]
QED

(* The listen on a succeeded: the fdok events, the listen, then E1's rounds
   forever *)
Theorem proxy_div_n_semantics:
  l0_rely w0 ∧ w0.hist = [] ∧
  FDOK3 w0 w1 w2 w3 o0 o1 o2 e0 e1 e2 ∧ fdok_all o0 o1 o2 ∧
  sys_listen_port a w3 = SOME (out, w4, ev) ∧ listen_fd out = SOME k ∧
  (∀n. erounds (n2w k) pol_never (pifds (n2w k) b hw) (pprog (n2w k) b hw) (w4, einit) n ≠ NONE) ⇒
  semantics_prog (init_state (l0_ffi w0)) init_env (proxy_prog a b hw)
    (Diverge (LAPPEND (fromList [e0; e1; e2; ev]) (LFLATTEN (LGENLIST
       (λi. fromList (eround_evs (n2w k) pol_never (pifds (n2w k) b hw) (pprog (n2w k) b hw)
                                 (w4, einit) i)) NONE))))
Proof
  strip_tac >> irule proxy_div_semantics >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  BETA_TAC >> irule (lit_args proxy_main_div_spec) >> simp[main_args_types, limited_parts_l0, l0_reach_init] >>
  qexistsl [‘o0’, ‘o1’, ‘o2’, ‘out’, ‘w1’, ‘w2’, ‘w3’] >> simp[]
QED
