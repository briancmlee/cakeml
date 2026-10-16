(*
  The echo program's whole-program semantics on the honest L0 world (P3):
  from the startup world w0, listening on the port either fails, and the
  program terminates after that one event, or succeeds, and the program
  diverges with that event then the prefetching L1 loop's rounds.
*)
Theory honestEchoL0Sem
Ancestors
  ml_translator ml_prog cfMain cfDiv cfStore llist std_prelude
  honestL0 honestL0World honestL1Model honestL0Part honestL0Proof honestL1PFSpec
  honestEchoL0Prog honestEchoL0Main ffiSpikeDivMain
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "honestEchoL0Prog";

(* The program's declarations, and the whole program *)
val echo_l0_decs_tm =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> concl |> strip_comb |> snd |> (fn args => List.nth (args, 2));

Definition echo_l0_decs_def:
  echo_l0_decs = ^echo_l0_decs_tm
End

Definition echo_l0_prog_def:
  echo_l0_prog = SNOC (main_call «main») echo_l0_decs
End

(* ------------------------------------------------------------------------
   The L0 world as the program's only FFI part
   ------------------------------------------------------------------------ *)

Theorem limited_parts_l0:
  limited_parts l0_names (l0_proj w0)
Proof
  simp[limited_parts_def, l0_proj_def]
QED

Theorem l0_part_in_heap[local]:
  st.ffi = l0_ffi w0 ∧ parts_ok st.ffi (l0_proj w0) ⇒
  FFI_part (l0_enc w0 w0) (l0_next w0) l0_names [] ∈ st2heap (l0_proj w0) st
Proof
  strip_tac >> gvs[st2heap_def, l0_proj_def, ffi2heap_def] >>
  simp[l0_ffi_def, l0_names_def] >>
  disj2_tac >> rw[FUPDATE_LIST_THM, FLOOKUP_UPDATE]
QED

(* The initial heap holds the L0 part with no events *)
Theorem l0_init_heap:
  st.ffi = l0_ffi w0 ∧ l0_rely w0 ∧ w0.hist = [] ⇒
  ∃h1 h2. SPLIT (st2heap (l0_proj w0) st) (h1,h2) ∧ L0_EV w0 w0 [] h1
Proof
  strip_tac >>
  ‘parts_ok st.ffi (l0_proj w0)’ by simp[l0_parts_ok] >>
  drule_all l0_part_in_heap >> strip_tac >>
  qexistsl [‘{FFI_part (l0_enc w0 w0) (l0_next w0) l0_names []}’,
            ‘st2heap (l0_proj w0) st DIFF {FFI_part (l0_enc w0 w0) (l0_next w0) l0_names []}’] >>
  simp[L0_EV_def, l0_reach_init, SEP_CLAUSES, one_def] >>
  rw[SPLIT_def, EXTENSION, IN_DISJOINT] >> metis_tac[]
QED

Theorem FFI_part_hprop_L0_EV[local]:
  FFI_part_hprop (L0_EV w0 w evs)
Proof
  simp[L0_EV_def] >> irule FFI_part_hprop_STAR >> disj1_tac >>
  simp[FFI_part_hprop_def, one_def]
QED

(* ------------------------------------------------------------------------
   The whole program
   ------------------------------------------------------------------------ *)

val Decls_th =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> GEN_ALL |> ISPEC “l0_ffi w0” |> SPEC_ALL
  |> REWRITE_RULE [GSYM echo_l0_decs_def];

val (_, decls_args) = strip_comb (concl Decls_th);
val env2_tm = List.nth (decls_args, 3);
val st2_tm = List.nth (decls_args, 4);

val lookup_main = let
  val g = “nsLookup (^env2_tm).v (Short «main») = SOME main_v”
  in prove (g, REWRITE_TAC [fst (dest_eq g) |> nsLookup_conv]) end;

val st2_ffi = prove (“(^st2_tm).ffi = l0_ffi w0”, EVAL_TAC);

(* sys_listen always returns *)
Theorem sys_listen_echo_SOME:
  ∃out w1 ev. sys_listen_echo w = SOME (out, w1, ev)
Proof
  simp[sys_listen_echo_def, l0_do_def, l0_ffi_fn_def, l0_call_def,
       echo_port_conf_def, l0_hdr_def] >>
  every_case_tac >> gvs[]
QED

(* The listen fails: the program terminates after the one event *)
Theorem echo_l0_fail_semantics:
  l0_rely w0 ∧ w0.hist = [] ∧
  sys_listen_echo w0 = SOME (out, w1, ev) ∧ listen_fd out = NONE ⇒
  semantics_dec_list (init_state (l0_ffi w0)) init_env echo_l0_prog
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
  gvs[echo_l0_prog_def, main_call_def]
QED

(* The listen succeeds with a small listener fd: the program diverges with
   the listen event, then the prefetching L1 loop's rounds *)
Theorem echo_l0_div_semantics:
  l0_rely w0 ∧ w0.hist = [] ∧
  sys_listen_echo w0 = SOME (out, w1, ev) ∧ listen_fd out = SOME k ∧ k < 2147483648 ⇒
  semantics_dec_list (init_state (l0_ffi w0)) init_env echo_l0_prog
    (Diverge (LCONS ev (echo_l0_run k w1)))
Proof
  strip_tac >> assume_tac Decls_th >>
  drule call_main_thm_div >>
  Cases_on ‘l0_proj w0’ >> rename1 ‘l0_proj w0 = (pj1, pj2)’ >>
  assume_tac st2_ffi >> drule l0_init_heap >> simp[] >> strip_tac >>
  disch_then (qspecl_then [‘pj2’, ‘pj1’, ‘h2’, ‘h1’, ‘main_v’, ‘«main»’,
                           ‘λio. io = LCONS ev (echo_l0_run k w1)’,
                           ‘L0_EV w0 w0 []’] mp_tac) >>
  impl_tac
  >- (gvs[lookup_var_def, lookup_main] >>
      irule (SIMP_RULE (srw_ss()) [] main_div_spec) >> simp[UNIT_TYPE_def, l0_reach_init] >>
      metis_tac[limited_parts_l0]) >>
  rw[echo_l0_prog_def, main_call_def] >> gvs[]
QED
