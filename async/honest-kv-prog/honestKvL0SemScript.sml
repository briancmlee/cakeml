(*
  The KV program's whole-program semantics on the honest L0 world (P4
  step F): from the startup world w0, the program first calls sys_fdok on
  fds 0, 1 and 2 (D33).  If one is closed, it terminates after those
  three events.  Otherwise listening on the KV port either fails, and the
  program terminates after four events, or succeeds, and the program
  diverges with those four events then the prefetching L1 loop's rounds
  with the KV server.  (honestEchoL0Sem's argument, for kv_l0_prog.)
*)
Theory honestKvL0Sem
Ancestors
  ml_translator ml_prog cfMain cfDiv cfStore llist std_prelude
  honestL0 honestL0World honestL0Rely honestL1Model honestL0WorldProps honestL0Part honestL0Proof honestL1PFSpec
  honestL1MainProg honestL1MainSpec honestL1MainWorld honestKvL0Prog honestKvL0Main ffiSpikeDivMain honestL0Fdok honestL1PFRefine
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "honestKvL0Prog";

(* The program's declarations, and the whole program *)
val kv_l0_decs_tm =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> concl |> strip_comb |> snd |> (fn args => List.nth (args, 2));

Definition kv_l0_decs_def:
  kv_l0_decs = ^kv_l0_decs_tm
End

Definition kv_l0_prog_def:
  kv_l0_prog = SNOC (main_call «main») kv_l0_decs
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
  |> REWRITE_RULE [GSYM kv_l0_decs_def];

val (_, decls_args) = strip_comb (concl Decls_th);
val env2_tm = List.nth (decls_args, 3);
val st2_tm = List.nth (decls_args, 4);

val lookup_main = let
  val g = “nsLookup (^env2_tm).v (Short «main») = SOME main_v”
  in prove (g, REWRITE_TAC [fst (dest_eq g) |> nsLookup_conv]) end;

val st2_ffi = prove (“(^st2_tm).ffi = l0_ffi w0”, EVAL_TAC);

(* sys_fdok always returns *)
Theorem fdok_SOME:
  ∃out w1 ev. l0_do «sys_fdok» [f] 1 w = SOME (out, w1, ev)
Proof
  simp[fdok_do]
QED

(* main returns with the events evs: the program terminates with them *)
Theorem kv_l0_term_semantics[local]:
  l0_rely w0 ∧ w0.hist = [] ∧
  (∀uv. UNIT_TYPE () uv ⇒
        app (l0_proj w0) main_v [uv] (L0_EV w0 w0 [])
          (POSTv v. &UNIT_TYPE () v * L0_EV w0 w1 evs)) ⇒
  semantics_dec_list (init_state (l0_ffi w0)) init_env kv_l0_prog
    (Terminate Success evs)
Proof
  strip_tac >> assume_tac Decls_th >>
  drule call_main_thm2 >>
  Cases_on ‘l0_proj w0’ >> rename1 ‘l0_proj w0 = (pj1, pj2)’ >>
  assume_tac st2_ffi >> drule l0_init_heap >> simp[] >> strip_tac >>
  disch_then (qspecl_then [‘pj2’, ‘pj1’, ‘h2’, ‘h1’, ‘main_v’, ‘«main»’,
                           ‘L0_EV w0 w1 evs’, ‘L0_EV w0 w0 []’] mp_tac) >>
  impl_tac
  >- (gvs[lookup_var_def, lookup_main, FFI_part_hprop_L0_EV] >>
      first_x_assum irule >> simp[UNIT_TYPE_def]) >>
  strip_tac >>
  ‘limited_parts l0_names (pj1,pj2)’ by metis_tac[limited_parts_l0] >>
  qpat_x_assum ‘L0_EV _ _ _ h3’ mp_tac >>
  simp[L0_EV_def, STAR_def, one_def, cond_def, SPLIT_def] >> strip_tac >>
  ‘FFI_part (l0_enc w0 w1) (l0_next w0) l0_names evs ∈ st2heap (pj1,pj2) st3’
    by (gvs[SPLIT3_def, EXTENSION] >> metis_tac[]) >>
  drule_all limited_FFI_part_IN_st2heap_IMP >> strip_tac >>
  gvs[kv_l0_prog_def, main_call_def]
QED

(* The stdio fds are open and the listen succeeds with a small listener
   fd: the program diverges with the four events, then the prefetching L1
   loop's rounds *)
Theorem kv_l0_div_semantics:
  l0_rely w0 ∧ w0.hist = [] ∧
  l0_do «sys_fdok» [0w] 1 w0 = SOME (o0, w1, e0) ∧
  l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1) ∧
  l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2) ∧ l1_stdio_all o0 o1 o2 ∧
  sys_listen_at kv_port_conf w3 = SOME (out, w4, ev) ∧ l1_listen_fd out = SOME k ∧ k < 2147483648 ⇒
  semantics_dec_list (init_state (l0_ffi w0)) init_env kv_l0_prog
    (Diverge (LAPPEND (fromList [e0; e1; e2; ev]) (kv_l0_run k w4)))
Proof
  strip_tac >> assume_tac Decls_th >>
  drule call_main_thm_div >>
  Cases_on ‘l0_proj w0’ >> rename1 ‘l0_proj w0 = (pj1, pj2)’ >>
  assume_tac st2_ffi >> drule l0_init_heap >> simp[] >> strip_tac >>
  disch_then (qspecl_then [‘pj2’, ‘pj1’, ‘h2’, ‘h1’, ‘main_v’, ‘«main»’,
                           ‘λio. io = LAPPEND (fromList [e0; e1; e2; ev]) (kv_l0_run k w4)’,
                           ‘L0_EV w0 w0 []’] mp_tac) >>
  impl_tac
  >- (gvs[lookup_var_def, lookup_main] >>
      irule (SIMP_RULE (srw_ss()) [] kv_main_div_spec) >> simp[UNIT_TYPE_def, l0_reach_init] >>
      metis_tac[limited_parts_l0]) >>
  rw[kv_l0_prog_def, main_call_def] >> gvs[]
QED

Theorem kv_l0_prog_eq =
  REWRITE_CONV [kv_l0_prog_def, kv_l0_decs_def, main_call_def,
                listTheory.SNOC_APPEND, listTheory.APPEND] “kv_l0_prog”;

Theorem kv_l0_prog_syntax_ok:
  prog_syntax_ok kv_l0_prog
Proof
  REWRITE_TAC [kv_l0_prog_eq, prog_syntax_ok_def] >> EVAL_TAC
QED

(* MAIN (P3 semantics): from a startup world, the program calls sys_fdok
   on fds 0, 1 and 2; if one is closed it terminates after the three
   events.  Else it listens; if that fails it terminates after the four
   events, else it diverges with the four events then the prefetching L1
   loop's rounds, running the KV server on the returned listener fd k *)
Theorem kv_l0_semantics_prog:
  l0_rely w0 ∧ w0.hist = [] ⇒
  ∃o0 w1 e0 o1 w2 e1 o2 w3 e2.
    l0_do «sys_fdok» [0w] 1 w0 = SOME (o0, w1, e0) ∧
    l0_do «sys_fdok» [1w] 1 w1 = SOME (o1, w2, e1) ∧
    l0_do «sys_fdok» [2w] 1 w2 = SOME (o2, w3, e2) ∧
    ((¬l1_stdio_all o0 o1 o2 ∧
      semantics_prog (init_state (l0_ffi w0)) init_env kv_l0_prog
        (Terminate Success [e0; e1; e2])) ∨
     (l1_stdio_all o0 o1 o2 ∧
      ∃out w4 ev.
        sys_listen_at kv_port_conf w3 = SOME (out, w4, ev) ∧
        ((l1_listen_fd out = NONE ∧
          semantics_prog (init_state (l0_ffi w0)) init_env kv_l0_prog
            (Terminate Success [e0; e1; e2; ev])) ∨
         (∃k. l1_listen_fd out = SOME k ∧
              semantics_prog (init_state (l0_ffi w0)) init_env kv_l0_prog
                (Diverge (LAPPEND (fromList [e0; e1; e2; ev]) (kv_l0_run k w4)))))))
Proof
  strip_tac >>
  qspecl_then [‘0w’, ‘w0’] strip_assume_tac (Q.GENL [‘f’, ‘w’] fdok_SOME) >>
  rename1 ‘l0_do _ _ _ w0 = SOME (o0, w1, e0)’ >>
  qspecl_then [‘1w’, ‘w1’] strip_assume_tac (Q.GENL [‘f’, ‘w’] fdok_SOME) >>
  rename1 ‘l0_do _ _ _ w1 = SOME (o1, w2, e1)’ >>
  qspecl_then [‘2w’, ‘w2’] strip_assume_tac (Q.GENL [‘f’, ‘w’] fdok_SOME) >>
  rename1 ‘l0_do _ _ _ w2 = SOME (o2, w3, e2)’ >>
  qexistsl [‘o0’, ‘w1’, ‘e0’, ‘o1’, ‘w2’, ‘e1’, ‘o2’, ‘w3’, ‘e2’] >> simp[] >>
  simp[GSYM (MATCH_MP prog_syntax_ok_semantics kv_l0_prog_syntax_ok)] >>
  Cases_on ‘l1_stdio_all o0 o1 o2’ >> simp[]
  >- (‘l0_rely w3’ by metis_tac[l0_do_rely] >>
      qspec_then ‘w3’ strip_assume_tac (Q.GEN ‘w’ (MATCH_MP sys_listen_at_SOME kv_port_conf_len)) >>
      qexistsl [‘out’, ‘w1'’, ‘ev’] >> simp[] >>
      Cases_on ‘l1_listen_fd out’ >> simp[]
      >- (irule kv_l0_term_semantics >> simp[] >> qexists_tac ‘w1'’ >>
          rpt strip_tac >> irule kv_main_fail_spec >> simp[] >> metis_tac[]) >>
      irule (SIMP_RULE (srw_ss()) [] kv_l0_div_semantics) >> simp[] >>
      metis_tac[l1_listen_fd_small, kv_port_conf_len]) >>
  irule kv_l0_term_semantics >> simp[] >> qexists_tac ‘w3’ >>
  rpt strip_tac >> irule kv_main_stdio_spec >> simp[] >> metis_tac[]
QED
