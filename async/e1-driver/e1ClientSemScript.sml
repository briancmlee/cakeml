(*
  The moonshot client binary's whole-program semantics on the honest L0
  world: client_prog a c N rqs is e1ClientProg's declarations, then

    val main = fn u => client_main c a N "<lits_enc of the requests>"

  then the call main ().  From a startup world w0, its behaviour is one of
  client_main's four outcomes (e1ClientMain): stdio closed (Terminate after
  the three fdok events), the listen on c failed (Terminate after it), the
  client finished after n rounds (Terminate), or it never finishes
  (Diverge).

  The request bytes are one string literal, decoded by lits_dec at startup
  (e1Lits): CF evaluates only literals and variables as arguments
  (exp2v), so a literal list of byte lists would need a chain of lets.
*)
Theory e1ClientSem
Ancestors
  ml_translator ml_prog cfMain cfDiv cfStore llist std_prelude
  honestL0 honestL0World honestL0Part honestL0Proof
  ffiSpikeDivMain e1DriverLoop e1DriverMain moonshotClient e1Lits e1ClientProg e1ClientMain
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "e1ClientProg";

(* ------------------------------------------------------------------------
   The program
   ------------------------------------------------------------------------ *)

val client_decs_tm =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> concl |> strip_comb |> snd |> (fn args => List.nth (args, 2));

Definition client_decs_def:
  client_decs = ^client_decs_tm
End

(* client_main c a N s, the arguments literals *)
Definition client_main_body_def:
  client_main_body a c (N : num) rqs =
    App Opapp [App Opapp [App Opapp [App Opapp [Var (Short «client_main»);
                                                Lit (IntLit (&c))];
                                     Lit (IntLit (&a))];
                          Lit (IntLit (&N))];
               Lit (StrLit (CLITS N rqs))]
End

Definition client_main_dec_def:
  client_main_dec a c N rqs =
    Dlet NoLocs (Pvar «main») (Fun «u» (client_main_body a c N rqs))
End

Definition client_prog_def:
  client_prog a c N rqs =
    SNOC (main_call «main») (client_decs ++ [client_main_dec a c N rqs])
End

(* ------------------------------------------------------------------------
   The L0 world as the program's only FFI part (copies of honestEchoL0Sem's
   lemmas, outside this directory's INCLUDES; to merge into a shared theory)
   ------------------------------------------------------------------------ *)

Theorem limited_parts_l0[local]:
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

Theorem l0_init_heap[local]:
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
   The declarations, then main
   ------------------------------------------------------------------------ *)

val Decls_th =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> GEN_ALL |> ISPEC “l0_ffi w0” |> SPEC_ALL
  |> REWRITE_RULE [GSYM client_decs_def];

val (_, decls_args) = strip_comb (concl Decls_th);
val env2_tm = List.nth (decls_args, 3);
val st2_tm = List.nth (decls_args, 4);

Overload CLIENT_ENV = “^env2_tm”
Overload CLIENT_ST = “λw0. ^st2_tm”
Overload MAIN_ENV = “merge_env CLIENT_ENV init_env”
Overload MAIN_CLOS = “λa c N rqs. Closure MAIN_ENV «u» (client_main_body a c N rqs)”

val lookup_client_main = let
  val g = “nsLookup (^env2_tm).v (Short «client_main») = SOME client_main_v”
  in prove (g, REWRITE_TAC [fst (dest_eq g) |> nsLookup_conv]) end;

val st2_ffi = prove (“(^st2_tm).ffi = l0_ffi w0”, EVAL_TAC);

Theorem client_Decls:
  Decls init_env (init_state (l0_ffi w0)) (client_decs ++ [client_main_dec a c N rqs])
    (merge_env (write «main» (MAIN_CLOS a c N rqs) empty_env) CLIENT_ENV) (CLIENT_ST w0)
Proof
  simp[Decls_APPEND] >>
  qexistsl [‘CLIENT_ENV’, ‘write «main» (MAIN_CLOS a c N rqs) empty_env’, ‘CLIENT_ST w0’] >>
  simp[Decls_th, client_main_dec_def, Decls_Dlet, eval_rel_def, evaluateTheory.evaluate_def] >>
  qexists_tac ‘MAIN_CLOS a c N rqs’ >> simp[] >> qexistsl [‘0’, ‘0’] >> simp[]
QED

Theorem lookup_main:
  lookup_var «main» (merge_env (write «main» (MAIN_CLOS a c N rqs) empty_env) CLIENT_ENV) =
    SOME (MAIN_CLOS a c N rqs)
Proof
  simp[lookup_var_def, merge_env_def, ml_progTheory.write_def, empty_env_def,
       namespacePropsTheory.nsLookup_nsAppend_some]
QED

(* main () is client_main c a N s *)
Theorem main_app:
  app p client_main_v [Litv (IntLit (&c)); Litv (IntLit (&a)); Litv (IntLit (&N));
                       Litv (StrLit (CLITS N rqs))] H Q ⇒
  app (p:'ffi ffi_proj) (MAIN_CLOS a c N rqs) [Conv NONE []] H Q
Proof
  strip_tac >>
  ‘MAIN_CLOS a c N rqs = naryClosure MAIN_ENV [«u»] (client_main_body a c N rqs)’
    by simp[naryClosure_def, naryFun_def] >>
  pop_assum SUBST1_TAC >> irule app_of_cf >> simp[client_main_body_def] >>
  simp[Once cf_def, dest_opapp_def, cf_app_def] >> irule local_elim >> simp[] >>
  simp[exp2v_def, exp2v_list_def, extend_env_def, merge_env_def,
       namespacePropsTheory.nsLookup_nsAppend_some, lookup_client_main] >>
  qexists_tac ‘client_main_v’ >>
  simp[extend_env_v_def, namespacePropsTheory.nsLookup_nsAppend_some, lookup_client_main]
QED

Overload MAIN_ARGS = “λa c N rqs. [Litv (IntLit (&c)); Litv (IntLit (&a)); Litv (IntLit (&N));
                                    Litv (StrLit (CLITS N rqs))]”

Theorem client_prog_syntax_ok:
  prog_syntax_ok (client_prog a c N rqs)
Proof
  REWRITE_TAC [client_prog_def, client_decs_def, client_main_dec_def, client_main_body_def,
               main_call_def, prog_syntax_ok_def, listTheory.SNOC_APPEND, listTheory.APPEND] >>
  EVAL_TAC
QED

(* client_main returns: the program terminates with its events *)
Theorem client_term_semantics:
  l0_rely w0 ∧ w0.hist = [] ∧
  app (l0_proj w0) client_main_v (MAIN_ARGS a c N rqs) (L0_EV w0 w0 [])
    (POSTv v. &UNIT_TYPE () v * L0_EV w0 w' evs) ⇒
  semantics_prog (init_state (l0_ffi w0)) init_env (client_prog a c N rqs)
    (Terminate Success evs)
Proof
  strip_tac >>
  simp[GSYM (MATCH_MP prog_syntax_ok_semantics client_prog_syntax_ok)] >>
  assume_tac client_Decls >>
  drule call_main_thm2 >>
  Cases_on ‘l0_proj w0’ >> rename1 ‘l0_proj w0 = (pj1, pj2)’ >>
  assume_tac st2_ffi >> drule l0_init_heap >> simp[] >> strip_tac >>
  disch_then (qspecl_then [‘pj2’, ‘pj1’, ‘h2’, ‘h1’, ‘MAIN_CLOS a c N rqs’, ‘«main»’,
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
  gvs[client_prog_def, main_call_def]
QED

(* client_main diverges: the program diverges with its events *)
Theorem client_div_semantics:
  l0_rely w0 ∧ w0.hist = [] ∧
  app (l0_proj w0) client_main_v (MAIN_ARGS a c N rqs) (L0_EV w0 w0 []) (POSTd io'. io' = io) ⇒
  semantics_prog (init_state (l0_ffi w0)) init_env (client_prog a c N rqs) (Diverge io)
Proof
  strip_tac >>
  simp[GSYM (MATCH_MP prog_syntax_ok_semantics client_prog_syntax_ok)] >>
  assume_tac client_Decls >>
  drule call_main_thm_div >>
  Cases_on ‘l0_proj w0’ >> rename1 ‘l0_proj w0 = (pj1, pj2)’ >>
  assume_tac st2_ffi >> drule l0_init_heap >> simp[] >> strip_tac >>
  disch_then (qspecl_then [‘pj2’, ‘pj1’, ‘h2’, ‘h1’, ‘MAIN_CLOS a c N rqs’, ‘«main»’,
                           ‘λio'. io' = io’, ‘L0_EV w0 w0 []’] mp_tac) >>
  impl_tac
  >- (simp[lookup_main] >> irule main_app >> gvs[]) >>
  rw[client_prog_def, main_call_def] >> gvs[]
QED

(* A client_main spec on the literal arguments *)
fun lit_args th =
  Q.INST [‘cv’ |-> ‘Litv (IntLit (&c))’, ‘av’ |-> ‘Litv (IntLit (&a))’,
          ‘nv’ |-> ‘Litv (IntLit (&N))’, ‘sv’ |-> ‘Litv (StrLit (CLITS N rqs))’] th;

Theorem main_args_types[local]:
  NUM c (Litv (IntLit (&c))) ∧ STRING_TYPE (CLITS N rqs) (Litv (StrLit (CLITS N rqs)))
Proof
  simp[NUM_def, INT_def, STRING_TYPE_def]
QED

(* ------------------------------------------------------------------------
   The program's four outcomes
   ------------------------------------------------------------------------ *)

(* stdin, stdout or stderr closed: the three fdok events, then stop *)
Theorem client_closed_semantics:
  l0_rely w0 ∧ w0.hist = [] ∧
  FDOK3 w0 w1 w2 w3 o0 o1 o2 e0 e1 e2 ∧ ¬fdok_all o0 o1 o2 ⇒
  semantics_prog (init_state (l0_ffi w0)) init_env (client_prog a c N rqs)
    (Terminate Success [e0; e1; e2])
Proof
  strip_tac >> irule client_term_semantics >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexists_tac ‘w3’ >> BETA_TAC >> irule (lit_args client_main_closed_spec) >> simp[main_args_types] >>
  qexistsl [‘o0’, ‘o1’, ‘o2’, ‘w1’, ‘w2’] >> simp[]
QED

(* The listen on c failed: the fdok events and the listen, then stop *)
Theorem client_nolisten_semantics:
  l0_rely w0 ∧ w0.hist = [] ∧
  FDOK3 w0 w1 w2 w3 o0 o1 o2 e0 e1 e2 ∧ fdok_all o0 o1 o2 ∧
  sys_listen_port c w3 = SOME (out, w4, ev) ∧ listen_fd out = NONE ⇒
  semantics_prog (init_state (l0_ffi w0)) init_env (client_prog a c N rqs)
    (Terminate Success [e0; e1; e2; ev])
Proof
  strip_tac >> irule client_term_semantics >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexists_tac ‘w4’ >> BETA_TAC >> irule (lit_args client_main_nolisten_spec) >> simp[main_args_types] >>
  qexistsl [‘o0’, ‘o1’, ‘o2’, ‘out’, ‘w1’, ‘w2’, ‘w3’] >> simp[]
QED

(* The client finished after n rounds of E1 on the listener k *)
Theorem client_term_n_semantics:
  l0_rely w0 ∧ w0.hist = [] ∧
  FDOK3 w0 w1 w2 w3 o0 o1 o2 e0 e1 e2 ∧ fdok_all o0 o1 o2 ∧
  sys_listen_port c w3 = SOME (out, w4, ev) ∧ listen_fd out = SOME k ∧
  erounds (n2w k) pol_never (cifds a N rqs) (cprog a N rqs) (w4, einit) n =
    SOME (h, (w', es'), evs, logs) ∧
  call_done (cstate a N rqs h) ∧
  (∀j. j < n ⇒ ¬call_done (cstate a N rqs
                  (FST (erun (n2w k) pol_never (cifds a N rqs) (cprog a N rqs) (w4, einit) j)))) ⇒
  semantics_prog (init_state (l0_ffi w0)) init_env (client_prog a c N rqs)
    (Terminate Success ([e0; e1; e2; ev] ++ evs))
Proof
  strip_tac >> irule client_term_semantics >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexists_tac ‘w'’ >> BETA_TAC >> irule (lit_args client_main_term_spec) >> simp[main_args_types] >>
  qexistsl [‘es'’, ‘h’, ‘logs’, ‘n’] >>
  simp[]
QED

(* The client never finishes: the fdok events, the listen, then E1's rounds *)
Theorem client_div_n_semantics:
  l0_rely w0 ∧ w0.hist = [] ∧
  FDOK3 w0 w1 w2 w3 o0 o1 o2 e0 e1 e2 ∧ fdok_all o0 o1 o2 ∧
  sys_listen_port c w3 = SOME (out, w4, ev) ∧ listen_fd out = SOME k ∧
  (∀n. erounds (n2w k) pol_never (cifds a N rqs) (cprog a N rqs) (w4, einit) n ≠ NONE) ∧
  (∀n. ¬call_done (cstate a N rqs
                  (FST (erun (n2w k) pol_never (cifds a N rqs) (cprog a N rqs) (w4, einit) n)))) ⇒
  semantics_prog (init_state (l0_ffi w0)) init_env (client_prog a c N rqs)
    (Diverge (LAPPEND (fromList [e0; e1; e2; ev]) (LFLATTEN (LGENLIST
       (λi. fromList (eround_evs (n2w k) pol_never (cifds a N rqs) (cprog a N rqs)
                                 (w4, einit) i)) NONE))))
Proof
  strip_tac >> irule client_div_semantics >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  BETA_TAC >> irule (lit_args client_main_div_spec) >> simp[main_args_types, limited_parts_l0, l0_reach_init] >>
  qexistsl [‘o0’, ‘o1’, ‘o2’, ‘out’, ‘w1’, ‘w2’, ‘w3’] >> simp[]
QED
