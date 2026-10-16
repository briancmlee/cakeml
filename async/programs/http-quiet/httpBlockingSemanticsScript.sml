(*
  Option C §2.4: the HTTP-bodies program on the select-on-interest loop,
  end to end (as echoBlockingMain does for the live-fd echo).

      fun main u = run_q ([3], proto_server2 b_parse bresp_demo 3)

  The computation is hb_c, the Level 2 protocol server for the bodies
  protocol in the socket vocabulary; its run is cf-actions' polling server
  srelabel (proto_server P_b resp_b 3) (hb_run), so the generic polling
  safety and liveness (proto_comp_safe, proto_live_rounds) carry over to
  the select loop's trace (protoTransfer).

  MAIN:
  - http_blocking_semantics: the program diverges with the trace lblock_io, or
    ends in an FFI divergence of «sock_select» on the declared fds after
    the finite trace of its first n rounds;
  - http_blocking_spec: in both cases the trace is http_safe, and http_live
    when the world is sched_wf.
*)
Theory httpBlockingSemantics
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncLevel2 echoServer libModel
  libProg loopPollWorld loopPoll loopRounds loopPollDyn
  relabel echoSockModel echoSockServer loopSelectWorld
  loopSelectTrace loopSelect echoSelectMain loopSelectSet
  skeletonRunOk skeletonV protoInterface protoServer protoSafe
  protoLive httpProto protoSockSpec proto2
  lib2SockProg relabel2 proto2SockModel proto2SockSpec loopInterestFinite
  loopInterestSel loopInterestProg loopInterestRun protoTransfer httpBlockingMain httpProg
  HttpSpec socketWorld composedWorld divMain
  ml_translator ml_prog cfMain cfDiv cfStore llist
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "httpBlockingMain"

val st = get_ml_prog_state ();

(* The bodies spec's safety and liveness are the generic ones, for P_b
   (the two halves of httpProto.http_spec_proto) *)
Theorem http_safe_proto:
  http_safe files io ⇔ proto_safe P_b (print_response o bhandle files) io
Proof
  simp[http_safe_def, proto_safe_def, brequests_def, bresponses_def, no_full_brequest_def,
       preqs_def, presps_def, no_full_def, P_b_def]
QED

Theorem http_live_proto:
  http_live files sk io ⇔ proto_live P_b (print_response o bhandle files) sk io
Proof
  simp[http_live_def, proto_live_def, brequests_def, bresponses_def, no_full_brequest_def,
       preqs_def, presps_def, P_b_def]
QED

Overload resp_b = “λr. print_response (bhandle demo_files r)”
Overload hb_c = “srelabel2 (proto_server_v2 idVu P_b (K (NONE : unit option))
                              (λr (k : unit option). resp_b r) 3)”
Overload hb_sel = “qsel hb_c”

(* ------------------------------------------------------------------------
   The computation
   ------------------------------------------------------------------------ *)

Theorem hb_run:
  hb_c.run = srelabel (proto_server P_b resp_b 3)
Proof
  ‘hb_c.run = erase hb_c’ by simp[erase_def] >> pop_assum SUBST1_TAC >>
  simp[erase_srelabel2, erase_proto_server_idV2]
QED

Theorem hb_ok:
  wf hb_c.run ∧ quiet hb_c ∧ finite2 hb_c
Proof
  ‘wf2 hb_c’ by (irule wf2_srelabel2 >> simp[wf2_proto_server_v2]) >>
  fs[wf2_def, finite2_sproto_server_v2]
QED

Theorem hb_grun_ok:
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ⇒
  grun_ok (interest [3w]) hb_c.run sk
Proof
  rw[hb_run] >> irule gen_grun_ok >> fs[] >> qexists_tac ‘3’ >>
  simp[uses_ok_def] >> metis_tac[proto_server_uses_accepted, proto_ok_b]
QED

Theorem proto_impl_hb:
  PROTO_IMPL HTTPSPEC_BREQUEST_TYPE P_b resp_b
    httpBlockingMain$b_parse_v httpBlockingMain$bresp_demo_v
Proof
  simp[PROTO_IMPL_def] >>
  mp_tac (fetch "httpBlockingMain" "b_parse_v_thm") >>
  mp_tac (fetch "httpBlockingMain" "bresp_demo_v_thm") >>
  simp[b_parse_P_b, bresp_demo_eq, combinTheory.o_DEF]
QED

(* ------------------------------------------------------------------------
   main
   ------------------------------------------------------------------------ *)

val main_prelude =
  xcf_with_def (fetch "httpBlockingMain" "main_v_def") >>
  xlet ‘POSTv cv. &COMPI p SACT UNIT_TYPE SEV SSNAP hb_c cv * SSEL sk []’
  >- (xapp_spec (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] sproto_server2_spec)
                            proto_impl_hb) >>
      xsimpl >> simp[NUM_def, INT_def]) >>
  rpt (xlet_auto >- (xcon >> xsimpl)) >> rveq;

Theorem main_q_spec_div:
  limited_parts ssel_names p ∧
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ∧
  (∀n. lbgrounds hb_sel [3w] hb_c.run sk n ≠ NONE) ⇒
  app (p:'ffi ffi_proj) httpBlockingMain$main_v [Conv NONE []] (SSEL sk [])
    (POSTd io. io = lblock_io hb_sel [3w] hb_c.run sk)
Proof
  strip_tac >> main_prelude >>
  xapp_spec (run_q_spec |> Q.GEN ‘c’ |> Q.ISPEC ‘hb_c’) >>
  simp[LIST_TYPE_def, NUM_def, INT_def, hb_ok, hb_grun_ok] >>
  metis_tac[]
QED

Theorem main_q_spec_stuck:
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ∧
  lbgrounds hb_sel [3w] hb_c.run sk n = SOME (kept, N, s) ∧
  new_actions (log_of hb_c.run) kept = [] ∧
  sock_wait (hb_sel kept) s = NONE ⇒
  app (p:'ffi ffi_proj) httpBlockingMain$main_v [Conv NONE []] (SSEL sk [])
    (POSTf nm. λcf b.
       &(nm = «sock_select» ∧ cf = fds_bytes (hb_sel kept) ∧ b = []) *
       SSEL s (FLAT (GENLIST (lbround_events hb_sel [3w] hb_c.run sk) n)) *
       SEP_EXISTS av. W8ARRAY av [])
Proof
  strip_tac >> main_prelude >>
  xapp_spec (run_q_stuck_spec |> Q.GEN ‘c’ |> Q.ISPEC ‘hb_c’) >>
  simp[LIST_TYPE_def, NUM_def, INT_def, hb_ok, hb_grun_ok] >>
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

val http_blocking_prog_def = new_definition ("http_blocking_prog_def",
  mk_eq (mk_var ("http_blocking_prog", type_of decs_tm), decs_tm));

val lookup_main = let
  val g = “nsLookup (^env2_tm).v (Short «main») = SOME httpBlockingMain$main_v”
  in prove (g, REWRITE_TAC [fst (dest_eq g) |> nsLookup_conv]) end;

val st2_ffi = prove (“(^st2_tm).ffi = ssel_ffi sk”, EVAL_TAC);

(* MAIN: the program's two outcomes, in CakeML's semantics *)
Theorem http_blocking_semantics:
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ⇒
  (∃io. semantics_dec_list (init_state (ssel_ffi sk)) init_env
          (SNOC (main_call «main») http_blocking_prog) (Diverge io) ∧
        (∀n. lbgrounds hb_sel [3w] hb_c.run sk n ≠ NONE) ∧
        io = lblock_io hb_sel [3w] hb_c.run sk) ∨
  (∃n kept N s.
     lbgrounds hb_sel [3w] hb_c.run sk n = SOME (kept, N, s) ∧
     new_actions (log_of hb_c.run) kept = [] ∧
     sock_wait (hb_sel kept) s = NONE ∧
     semantics_dec_list (init_state (ssel_ffi sk)) init_env
       (SNOC (main_call «main») http_blocking_prog)
       (Terminate (FFI_outcome (Final_event (ExtCall «sock_select»)
                                  (fds_bytes (hb_sel kept)) []
                                  FFI_diverged))
                  (FLAT (GENLIST (lbround_events hb_sel [3w] hb_c.run sk) n))))
Proof
  strip_tac >>
  assume_tac (REWRITE_RULE [GSYM http_blocking_prog_def] Decls_th) >>
  assume_tac st2_ffi >>
  drule ssel_init_heap >> strip_tac >>
  Cases_on ‘∀n. lbgrounds hb_sel [3w] hb_c.run sk n ≠ NONE’
  >- (disj1_tac >> simp[] >>
      drule call_main_thm_div >>
      disch_then (qspecl_then [‘ssel_proj2’, ‘ssel_proj1’, ‘h2’, ‘h1’,
         ‘httpBlockingMain$main_v’, ‘«main»’,
         ‘λio. io = lblock_io hb_sel [3w] hb_c.run sk’,
         ‘SSEL sk []’] mp_tac) >>
      impl_tac
      >- (simp [lookup_var_def, lookup_main] >>
          irule main_q_spec_div >> simp [limited_parts_ssel]) >>
      simp [])
  >- (disj2_tac >>
      ‘∃n kept N s. lbgrounds hb_sel [3w] hb_c.run sk n = SOME (kept, N, s) ∧
                    new_actions (log_of hb_c.run) kept = [] ∧
                    sock_wait (hb_sel kept) s = NONE’
        by metis_tac[lbgrounds_two_outcomes] >>
      qexistsl [‘n’, ‘kept’, ‘N’, ‘s’] >> simp[] >>
      drule call_main_thm2_ffidiv >>
      disch_then (qspecl_then [‘ssel_proj2’, ‘ssel_proj1’, ‘h2’, ‘h1’,
         ‘httpBlockingMain$main_v’, ‘«main»’,
         ‘λnm cf b. &(nm = «sock_select» ∧ cf = fds_bytes (hb_sel kept) ∧
                      b = []) *
                    SSEL s (FLAT (GENLIST (lbround_events hb_sel [3w] hb_c.run sk) n)) *
                    SEP_EXISTS av. W8ARRAY av []’,
         ‘SSEL sk []’] mp_tac) >>
      impl_tac
      >- (simp [lookup_var_def, lookup_main] >>
          irule main_q_spec_stuck >> simp [] >> metis_tac []) >>
      strip_tac >>
      fs [SEP_CLAUSES, SEP_EXISTS_THM, cond_STAR] >> rveq >>
      fs [GSYM STAR_ASSOC, cond_STAR] >> rveq >>
      qpat_x_assum ‘(_ * _) h3’ mp_tac >>
      simp [SSEL_def, STAR_def, one_def] >> strip_tac >>
      gvs [SPLIT_def, SPLIT3_def] >>
      ‘FFI_part (sockets_encode s) (mk_ffi_next ssel_ffi_part) ssel_names
         (FLAT (GENLIST (lbround_events hb_sel [3w] hb_c.run sk) n)) ∈
         st2heap (ssel_proj1, ssel_proj2) st3’
        by (qpat_x_assum ‘_ = st2heap _ st3’ (SUBST1_TAC o SYM) >> simp []) >>
      drule_at Any limited_FFI_part_IN_st2heap_IMP >>
      simp [limited_parts_ssel] >> strip_tac >>
      gvs [main_call_def])
QED

(* The polling loop's trace for the same computation is safe and live *)
Theorem hb_poll_safe:
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ⇒
  proto_safe P_b resp_b (poll_io [3w] hb_c.run sk)
Proof
  rw[hb_run] >> irule proto_comp_safe >> simp[proto_ok_b]
QED

Theorem hb_poll_live:
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ∧ sched_wf sk ⇒
  proto_live P_b resp_b sk (poll_io [3w] hb_c.run sk)
Proof
  rw[hb_run] >>
  ‘interest [3w] = EI 3’ by simp[] >> pop_assum SUBST1_TAC >>
  irule proto_live_rounds >> simp[proto_ok_b]
QED

Theorem resp_b_o[local]:
  print_response o bhandle files = (λr. print_response (bhandle files r))
Proof
  simp[FUN_EQ_THM]
QED

(* MAIN: in HttpSpec' terms: in both outcomes the trace is safe, and
   live when the world is sched_wf *)
Theorem http_blocking_spec:
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ⇒
  (∃io. semantics_dec_list (init_state (ssel_ffi sk)) init_env
          (SNOC (main_call «main») http_blocking_prog) (Diverge io) ∧
        http_safe demo_files io ∧
        (sched_wf sk ⇒ http_live demo_files sk io)) ∨
  (∃n kept N s io.
     lbgrounds hb_sel [3w] hb_c.run sk n = SOME (kept, N, s) ∧
     new_actions (log_of hb_c.run) kept = [] ∧
     sock_wait (hb_sel kept) s = NONE ∧
     io = FLAT (GENLIST (lbround_events hb_sel [3w] hb_c.run sk) n) ∧
     semantics_dec_list (init_state (ssel_ffi sk)) init_env
       (SNOC (main_call «main») http_blocking_prog)
       (Terminate (FFI_outcome (Final_event (ExtCall «sock_select»)
                                  (fds_bytes (hb_sel kept)) [] FFI_diverged)) io) ∧
     http_safe demo_files (fromList io) ∧
     (sched_wf sk ⇒ http_live demo_files sk (fromList io)))
Proof
  strip_tac >>
  ‘wf hb_c.run ∧ quiet hb_c ∧ sel_covers hb_c hb_sel’
    by simp[hb_ok, sel_covers_qsel] >>
  simp[http_safe_proto, http_live_proto, resp_b_o] >>
  drule_all hb_poll_safe >> strip_tac >>
  drule_all http_blocking_semantics >> strip_tac
  >- (disj1_tac >> qexists_tac ‘io’ >> simp[] >> rw[]
      >- (irule (cj 1 (SIMP_RULE bool_ss [IMP_CONJ_THM, AND_IMP_INTRO]
                         lblocking_proto_div)) >>
          simp[hb_ok, sel_covers_qsel, hb_poll_safe])
      >- (irule (cj 2 (SIMP_RULE bool_ss [IMP_CONJ_THM, AND_IMP_INTRO]
                         lblocking_proto_div)) >>
          simp[hb_ok, sel_covers_qsel, hb_poll_live]))
  >- (disj2_tac >> qexistsl [‘n’, ‘kept’, ‘N’, ‘s’] >> simp[] >> rw[]
      >- (irule (cj 1 (SIMP_RULE bool_ss [IMP_CONJ_THM, AND_IMP_INTRO]
                         lblocking_proto_stuck)) >>
          simp[hb_ok, sel_covers_qsel, hb_poll_safe] >> metis_tac[])
      >- (irule (cj 2 (SIMP_RULE bool_ss [IMP_CONJ_THM, AND_IMP_INTRO]
                         lblocking_proto_stuck)) >>
          simp[hb_ok, sel_covers_qsel, hb_poll_live] >> metis_tac[]))
QED
