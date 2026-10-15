(*
  The whole header-tolerant HTTP program's semantics: it diverges, and
  its I/O trace is the socket-model run of http_server_h under M4's
  dynamic-interest loop, which satisfies HttpSpecHeaders' http_safe_h.
  As http-safety/asyncHttpSemantics:
   - main_spec: main () runs run_i on ([3], http_server_h demo_files 3)
     (run_i_spec with shttp_server_h_spec; no misuse by gen_grun_ok);
   - the world: socket_only_ffi s0, from a state with listener 3w, no
     pending connections and no connections;
   - safety: http_comp_safe_h.
*)
Theory asyncHttpSemanticsH
Ancestors
  asyncCore asyncLevel1 asyncCfActModel asyncCfActProg asyncM3World
  asyncM3Prog asyncM3Loop asyncM4GRounds asyncM4Loop asyncM4SockModel
  asyncM4SockApprox asyncM4SockServer asyncServerWith asyncHttpServer
  asyncServerWithUses asyncRunOkGen asyncHttpSafe asyncHttpSockModel
  asyncHttpSockProg asyncHttpSockSpec asyncHttpMain HttpSpecHeaders
  asyncHttpParseH asyncHttpServerH asyncHttpSafeH asyncHttpSockModelH
  asyncHttpSockProgH asyncHttpSockSpecH asyncHttpMainH
  ffiSpikeSocketFFI ffiSpikeSocketProof ffiSpikeSocketDiv ffiSpikeDivMain
  HttpSpec cfDiv ml_translator ml_prog std_prelude llist
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncHttpMainH"

(* The HTTP server's run against the socket world s0: round i polls
   listener 3w and every connection accepted so far *)
Overload http_trace_h =
  “λs0. LFLATTEN (LGENLIST
          (λi. fromList (grounds_events (interest [3w])
                           (srelabel (http_server_h demo_files 3)) s0 i))
          NONE)”

(* The initial world: one listener, 3w, with no pending connections, and no
   connections; any future arrivals (s0.sched) *)
Overload start_world = “λs0:sockets. s0.listeners = [(3w, [])] ∧ s0.conns = []”

(* MAIN (helper): main () runs the event loop on the HTTP server: it never
   terminates, and its I/O trace is the server's run *)
Theorem main_spec:
  limited_parts socket_names p ∧ start_world s0 ∧ UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) asyncHttpMainH$main_v [uv] (SOCKETS_EV s0 [])
    (POSTd io. io = http_trace_h s0)
Proof
  rpt strip_tac >> xcf_with_def asyncHttpMainHTheory.main_v_def >>
  xlet ‘POSTv cv. &COMP p SACT UNIT_TYPE SSNAP
                     (srelabel (http_server_h demo_files 3)) cv * SOCKETS_EV s0 []’
  >- (xapp_spec shttp_server_h_spec >> xsimpl >> qexists_tac ‘demo_files’ >>
      simp[demo_files_v_thm]) >>
  rpt (xlet_auto >- (xcon >> xsimpl)) >>
  gvs[] >>
  ‘app p run_i_v [Conv NONE [Conv (SOME (TypeStamp «::» 1))
                     [Litv (IntLit 3); Conv (SOME (TypeStamp «[]» 1)) []]; cv]]
     (SOCKETS_EV s0 []) (POSTd io. io = http_trace_h s0)’
    by (irule run_i_spec >> simp[wf_shttp_server_h, LIST_TYPE_def] >>
        conj_tac
        >- (irule gen_grun_ok >> simp[] >> qexists_tac ‘3’ >>
            simp[uses_ok_def, http_server_h_uses_accepted]) >>
        metis_tac[]) >>
  qpat_x_assum ‘app _ run_i_v _ _ _’ xapp_spec
QED

(* ------------------------------------------------------------------------
   The whole program
   ------------------------------------------------------------------------ *)

val Decls_th =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> GEN_ALL |> ISPEC “socket_only_ffi s0” |> SPEC_ALL
  |> REWRITE_RULE [GSYM http_decs_h_def];

val (_, decls_args) = strip_comb (concl Decls_th);
val env2_tm = List.nth (decls_args, 3);
val st2_tm = List.nth (decls_args, 4);

val lookup_main = let
  val g = “nsLookup (^env2_tm).v (Short «main») = SOME asyncHttpMainH$main_v”
  in prove (g, REWRITE_TAC [fst (dest_eq g) |> nsLookup_conv]) end;

val st2_ffi = prove (“(^st2_tm).ffi = socket_only_ffi s0”, EVAL_TAC);

(* MAIN: in a sockets-only world whose initial state has one listener, 3w,
   and no connections, the whole HTTP program diverges; its I/O trace is
   the server's run, and it satisfies HttpSpec's safety: on every
   connection, at every point, if the bytes read are complete valid
   requests rs followed by a rest without a full request, the bytes written
   are a prefix of the responses to rs. *)
Theorem http_semantics_headers:
  start_world s0 ⇒
  ∃io. semantics_dec_list (init_state (socket_only_ffi s0)) init_env
         http_prog_h (Diverge io) ∧
       io = http_trace_h s0 ∧ http_safe_h demo_files io
Proof
  strip_tac
  \\ assume_tac Decls_th
  \\ drule call_main_thm_div \\ strip_tac
  \\ assume_tac st2_ffi
  \\ drule sonly_init_heap \\ strip_tac
  \\ first_x_assum (qspecl_then [‘sonly_proj2’, ‘sonly_proj1’, ‘h2’, ‘h1’,
       ‘asyncHttpMainH$main_v’, ‘«main»’, ‘λio. io = http_trace_h s0’,
       ‘SOCKETS_EV s0 []’] mp_tac)
  \\ impl_tac
  >- (simp [lookup_var_def, lookup_main]
      \\ irule main_spec \\ simp [limited_parts_sonly])
  \\ rw [http_prog_h_def]
  \\ irule http_comp_safe_h \\ simp []
QED

Theorem http_prog_h_syntax_ok:
  prog_syntax_ok http_prog_h
Proof
  REWRITE_TAC [http_prog_h_eq, prog_syntax_ok_def] >> EVAL_TAC
QED

(* MAIN: the same, in the form CakeML's compiler correctness theorem
   (compile_correct) takes: the HTTP program's semantics_prog behaviour in
   the world socket_only_ffi s0 is the divergent trace http_trace_h s0, which
   satisfies http_safe. *)
Theorem http_semantics_prog_headers:
  start_world s0 ⇒
  semantics_prog (init_state (socket_only_ffi s0)) init_env http_prog_h
    (Diverge (http_trace_h s0)) ∧
  http_safe_h demo_files (http_trace_h s0)
Proof
  strip_tac >> drule http_semantics_headers >> strip_tac >>
  gvs [GSYM (MATCH_MP prog_syntax_ok_semantics http_prog_h_syntax_ok)]
QED
