(*
  The whole chat program's semantics: it diverges, and its I/O trace is
  the socket-model run of chat_server 3 under M4's dynamic-interest loop,
  which satisfies ChatSpec's chat_safe.
   - main_spec: main () runs run_i on ([3], chat_server 3)
     (run_i_spec with chat_server_spec; no misuse by gen_grun_ok);
   - the world: socket_only_ffi s0, from a state with listener 3w, no
     pending connections and no connections;
   - safety: chat_comp_safe.
*)
Theory asyncChatSemantics
Ancestors
  asyncCore asyncLevel1 asyncCfActModel asyncCfActProg asyncM3World
  asyncM3Prog asyncM3Loop asyncM4GRounds asyncM4Loop asyncM4SockModel
  asyncM4SockApprox asyncM4SockServer asyncRunOkGen
  asyncWithTap asyncChatModel asyncChatSafe asyncChatSockModel
  asyncChatProg asyncChatSpec asyncChatTrace asyncChatMain ChatSpec
  ffiSpikeSocketFFI ffiSpikeSocketProof ffiSpikeSocketDiv ffiSpikeDivMain
  cfDiv ml_translator ml_prog std_prelude llist
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncChatMain"

(* The chat server's run against the socket world s0: round i polls
   listener 3w and every connection accepted so far *)
Overload chat_trace =
  “λs0. LFLATTEN (LGENLIST
          (λi. fromList (grounds_events (interest [3w])
                           (srelabel (chat_server 3)) s0 i))
          NONE)”

(* The initial world: one listener, 3w, with no pending connections, and no
   connections; any future arrivals (s0.sched) *)
Overload start_world = “λs0:sockets. s0.listeners = [(3w, [])] ∧ s0.conns = []”

(* MAIN (helper): main () runs the event loop on the chat server: it never
   terminates, and its I/O trace is the server's run *)
Theorem main_spec:
  limited_parts socket_names p ∧ start_world s0 ∧ UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) asyncChatMain$main_v [uv] (SOCKETS_EV s0 [])
    (POSTd io. io = chat_trace s0)
Proof
  rpt strip_tac >> xcf_with_def asyncChatMainTheory.main_v_def >>
  xlet ‘POSTv cv. &COMP p SACT UNIT_TYPE SSNAP
                     (srelabel (chat_server 3)) cv * SOCKETS_EV s0 []’
  >- (xapp_spec chat_server_spec >> xsimpl) >>
  rpt (xlet_auto >- (xcon >> xsimpl)) >>
  gvs[] >>
  ‘app p run_i_v [Conv NONE [Conv (SOME (TypeStamp «::» 1))
                     [Litv (IntLit 3); Conv (SOME (TypeStamp «[]» 1)) []]; cv]]
     (SOCKETS_EV s0 []) (POSTd io. io = chat_trace s0)’
    by (irule run_i_spec >> simp[wf_schat_server, LIST_TYPE_def] >>
        conj_tac
        >- (irule gen_grun_ok >> simp[] >> qexists_tac ‘3’ >>
            simp[chat_server_uses_ok]) >>
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
  |> REWRITE_RULE [GSYM chat_decs_def];

val (_, decls_args) = strip_comb (concl Decls_th);
val env2_tm = List.nth (decls_args, 3);
val st2_tm = List.nth (decls_args, 4);

val lookup_main = let
  val g = “nsLookup (^env2_tm).v (Short «main») = SOME asyncChatMain$main_v”
  in prove (g, REWRITE_TAC [fst (dest_eq g) |> nsLookup_conv]) end;

val st2_ffi = prove (“(^st2_tm).ffi = socket_only_ffi s0”, EVAL_TAC);

(* MAIN: in a sockets-only world whose initial state has one listener, 3w,
   and no connections, the whole chat program diverges; its I/O trace is
   the server's run, and it satisfies ChatSpec's safety. *)
Theorem chat_semantics:
  start_world s0 ⇒
  ∃io. semantics_dec_list (init_state (socket_only_ffi s0)) init_env
         chat_prog (Diverge io) ∧
       io = chat_trace s0 ∧ chat_safe io
Proof
  strip_tac
  \\ assume_tac Decls_th
  \\ drule call_main_thm_div \\ strip_tac
  \\ assume_tac st2_ffi
  \\ drule sonly_init_heap \\ strip_tac
  \\ first_x_assum (qspecl_then [‘sonly_proj2’, ‘sonly_proj1’, ‘h2’, ‘h1’,
       ‘asyncChatMain$main_v’, ‘«main»’, ‘λio. io = chat_trace s0’,
       ‘SOCKETS_EV s0 []’] mp_tac)
  \\ impl_tac
  >- (simp [lookup_var_def, lookup_main]
      \\ irule main_spec \\ simp [limited_parts_sonly])
  \\ rw [chat_prog_def]
  \\ irule chat_comp_safe \\ simp []
QED

Theorem chat_prog_syntax_ok:
  prog_syntax_ok chat_prog
Proof
  REWRITE_TAC [chat_prog_eq, prog_syntax_ok_def] >> EVAL_TAC
QED

(* MAIN: the same, in the form CakeML's compiler correctness theorem
   (compile_correct) takes. *)
Theorem chat_semantics_prog:
  start_world s0 ⇒
  semantics_prog (init_state (socket_only_ffi s0)) init_env chat_prog
    (Diverge (chat_trace s0)) ∧
  chat_safe (chat_trace s0)
Proof
  strip_tac >> drule chat_semantics >> strip_tac >>
  gvs [GSYM (MATCH_MP prog_syntax_ok_semantics chat_prog_syntax_ok)]
QED
