(*
  The GC chat program's semantics: as asyncChatSemantics, for gc_server.
  Its trace is chat_trace s0 (gc_trace_eq), so it meets ChatSpec and
  ChatSpecTimely (gc_prog_timely), and its hub holds exactly the log after
  the least client cursor (gc_run_space).

  Previously: the whole chat program's semantics: it diverges, and its I/O trace is
  the socket-model run of chat_server 3 under M4's dynamic-interest loop,
  which satisfies ChatSpec's chat_safe.
   - main_spec: main () runs run_i on ([3], chat_server 3)
     (run_i_spec with chat_server_spec; no misuse by gen_grun_ok);
   - the world: socket_only_ffi s0, from a state with listener 3w, no
     pending connections and no connections;
   - safety: chat_comp_safe.
*)
Theory asyncChatGCSemantics
Ancestors
  asyncCore asyncLevel1 asyncCfActModel asyncCfActProg asyncM3World
  asyncM3Prog asyncM3Loop asyncM4GRounds asyncM4Loop asyncM4SockModel
  asyncM4SockApprox asyncM4SockServer asyncRunOkGen
  asyncWithTap asyncChatSW asyncM4ServerUses asyncChatModel asyncChatSafe asyncChatSockModel
  asyncChatProg asyncChatSpec asyncChatTrace asyncChatMain ChatSpec
  asyncChatSemantics asyncChatGC asyncChatGCRun asyncChatGCWorld asyncChatGCProg
  asyncChatGCSpec asyncChatGCMain ChatSpecTimely ChatSpecTimelyBite EchoSpec
  asyncHeadline asyncChatLiveHeadline asyncChatTimelyHeadline
  ffiSpikeSocketFFI ffiSpikeSocketProof ffiSpikeSocketDiv ffiSpikeDivMain
  cfDiv ml_translator ml_prog std_prelude llist
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncChatGCMain"

Theorem gc_server_uses_ok:
  uses_ok lfd (gc_server lfd)
Proof
  simp[uses_ok_def, gc_server_def] >> gen_tac >>
  simp[trans_with_tap, wf_chat_inner] >> simp[chat_inner_def] >>
  metis_tac[cserver_with_uses_accepted, chat_handler_on_fdc]
QED

(* MAIN (helper): main () runs the event loop on the chat server: it never
   terminates, and its I/O trace is the server's run *)
Theorem gc_main_spec:
  limited_parts socket_names p ∧ start_world s0 ∧ UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) asyncChatGCMain$main_v [uv] (SOCKETS_EV s0 [])
    (POSTd io. io = chat_trace s0)
Proof
  rpt strip_tac >> xcf_with_def asyncChatGCMainTheory.main_v_def >>
  xlet ‘POSTv cv. &COMP p SACT UNIT_TYPE SSNAP
                     (srelabel (gc_server 3)) cv * SOCKETS_EV s0 []’
  >- (xapp_spec gc_server_spec >> xsimpl) >>
  rpt (xlet_auto >- (xcon >> xsimpl)) >>
  gvs[] >>
  ‘app p run_i_v [Conv NONE [Conv (SOME (TypeStamp «::» 1))
                     [Litv (IntLit 3); Conv (SOME (TypeStamp «[]» 1)) []]; cv]]
     (SOCKETS_EV s0 []) (POSTd io. io = chat_trace s0)’
    by (‘chat_trace s0 =
          LFLATTEN (LGENLIST
            (λi. fromList (grounds_events (interest [3w]) (srelabel (gc_server 3)) s0 i))
            NONE)’
          by (‘(3w : word64) = n2w 3’ by simp[] >>
              pop_assum SUBST1_TAC >> irule (GSYM gc_trace_eq) >> gvs[]) >>
        pop_assum SUBST1_TAC >>
        irule run_i_spec >> simp[wf_sgc_server, LIST_TYPE_def] >>
        conj_tac
        >- (irule gen_grun_ok >> simp[] >> qexists_tac ‘3’ >>
            simp[gc_server_uses_ok]) >>
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
  |> REWRITE_RULE [GSYM chat_gc_decs_def];

val (_, decls_args) = strip_comb (concl Decls_th);
val env2_tm = List.nth (decls_args, 3);
val st2_tm = List.nth (decls_args, 4);

val lookup_main = let
  val g = “nsLookup (^env2_tm).v (Short «main») = SOME asyncChatGCMain$main_v”
  in prove (g, REWRITE_TAC [fst (dest_eq g) |> nsLookup_conv]) end;

val st2_ffi = prove (“(^st2_tm).ffi = socket_only_ffi s0”, EVAL_TAC);

(* MAIN: in a sockets-only world whose initial state has one listener, 3w,
   and no connections, the whole chat program diverges; its I/O trace is
   the server's run, and it satisfies ChatSpec's safety. *)
Theorem gc_semantics:
  start_world s0 ⇒
  ∃io. semantics_dec_list (init_state (socket_only_ffi s0)) init_env
         chat_prog_gc (Diverge io) ∧
       io = chat_trace s0 ∧ chat_safe io
Proof
  strip_tac
  \\ assume_tac Decls_th
  \\ drule call_main_thm_div \\ strip_tac
  \\ assume_tac st2_ffi
  \\ drule sonly_init_heap \\ strip_tac
  \\ first_x_assum (qspecl_then [‘sonly_proj2’, ‘sonly_proj1’, ‘h2’, ‘h1’,
       ‘asyncChatGCMain$main_v’, ‘«main»’, ‘λio. io = chat_trace s0’,
       ‘SOCKETS_EV s0 []’] mp_tac)
  \\ impl_tac
  >- (simp [lookup_var_def, lookup_main]
      \\ irule gc_main_spec \\ simp [limited_parts_sonly])
  \\ rw [chat_prog_gc_def]
  \\ irule chat_comp_safe \\ simp []
QED

Theorem chat_prog_gc_syntax_ok:
  prog_syntax_ok chat_prog_gc
Proof
  REWRITE_TAC [chat_prog_gc_eq, prog_syntax_ok_def] >> EVAL_TAC
QED

(* MAIN: the same, in the form CakeML's compiler correctness theorem
   (compile_correct) takes. *)
Theorem gc_semantics_prog:
  start_world s0 ⇒
  semantics_prog (init_state (socket_only_ffi s0)) init_env chat_prog_gc
    (Diverge (chat_trace s0)) ∧
  chat_safe (chat_trace s0)
Proof
  strip_tac >> drule gc_semantics >> strip_tac >>
  gvs [GSYM (MATCH_MP prog_syntax_ok_semantics chat_prog_gc_syntax_ok)]
QED

(* MAIN: the GC chat program meets ChatSpecTimely, as the chat program does *)
Theorem gc_prog_timely:
  chat_spec_timely 4 3 3w chat_prog_gc
Proof
  rw[chat_spec_timely_def] >> qexists_tac ‘chat_trace sk’ >>
  drule chat_live_trace >> strip_tac >>
  drule chat_timely_trace >> strip_tac >>
  ‘sk.listeners = [(3w, [])] ∧ sk.conns = []’ by fs[server_world_def] >>
  qspec_then ‘sk’ mp_tac (Q.GEN ‘s0’ gc_semantics_prog) >>
  simp[socket_only_ffi_eq, chat_live_open_of_chat_live]
QED
