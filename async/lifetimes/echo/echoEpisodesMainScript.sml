(*
  The version-2 echo program and its divergence semantics.

      fun main u = run_h (3, [3], ([], 0), server 3)

  The program is version 1's (basis, Socket, Async, the socket-vocabulary
  echo server, all unchanged) plus SocketClose and the handle-layer loop,
  with this main.  In EchoEpisodesSpec's world (lifetime_ffi sk), if no action of
  the run is a misuse (hrun_ok, discharged by the simulation), it diverges
  and its I/O trace is the handle loop's run, echo2_trace sk.
*)
Theory echoEpisodesMain
Ancestors
  asyncCore asyncLevel1 libModel libProg loopPollWorld
  loopPollProg loopPoll loopPollDyn echoSockModel libSockApprox
  echoSockServer lifetimeWorld lifetimePart lifetimeProof lifetimeDiv
  EchoEpisodesSpec loopHandlesModel loopHandlesProg loopHandlesSpec divMain
  cfDiv ml_translator ml_prog std_prelude llist
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "loopHandlesProg"

Quote add_cakeml:
  fun main u = run_h (3, [3], ([], 0), server 3);
End

val st = get_ml_prog_state ();

(* The program's declarations, and the whole program *)
val echo2_decs_tm =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> concl |> strip_comb |> snd |> (fn args => List.nth (args, 2));

Definition echo2_decs_def:
  echo2_decs = ^echo2_decs_tm
End

Definition echo_episodes_prog_def:
  echo_episodes_prog = SNOC (main_call «main») echo2_decs
End

Theorem echo_episodes_prog_eq =
  REWRITE_CONV [echo_episodes_prog_def, echo2_decs_def, main_call_def,
                listTheory.SNOC_APPEND, listTheory.APPEND] “echo_episodes_prog”;

(* The echo server's run with the handle layer, against the world s0 *)
Overload echo2_trace =
  “λs0. LFLATTEN (LGENLIST
          (λi. fromList (hround_events 3w (interest [3w]) (srelabel (server 3)) s0 i))
          NONE)”

Overload echo2_run_ok = “λs0. hrun_ok 3w (interest [3w]) (srelabel (server 3)) s0”

(* main () runs the handle loop on the server *)
Theorem main2_spec:
  limited_parts socket2_names p ∧ echo2_run_ok s0 ∧ UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) main_v [uv] (SOCKETS2_EV s0 [])
    (POSTd io. io = echo2_trace s0)
Proof
  rpt strip_tac >> xcf_with_def (fetch "-" "main_v_def") >>
  xlet ‘POSTv cv. &COMP p SACT UNIT_TYPE SSNAP (srelabel (server 3)) cv *
                  SOCKETS2_EV s0 []’
  >- (xapp_spec sserver_spec >> xsimpl >> simp[]) >>
  rpt (xlet_auto >- (xcon >> xsimpl)) >>
  gvs[] >>
  ‘app p run_h_v [Conv NONE [Litv (IntLit 3);
                     Conv (SOME (TypeStamp «::» 1))
                       [Litv (IntLit 3); Conv (SOME (TypeStamp «[]» 1)) []];
                     Conv NONE [Conv (SOME (TypeStamp «[]» 1)) []; Litv (IntLit 0)];
                     cv]]
     (SOCKETS2_EV s0 []) (POSTd io. io = echo2_trace s0)’
    by (irule run_h_spec >>
        simp[wf_sserver, LIST_TYPE_def, HSV_def, hinit_def] >> metis_tac[]) >>
  qpat_x_assum ‘app _ run_h_v _ _ _’ xapp_spec
QED

(* ------------------------------------------------------------------------
   The whole program
   ------------------------------------------------------------------------ *)

val Decls_th =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> GEN_ALL |> ISPEC “socket2_only_ffi s0” |> SPEC_ALL
  |> REWRITE_RULE [GSYM echo2_decs_def];

val (_, decls_args) = strip_comb (concl Decls_th);
val env2_tm = List.nth (decls_args, 3);
val st2_tm = List.nth (decls_args, 4);

val lookup_main = let
  val g = “nsLookup (^env2_tm).v (Short «main») = SOME main_v”
  in prove (g, REWRITE_TAC [fst (dest_eq g) |> nsLookup_conv]) end;

val st2_ffi = prove (“(^st2_tm).ffi = socket2_only_ffi s0”, EVAL_TAC);

Theorem echo2_semantics:
  echo2_run_ok s0 ⇒
  semantics_dec_list (init_state (socket2_only_ffi s0)) init_env
    echo_episodes_prog (Diverge (echo2_trace s0))
Proof
  strip_tac
  \\ assume_tac Decls_th
  \\ drule call_main_thm_div \\ strip_tac
  \\ assume_tac st2_ffi
  \\ drule s2only_init_heap \\ strip_tac
  \\ first_x_assum (qspecl_then [‘s2only_proj2’, ‘s2only_proj1’, ‘h2’, ‘h1’,
       ‘main_v’, ‘«main»’, ‘λio. io = echo2_trace s0’, ‘SOCKETS2_EV s0 []’] mp_tac)
  \\ impl_tac
  >- (simp [lookup_var_def, lookup_main]
      \\ irule main2_spec \\ simp [limited_parts_s2only])
  \\ rw [echo_episodes_prog_def] \\ gvs []
QED

Theorem echo_episodes_prog_syntax_ok:
  prog_syntax_ok echo_episodes_prog
Proof
  REWRITE_TAC [echo_episodes_prog_eq, prog_syntax_ok_def] >> EVAL_TAC
QED

(* MAIN: in EchoEpisodesSpec's world, if no action of the run is a misuse, the
   version-2 echo program diverges, and its I/O trace is the handle loop's
   run of the (unchanged) echo server *)
Theorem echo2_semantics_prog:
  echo2_run_ok sk ⇒
  semantics_prog (init_state (lifetime_ffi sk)) init_env echo_episodes_prog
    (Diverge (echo2_trace sk))
Proof
  strip_tac >> drule echo2_semantics >>
  simp [socket2_only_ffi_eq,
        GSYM (MATCH_MP prog_syntax_ok_semantics echo_episodes_prog_syntax_ok)]
QED
