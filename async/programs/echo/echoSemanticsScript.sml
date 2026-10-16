(*
  The whole echo program's semantics: it diverges, and its I/O trace is the
  socket-model run of the echo server under M4's dynamic-interest loop,
  which satisfies EchoSpec's echo_safe.

  This is the source-level half of a machine-code theorem: CakeML's
  compile_correct turns a semantics_prog fact about echo_prog into one about
  the machine code (design/22-machine-code.md).  It follows
  asyncM3Example's m3_semantics, with
   - main_spec: main () runs run_i on ([3], server 3) (run_i_spec with
     sserver_spec; no misuse by echo_grun_ok);
   - the world: socket_only_ffi s0 (socketDiv), the socket FFI part
     alone, from a state with listener 3w, no pending connections and no
     connections (EchoSpec's server_world shape).
*)
Theory echoSemantics
Ancestors
  asyncCore asyncLevel1 libModel libProg loopPollWorld
  loopPollProg loopPoll loopRounds loopPollDyn echoSockModel
  libSockApprox echoSockServer echoRunOk echoSafe
  echoMain socketWorld socketProof socketDiv
  divMain EchoSpec cfDiv ml_translator ml_prog std_prelude llist

Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "echoMain"

(* The echo server's run against the socket world s0: round i polls
   listener 3w and every connection accepted so far *)
Overload echo_trace =
  “λs0. LFLATTEN (LGENLIST
          (λi. fromList (grounds_events (interest [3w]) (srelabel (server 3)) s0 i))
          NONE)”

(* The initial world: one listener, 3w, with no pending connections, and no
   connections; any future arrivals (s0.sched) *)
Overload start_world = “λs0:sockets. s0.listeners = [(3w, [])] ∧ s0.conns = []”

(* MAIN (helper): main () runs the event loop on the server: it never
   terminates, and its I/O trace is the server's run *)
Theorem main_spec:
  limited_parts socket_names p ∧ start_world s0 ∧ UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) main_v [uv] (SOCKETS_EV s0 [])
    (POSTd io. io = echo_trace s0)
Proof
  rpt strip_tac >> xcf_with_def main_v_def >>
  xlet ‘POSTv cv. &COMP p SACT UNIT_TYPE SSNAP (srelabel (server 3)) cv *
                  SOCKETS_EV s0 []’
  >- (xapp_spec sserver_spec >> xsimpl >> simp[]) >>
  rpt (xlet_auto >- (xcon >> xsimpl)) >>
  gvs[] >>
  ‘app p run_i_v [Conv NONE [Conv (SOME (TypeStamp «::» 1))
                     [Litv (IntLit 3); Conv (SOME (TypeStamp «[]» 1)) []]; cv]]
     (SOCKETS_EV s0 []) (POSTd io. io = echo_trace s0)’
    by (irule run_i_spec >> simp[wf_sserver, LIST_TYPE_def] >>
        conj_tac >- (irule echo_grun_ok >> simp[]) >>
        metis_tac[]) >>
  qpat_x_assum ‘app _ run_i_v _ _ _’ xapp_spec
QED

(* ------------------------------------------------------------------------
   The whole program (following asyncM3Example's m3_semantics)
   ------------------------------------------------------------------------ *)

val Decls_th =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> GEN_ALL |> ISPEC “socket_only_ffi s0” |> SPEC_ALL
  |> REWRITE_RULE [GSYM echo_decs_def];

val (_, decls_args) = strip_comb (concl Decls_th);
val env2_tm = List.nth (decls_args, 3);
val st2_tm = List.nth (decls_args, 4);

val lookup_main = let
  val g = “nsLookup (^env2_tm).v (Short «main») = SOME main_v”
  in prove (g, REWRITE_TAC [fst (dest_eq g) |> nsLookup_conv]) end;

val st2_ffi = prove (“(^st2_tm).ffi = socket_only_ffi s0”, EVAL_TAC);

(* MAIN: in a sockets-only world whose initial state has one listener, 3w,
   and no connections, the whole echo program diverges; its I/O trace is
   the server's run, and it satisfies EchoSpec's safety: on every
   connection, at every point, the bytes written are a prefix of the bytes
   read. *)
Theorem echo_semantics:
  start_world s0 ⇒
  ∃io. semantics_dec_list (init_state (socket_only_ffi s0)) init_env
         echo_prog (Diverge io) ∧
       io = echo_trace s0 ∧ echo_safe io
Proof
  strip_tac
  \\ assume_tac Decls_th
  \\ drule call_main_thm_div \\ strip_tac
  \\ assume_tac st2_ffi
  \\ drule sonly_init_heap \\ strip_tac
  \\ first_x_assum (qspecl_then [‘sonly_proj2’, ‘sonly_proj1’, ‘h2’, ‘h1’,
       ‘main_v’, ‘«main»’, ‘λio. io = echo_trace s0’, ‘SOCKETS_EV s0 []’] mp_tac)
  \\ impl_tac
  >- (simp [lookup_var_def, lookup_main]
      \\ irule main_spec \\ simp [limited_parts_sonly])
  \\ rw [echo_prog_def]
  \\ irule echo_comp_safe \\ simp []
QED

(* The program's constructors are all declared before use (checked by
   evaluation); this lets semantics_dec_list be read as semantics_prog *)
Theorem echo_prog_syntax_ok:
  prog_syntax_ok echo_prog
Proof
  REWRITE_TAC [echo_prog_eq, prog_syntax_ok_def] >> EVAL_TAC
QED

(* MAIN: the same, in the form CakeML's compiler correctness theorem
   (compile_correct) takes: the program's semantics_prog behaviour in the
   world socket_only_ffi s0 is the divergent trace echo_trace s0, which
   satisfies echo_safe.  (With semanticsProps' semantics_prog_Diverge_not_Fail
   this is also ¬Fail and the only behaviour.) *)
Theorem echo_semantics_prog:
  start_world s0 ⇒
  semantics_prog (init_state (socket_only_ffi s0)) init_env echo_prog
    (Diverge (echo_trace s0)) ∧
  echo_safe (echo_trace s0)
Proof
  strip_tac >> drule echo_semantics >> strip_tac >>
  gvs [GSYM (MATCH_MP prog_syntax_ok_semantics echo_prog_syntax_ok)]
QED
