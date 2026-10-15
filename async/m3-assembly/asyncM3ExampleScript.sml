(*
  M3 end-to-end example: a whole CakeML program that runs a library
  computation in the async event loop against the socket model, proved
  down to the source semantics (Diverge).

      fun has3 l = (3 is in l)
      fun ready3 w = case w of (rdy, t, res) =>
                       if has3 rdy then Some () else None
      fun accept3 u = Async.emit (Accept 3)
      fun main u = run ([3], Async.bind (Async.wait ready3) accept3)

  The computation is the model's accept3 = bind (wait ready3) (λu. emit
  (Accept 3w)): wait until listener 3 is ready, then accept a connection.
  The program (basis, the Socket module, the Async library, the event loop,
  this code and a call to main) diverges in a sockets-only world in which
  3 is a listener, and its I/O trace is, round by round, the socket calls
  performing accept3's actions followed by the poll of listener 3, for the
  history the socket world generates.
*)
Theory asyncM3Example
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncCfActModel asyncCfActProg
  asyncM3World asyncM3ExampleModel asyncM3Prog asyncM3Loop
  ffiSpikeSocketFFI ffiSpikeSocketProof ffiSpikeSocketDiv ffiSpikeDivMain
  cfDiv cfMain ml_translator ml_prog std_prelude llist basis_ffi
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncM3Loop"

Quote add_cakeml:
  fun has3 l =
    case l of
      [] => False
    | x :: rest => if x = 3 then True else has3 rest;

  fun ready3 w =
    case w of (rdy, t, res) => if has3 rdy then Some () else None;

  fun accept3 u = Async.emit (Accept 3);

  fun main u = run ([3], Async.bind (Async.wait ready3) accept3);
End

val st = get_ml_prog_state ();

(* ------------------------------------------------------------------------
   Specs of the example's functions
   ------------------------------------------------------------------------ *)

val eq_num_v_thm =
  MATCH_MP (DISCH_ALL (fetch "mlbasicsProg" "eq_v_thm"))
           (EqualityType_NUM_BOOL |> CONJUNCT1);

Theorem has3_spec:
  ∀ns v. LIST_TYPE NUM ns v ⇒
    app (p:'ffi ffi_proj) has3_v [v] emp (POSTv b. &BOOL (MEM 3 ns) b)
Proof
  Induct >> rpt strip_tac >> xcf_with_def (fetch "-" "has3_v_def") >>
  gvs[LIST_TYPE_def] >> xmatch
  >- (xcon >> xsimpl >> EVAL_TAC)
  >- (xlet ‘POSTv bv. &BOOL (h = 3) bv’
      >- (xapp_spec eq_num_v_thm >> xsimpl >> metis_tac[]) >>
      xif
      >- (xcon >> xsimpl >> EVAL_TAC)
      >- (xapp >> simp[]))
QED

Theorem MEM_3_MAP_w2n[local]:
  MEM 3 (MAP w2n (fds:word64 list)) ⇔ MEM 3w fds
Proof
  simp[MEM_MAP] >> eq_tac >> rw[] >> gvs[]
  >- (Cases_on ‘y’ >> gvs[])
  >- (qexists_tac ‘3w’ >> simp[])
QED

Theorem ready3_spec:
  SNAPSHOT SREADY SRESP w wv ⇒
  app (p:'ffi ffi_proj) ready3_v [wv] emp
    (POSTv v. &OPTION_TYPE UNIT_TYPE (ready3 w) v)
Proof
  rw[SNAPSHOT_def, SREADY_def] >>
  xcf_with_def (fetch "-" "ready3_v_def") >> xmatch >>
  xlet ‘POSTv b. &BOOL (MEM 3 (MAP w2n fds)) b’
  >- (xapp >> metis_tac[]) >>
  xif
  >- (rpt (xlet_auto >- (xcon >> xsimpl)) >> xcon >> xsimpl >>
      gvs[ready3_def, MEM_3_MAP_w2n, OPTION_TYPE_def, UNIT_TYPE_def])
  >- (xcon >> xsimpl >>
      gvs[ready3_def, MEM_3_MAP_w2n, OPTION_TYPE_def, UNIT_TYPE_def])
QED

Theorem accept3_spec:
  UNIT_TYPE x xv ⇒
  app (p:'ffi ffi_proj) accept3_v [xv] emp
    (POSTv v. &COMP p SACT SRESP (SNAPSHOT SREADY SRESP) (emit (Accept 3w)) v)
Proof
  rpt strip_tac >> xcf_with_def (fetch "-" "accept3_v_def") >>
  xlet ‘POSTv av. &SACT (Accept 3w) av’
  >- (xcon >> xsimpl >> simp[SACT_def] >> EVAL_TAC) >>
  ‘app p Async_emit_v [av] emp
     (POSTv v. &COMP p SACT SRESP (SNAPSHOT SREADY SRESP) (emit (Accept 3w)) v)’
    by (irule Async_emit_spec >> simp[]) >>
  qpat_x_assum ‘app _ Async_emit_v _ _ _’ xapp_spec >> xsimpl
QED

(* MAIN: main runs accept3 in the event loop, polling listener 3: it never
   terminates, and its I/O trace is, round by round, the socket calls
   performing accept3's actions followed by the poll of listener 3, for
   the history the socket world generates.  Needs only that 3 is a
   listener in the initial world (this gives srun_ok). *)
Theorem main_spec:
  limited_parts socket_names p ∧ is_listener sk 3w ∧ UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) main_v [uv] (SOCKETS_EV sk [])
    (POSTd io. io = LFLATTEN (LGENLIST
                      (λi. fromList (sround_events [3w] accept3 sk i)) NONE))
Proof
  rpt strip_tac >> xcf_with_def (fetch "-" "main_v_def") >>
  (* the computation: Async.bind (Async.wait ready3) accept3 *)
  ‘app p Async_wait_v [ready3_v] emp
     (POSTv v. &COMP p SACT UNIT_TYPE (SNAPSHOT SREADY SRESP) (wait ready3) v)’
    by (irule Async_wait_spec >> rw[returns_def] >>
        irule ready3_spec >> simp[]) >>
  xlet ‘POSTv wv. &COMP p SACT UNIT_TYPE (SNAPSHOT SREADY SRESP) (wait ready3) wv *
                  SOCKETS_EV sk []’
  >- (qpat_x_assum ‘app _ Async_wait_v _ _ _’ xapp_spec >> xsimpl) >>
  sg ‘app p Async_bind_v [wv; accept3_v] emp
     (POSTv v. &COMP p SACT SRESP (SNAPSHOT SREADY SRESP) accept3 v)’
  >- (simp[accept3_def] >> irule Async_bind_spec >>
      simp[wf_wait, returns_def] >> qexists_tac ‘UNIT_TYPE’ >> rw[] >>
      irule accept3_spec >> simp[]) >>
  xlet ‘POSTv cv. &COMP p SACT SRESP (SNAPSHOT SREADY SRESP) accept3 cv *
                  SOCKETS_EV sk []’
  >- (qpat_x_assum ‘app _ Async_bind_v _ _ _’ xapp_spec >> xsimpl) >>
  (* the loop state ([3], c) *)
  rpt (xlet_auto >- (xcon >> xsimpl)) >>
  gvs[] >>
  sg ‘app p run_v [Conv NONE [Conv (SOME (TypeStamp «::» 1))
                         [Litv (IntLit 3); Conv (SOME (TypeStamp «[]» 1)) []]; cv]]
         (SOCKETS_EV sk [])
         (POSTd io. io = LFLATTEN (LGENLIST
                      (λi. fromList (sround_events [3w] accept3 sk i)) NONE))’
  >- (irule run_spec >> simp[wf_accept3, srun_ok_accept3] >>
      simp[LIST_TYPE_def] >> metis_tac[]) >>
  qpat_x_assum ‘app _ run_v _ _ _’ xapp_spec
QED

(* ------------------------------------------------------------------------
   The whole program (following ffiSpikeSocketDiv's serve_semantics)
   ------------------------------------------------------------------------ *)

val Decls_th =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> GEN_ALL |> ISPEC “socket_only_ffi sk” |> SPEC_ALL;

val (_, decls_args) = strip_comb (concl Decls_th);
val decs_tm = List.nth (decls_args, 2);
val env2_tm = List.nth (decls_args, 3);
val st2_tm = List.nth (decls_args, 4);

(* The program: basis, the Socket module, the Async library, the event
   loop and the example's code *)
val m3_prog_def = new_definition ("m3_prog_def",
  mk_eq (mk_var ("m3_prog", type_of decs_tm), decs_tm));

val lookup_main = let
  val g = “nsLookup (^env2_tm).v (Short «main») = SOME main_v”
  in prove (g, REWRITE_TAC [fst (dest_eq g) |> nsLookup_conv]) end;

val st2_ffi = prove (“(^st2_tm).ffi = socket_only_ffi sk”, EVAL_TAC);

(* MAIN: in a sockets-only world in which 3 is a listener, the whole
   program (basis, Socket, the Async library, the event loop, the example,
   and a call to main) diverges, and its I/O trace is, round by round, the
   socket calls performing accept3's actions followed by the poll of
   listener 3, for the history the socket world generates. *)
Theorem m3_semantics:
  is_listener sk 3w ⇒
  ∃io. semantics_dec_list (init_state (socket_only_ffi sk)) init_env
         (SNOC (main_call «main») m3_prog) (Diverge io) ∧
       io = LFLATTEN (LGENLIST
              (λi. fromList (sround_events [3w] accept3 sk i)) NONE)
Proof
  strip_tac
  \\ assume_tac (REWRITE_RULE [GSYM m3_prog_def] Decls_th)
  \\ drule call_main_thm_div \\ strip_tac
  \\ assume_tac st2_ffi
  \\ drule sonly_init_heap \\ strip_tac
  \\ first_x_assum (qspecl_then [‘sonly_proj2’, ‘sonly_proj1’, ‘h2’, ‘h1’,
       ‘main_v’, ‘«main»’,
       ‘λio. io = LFLATTEN (LGENLIST
                    (λi. fromList (sround_events [3w] accept3 sk i)) NONE)’,
       ‘SOCKETS_EV sk []’] mp_tac)
  \\ impl_tac
  >- (simp [lookup_var_def, lookup_main]
      \\ irule main_spec \\ simp [limited_parts_sonly])
  \\ simp []
QED

(* MAIN: and the trace agrees with the model: the actions performed by the
   socket calls in the first n+1 rounds are exactly accept3's action log
   on the history the socket world generates. *)
Theorem m3_trace_actions:
  is_listener sk 3w ⇒
  strace_actions (FLAT (GENLIST (sround_events [3w] accept3 sk) (SUC n))) =
  (accept3 (shist [3w] accept3 sk n)).actions
Proof
  strip_tac >> irule strace_actions_rounds >>
  simp[wf_accept3, srun_ok_accept3]
QED
