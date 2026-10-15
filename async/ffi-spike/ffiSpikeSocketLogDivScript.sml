(*
  A never-ending, logging server loop in the COMPOSED world (command line +
  file system + clock + sockets), proved down to Diverge with the
  multi-part divergence rule of ffiSpikeDivMulti.

      fun logpoll u = let val r = Socket.poll [3] in TextIO.print "polled\n" end
      fun serve u = serve (logpoll u)

  Each round uses two FFI parts: the socket part (poll) and the file
  system (print).  The rule tracks the socket part; the file system is in
  the frame, growing by one line per round.
*)
Theory ffiSpikeSocketLogDiv
Ancestors
  ml_translator cfMain cfDiv cfStore llist lprefix_lub basis_ffi TextIOProof
  mlstring fsFFI fsFFIProps clFFI CommandLineProof
  ffiSpikeClockFFI ffiSpikeClockProof ffiSpikeClockWorld
  ffiSpikeSocketFFI ffiSpikeSocketProof ffiSpikeSocketFair
  ffiSpikeSocketWorld ffiSpikeSocketDiv ffiSpikeDivMain ffiSpikeDivMulti ml_prog
Libs
  preamble basis ffiSpikeDivMultiLib

val _ = translation_extends "ffiSpikeSocketProg";

Quote add_cakeml:
  fun logpoll u = let val r = Socket.poll [3] in TextIO.print "polled\n" end
End

Quote add_cakeml:
  fun serve u = serve (logpoll u)
End

val st = get_ml_prog_state ();

Theorem logpoll_spec:
  UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) logpoll_v [uv]
    (STDIO fs * SOCKETS_EV s evs)
    (POSTv v. &UNIT_TYPE () v * STDIO (add_stdout fs «polled\n») *
              SOCKETS_EV (tick s) (evs ++ [poll_event [3w] s]))
Proof
  strip_tac
  \\ xcf "logpoll" st
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet ‘POSTv v. STDIO fs * SOCKETS_EV (tick s) (evs ++ [poll_event [3w] s])’
  >- (xapp_spec Socket_poll_spec_ev
      \\ qexistsl [‘STDIO fs’, ‘s’, ‘[3w]’, ‘evs’] \\ xsimpl
      \\ fs [LIST_TYPE_def] \\ rw [] \\ xsimpl)
  \\ xapp
  \\ qexistsl [‘SOCKETS_EV (tick s) (evs ++ [poll_event [3w] s])’,
               ‘«polled\n»’, ‘fs’]
  \\ xsimpl
QED

(* The log after n rounds. *)
Definition logs_def:
  logs fs n = FUNPOW (λfs. add_stdout fs «polled\n») n fs
End

Theorem GENLIST_prefix[local]:
  m ≤ n ⇒ GENLIST f m ≼ GENLIST f n
Proof
  strip_tac
  \\ ‘∃d. n = d + m’ by (qexists_tac ‘n - m’ \\ decide_tac)
  \\ pop_assum SUBST1_TAC \\ REWRITE_TAC [GENLIST_APPEND]
  \\ simp [IS_PREFIX_APPEND]
QED

Theorem lprefix_lub_GENLIST[local]:
  lprefix_lub (IMAGE (fromList o (λi. GENLIST f i)) UNIV) (LGENLIST f NONE)
Proof
  ‘lprefix_chain (IMAGE (fromList o (λi. GENLIST f i)) UNIV)’
    by (rw [lprefix_chain_def] \\ simp [LPREFIX_fromList, from_toList]
        \\ metis_tac [GENLIST_prefix, LESS_EQ_CASES])
  \\ simp [lprefix_lub_nth, LNTH_LGENLIST]
  \\ rw [] \\ CONV_TAC SYM_CONV
  \\ irule exists_lprefix_chain_nth \\ simp [PULL_EXISTS]
  \\ qexists_tac ‘SUC n’ \\ simp [LNTH_fromList]
QED

(* MAIN: serve never terminates; filtered to the socket names, its trace is
   the infinite sequence of polls of listener 3 in the world left alone. *)
Theorem serve_spec:
  UNIT_TYPE () uv ⇒
  app (socket_proj1, socket_proj2) serve_v [uv]
    (COMMANDLINE cl * STDIO fs * CLOCK clk * SOCKETS_EV sk [])
    (POSTd io. LFILTER (ffi_has_index_in socket_names) io =
               LGENLIST (λi. poll_event [3w] (ticks i sk)) NONE)
Proof
  xcf_div_filter ‘socket_names’ "serve" st
  \\ qexists_tac ‘λi. COMMANDLINE cl * STDIO (logs fs i) * CLOCK clk’
  \\ qexists_tac ‘λi. GENLIST (λj. poll_event [3w] (ticks j sk)) i’
  \\ qexists_tac ‘λi v. UNIT_TYPE () v’
  \\ qexists_tac ‘λi. sockets_encode (ticks i sk)’
  \\ qexists_tac ‘mk_ffi_next sockets_ffi_part’
  \\ qexists_tac ‘LGENLIST (λj. poll_event [3w] (ticks j sk)) NONE’
  \\ simp [lprefix_lub_GENLIST] \\ rpt conj_tac
  >- (simp [SOCKETS_EV_def, ticks_def, logs_def] \\ xsimpl)
  \\ rpt strip_tac
  \\ xlet ‘POSTv v. &UNIT_TYPE () v * STDIO (add_stdout (logs fs i) «polled\n») *
                     SOCKETS_EV (tick (ticks i sk))
                       (GENLIST (λj. poll_event [3w] (ticks j sk)) i ++
                        [poll_event [3w] (ticks i sk)]) *
                     COMMANDLINE cl * CLOCK clk’
  >- (cfTacticsLib.xapp_prepare_goal
      \\ mp_tac (logpoll_spec
                 |> Q.INST [‘fs’ |-> ‘logs fs i’, ‘s’ |-> ‘ticks i sk’,
                            ‘evs’ |-> ‘GENLIST (λj. poll_event [3w] (ticks j sk)) i’,
                            ‘uv’ |-> ‘xv'’]
                 |> Q.GEN ‘p’ |> ISPEC “(socket_proj1, socket_proj2)”)
      \\ impl_tac >- gvs []
      \\ strip_tac
      \\ first_x_assum (match_mp_tac o MP_CANON o MATCH_MP app_wgframe)
      \\ simp [SOCKETS_EV_def] \\ xsimpl)
  \\ xvar \\ xsimpl
  \\ simp [SOCKETS_EV_def, ticks_SUC, logs_def, FUNPOW_SUC, GENLIST, SNOC_APPEND]
  \\ xsimpl
QED

(*---------------------------------------------------------------------------*)
(* The whole program *)

(* socket_world_init_heap, with the socket part's (empty) event list
   exposed (a copy, changed in one line). *)
Theorem socket_world_init_heap_ev:
  st.ffi = socket_world_ffi cl fs clk sk ∧ is_refs_basis st.refs ∧
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ⇒
  ∃h1 h2. SPLIT (st2heap (socket_proj1, socket_proj2) st) (h1,h2) ∧
          (COMMANDLINE cl * STDIO fs * CLOCK clk * SOCKETS_EV sk []) h1
Proof
  rw [is_refs_basis_def]
  \\ irule SPLIT_exists
  \\ qabbrev_tac ‘cl_part =
        FFI_part (encode cl) (mk_ffi_next cl_ffi_part)
          [«get_arg_count»; «get_arg_length»; «get_arg»] []’
  \\ qabbrev_tac ‘fs_part =
        FFI_part (encode fs) (mk_ffi_next fs_ffi_part)
          (MAP FST (SND (SND fs_ffi_part))) []’
  \\ qabbrev_tac ‘clock_part =
        FFI_part (clock_encode clk) (mk_ffi_next clock_ffi_part) [«now»] []’
  \\ qabbrev_tac ‘socket_part =
        FFI_part (sockets_encode sk) (mk_ffi_next sockets_ffi_part)
          [«sock_poll»; «sock_accept»; «sock_read»; «sock_write»] []’
  \\ qexists_tac ‘{cl_part} ∪ ({fs_part} ∪ {Mem 1 (W8array bs2)}) ∪
                   {clock_part} ∪ {socket_part}’
  \\ conj_tac
  >- (rw [SUBSET_DEF] \\ unabbrev_all_tac
      \\ TRY (simp [st2heap_def, store2heap_def, store2heap_aux_def] \\ NO_TAC)
      \\ drule_then irule socket_world_part_in_heap
      \\ simp [socket_proj2_def, clock_proj2_def, basis_proj2_def,
               mk_proj2_def, basis_ffi_part_defs, clock_ffi_part_def,
               sockets_ffi_part_def]
      \\ rw [] \\ gvs []
      \\ simp [socket_proj1_def, mk_proj1_sockets, socket_names_def,
               clock_proj1_def, basis_proj1_def, mk_proj1_def,
               basis_ffi_part_defs, clock_ffi_part_def, FLOOKUP_UPDATE,
               FUPDATE_LIST_THM])
  \\ irule append_hprop \\ rpt conj_tac
  >- (irule append_hprop \\ rpt conj_tac
      >- (irule append_hprop \\ rpt conj_tac
          >- (unabbrev_all_tac
              \\ mp_tac (Q.INST [‘events’ |-> ‘[]’]
                            (DISCH_ALL COMMANDLINE_precond))
              \\ simp [cl_ffi_part_def])
          >- (unabbrev_all_tac
              \\ mp_tac (Q.INST [‘events’ |-> ‘[]’, ‘v’ |-> ‘bs2’]
                            STDIO_precond_1)
              \\ simp [])
          \\ unabbrev_all_tac \\ simp [fs_ffi_part_def])
      >- (unabbrev_all_tac \\ simp [CLOCK_precond])
      \\ unabbrev_all_tac \\ simp [fs_ffi_part_def])
  >- (unabbrev_all_tac \\ simp [SOCKETS_EV_def, one_def, socket_names_def])
  \\ unabbrev_all_tac \\ simp [fs_ffi_part_def]
QED

val Decls_th =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> GEN_ALL |> ISPEC “socket_world_ffi cl fs clk sk” |> SPEC_ALL;

val (_, decls_args) = strip_comb (concl Decls_th);
val decs_tm = List.nth (decls_args, 2);
val env2_tm = List.nth (decls_args, 3);
val st2_tm = List.nth (decls_args, 4);

val logserve_prog_def = new_definition ("logserve_prog_def",
  mk_eq (mk_var ("logserve_prog", type_of decs_tm), decs_tm));

val lookup_serve = let
  val g = “nsLookup (^env2_tm).v (Short «serve») = SOME serve_v”
  in prove (g, REWRITE_TAC [fst (dest_eq g) |> nsLookup_conv]) end;

val st2_ffi = prove (“(^st2_tm).ffi = socket_world_ffi cl fs clk sk”, EVAL_TAC);

val st2_refs = prove (“is_refs_basis (^st2_tm).refs”,
  EVAL_TAC
  \\ REWRITE_TAC [semanticPrimitivesTheory.store_v_11, APPEND, CONS_11,
                  basis_ffiTheory.basis_refs_eqs]
  \\ simp_tac std_ss [] \\ EVAL_TAC);

(* MAIN: in the composed world (command line, file system, clock,
   sockets), the whole program (basis, Socket, logpoll, serve, and a call
   to serve) diverges; filtered to the socket names, its trace is the
   infinite sequence of polls of listener 3, while the program also writes
   to stdout every round. *)
Theorem logserve_semantics:
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ⇒
  ∃io. semantics_dec_list (init_state (socket_world_ffi cl fs clk sk)) init_env
         (SNOC (main_call «serve») logserve_prog) (Diverge io) ∧
       LFILTER (ffi_has_index_in socket_names) io =
         LGENLIST (λi. poll_event [3w] (ticks i sk)) NONE
Proof
  strip_tac
  \\ assume_tac (REWRITE_RULE [GSYM logserve_prog_def] Decls_th)
  \\ drule call_main_thm_div \\ strip_tac
  \\ assume_tac st2_ffi \\ assume_tac st2_refs
  \\ drule_all socket_world_init_heap_ev \\ strip_tac
  \\ first_x_assum (qspecl_then [‘socket_proj2’, ‘socket_proj1’, ‘h2’, ‘h1’,
       ‘serve_v’, ‘«serve»’,
       ‘λio. LFILTER (ffi_has_index_in socket_names) io =
             LGENLIST (λi. poll_event [3w] (ticks i sk)) NONE’,
       ‘COMMANDLINE cl * STDIO fs * CLOCK clk * SOCKETS_EV sk []’] mp_tac)
  \\ impl_tac
  >- (simp [lookup_var_def, lookup_serve]
      \\ irule serve_spec \\ simp [])
  \\ simp []
QED
