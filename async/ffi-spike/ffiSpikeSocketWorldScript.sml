(*
  The composed world: command line + file system (the basis library's
  world) + clock + sockets, and its whole-program theorem.

  It is built on top of the clock world (ffiSpikeClockWorld), exactly as
  the clock world is built on top of basis_ffi: the socket names go to the
  socket part, every other name goes to the clock world's oracle, which
  leaves the sockets alone.  Nothing of basis_ffi or the clock world is
  edited; their lemmas are reused.
*)
Theory ffiSpikeSocketWorld
Ancestors
  semanticPrimitives ffi evaluateProps ml_prog cfHeapsBase cfStore cfMain
  set_sep fsFFI fsFFIProps clFFI CommandLineProof TextIOProof basis_ffi
  ffiSpikeClockFFI ffiSpikeClockProof ffiSpikeClockWorld
  ffiSpikeSocketFFI ffiSpikeSocketProof ffiSpikeDivMain
Libs
  preamble cfLib

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

(*---------------------------------------------------------------------------*)
(* The world: state, oracle and initial FFI state *)

Type socket_world_state = “:clock_world_state # sockets”

Definition socket_names_def:
  socket_names = [«sock_poll»; «sock_accept»; «sock_read»; «sock_write»]
End

(* The socket FFI function of a name. *)
Definition socket_call_def:
  socket_call m conf bytes (sk:sockets) =
    case ALOOKUP (SND (SND sockets_ffi_part)) m of
    | SOME f => f conf bytes sk
    | NONE => NONE
End

Definition socket_name_def:
  socket_name (ExtCall m) = (if MEM m socket_names then SOME m else NONE) ∧
  socket_name _ = NONE
End

(* The oracle: socket names go to the socket part, every other name to
   the clock world's oracle, which leaves the sockets alone. *)
Definition socket_world_oracle_def:
  socket_world_oracle (name:ffiname) ((cst,sk):socket_world_state) conf bytes =
    case socket_name name of
    | SOME m =>
        (case socket_call m conf bytes sk of
         | SOME (FFIreturn bytes' sk') => Oracle_return (cst,sk') bytes'
         | _ => Oracle_final FFI_failed)
    | NONE =>
        (case clock_world_oracle name cst conf bytes of
         | Oracle_return cst' bytes' => Oracle_return (cst',sk) bytes'
         | Oracle_final outcome => Oracle_final outcome)
End

Definition socket_world_ffi_def:
  socket_world_ffi cl fs clk sk =
    <| oracle := socket_world_oracle
     ; ffi_state := (((cl,fs),clk),sk)
     ; io_events := [] |>
End

Definition socket_proj1_def:
  socket_proj1 ((cst,sk):socket_world_state) =
    clock_proj1 cst |++ mk_proj1 sockets_ffi_part sk
End

Definition socket_proj2_def:
  socket_proj2 = clock_proj2 ++ [mk_proj2 sockets_ffi_part]
End

(*---------------------------------------------------------------------------*)
(* parts_ok *)

Definition is_clock_world_name_def:
  is_clock_world_name m ⇔ is_basis_ffi_name m ∨ m = «now»
End

Theorem clock_proj2_names:
  MEM (ns,u) clock_proj2 ∧ MEM m ns ⇒ is_clock_world_name m
Proof
  rw [clock_proj2_def, is_clock_world_name_def]
  >- metis_tac [basis_proj2_names]
  \\ gvs [mk_proj2_def, clock_ffi_part_def]
QED

Theorem socket_name_not_clock_world_name:
  MEM m socket_names ⇒ ¬is_clock_world_name m
Proof
  rw [socket_names_def, is_clock_world_name_def] \\ EVAL_TAC
QED

Theorem socket_name_clock_world_name:
  is_clock_world_name m ⇒ socket_name (ExtCall m) = NONE
Proof
  metis_tac [socket_name_def, socket_name_not_clock_world_name]
QED

Theorem mk_proj1_sockets:
  mk_proj1 sockets_ffi_part sk = MAP (λn. (n, sockets_encode sk)) socket_names
Proof
  simp [mk_proj1_def, sockets_ffi_part_def, socket_names_def]
QED

Theorem socket_proj1_clock_name:
  is_clock_world_name m ⇒ socket_proj1 (cst,sk) ' m = clock_proj1 cst ' m
Proof
  rw [socket_proj1_def, mk_proj1_sockets]
  \\ irule FUPDATE_LIST_APPLY_NOT_MEM
  \\ simp [MAP_MAP_o, combinTheory.o_DEF]
  \\ metis_tac [socket_name_not_clock_world_name]
QED

Theorem socket_proj1_socket_name:
  MEM m socket_names ⇒ socket_proj1 (cst,sk) ' m = sockets_encode sk
Proof
  rw [socket_proj1_def, mk_proj1_sockets, socket_names_def]
  \\ simp [FUPDATE_LIST_THM, FAPPLY_FUPDATE_THM]
QED

Theorem FLOOKUP_socket_proj1_clock:
  is_clock_world_name n ⇒
  FLOOKUP (socket_proj1 (cst,sk)) n = FLOOKUP (clock_proj1 cst) n
Proof
  strip_tac
  \\ ‘¬MEM n socket_names’ by metis_tac [socket_name_not_clock_world_name]
  \\ simp [socket_proj1_def, mk_proj1_sockets, FLOOKUP_FUPDATE_LIST,
           ALOOKUP_NONE, MAP_REVERSE, MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem FLOOKUP_socket_proj1_socket:
  MEM n socket_names ⇒
  FLOOKUP (socket_proj1 (cst,sk)) n = SOME (sockets_encode sk)
Proof
  rw [socket_proj1_def, mk_proj1_sockets, socket_names_def]
  \\ simp [FUPDATE_LIST_THM, FLOOKUP_UPDATE]
QED

Theorem socket_world_oracle_clock_name:
  is_clock_world_name m ⇒
  socket_world_oracle (ExtCall m) (cst,sk) conf bytes =
    case clock_world_oracle (ExtCall m) cst conf bytes of
    | Oracle_return cst' bytes' => Oracle_return (cst',sk) bytes'
    | Oracle_final outcome => Oracle_final outcome
Proof
  rw [socket_world_oracle_def, socket_name_clock_world_name]
QED

(* The socket part's half of parts_ok. *)
Theorem socket_part_return:
  mk_ffi_next sockets_ffi_part m conf bytes (sockets_encode sk) =
    SOME (FFIreturn new_bytes w) ⇒
  LENGTH new_bytes = LENGTH bytes ∧
  ∃sk'. socket_call m conf bytes sk = SOME (FFIreturn new_bytes sk') ∧
        w = sockets_encode sk'
Proof
  strip_tac
  \\ gvs [mk_ffi_next_def, sockets_ffi_part_def, socket_call_def,
          AllCaseEqs()]
  \\ metis_tac [ffi_sock_length]
QED

Theorem socket_part_not_diverge:
  mk_ffi_next sockets_ffi_part m conf bytes (sockets_encode sk) ≠ SOME FFIdiverge
Proof
  rw [mk_ffi_next_def, sockets_ffi_part_def, AllCaseEqs()]
  \\ rw [] \\ metis_tac [ffi_sock_not_diverge]
QED

(* Updating our projection on clock-world names commutes with the socket
   entries. *)
Theorem socket_proj1_update_clock:
  (∀n. MEM n ns ⇒ is_clock_world_name n) ∧
  clock_proj1 cst |++ MAP (λn. (n,w)) ns = clock_proj1 cst' ⇒
  socket_proj1 (cst,sk) |++ MAP (λn. (n,w)) ns = socket_proj1 (cst',sk)
Proof
  rw [socket_proj1_def, mk_proj1_sockets]
  \\ pop_assum (SUBST1_TAC o SYM)
  \\ irule FUPDATE_LIST_APPEND_COMMUTES
  \\ simp [MAP_MAP_o, combinTheory.o_DEF, IN_DISJOINT, MEM_MAP]
  \\ rw [] \\ CCONTR_TAC \\ gvs []
  \\ metis_tac [socket_name_not_clock_world_name]
QED

Theorem ALOOKUP_MAP_const:
  ∀ns. ALOOKUP (MAP (λn. (n,b)) ns) k = if MEM k ns then SOME b else NONE
Proof
  Induct \\ rw [] \\ gvs []
QED

(* Updating the same keys twice: the second update wins. *)
Theorem FUPDATE_LIST_same_keys:
  fm |++ MAP (λn. (n,a)) ns |++ MAP (λn. (n,b)) ns =
  fm |++ MAP (λn. (n,b)) ns
Proof
  rw [GSYM FUPDATE_LIST_APPEND, fmap_eq_flookup, FLOOKUP_FUPDATE_LIST,
      REVERSE_APPEND, ALOOKUP_APPEND, MAP_REVERSE, ALOOKUP_MAP_const]
  \\ rw [] \\ gvs []
QED

Theorem socket_world_oracle_parts:
  MEM (ns,u) socket_proj2 ∧ MEM m ns ∧
  u m conf bytes (socket_proj1 x ' m) = SOME (FFIreturn new_bytes w) ⇒
  LENGTH new_bytes = LENGTH bytes ∧
  ∃y. socket_world_oracle (ExtCall m) x conf bytes = Oracle_return y new_bytes ∧
      socket_proj1 x |++ MAP (λn. (n,w)) ns = socket_proj1 y
Proof
  PairCases_on ‘x’ \\ rw [socket_proj2_def]
  >~ [‘MEM (ns,u) clock_proj2’]
  >- (‘is_clock_world_name m’ by metis_tac [clock_proj2_names]
      \\ gvs [socket_proj1_clock_name]
      \\ drule_all clock_world_oracle_parts \\ simp [])
  >~ [‘MEM (ns,u) clock_proj2’]
  >- (‘is_clock_world_name m’ by metis_tac [clock_proj2_names]
      \\ gvs [socket_proj1_clock_name]
      \\ drule_all clock_world_oracle_parts \\ strip_tac
      \\ simp [socket_world_oracle_clock_name]
      \\ irule socket_proj1_update_clock
      \\ metis_tac [clock_proj2_names])
  \\ ‘ns = socket_names ∧ u = mk_ffi_next sockets_ffi_part’
    by gvs [mk_proj2_def, sockets_ffi_part_def, socket_names_def]
  \\ gvs []
  \\ gvs [socket_proj1_socket_name]
  \\ drule socket_part_return \\ strip_tac \\ simp []
  \\ simp [socket_world_oracle_def, socket_name_def]
  \\ simp [socket_proj1_def, mk_proj1_sockets, FUPDATE_LIST_same_keys]
QED

Theorem socket_world_oracle_parts_div:
  MEM (ns,u) socket_proj2 ∧ MEM m ns ∧
  u m conf bytes (socket_proj1 x ' m) = SOME FFIdiverge ⇒
  socket_world_oracle (ExtCall m) x conf bytes = Oracle_final FFI_diverged
Proof
  PairCases_on ‘x’ \\ rw [socket_proj2_def]
  >- (‘is_clock_world_name m’ by metis_tac [clock_proj2_names]
      \\ gvs [socket_proj1_clock_name]
      \\ drule_all clock_world_oracle_parts_div
      \\ simp [socket_world_oracle_clock_name])
  \\ ‘ns = socket_names ∧ u = mk_ffi_next sockets_ffi_part’
    by gvs [mk_proj2_def, sockets_ffi_part_def, socket_names_def]
  \\ gvs []
  \\ gvs [socket_proj1_socket_name, socket_part_not_diverge]
QED

Theorem parts_ok_socket_world_ffi:
  parts_ok (socket_world_ffi cl fs clk sk) (socket_proj1, socket_proj2)
Proof
  rw [parts_ok_def, socket_world_ffi_def]
  >- EVAL_TAC
  >- (gvs [socket_proj2_def]
      >- (mp_tac (Q.INST [‘clk’ |-> ‘clk’] parts_ok_clock_world_ffi)
          \\ rw [parts_ok_def, clock_world_ffi_def]
          \\ qpat_x_assum ‘∀ns u. MEM _ clock_proj2 ⇒ ∃s. _’ drule
          \\ strip_tac \\ qexists_tac ‘s’ \\ rw []
          \\ ‘is_clock_world_name n’ by metis_tac [clock_proj2_names]
          \\ simp [FLOOKUP_socket_proj1_clock])
      \\ qexists_tac ‘sockets_encode sk’
      \\ gvs [mk_proj2_def, sockets_ffi_part_def]
      \\ rw [FLOOKUP_socket_proj1_socket, socket_names_def])
  >- (drule_all socket_world_oracle_parts_div \\ simp [])
  >- (drule_all socket_world_oracle_parts \\ simp [])
  \\ drule_all socket_world_oracle_parts \\ simp []
QED

(*---------------------------------------------------------------------------*)
(* The clock world's view of a run in our world *)

Definition is_socket_event_def:
  is_socket_event (IO_event name conf bytes) ⇔ socket_name name ≠ NONE
End

Definition clock_view_def:
  clock_view (s : socket_world_state ffi_state) =
    <| oracle := clock_world_oracle
     ; ffi_state := FST s.ffi_state
     ; io_events := FILTER ($¬ o is_socket_event) s.io_events |>
End

(* One FFI step of our world is either invisible to the clock world (a
   socket call) or a step of the clock world. *)
Theorem call_FFI_rel_clock_view:
  call_FFI_rel s s' ∧ s.oracle = socket_world_oracle ⇒
  s'.oracle = socket_world_oracle ∧
  (clock_view s' = clock_view s ∨ call_FFI_rel (clock_view s) (clock_view s'))
Proof
  rw [call_FFI_rel_def, call_FFI_def] \\ gvs [AllCaseEqs()]
  \\ Cases_on ‘s.ffi_state’ \\ rename1 ‘s.ffi_state = (cst,sk)’
  \\ Cases_on ‘socket_name n’
  >- (gvs [socket_world_oracle_def, AllCaseEqs()]
      \\ disj2_tac
      \\ simp [call_FFI_rel_def, call_FFI_def, clock_view_def]
      \\ qexistsl [‘n’, ‘conf’, ‘bytes’]
      \\ simp [FILTER_APPEND, is_socket_event_def])
  \\ gvs [socket_world_oracle_def, AllCaseEqs()]
  \\ disj1_tac
  \\ simp [clock_view_def, FILTER_APPEND, is_socket_event_def]
QED

Theorem RTC_call_FFI_rel_clock_view:
  ∀s s'. call_FFI_rel^* s s' ⇒ s.oracle = socket_world_oracle ⇒
         call_FFI_rel^* (clock_view s) (clock_view s')
Proof
  ho_match_mp_tac RTC_INDUCT \\ rw []
  \\ drule_all call_FFI_rel_clock_view \\ rw [] \\ gvs []
  \\ metis_tac [RTC_RULES]
QED

(* The file system after a run, replayed from the basis events. *)
Definition socket_extract_fs_def:
  socket_extract_fs cl fs events =
    clock_extract_fs cl fs (FILTER ($¬ o is_socket_event) events)
End

Theorem socket_world_extract:
  call_FFI_rel^* (socket_world_ffi cl fs clk sk) s ⇒
  extract_fs_with_numchars no_ext (cl,fs)
    (FILTER ($¬ o is_clock_event) (FILTER ($¬ o is_socket_event) s.io_events)) =
  SOME (FST (FST s.ffi_state))
Proof
  strip_tac
  \\ drule RTC_call_FFI_rel_clock_view
  \\ simp [socket_world_ffi_def] \\ strip_tac
  \\ ‘clock_view (socket_world_ffi cl fs clk sk) = clock_world_ffi cl fs clk’
    by simp [clock_view_def, socket_world_ffi_def, clock_world_ffi_def]
  \\ gvs [socket_world_ffi_def]
  \\ drule clock_world_extract
  \\ simp [clock_view_def]
QED

(*---------------------------------------------------------------------------*)
(* Heaps *)

Theorem socket_world_part_in_heap:
  st.ffi = socket_world_ffi cl fs clk sk ⇒
  MEM (ns,u) socket_proj2 ∧ ns ≠ [] ∧
  (∀n. MEM n ns ⇒ FLOOKUP (socket_proj1 (((cl,fs),clk),sk)) n = SOME s) ⇒
  FFI_part s u ns [] ∈ st2heap (socket_proj1, socket_proj2) st
Proof
  rw [st2heap_def, ffi2heap_def, parts_ok_socket_world_ffi]
  \\ simp [socket_world_ffi_def]
QED

(* The initial heap satisfies the precondition of a whole-program spec. *)
Theorem socket_world_init_heap:
  st.ffi = socket_world_ffi cl fs clk sk ∧ is_refs_basis st.refs ∧
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ⇒
  ∃h1 h2. SPLIT (st2heap (socket_proj1, socket_proj2) st) (h1,h2) ∧
          (COMMANDLINE cl * STDIO fs * CLOCK clk * SOCKETS sk) h1
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
  >- (unabbrev_all_tac \\ simp [SOCKETS_precond])
  \\ unabbrev_all_tac \\ simp [fs_ffi_part_def]
QED

Theorem FLOOKUP_socket_proj1_write:
  FLOOKUP (socket_proj1 x) «write» = SOME (encode (SND (FST (FST x))))
Proof
  PairCases_on ‘x’
  \\ ‘is_clock_world_name «write»’ by EVAL_TAC
  \\ simp [FLOOKUP_socket_proj1_clock, FLOOKUP_clock_proj1_write]
QED

(* If part of the heap of a state satisfies STDIO fs', then the state's
   file system is fs' (up to numchars). *)
Theorem socket_world_STDIO_heap:
  STDIO fs' h ∧ h ⊆ st2heap (socket_proj1, socket_proj2) st ⇒
  ∃ll. SND (FST (FST st.ffi.ffi_state)) = fs' with numchars := ll
Proof
  rw [SUBSET_DEF]
  \\ drule STDIO_FFI_part \\ strip_tac
  \\ first_x_assum drule
  \\ simp [st2heap_def, FFI_part_NOT_IN_store2heap, ffi2heap_def]
  \\ Cases_on ‘parts_ok st.ffi (socket_proj1, socket_proj2)’ \\ gvs []
  \\ rpt strip_tac
  \\ first_x_assum (qspec_then ‘«write»’ mp_tac)
  \\ simp [fs_ffi_part_def, FLOOKUP_socket_proj1_write]
  \\ metis_tac []
QED

(* If part of the heap of a state satisfies SOCKETS sk', then the state's
   socket component is sk'. *)
Theorem socket_world_SOCKETS_heap:
  SOCKETS sk' h ∧ h ⊆ st2heap (socket_proj1, socket_proj2) st ⇒
  SND st.ffi.ffi_state = sk'
Proof
  rw [SUBSET_DEF]
  \\ gvs [SOCKETS_def, sockets_ffi_part_def, IOx_def, IO_def, SEP_EXISTS_THM,
          cond_STAR, one_def]
  \\ pop_assum mp_tac
  \\ simp [st2heap_def, FFI_part_NOT_IN_store2heap, ffi2heap_def]
  \\ IF_CASES_TAC \\ simp [] \\ rpt strip_tac
  \\ first_x_assum (qspec_then ‘«sock_poll»’ mp_tac)
  \\ Cases_on ‘st.ffi.ffi_state’
  \\ simp [sockets_ffi_part_def, FLOOKUP_socket_proj1_socket, socket_names_def]
  \\ strip_tac
  \\ pop_assum (mp_tac o AP_TERM “sockets_decode”) \\ simp []
QED

(*---------------------------------------------------------------------------*)
(* The whole-program theorems *)

(* A spec for main in our world: from the command line, standard streams,
   clock and sockets, main returns unit and leaves standard streams and
   sockets satisfying post. *)
Definition socket_whole_prog_spec_def:
  socket_whole_prog_spec fv cl fs clk sk post ⇔
    ∃fs' sk'.
      app (socket_proj1, socket_proj2) fv [Conv NONE []]
        (COMMANDLINE cl * STDIO fs * CLOCK clk * SOCKETS sk)
        (POSTv uv. &UNIT_TYPE () uv * (STDIO fs' * SOCKETS sk')) ∧
      post (fs' with numchars := fs.numchars) sk'
End

(* MAIN: a program whose main satisfies a socket_whole_prog_spec
   terminates successfully in our world; replaying its file-system events
   gives a file system fs', and its run ends in a socket state sk' (the
   state reached by its FFI events), with post fs' sk'. *)
Theorem socket_whole_prog_spec_semantics:
  socket_whole_prog_spec main_v cl fs clk sk post ∧
  Decls init_env (init_state (socket_world_ffi cl fs clk sk)) decs res_env res_st
  ⇒
  ∀main_name.
    let all_decs = SNOC (Dlet NoLocs (Pcon NONE [])
                     (App Opapp [Var (Short main_name); Con NONE []])) decs in
    nsLookup res_env.v (Short main_name) = SOME main_v
    ⇒
    res_st.ffi = socket_world_ffi cl fs clk sk
    ⇒
    is_refs_basis res_st.refs
    ⇒
    wfcl cl ∧ wfFS fs ∧ STD_streams fs ⇒
    ∃io_events fs' ffi'.
      semantics_dec_list
        (init_state (socket_world_ffi cl fs clk sk)) init_env
        all_decs
        (Terminate Success io_events) ∧
      socket_extract_fs cl fs io_events = SOME fs' ∧
      call_FFI_rel^* (socket_world_ffi cl fs clk sk) ffi' ∧
      ffi'.io_events = io_events ∧
      post fs' (SND ffi'.ffi_state)
Proof
  simp [] \\ rpt strip_tac
  \\ gvs [socket_whole_prog_spec_def]
  \\ ‘lookup_var main_name res_env = SOME main_v’ by simp [lookup_var_def]
  \\ drule_all socket_world_init_heap \\ strip_tac
  \\ drule call_main_thm2 \\ rpt (disch_then drule)
  \\ disch_then (qspecl_then [‘h2’, ‘h1’] mp_tac)
  \\ impl_tac
  >- (simp []
      \\ match_mp_tac FFI_part_hprop_STAR \\ disj2_tac
      \\ simp [SOCKETS_FFI_part_hprop])
  \\ strip_tac
  \\ first_x_assum (irule_at Any)
  \\ ‘h3 ⊆ st2heap (socket_proj1, socket_proj2) st3’
    by (fs [SPLIT3_def] \\ simp [SUBSET_DEF] \\ metis_tac [IN_UNION])
  \\ qpat_x_assum ‘(STDIO _ * SOCKETS _) _’
       (strip_assume_tac o SIMP_RULE std_ss [STAR_def, SPLIT_def])
  \\ rveq
  \\ ‘u ⊆ st2heap (socket_proj1, socket_proj2) st3 ∧
      v ⊆ st2heap (socket_proj1, socket_proj2) st3’
    by fs [SUBSET_DEF]
  \\ drule_all socket_world_STDIO_heap \\ strip_tac
  \\ drule_all socket_world_SOCKETS_heap \\ strip_tac
  \\ gvs [ml_progTheory.init_state_def]
  \\ qexists_tac ‘fs' with numchars := fs.numchars’ \\ simp []
  \\ drule socket_world_extract
  \\ simp [socket_extract_fs_def, clock_extract_fs_def, extract_fs_def]
QED

(* A spec for a main that never returns (a server). *)
Definition socket_whole_prog_div_spec_def:
  socket_whole_prog_div_spec fv cl fs clk sk Q ⇔
    app (socket_proj1, socket_proj2) fv [Conv NONE []]
      (COMMANDLINE cl * STDIO fs * CLOCK clk * SOCKETS sk) ($POSTd Q)
End

(* MAIN: a program whose main satisfies a socket_whole_prog_div_spec
   diverges in our world, and its infinite I/O trace satisfies Q. *)
Theorem socket_whole_prog_div_spec_semantics:
  socket_whole_prog_div_spec main_v cl fs clk sk Q ∧
  Decls init_env (init_state (socket_world_ffi cl fs clk sk)) decs res_env res_st
  ⇒
  ∀main_name.
    nsLookup res_env.v (Short main_name) = SOME main_v
    ⇒
    res_st.ffi = socket_world_ffi cl fs clk sk
    ⇒
    is_refs_basis res_st.refs
    ⇒
    wfcl cl ∧ wfFS fs ∧ STD_streams fs ⇒
    ∃io. semantics_dec_list
           (init_state (socket_world_ffi cl fs clk sk)) init_env
           (SNOC (main_call main_name) decs) (Diverge io) ∧
         Q io
Proof
  rpt strip_tac
  \\ gvs [socket_whole_prog_div_spec_def]
  \\ ‘lookup_var main_name res_env = SOME main_v’ by simp [lookup_var_def]
  \\ drule_all socket_world_init_heap \\ strip_tac
  \\ drule call_main_thm_div \\ rpt (disch_then drule)
  \\ disch_then irule \\ metis_tac []
QED
