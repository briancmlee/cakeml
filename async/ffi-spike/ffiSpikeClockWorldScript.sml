(*
  Our own top-level world: the basis library's world (command line, file
  system, runtime) extended with the clock part, and a whole-program
  theorem for it, adapted from basis_ffi's whole_prog_spec theorems.

  basis_ffi is reused, not edited: the basis oracle, projections and
  their lemmas are used as they are, and the clock is added around them.
*)
Theory ffiSpikeClockWorld
Ancestors
  semanticPrimitives ffi evaluateProps ml_prog cfHeapsBase cfStore cfMain
  set_sep fsFFI fsFFIProps clFFI runtimeFFI CommandLineProof TextIOProg
  TextIOProof basis_ffi ffiSpikeClockFFI ffiSpikeClockProof
Libs
  preamble cfLib

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

(*---------------------------------------------------------------------------*)
(* The world: state, oracle and initial FFI state *)

(* The state of our world: the basis library's state (command-line
   arguments, file system) paired with the clock's schedule. *)
Type clock_world_state = “:(mlstring list # IO_fs) # num llist”

(* The oracle: «now» goes to the clock; every other name goes to the
   basis oracle (with no extension), which leaves the clock alone. *)
Definition clock_world_oracle_def:
  clock_world_oracle (name:ffiname) ((st,clk):clock_world_state) conf bytes =
    if name = ExtCall «now» then
      case ffi_now conf bytes clk of
      | SOME (FFIreturn bytes' clk') => Oracle_return (st,clk') bytes'
      | _ => Oracle_final FFI_failed
    else
      case basis_ffi_oracle no_ext name st conf bytes of
      | Oracle_return st' bytes' => Oracle_return (st',clk) bytes'
      | Oracle_final outcome => Oracle_final outcome
End

(* The initial FFI state of a program run in our world. *)
Definition clock_world_ffi_def:
  clock_world_ffi cl fs clk =
    <| oracle := clock_world_oracle
     ; ffi_state := ((cl,fs),clk)
     ; io_events := [] |>
End

(* The projections for CF: basis_ffi's, plus the clock part. *)
Definition clock_proj1_def:
  clock_proj1 ((st,clk):clock_world_state) =
    basis_proj1 st |++ mk_proj1 clock_ffi_part clk
End

Definition clock_proj2_def:
  clock_proj2 = basis_proj2 ++ [mk_proj2 clock_ffi_part]
End

(*---------------------------------------------------------------------------*)
(* parts_ok: the projections agree with the oracle *)

Theorem basis_proj2_names:
  MEM (ns,u) basis_proj2 ∧ MEM m ns ⇒ is_basis_ffi_name m
Proof
  rw [basis_proj2_def, mk_proj2_def, basis_ffi_part_defs, is_basis_ffi_name_def]
  \\ gvs []
QED

Theorem now_not_basis_ffi_name:
  ¬is_basis_ffi_name «now»
Proof
  EVAL_TAC
QED

(* On a basis name, our projection is the basis projection. *)
Theorem clock_proj1_basis_name:
  is_basis_ffi_name m ⇒ clock_proj1 (st,clk) ' m = basis_proj1 st ' m
Proof
  strip_tac
  \\ ‘m ≠ «now»’ by (strip_tac \\ gvs [now_not_basis_ffi_name])
  \\ simp [clock_proj1_def, clock_ffi_part_def, mk_proj1_def,
           FUPDATE_LIST_THM, FAPPLY_FUPDATE_THM]
QED

Theorem clock_proj1_now:
  clock_proj1 (st,clk) ' «now» = clock_encode clk
Proof
  simp [clock_proj1_def, clock_ffi_part_def, mk_proj1_def,
        FUPDATE_LIST_THM, FAPPLY_FUPDATE_THM]
QED

(* On a basis name, our oracle is the basis oracle, lifted. *)
Theorem clock_world_oracle_basis_name:
  is_basis_ffi_name m ⇒
  clock_world_oracle (ExtCall m) (st,clk) conf bytes =
    case basis_ffi_oracle no_ext (ExtCall m) st conf bytes of
    | Oracle_return st' bytes' => Oracle_return (st',clk) bytes'
    | Oracle_final outcome => Oracle_final outcome
Proof
  strip_tac
  \\ ‘m ≠ «now»’ by (strip_tac \\ gvs [now_not_basis_ffi_name])
  \\ simp [clock_world_oracle_def]
QED

(* basis_ffi's oracle_parts and oracle_parts_div talk about the oracle of
   an arbitrary semantic state; these are the same facts about the oracle
   itself. *)
Theorem basis_oracle_parts:
  MEM (ns,u) basis_proj2 ∧ MEM m ns ∧
  u m conf bytes (basis_proj1 x ' m) = SOME (FFIreturn new_bytes w) ⇒
  ∃y. basis_ffi_oracle no_ext (ExtCall m) x conf bytes =
        Oracle_return y new_bytes ∧
      basis_proj1 x |++ MAP (λn. (n,w)) ns = basis_proj1 y
Proof
  strip_tac
  \\ qspec_then ‘ARB with ffi := basis_ffi no_ext ARB ARB’ mp_tac
       (Q.INST [‘ext’ |-> ‘no_ext’] oracle_parts)
  \\ simp [basis_ffi_def]
  \\ disch_then drule_all \\ simp []
QED

Theorem basis_oracle_parts_div:
  MEM (ns,u) basis_proj2 ∧ MEM m ns ∧
  u m conf bytes (basis_proj1 x ' m) = SOME FFIdiverge ⇒
  basis_ffi_oracle no_ext (ExtCall m) x conf bytes = Oracle_final FFI_diverged
Proof
  strip_tac
  \\ qspec_then ‘ARB with ffi := basis_ffi no_ext ARB ARB’ mp_tac
       (Q.INST [‘ext’ |-> ‘no_ext’] oracle_parts_div)
  \\ simp [basis_ffi_def]
  \\ disch_then drule_all \\ simp []
QED

(* The basis parts preserve buffer lengths (copied from the length part of
   basis_ffi's parts_ok_basis_st, which proves it inline). *)
Theorem basis_parts_length:
  MEM (ns,u) basis_proj2 ∧
  u m conf bytes s = SOME (FFIreturn new_bytes w) ⇒
  LENGTH new_bytes = LENGTH bytes
Proof
  rw [basis_proj2_def, basis_ffi_part_defs, mk_proj2_def]
  \\ gvs [mk_ffi_next_def, AllCaseEqs()]
  \\ EVERY (map imp_res_tac (CONJUNCTS basis_ffi_length_thms)) \\ fs []
QED

(* The clock part's half of parts_ok. *)
Theorem clock_part_return:
  mk_ffi_next clock_ffi_part m conf bytes (clock_encode clk) =
    SOME (FFIreturn new_bytes w) ∧ m = «now» ⇒
  LENGTH new_bytes = LENGTH bytes ∧
  ∃clk'. ffi_now conf bytes clk = SOME (FFIreturn new_bytes clk') ∧
         w = clock_encode clk'
Proof
  rw [mk_ffi_next_def, clock_ffi_part_def]
  \\ gvs [AllCaseEqs(), ffi_now_not_diverge]
  \\ imp_res_tac ffi_now_length \\ simp []
QED

(* Updating our projection on basis names commutes with the clock entry. *)
Theorem clock_proj1_update_basis:
  (∀n. MEM n ns ⇒ is_basis_ffi_name n) ∧
  basis_proj1 st |++ MAP (λn. (n,w)) ns = basis_proj1 st' ⇒
  clock_proj1 (st,clk) |++ MAP (λn. (n,w)) ns = clock_proj1 (st',clk)
Proof
  rw [clock_proj1_def, clock_ffi_part_def, mk_proj1_def]
  \\ pop_assum (SUBST1_TAC o SYM)
  \\ irule FUPDATE_LIST_APPEND_COMMUTES
  \\ simp [MAP_MAP_o, combinTheory.o_DEF, IN_DISJOINT, MEM_MAP]
  \\ rw [] \\ CCONTR_TAC \\ gvs []
  \\ metis_tac [now_not_basis_ffi_name]
QED

(* The oracle half of parts_ok, for returning calls. *)
Theorem clock_world_oracle_parts:
  MEM (ns,u) clock_proj2 ∧ MEM m ns ∧
  u m conf bytes (clock_proj1 x ' m) = SOME (FFIreturn new_bytes w) ⇒
  LENGTH new_bytes = LENGTH bytes ∧
  ∃y. clock_world_oracle (ExtCall m) x conf bytes = Oracle_return y new_bytes ∧
      clock_proj1 x |++ MAP (λn. (n,w)) ns = clock_proj1 y
Proof
  PairCases_on ‘x’ \\ rw [clock_proj2_def]
  >~ [‘MEM (ns,u) basis_proj2’]
  >- (imp_res_tac basis_parts_length)
  >~ [‘MEM (ns,u) basis_proj2’]
  >- (‘is_basis_ffi_name m’ by metis_tac [basis_proj2_names]
      \\ gvs [clock_proj1_basis_name]
      \\ drule_all basis_oracle_parts \\ strip_tac
      \\ simp [clock_world_oracle_basis_name]
      \\ irule clock_proj1_update_basis
      \\ metis_tac [basis_proj2_names])
  \\ gvs [mk_proj2_def, clock_ffi_part_def]
  \\ gvs [GSYM clock_ffi_part_def, clock_proj1_now]
  \\ drule clock_part_return \\ simp [] \\ strip_tac
  \\ simp [clock_world_oracle_def, clock_proj1_def, clock_ffi_part_def,
           mk_proj1_def, FUPDATE_LIST_THM, FUPDATE_EQ]
QED

(* The oracle half of parts_ok, for diverging calls. *)
Theorem clock_world_oracle_parts_div:
  MEM (ns,u) clock_proj2 ∧ MEM m ns ∧
  u m conf bytes (clock_proj1 x ' m) = SOME FFIdiverge ⇒
  clock_world_oracle (ExtCall m) x conf bytes = Oracle_final FFI_diverged
Proof
  PairCases_on ‘x’ \\ rw [clock_proj2_def]
  >- (‘is_basis_ffi_name m’ by metis_tac [basis_proj2_names]
      \\ gvs [clock_proj1_basis_name]
      \\ drule_all basis_oracle_parts_div
      \\ simp [clock_world_oracle_basis_name])
  \\ gvs [mk_proj2_def, clock_ffi_part_def, mk_ffi_next_def, clock_proj1_def,
          mk_proj1_def, FUPDATE_LIST_THM, AllCaseEqs(), ffi_now_not_diverge]
QED

(* Our projections are well-formed for the initial FFI state. *)
Theorem parts_ok_clock_world_ffi:
  parts_ok (clock_world_ffi cl fs clk) (clock_proj1, clock_proj2)
Proof
  rw [parts_ok_def, clock_world_ffi_def]
  >- EVAL_TAC
  >- (gvs [clock_proj2_def, basis_proj2_def, mk_proj2_def,
           basis_ffi_part_defs, clock_ffi_part_def]
      \\ simp [clock_proj1_def, basis_proj1_def, mk_proj1_def,
               basis_ffi_part_defs, clock_ffi_part_def,
               FLOOKUP_UPDATE, FUPDATE_LIST_THM]
      \\ rw []
      \\ FIRST (map (fn w => qexists_tac w \\ rw [] \\ gvs [] \\ NO_TAC)
                   [‘encode fs’, ‘encode cl’]))
  >- (drule_all clock_world_oracle_parts_div \\ simp [])
  >- (drule_all clock_world_oracle_parts \\ simp [])
  \\ drule_all clock_world_oracle_parts \\ simp []
QED

(*---------------------------------------------------------------------------*)
(* The basis library's view of a run in our world *)

(* Clock events: the I/O events of the FFI name «now». *)
Definition is_clock_event_def:
  is_clock_event (IO_event name conf bytes) ⇔ name = ExtCall «now»
End

(* What the basis library sees of an FFI state of our world: its own
   state and its own events, under the basis oracle. *)
Definition basis_view_def:
  basis_view (s : clock_world_state ffi_state) =
    <| oracle := basis_ffi_oracle no_ext
     ; ffi_state := FST s.ffi_state
     ; io_events := FILTER ($¬ o is_clock_event) s.io_events |>
End

(* One FFI step of our world is either invisible to the basis (a clock
   call) or a step of the basis world. *)
Theorem call_FFI_rel_basis_view:
  call_FFI_rel s s' ∧ s.oracle = clock_world_oracle ⇒
  s'.oracle = clock_world_oracle ∧
  (basis_view s' = basis_view s ∨ call_FFI_rel (basis_view s) (basis_view s'))
Proof
  rw [call_FFI_rel_def, call_FFI_def] \\ gvs [AllCaseEqs()]
  \\ Cases_on ‘s.ffi_state’ \\ rename1 ‘s.ffi_state = (st,clk)’
  \\ Cases_on ‘n = ExtCall «now»’
  >- (gvs [clock_world_oracle_def, AllCaseEqs()]
      \\ disj1_tac
      \\ simp [basis_view_def, FILTER_APPEND, is_clock_event_def])
  \\ gvs [clock_world_oracle_def, AllCaseEqs()]
  \\ disj2_tac
  \\ simp [call_FFI_rel_def, call_FFI_def, basis_view_def]
  \\ qexistsl [‘n’, ‘conf’, ‘bytes’]
  \\ simp [FILTER_APPEND, is_clock_event_def]
QED

Theorem RTC_call_FFI_rel_basis_view:
  ∀s s'. call_FFI_rel^* s s' ⇒ s.oracle = clock_world_oracle ⇒
         call_FFI_rel^* (basis_view s) (basis_view s')
Proof
  ho_match_mp_tac RTC_INDUCT \\ rw []
  \\ drule_all call_FFI_rel_basis_view \\ rw [] \\ gvs []
  \\ metis_tac [RTC_RULES]
QED

(* The file system after a run of our world, replayed from the non-clock
   events, as in basis_ffi's extract_fs. *)
Definition clock_extract_fs_def:
  clock_extract_fs cl fs events =
    extract_fs no_ext (cl,fs) (FILTER ($¬ o is_clock_event) events)
End

(* Replaying the basis events reproduces the basis state (reuses basis_ffi's
   RTC_call_FFI_rel_IMP_basis_events on the basis view). *)
Theorem clock_world_extract:
  call_FFI_rel^* (clock_world_ffi cl fs clk) s ⇒
  extract_fs_with_numchars no_ext (cl,fs)
    (FILTER ($¬ o is_clock_event) s.io_events) = SOME (FST s.ffi_state)
Proof
  strip_tac
  \\ drule RTC_call_FFI_rel_basis_view
  \\ simp [clock_world_ffi_def] \\ strip_tac
  \\ drule RTC_call_FFI_rel_IMP_basis_events
  \\ disch_then (qspecl_then [‘(cl,fs)’, ‘no_ext’] mp_tac)
  \\ simp [basis_view_def, extract_fs_with_numchars_def]
QED

(*---------------------------------------------------------------------------*)
(* Heaps: the initial heap, and reading the file system off the final one *)

(* Before any FFI call, the heap holds each part of our world, with the
   part's state as given by the projection. *)
Theorem clock_world_part_in_heap:
  st.ffi = clock_world_ffi cl fs clk ⇒
  MEM (ns,u) clock_proj2 ∧ ns ≠ [] ∧
  (∀n. MEM n ns ⇒ FLOOKUP (clock_proj1 ((cl,fs),clk)) n = SOME s) ⇒
  FFI_part s u ns [] ∈ st2heap (clock_proj1, clock_proj2) st
Proof
  rw [st2heap_def, ffi2heap_def, parts_ok_clock_world_ffi]
  \\ simp [clock_world_ffi_def]
QED

(* basis_ffi's STDIO_precond, with the location of the I/O buffer
   simplified to 1. *)
Theorem STDIO_precond_1 =
  STDIO_precond |> SIMP_RULE (srw_ss()) [basis_refs_eqs] |> DISCH_ALL;

(* The initial heap (after the basis library's declarations, which make
   no FFI calls) satisfies the precondition of a whole-program spec. *)
Theorem clock_world_init_heap:
  st.ffi = clock_world_ffi cl fs clk ∧ is_refs_basis st.refs ∧
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ⇒
  ∃h1 h2. SPLIT (st2heap (clock_proj1, clock_proj2) st) (h1,h2) ∧
          (COMMANDLINE cl * STDIO fs * CLOCK clk) h1
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
  \\ qexists_tac ‘{cl_part} ∪ ({fs_part} ∪ {Mem 1 (W8array bs2)}) ∪ {clock_part}’
  \\ conj_tac
  >- (rw [SUBSET_DEF] \\ unabbrev_all_tac
      \\ TRY (simp [st2heap_def, store2heap_def, store2heap_aux_def] \\ NO_TAC)
      \\ drule_then irule clock_world_part_in_heap
      \\ simp [clock_proj2_def, basis_proj2_def, mk_proj2_def,
               basis_ffi_part_defs, clock_ffi_part_def, clock_proj1_def,
               basis_proj1_def, mk_proj1_def, FLOOKUP_UPDATE,
               FUPDATE_LIST_THM]
      \\ rw [] \\ gvs [])
  >- (irule append_hprop \\ rpt conj_tac
      >- (irule append_hprop \\ rpt conj_tac
          >- (unabbrev_all_tac \\ mp_tac (Q.INST [‘events’ |-> ‘[]’] (DISCH_ALL COMMANDLINE_precond))
              \\ simp [cl_ffi_part_def])
          >- (unabbrev_all_tac \\ mp_tac (Q.INST [‘events’ |-> ‘[]’, ‘v’ |-> ‘bs2’] STDIO_precond_1)
              \\ simp [])
          \\ unabbrev_all_tac \\ simp [fs_ffi_part_def])
      >- (unabbrev_all_tac \\ simp [CLOCK_precond])
      \\ unabbrev_all_tac \\ simp [fs_ffi_part_def])
QED

(* A heap satisfying STDIO fs contains the file-system part, in state fs
   up to the numchars schedule. *)
Theorem STDIO_FFI_part:
  STDIO fs h ⇒
  ∃ll events.
    FFI_part (encode (fs with numchars := ll)) (mk_ffi_next fs_ffi_part)
      (MAP FST (SND (SND fs_ffi_part))) events ∈ h
Proof
  rw [STDIO_def, IOFS_def, fs_ffi_part_def, IOx_def, IO_def, SEP_CLAUSES,
      SEP_EXISTS_THM, cond_STAR, GSYM STAR_ASSOC, one_STAR]
  \\ metis_tac []
QED

(* Our projection maps the file-system name «write» to the file system. *)
Theorem FLOOKUP_clock_proj1_write:
  FLOOKUP (clock_proj1 x) «write» = SOME (encode (SND (FST x)))
Proof
  PairCases_on ‘x’
  \\ simp [clock_proj1_def, basis_proj1_def, mk_proj1_def, basis_ffi_part_defs,
           clock_ffi_part_def, FLOOKUP_UPDATE, FUPDATE_LIST_THM]
QED

(* If part of the heap of a state satisfies STDIO fs', then the state's file
   system is fs' (up to numchars). *)
Theorem clock_world_STDIO_heap:
  STDIO fs' h ∧ h ⊆ st2heap (clock_proj1, clock_proj2) st ⇒
  ∃ll. SND (FST st.ffi.ffi_state) = fs' with numchars := ll
Proof
  rw [SUBSET_DEF]
  \\ drule STDIO_FFI_part \\ strip_tac
  \\ first_x_assum drule
  \\ simp [st2heap_def, FFI_part_NOT_IN_store2heap, ffi2heap_def]
  \\ Cases_on ‘parts_ok st.ffi (clock_proj1, clock_proj2)’ \\ gvs []
  \\ rpt strip_tac
  \\ first_x_assum (qspec_then ‘«write»’ mp_tac)
  \\ simp [fs_ffi_part_def, FLOOKUP_clock_proj1_write]
  \\ metis_tac []
QED

(*---------------------------------------------------------------------------*)
(* The whole-program theorem *)

(* A spec for main in our world, like basis_ffi's whole_prog_spec: from the
   command line, standard streams and the clock, main returns unit and
   leaves the standard streams satisfying post. *)
Definition clock_whole_prog_spec_def:
  clock_whole_prog_spec fv cl fs clk post ⇔
    ∃fs'.
      app (clock_proj1, clock_proj2) fv [Conv NONE []]
        (COMMANDLINE cl * STDIO fs * CLOCK clk)
        (POSTv uv. &UNIT_TYPE () uv * STDIO fs') ∧
      post (fs' with numchars := fs.numchars)
End

(* MAIN: a program whose main satisfies a clock_whole_prog_spec terminates
   successfully in our world, and replaying its file-system events gives a
   file system satisfying post. *)
Theorem clock_whole_prog_spec_semantics:
  clock_whole_prog_spec main_v cl fs clk post ∧
  Decls init_env (init_state (clock_world_ffi cl fs clk)) decs res_env res_st
  ⇒
  ∀main_name.
    let all_decs = SNOC (Dlet NoLocs (Pcon NONE [])
                     (App Opapp [Var (Short main_name); Con NONE []])) decs in
    nsLookup res_env.v (Short main_name) = SOME main_v
    ⇒
    res_st.ffi = clock_world_ffi cl fs clk
    ⇒
    is_refs_basis res_st.refs
    ⇒
    wfcl cl ∧ wfFS fs ∧ STD_streams fs ⇒
    ∃io_events fs'.
      semantics_dec_list
        (init_state (clock_world_ffi cl fs clk)) init_env
        all_decs
        (Terminate Success io_events) ∧
      clock_extract_fs cl fs io_events = SOME fs' ∧
      post fs'
Proof
  simp [] \\ rpt strip_tac
  \\ gvs [clock_whole_prog_spec_def]
  \\ ‘lookup_var main_name res_env = SOME main_v’ by simp [lookup_var_def]
  \\ drule_all clock_world_init_heap \\ strip_tac
  (* run main, using cfMain's call_main_thm2 *)
  \\ drule call_main_thm2 \\ rpt (disch_then drule)
  \\ disch_then (qspecl_then [‘h2’, ‘h1’] mp_tac)
  \\ impl_tac
  >- (simp []
      \\ rw [STDIO_def]
      \\ match_mp_tac FFI_part_hprop_STAR \\ disj1_tac
      \\ ho_match_mp_tac FFI_part_hprop_SEP_EXISTS
      \\ metis_tac [IOFS_FFI_part_hprop])
  \\ strip_tac
  \\ first_x_assum (irule_at Any)
  (* the file system at the end *)
  \\ ‘h3 ⊆ st2heap (clock_proj1, clock_proj2) st3’
    by (fs [SPLIT3_def] \\ simp [SUBSET_DEF] \\ metis_tac [IN_UNION])
  \\ drule_all clock_world_STDIO_heap \\ strip_tac
  (* replaying the events gives that file system *)
  \\ gvs [ml_progTheory.init_state_def]
  \\ drule clock_world_extract
  \\ simp [clock_extract_fs_def, extract_fs_def]
QED
