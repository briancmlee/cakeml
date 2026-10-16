(*
  The blocking echo program, end to end: CakeML semantics in a world of
  sockets with a blocking select.

      fun main u = run_b ([3], server 3)

  The world: ssel_ffi sk, the socket model's four calls plus «sock_select»
  (asyncM4BlkLoop's ffi_sock_select), on the world sk.  This is
  EchoSpec's socket_ffi with one more call; EchoSpec itself is untouched.

  MAIN:
  - echo_blocking_semantics: the program either diverges with the
    blocking loop's trace block_io, or ends in an FFI divergence of
    «sock_select» after the finite trace of its first n rounds, having
    done everything the polling loop would ever do;
  - echo_blocking_spec: in both cases the trace is EchoSpec's echo_safe
    (unconditionally: echo_comp_safe on spike/m4-safety covers the polling
    trace), and echo_live whenever the polling loop's trace is.
*)
Theory asyncM4BlkMain
Ancestors
  asyncCore asyncLevel1 asyncChoose asyncServer asyncCfActModel
  asyncCfActProg asyncM3World asyncM3Loop asyncM4GRounds asyncM4Loop
  asyncM4SockModel asyncM4SockServer asyncM4EchoRunOk asyncM4EchoSafe
  asyncM4BlkWorld
  asyncM4BlkTrace asyncM4BlkEcho asyncM4BlkLoop EchoSpec
  ffiSpikeSocketFFI ffiSpikeSocketWorld ffiSpikeDivMain
  ml_translator ml_prog cfMain cfDiv cfStore llist
Libs
  preamble basis cfDivLib cfTacticsLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncM4BlkLoop"

(* The computation the program runs *)
Overload echo_m = “srelabel (server 3)”

(* ------------------------------------------------------------------------
   The program
   ------------------------------------------------------------------------ *)

Quote add_cakeml:
  fun main u = run_b ([3], server 3);
End

val st = get_ml_prog_state ();

(* The loop's start: interest [3], the server's computation *)
Theorem main_spec_div:
  limited_parts ssel_names p ∧
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ∧
  (∀n. bgrounds [3w] echo_m sk n ≠ NONE) ⇒
  app (p:'ffi ffi_proj) main_v [Conv NONE []] (SSEL sk [])
    (POSTd io. io = block_io [3w] echo_m sk)
Proof
  strip_tac >>
  xcf_with_def (fetch "-" "main_v_def") >>
  xlet ‘POSTv cv. &COMP p SACT UNIT_TYPE SSNAP echo_m cv * SSEL sk []’
  >- (xapp_spec sserver_spec >> xsimpl >> simp[NUM_def, INT_def]) >>
  xlet_auto >- (xcon >> xsimpl) >>
  xlet_auto >- (xcon >> xsimpl) >>
  xlet_auto >- (xcon >> xsimpl) >>
  rveq >> xapp_spec run_b_spec >>
  simp[LIST_TYPE_def, NUM_def, INT_def, idle_quiet_echo, wf_echo] >>
  conj_tac >- (irule echo_grun_ok >> simp[]) >>
  metis_tac[]
QED

Theorem main_spec_stuck:
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ∧
  bgrounds [3w] echo_m sk n = SOME (kept, N, s) ∧
  new_actions (log_of echo_m) kept = [] ∧
  sock_wait (interest [3w] kept) s = NONE ⇒
  app (p:'ffi ffi_proj) main_v [Conv NONE []] (SSEL sk [])
    (POSTf nm. λc b.
       &(nm = «sock_select» ∧ c = fds_bytes (interest [3w] kept) ∧ b = []) *
       SSEL s (FLAT (GENLIST (bround_events [3w] echo_m sk) n)) *
       SEP_EXISTS av. W8ARRAY av [])
Proof
  strip_tac >>
  xcf_with_def (fetch "-" "main_v_def") >>
  xlet ‘POSTv cv. &COMP p SACT UNIT_TYPE SSNAP echo_m cv * SSEL sk []’
  >- (xapp_spec sserver_spec >> xsimpl >> simp[NUM_def, INT_def]) >>
  xlet_auto >- (xcon >> xsimpl) >>
  xlet_auto >- (xcon >> xsimpl) >>
  xlet_auto >- (xcon >> xsimpl) >>
  rveq >> xapp_spec run_b_stuck_spec >>
  simp[LIST_TYPE_def, NUM_def, INT_def, idle_quiet_echo, wf_echo] >>
  conj_tac >- (irule echo_grun_ok >> simp[]) >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------
   The world: sockets with select
   ------------------------------------------------------------------------ *)

(* A call of the part: the model's function for the name, if any *)
Definition ssel_call_def:
  ssel_call m conf bs (sk:sockets) =
    case ALOOKUP (SND (SND ssel_ffi_part)) m of
    | SOME f => f conf bs sk
    | NONE => NONE
End

(* The oracle: a socket call or select runs the model's function; a
   select that blocks forever ends the program with FFI_diverged; anything
   else ends it with an FFI failure. *)
Definition ssel_oracle_def:
  ssel_oracle (ExtCall m) (sk:sockets) conf bs =
    (case ssel_call m conf bs sk of
     | SOME (FFIreturn bs' sk') => Oracle_return sk' bs'
     | SOME FFIdiverge => Oracle_final FFI_diverged
     | NONE => Oracle_final FFI_failed) ∧
  ssel_oracle _ sk conf bs = Oracle_final FFI_failed
End

Definition ssel_ffi_def:
  ssel_ffi sk = <| oracle := ssel_oracle; ffi_state := sk; io_events := [] |>
End

Definition ssel_proj1_def:
  ssel_proj1 (sk:sockets) = FEMPTY |++ mk_proj1 ssel_ffi_part sk
End

Definition ssel_proj2_def:
  ssel_proj2 = [mk_proj2 ssel_ffi_part]
End

Theorem limited_parts_ssel:
  limited_parts ssel_names (ssel_proj1, ssel_proj2)
Proof
  rw [limited_parts_def, ssel_proj2_def, mk_proj2_def, ssel_ffi_part_def,
      ssel_names_def]
QED

Theorem ssel_proj2_part[local]:
  MEM (ns,u) ssel_proj2 ⇔ ns = ssel_names ∧ u = mk_ffi_next ssel_ffi_part
Proof
  rw [ssel_proj2_def, mk_proj2_def, ssel_ffi_part_def, ssel_names_def]
  \\ metis_tac []
QED

Theorem mk_proj1_ssel[local]:
  mk_proj1 ssel_ffi_part sk = MAP (λn. (n, sockets_encode sk)) ssel_names
Proof
  simp [mk_proj1_def, ssel_ffi_part_def, ssel_names_def]
QED

Theorem FLOOKUP_ssel_proj1[local]:
  MEM n ssel_names ⇒ FLOOKUP (ssel_proj1 sk) n = SOME (sockets_encode sk)
Proof
  rw [ssel_proj1_def, mk_proj1_ssel, FLOOKUP_FUPDATE_LIST,
      ALOOKUP_MAP_const, MAP_REVERSE |> GSYM]
  \\ simp [MAP_REVERSE |> GSYM, ALOOKUP_MAP_const]
QED

Theorem ssel_proj1_apply[local]:
  MEM n ssel_names ⇒ ssel_proj1 sk ' n = sockets_encode sk
Proof
  strip_tac \\ drule FLOOKUP_ssel_proj1
  \\ disch_then (qspec_then ‘sk’ mp_tac) \\ simp [FLOOKUP_DEF]
QED

Theorem ffi_sock_select_length[local]:
  ffi_sock_select conf bs s = SOME (FFIreturn bs' s') ⇒
  LENGTH bs' = LENGTH bs
Proof
  rw [ffi_sock_select_def, AllCaseEqs()] \\ simp []
QED

Theorem ssel_part_return[local]:
  mk_ffi_next ssel_ffi_part m conf bs (sockets_encode sk) =
    SOME (FFIreturn new_bytes w) ⇒
  LENGTH new_bytes = LENGTH bs ∧
  ∃sk'. ssel_call m conf bs sk = SOME (FFIreturn new_bytes sk') ∧
        w = sockets_encode sk'
Proof
  strip_tac
  \\ gvs [mk_ffi_next_def, ssel_ffi_part_def, ssel_call_def, AllCaseEqs()]
  \\ metis_tac [ffi_sock_length, ffi_sock_select_length]
QED

Theorem ssel_part_diverge[local]:
  mk_ffi_next ssel_ffi_part m conf bs (sockets_encode sk) = SOME FFIdiverge ⇒
  ssel_call m conf bs sk = SOME FFIdiverge
Proof
  rw [mk_ffi_next_def, ssel_ffi_part_def, ssel_call_def, AllCaseEqs()]
  \\ gvs [AllCaseEqs()]
QED

Theorem parts_ok_ssel:
  parts_ok (ssel_ffi sk) (ssel_proj1, ssel_proj2)
Proof
  rw [parts_ok_def, ssel_ffi_def, ssel_proj2_part]
  >- EVAL_TAC
  >- (qexists_tac ‘sockets_encode sk’ \\ rw [FLOOKUP_ssel_proj1])
  >- (‘ssel_proj1 x ' m = sockets_encode x’ by simp [ssel_proj1_apply]
      \\ gvs [] \\ drule ssel_part_diverge
      \\ simp [ssel_oracle_def])
  >- (‘ssel_proj1 x ' m = sockets_encode x’ by simp [ssel_proj1_apply]
      \\ gvs [] \\ metis_tac [ssel_part_return])
  \\ ‘ssel_proj1 x ' m = sockets_encode x’ by simp [ssel_proj1_apply]
  \\ gvs [] \\ drule ssel_part_return \\ strip_tac
  \\ gvs [ssel_oracle_def]
  \\ simp [ssel_proj1_def, mk_proj1_ssel, FUPDATE_LIST_same_keys]
QED

Theorem ssel_init_heap:
  st.ffi = ssel_ffi sk ⇒
  ∃h1 h2. SPLIT (st2heap (ssel_proj1, ssel_proj2) st) (h1,h2) ∧
          SSEL sk [] h1
Proof
  strip_tac
  \\ qabbrev_tac ‘sock_part = FFI_part (sockets_encode sk)
                     (mk_ffi_next ssel_ffi_part) ssel_names []’
  \\ ‘sock_part ∈ st2heap (ssel_proj1, ssel_proj2) st’
    by (gvs [Abbr ‘sock_part’, st2heap_def, ffi2heap_def, parts_ok_ssel,
             ssel_proj2_part]
        \\ simp [ssel_ffi_def, FLOOKUP_ssel_proj1, ssel_names_def])
  \\ qexistsl [‘{sock_part}’, ‘st2heap (ssel_proj1, ssel_proj2) st DIFF {sock_part}’]
  \\ simp [SSEL_def, one_def, Abbr ‘sock_part’]
  \\ rw [SPLIT_def, EXTENSION, IN_DISJOINT] \\ metis_tac []
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

val echo_b_prog_def = new_definition ("echo_b_prog_def",
  mk_eq (mk_var ("echo_b_prog", type_of decs_tm), decs_tm));

val lookup_main = let
  val g = “nsLookup (^env2_tm).v (Short «main») = SOME main_v”
  in prove (g, REWRITE_TAC [fst (dest_eq g) |> nsLookup_conv]) end;

val st2_ffi = prove (“(^st2_tm).ffi = ssel_ffi sk”, EVAL_TAC);

(* MAIN: the blocking echo program, in a world of sockets with select
   starting with one listener 3 and nothing else, either
   - diverges, with the blocking loop's trace block_io; or
   - blocks forever in a select on the interest fds of round n, after
     the trace of its first n rounds, in which case the polling loop
     would never have performed another action after that point. *)
Theorem echo_blocking_semantics:
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ⇒
  (∃io. semantics_dec_list (init_state (ssel_ffi sk)) init_env
          (SNOC (main_call «main») echo_b_prog) (Diverge io) ∧
        (∀n. bgrounds [3w] echo_m sk n ≠ NONE) ∧
        io = block_io [3w] echo_m sk) ∨
  (∃n kept N s.
     bgrounds [3w] echo_m sk n = SOME (kept, N, s) ∧
     new_actions (log_of echo_m) kept = [] ∧
     sock_wait (interest [3w] kept) s = NONE ∧
     semantics_dec_list (init_state (ssel_ffi sk)) init_env
       (SNOC (main_call «main») echo_b_prog)
       (Terminate (FFI_outcome (Final_event (ExtCall «sock_select»)
                                  (fds_bytes (interest [3w] kept)) []
                                  FFI_diverged))
                  (FLAT (GENLIST (bround_events [3w] echo_m sk) n))))
Proof
  strip_tac >>
  assume_tac (REWRITE_RULE [GSYM echo_b_prog_def] Decls_th) >>
  assume_tac st2_ffi >>
  drule ssel_init_heap >> strip_tac >>
  Cases_on ‘∀n. bgrounds [3w] echo_m sk n ≠ NONE’
  >- (disj1_tac >> simp[] >>
      drule call_main_thm_div >>
      disch_then (qspecl_then [‘ssel_proj2’, ‘ssel_proj1’, ‘h2’, ‘h1’,
         ‘main_v’, ‘«main»’, ‘λio. io = block_io [3w] echo_m sk’,
         ‘SSEL sk []’] mp_tac) >>
      impl_tac
      >- (simp [lookup_var_def, lookup_main] >>
          irule main_spec_div >> simp [limited_parts_ssel]) >>
      simp [])
  >- (disj2_tac >>
      ‘∃n kept N s. bgrounds [3w] echo_m sk n = SOME (kept, N, s) ∧
                    new_actions (log_of echo_m) kept = [] ∧
                    sock_wait (interest [3w] kept) s = NONE’
        by metis_tac[bgrounds_two_outcomes] >>
      qexistsl [‘n’, ‘kept’, ‘N’, ‘s’] >> simp[] >>
      drule call_main_thm2_ffidiv >>
      disch_then (qspecl_then [‘ssel_proj2’, ‘ssel_proj1’, ‘h2’, ‘h1’,
         ‘main_v’, ‘«main»’,
         ‘λnm c b. &(nm = «sock_select» ∧ c = fds_bytes (interest [3w] kept) ∧
                     b = []) *
                   SSEL s (FLAT (GENLIST (bround_events [3w] echo_m sk) n)) *
                   SEP_EXISTS av. W8ARRAY av []’,
         ‘SSEL sk []’] mp_tac) >>
      impl_tac
      >- (simp [lookup_var_def, lookup_main] >>
          irule main_spec_stuck >> simp [] >> metis_tac []) >>
      strip_tac >>
      fs [SEP_CLAUSES, SEP_EXISTS_THM, cond_STAR] >> rveq >>
      fs [GSYM STAR_ASSOC, cond_STAR] >> rveq >>
      qpat_x_assum ‘(_ * _) h3’ mp_tac >>
      simp [SSEL_def, STAR_def, one_def] >> strip_tac >>
      gvs [SPLIT_def, SPLIT3_def] >>
      ‘FFI_part (sockets_encode s) (mk_ffi_next ssel_ffi_part) ssel_names
         (FLAT (GENLIST (bround_events [3w] echo_m sk) n)) ∈
         st2heap (ssel_proj1, ssel_proj2) st3’
        by (qpat_x_assum ‘_ = st2heap _ st3’ (SUBST1_TAC o SYM) >> simp []) >>
      drule_at Any limited_FFI_part_IN_st2heap_IMP >>
      simp [limited_parts_ssel] >> strip_tac >>
      gvs [main_call_def])
QED

(* MAIN: what the blocking echo program does, in EchoSpec's terms.
   Either it runs forever, and its trace is echo_safe, and echo_live
   whenever the polling loop's is; or it blocks forever in select after a
   finite trace that is echo_safe, and echo_live whenever the polling
   loop's is. *)
Theorem echo_blocking_spec:
  sk.listeners = [(3w, [])] ∧ sk.conns = [] ⇒
  (∃io. semantics_dec_list (init_state (ssel_ffi sk)) init_env
          (SNOC (main_call «main») echo_b_prog) (Diverge io) ∧
        echo_safe io ∧
        (echo_live sk (poll_io [3w] echo_m sk) ⇒ echo_live sk io)) ∨
  (∃c io. semantics_dec_list (init_state (ssel_ffi sk)) init_env
            (SNOC (main_call «main») echo_b_prog)
            (Terminate (FFI_outcome (Final_event (ExtCall «sock_select») c []
                                       FFI_diverged)) io) ∧
          echo_safe (fromList io) ∧
          (echo_live sk (poll_io [3w] echo_m sk) ⇒ echo_live sk (fromList io)))
Proof
  strip_tac >>
  ‘echo_safe (poll_io [3w] echo_m sk)’ by (irule echo_comp_safe >> simp[]) >>
  ‘wf echo_m ∧ idle_quiet echo_m’ by simp[wf_echo, idle_quiet_echo] >>
  drule_all echo_blocking_semantics >> strip_tac
  >- (disj1_tac >> qexists_tac ‘io’ >> simp[] >>
      drule_all blocking_echo_div >> simp[])
  >- (disj2_tac >>
      qexistsl [‘fds_bytes (interest [3w] kept)’,
                ‘FLAT (GENLIST (bround_events [3w] echo_m sk) n)’] >>
      simp[] >> drule_all blocking_echo_stuck >> simp[])
QED
