(*
  A never-ending program (server-shaped) against the socket model, proved
  with CakeML's divergence CF (cfDiv) down to the source semantics.

      fun tick3 u = let val r = Socket.poll [3] in () end
      fun serve u = serve (tick3 u)

  cfDiv's FFI-part loop rule (IMP_app_POSTd_one_FFI_part_FLATTEN) needs a
  world with a single FFI part (limited_parts), so this example runs in a
  sockets-only world, not in the composed world of composedWorld
  (whose diverging whole-program theorem has no instance yet; see
  07-socket-model.md).
*)
Theory socketDiv
Ancestors
  ml_translator ml_prog cfMain cfDiv cfStore llist basis_ffi
  socketWorld socketProof socketFair
  composedWorld divMain
Libs
  preamble basis cfDivLib

val _ = translation_extends "socketProg";

(*---------------------------------------------------------------------------*)
(* The socket part with its events made explicit *)

Definition SOCKETS_EV_def:
  SOCKETS_EV s evs =
    one (FFI_part (sockets_encode s) (mk_ffi_next sockets_ffi_part)
           socket_names evs)
End

(* The event of «sock_poll» on fds in state s. *)
Definition poll_event_def:
  poll_event fds s =
    IO_event (ExtCall «sock_poll») (fds_bytes fds)
      (ZIP (REPLICATE (LENGTH fds) 0w,
            MAP (λfd. if is_ready (tick s) fd then 1w else 0w) fds))
End

Theorem socket_names_sockets_ffi_part[local]:
  MAP FST (SND (SND sockets_ffi_part)) = socket_names
Proof
  simp [sockets_ffi_part_def, socket_names_def]
QED

(* Socket.poll, recording its event (Socket_poll_spec hides events). *)
Theorem Socket_poll_spec_ev:
  LIST_TYPE NUM (MAP w2n fds) fdsv ⇒
  app (p:'ffi ffi_proj) Socket_poll_v [fdsv]
    (SOCKETS_EV s evs)
    (POSTv v. &LIST_TYPE NUM (MAP w2n (FST (sock_poll fds s))) v *
              SOCKETS_EV (tick s) (evs ++ [poll_event fds s]))
Proof
  strip_tac
  \\ xcf_with_def (fetch "socketProg" "Socket_poll_v_def")
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ rename1 ‘W8ARRAY av (REPLICATE _ _)’
  \\ xlet ‘POSTv uv. W8ARRAY av
             (MAP (λfd. if is_ready (tick s) fd then 1w else 0w) fds) *
           SOCKETS_EV (tick s) (evs ++ [poll_event fds s])’
  >- (simp [SOCKETS_EV_def]
      \\ xffi \\ xsimpl
      \\ gvs [STRING_TYPE_def, fds_conf_fds_bytes]
      \\ qexistsl [‘fds_bytes fds’, ‘emp’, ‘sockets_encode s’,
                   ‘mk_ffi_next sockets_ffi_part’, ‘socket_names’, ‘evs’]
      \\ xsimpl
      \\ simp [sockets_ffi_part_def, mk_ffi_next_def, ffi_sock_poll_call,
               poll_event_def]
      \\ xsimpl \\ EVAL_TAC)
  \\ qmatch_goalsub_abbrev_tac ‘W8ARRAY av flagbytes’
  \\ ‘LENGTH flagbytes = LENGTH fds’ by simp [Abbr ‘flagbytes’]
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xapp
  \\ qexistsl [‘W8ARRAY av flagbytes * SOCKETS_EV (tick s) (evs ++ [poll_event fds s])’,
               ‘MAP (CHR o w2n) (TAKE (LENGTH fds) flagbytes)’,
               ‘MAP w2n fds’]
  \\ gvs [Abbr ‘flagbytes’] \\ xsimpl
  \\ simp [CHR_o_w2n, TAKE_LENGTH_ID_rwt]
  \\ rpt strip_tac \\ fs [ready_of_flags, sock_poll_def]
  >- (‘(λfd. is_ready (tick s) fd) = is_ready (tick s)’ by simp [FUN_EQ_THM]
      \\ fs [])
  \\ xsimpl
QED

(*---------------------------------------------------------------------------*)
(* Lazy-list lemmas for the trace (copied from cf-spike's asyncCfSnap) *)

Theorem LGENLIST_shift[local]:
  LGENLIST (λi. f (i + k)) NONE = f k ::: LGENLIST (λi. f (i + (k + 1))) NONE
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LGENLIST_NONE_UNFOLD])) >>
  simp[combinTheory.o_DEF] >>
  AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM]
QED

Theorem LGENLIST_singletons_shift[local]:
  LGENLIST (λi. [|e (i + k)|]) NONE =
  [|e k|] ::: LGENLIST (λi. [|e (i + (k + 1))|]) NONE
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LGENLIST_NONE_UNFOLD])) >>
  simp[combinTheory.o_DEF] >>
  AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM]
QED

Theorem LFLATTEN_LGENLIST_singletons[local]:
  LFLATTEN (LGENLIST (λi. [|e i|]) NONE) = LGENLIST e NONE
Proof
  simp[Once LLIST_BISIMULATION0] >>
  qexists_tac ‘λa b. ∃k. a = LFLATTEN (LGENLIST (λi. [|e (k + i)|]) NONE) ∧
                         b = LGENLIST (λi. e (k + i)) NONE’ >>
  rw[] >- (qexists_tac ‘0’ >> simp[ETA_AX]) >>
  ONCE_REWRITE_TAC[LGENLIST_shift] >> simp[] >>
  qexists_tac ‘LFLATTEN (LGENLIST (λi. [|e (i + (k + 1))|]) NONE)’ >>
  conj_tac
  >- (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LGENLIST_singletons_shift])) >>
      simp[]) >>
  qexists_tac ‘k + 1’ >> simp[] >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LGENLIST_shift])) >> simp[]
QED

(*---------------------------------------------------------------------------*)
(* The program and its divergence spec *)

Quote add_cakeml:
  fun tick3 u = let val r = Socket.poll [3] in () end
End

Quote add_cakeml:
  fun serve u = serve (tick3 u)
End

val st = get_ml_prog_state ();

Theorem tick3_spec:
  UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) tick3_v [uv]
    (SOCKETS_EV s evs)
    (POSTv v. &UNIT_TYPE () v *
              SOCKETS_EV (tick s) (evs ++ [poll_event [3w] s]))
Proof
  strip_tac
  \\ xcf "tick3" st
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet ‘POSTv v. SOCKETS_EV (tick s) (evs ++ [poll_event [3w] s])’
  >- (xapp_spec Socket_poll_spec_ev
      \\ qexistsl [‘emp’, ‘s’, ‘[3w]’, ‘evs’] \\ xsimpl
      \\ fs [LIST_TYPE_def] \\ rw [] \\ xsimpl)
  \\ xcon \\ xsimpl
QED

(* MAIN: serve never terminates; its I/O trace is the infinite sequence of
   polls of listener 3, round i reporting whether 3 is ready after i+1
   rounds of the world left alone. *)
Theorem serve_spec:
  limited_parts socket_names p ∧ UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) serve_v [uv]
    (SOCKETS_EV s [])
    (POSTd io. io = LGENLIST (λi. poll_event [3w] (ticks i s)) NONE)
Proof
  xcf_div_rule IMP_app_POSTd_one_FFI_part_FLATTEN "serve" st
  \\ qexists_tac ‘K emp’
  \\ qexists_tac ‘λi. if i = 0 then [] else [poll_event [3w] (ticks (i - 1) s)]’
  \\ qexists_tac ‘λi v. UNIT_TYPE () v’
  \\ qexists_tac ‘λi. sockets_encode (ticks i s)’
  \\ qexists_tac ‘mk_ffi_next sockets_ffi_part’
  \\ gvs [] \\ rpt conj_tac
  >- (simp [SOCKETS_EV_def, ticks_def] \\ xsimpl)
  >- (rpt strip_tac
      \\ xlet ‘POSTv v. &UNIT_TYPE () v *
                         SOCKETS_EV (tick (ticks i s)) [poll_event [3w] (ticks i s)]’
      >- (xapp_spec tick3_spec
          \\ qexistsl [‘emp’, ‘ticks i s’, ‘[]’] \\ xsimpl
          \\ simp [SOCKETS_EV_def] \\ xsimpl)
      \\ xvar \\ xsimpl
      \\ simp [SOCKETS_EV_def, ticks_SUC] \\ xsimpl)
  \\ CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [LGENLIST_NONE_UNFOLD]))
  \\ simp [combinTheory.o_DEF, LFLATTEN_LGENLIST_singletons]
QED

(*---------------------------------------------------------------------------*)
(* A sockets-only world *)

Definition socket_only_oracle_def:
  socket_only_oracle (name:ffiname) (sk:sockets) conf bytes =
    case socket_name name of
    | SOME m =>
        (case socket_call m conf bytes sk of
         | SOME (FFIreturn bytes' sk') => Oracle_return sk' bytes'
         | _ => Oracle_final FFI_failed)
    | NONE => Oracle_final FFI_failed
End

Definition socket_only_ffi_def:
  socket_only_ffi sk =
    <| oracle := socket_only_oracle; ffi_state := sk; io_events := [] |>
End

Definition sonly_proj1_def:
  sonly_proj1 (sk:sockets) = FEMPTY |++ mk_proj1 sockets_ffi_part sk
End

Definition sonly_proj2_def:
  sonly_proj2 = [mk_proj2 sockets_ffi_part]
End

Theorem limited_parts_sonly:
  limited_parts socket_names (sonly_proj1, sonly_proj2)
Proof
  rw [limited_parts_def, sonly_proj2_def, mk_proj2_def, sockets_ffi_part_def,
      socket_names_def]
QED

Theorem sonly_proj2_part[local]:
  MEM (ns,u) sonly_proj2 ⇔ ns = socket_names ∧ u = mk_ffi_next sockets_ffi_part
Proof
  rw [sonly_proj2_def, mk_proj2_def, sockets_ffi_part_def, socket_names_def]
  \\ metis_tac []
QED

Theorem FLOOKUP_sonly_proj1[local]:
  MEM n socket_names ⇒ FLOOKUP (sonly_proj1 sk) n = SOME (sockets_encode sk)
Proof
  rw [sonly_proj1_def, mk_proj1_sockets, FLOOKUP_FUPDATE_LIST,
      ALOOKUP_MAP_const, MAP_REVERSE |> GSYM]
  \\ simp [MAP_REVERSE |> GSYM, ALOOKUP_MAP_const]
QED

Theorem sonly_proj1_apply[local]:
  MEM n socket_names ⇒ sonly_proj1 sk ' n = sockets_encode sk
Proof
  strip_tac \\ drule FLOOKUP_sonly_proj1
  \\ disch_then (qspec_then ‘sk’ mp_tac) \\ simp [FLOOKUP_DEF]
QED

Theorem parts_ok_sonly:
  parts_ok (socket_only_ffi sk) (sonly_proj1, sonly_proj2)
Proof
  rw [parts_ok_def, socket_only_ffi_def, sonly_proj2_part]
  >- EVAL_TAC
  >- (qexists_tac ‘sockets_encode sk’ \\ rw [FLOOKUP_sonly_proj1])
  >- (‘sonly_proj1 x ' m = sockets_encode x’
        by simp [sonly_proj1_apply]
      \\ gvs [socket_part_not_diverge])
  >- (‘sonly_proj1 x ' m = sockets_encode x’
        by simp [sonly_proj1_apply]
      \\ gvs [] \\ metis_tac [socket_part_return])
  \\ ‘sonly_proj1 x ' m = sockets_encode x’
    by simp [sonly_proj1_apply]
  \\ gvs [] \\ drule socket_part_return \\ strip_tac
  \\ gvs [socket_only_oracle_def, socket_name_def]
  \\ simp [sonly_proj1_def, mk_proj1_sockets, FUPDATE_LIST_same_keys]
QED

Theorem sonly_init_heap:
  st.ffi = socket_only_ffi sk ⇒
  ∃h1 h2. SPLIT (st2heap (sonly_proj1, sonly_proj2) st) (h1,h2) ∧
          SOCKETS_EV sk [] h1
Proof
  strip_tac
  \\ qabbrev_tac ‘sock_part = FFI_part (sockets_encode sk)
                     (mk_ffi_next sockets_ffi_part) socket_names []’
  \\ ‘sock_part ∈ st2heap (sonly_proj1, sonly_proj2) st’
    by (gvs [Abbr ‘sock_part’, st2heap_def, ffi2heap_def, parts_ok_sonly,
             sonly_proj2_part]
        \\ simp [socket_only_ffi_def, FLOOKUP_sonly_proj1, socket_names_def])
  \\ qexistsl [‘{sock_part}’, ‘st2heap (sonly_proj1, sonly_proj2) st DIFF {sock_part}’]
  \\ simp [SOCKETS_EV_def, one_def, Abbr ‘sock_part’]
  \\ rw [SPLIT_def, EXTENSION, IN_DISJOINT] \\ metis_tac []
QED

(*---------------------------------------------------------------------------*)
(* The whole program *)

val Decls_th =
  get_ml_prog_state () |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]
  |> GEN_ALL |> ISPEC “socket_only_ffi sk” |> SPEC_ALL;

val (_, decls_args) = strip_comb (concl Decls_th);
val decs_tm = List.nth (decls_args, 2);
val env2_tm = List.nth (decls_args, 3);
val st2_tm = List.nth (decls_args, 4);

val serve_prog_def = new_definition ("serve_prog_def",
  mk_eq (mk_var ("serve_prog", type_of decs_tm), decs_tm));

val lookup_serve = let
  val g = “nsLookup (^env2_tm).v (Short «serve») = SOME serve_v”
  in prove (g, REWRITE_TAC [fst (dest_eq g) |> nsLookup_conv]) end;

val st2_ffi = prove (“(^st2_tm).ffi = socket_only_ffi sk”, EVAL_TAC);

(* MAIN: in a sockets-only world, the program (basis, Socket, tick3, serve,
   and a call to serve) diverges, and its I/O trace is the infinite
   sequence of polls of listener 3, poll i in the world left alone for i
   rounds. *)
Theorem serve_semantics:
  ∃io. semantics_dec_list (init_state (socket_only_ffi sk)) init_env
         (SNOC (main_call «serve») serve_prog) (Diverge io) ∧
       io = LGENLIST (λi. poll_event [3w] (ticks i sk)) NONE
Proof
  assume_tac (REWRITE_RULE [GSYM serve_prog_def] Decls_th)
  \\ drule call_main_thm_div \\ strip_tac
  \\ assume_tac st2_ffi
  \\ drule sonly_init_heap \\ strip_tac
  \\ first_x_assum (qspecl_then [‘sonly_proj2’, ‘sonly_proj1’, ‘h2’, ‘h1’,
       ‘serve_v’, ‘«serve»’,
       ‘λio. io = LGENLIST (λi. poll_event [3w] (ticks i sk)) NONE’,
       ‘SOCKETS_EV sk []’] mp_tac)
  \\ impl_tac
  >- (simp [lookup_var_def, lookup_serve]
      \\ irule serve_spec \\ simp [limited_parts_sonly])
  \\ simp []
QED
