(*
  The sockets-only version-2 world, for cfDiv's whole-program theorem (as
  socketDiv for version 1): its FFI is EchoEpisodesSpec's lifetime_ffi
  (socket2_only_ffi_eq), the projections make the version-2 socket part
  its only FFI part (limited_parts_s2only, parts_ok_s2only), and its
  initial heap holds the part with no events (s2only_init_heap).
*)
Theory lifetimeDiv
Ancestors
  ml_translator ml_prog cfMain cfDiv cfStore llist
  socketWorld composedWorld lifetimeWorld lifetimePart lifetimeProof
  EchoEpisodesSpec
Libs
  preamble basis cfDivLib

Definition socket2_only_oracle_def:
  socket2_only_oracle (name:ffiname) (sk:sockets2) conf bytes =
    case socket2_name name of
    | SOME m =>
        (case socket2_call m conf bytes sk of
         | SOME (FFIreturn bytes' sk') => Oracle_return sk' bytes'
         | _ => Oracle_final FFI_failed)
    | NONE => Oracle_final FFI_failed
End

Definition socket2_only_ffi_def:
  socket2_only_ffi sk =
    <| oracle := socket2_only_oracle; ffi_state := sk; io_events := [] |>
End

(* MAIN: the sockets-only version-2 world is EchoEpisodesSpec's *)
Theorem socket2_only_ffi_eq:
  socket2_only_ffi = lifetime_ffi
Proof
  ‘socket2_only_oracle = socket2_oracle’
    by (simp [FUN_EQ_THM] >> Cases >>
        rw [socket2_only_oracle_def, socket2_oracle_def, socket2_name_def,
            socket2_fn_def, socket2_call_def, sockets2_ffi_part_def,
            socket2_names_def] >>
        gvs [])
  >> simp [FUN_EQ_THM, socket2_only_ffi_def, lifetime_ffi_def]
QED

Definition s2only_proj1_def:
  s2only_proj1 (sk:sockets2) = FEMPTY |++ mk_proj1 sockets2_ffi_part sk
End

Definition s2only_proj2_def:
  s2only_proj2 = [mk_proj2 sockets2_ffi_part]
End

Theorem limited_parts_s2only:
  limited_parts socket2_names (s2only_proj1, s2only_proj2)
Proof
  rw [limited_parts_def, s2only_proj2_def, mk_proj2_def, sockets2_ffi_part_def,
      socket2_names_def]
QED

Theorem s2only_proj2_part[local]:
  MEM (ns,u) s2only_proj2 ⇔
  ns = socket2_names ∧ u = mk_ffi_next sockets2_ffi_part
Proof
  rw [s2only_proj2_def, mk_proj2_def, sockets2_ffi_part_def, socket2_names_def]
  \\ metis_tac []
QED

Theorem FLOOKUP_s2only_proj1[local]:
  MEM n socket2_names ⇒
  FLOOKUP (s2only_proj1 sk) n = SOME (sockets2_encode sk)
Proof
  rw [s2only_proj1_def, mk_proj1_sockets2, FLOOKUP_FUPDATE_LIST,
      ALOOKUP_MAP_const, MAP_REVERSE |> GSYM]
  \\ simp [MAP_REVERSE |> GSYM, ALOOKUP_MAP_const]
QED

Theorem s2only_proj1_apply[local]:
  MEM n socket2_names ⇒ s2only_proj1 sk ' n = sockets2_encode sk
Proof
  strip_tac \\ drule FLOOKUP_s2only_proj1
  \\ disch_then (qspec_then ‘sk’ mp_tac) \\ simp [FLOOKUP_DEF]
QED

Theorem parts_ok_s2only:
  parts_ok (socket2_only_ffi sk) (s2only_proj1, s2only_proj2)
Proof
  rw [parts_ok_def, socket2_only_ffi_def, s2only_proj2_part]
  >- EVAL_TAC
  >- (qexists_tac ‘sockets2_encode sk’ \\ rw [FLOOKUP_s2only_proj1])
  >- (‘s2only_proj1 x ' m = sockets2_encode x’
        by simp [s2only_proj1_apply]
      \\ gvs [socket2_part_not_diverge])
  >- (‘s2only_proj1 x ' m = sockets2_encode x’
        by simp [s2only_proj1_apply]
      \\ gvs [] \\ metis_tac [socket2_part_return])
  \\ ‘s2only_proj1 x ' m = sockets2_encode x’
    by simp [s2only_proj1_apply]
  \\ gvs [] \\ drule socket2_part_return \\ strip_tac
  \\ gvs [socket2_only_oracle_def, socket2_name_def]
  \\ simp [s2only_proj1_def, mk_proj1_sockets2, FUPDATE_LIST_same_keys]
QED

Theorem s2only_init_heap:
  st.ffi = socket2_only_ffi sk ⇒
  ∃h1 h2. SPLIT (st2heap (s2only_proj1, s2only_proj2) st) (h1,h2) ∧
          SOCKETS2_EV sk [] h1
Proof
  strip_tac
  \\ qabbrev_tac ‘sock_part = FFI_part (sockets2_encode sk)
                     (mk_ffi_next sockets2_ffi_part) socket2_names []’
  \\ ‘sock_part ∈ st2heap (s2only_proj1, s2only_proj2) st’
    by (gvs [Abbr ‘sock_part’, st2heap_def, ffi2heap_def, parts_ok_s2only,
             s2only_proj2_part]
        \\ simp [socket2_only_ffi_def, FLOOKUP_s2only_proj1, socket2_names_def])
  \\ qexistsl [‘{sock_part}’,
               ‘st2heap (s2only_proj1, s2only_proj2) st DIFF {sock_part}’]
  \\ simp [SOCKETS2_EV_def, one_def, Abbr ‘sock_part’]
  \\ rw [SPLIT_def, EXTENSION, IN_DISJOINT] \\ metis_tac []
QED
