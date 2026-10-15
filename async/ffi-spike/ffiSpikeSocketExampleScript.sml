(*
  End-to-end example: a one-shot echo.  The program polls listener 3,
  accepts one connection, reads up to 100 bytes from it, and writes them
  back, then exits.  Its whole-program theorem: in a socket world where a
  connection c with data bs arrives in the first round, the program
  terminates, leaves the file system alone, and the outgoing log of c is
  exactly bs.
*)
Theory ffiSpikeSocketExample
Ancestors
  ml_translator cfMain basis_ffi TextIOProof mlstring
  ffiSpikeSocketFFI ffiSpikeSocketProof ffiSpikeSocketFair ffiSpikeSocketWorld
Libs
  preamble basis ffiSpikeSocketWorldLib

val _ = translation_extends "ffiSpikeSocketProg";

Quote add_cakeml:
  fun main u =
    let
      val ready = Socket.poll [3]
    in
      case Socket.accept 3 of
        Some c =>
          (case Socket.read c 100 of
             Some s => Socket.write c s
           | None => ())
      | None => ()
    end
End

val st = get_ml_prog_state ();

(* The world of the example: listener 3, no connections yet, and in the
   first round connection c arrives with the bytes bs; rest is any future. *)
Definition echo_world_def:
  echo_world c bs rest =
    <| listeners := [(3w, [])]
     ; conns := []
     ; sched := [Connect 3w c; Data c bs] ::: rest |>
End

(* The world after the program: c accepted, its data read and echoed. *)
Definition echo_final_def:
  echo_final c bs rest =
    <| listeners := [(3w, [])]
     ; conns := [(c, <| incoming := []; peer_closed := F; outgoing := bs |>)]
     ; sched := rest |>
End

Theorem echo_round[local]:
  c ≠ 3w ⇒
  tick (echo_world c bs rest) =
    <| listeners := [(3w, [c])]
     ; conns := [(c, empty_conn with incoming := bs)]
     ; sched := rest |>
Proof
  rw [tick_def, echo_world_def, deliver_def, deliver1_def, is_listener_def,
      is_conn_def, AFUPDKEY_def, empty_conn_def]
QED

Theorem bytes_roundtrip[local]:
  MAP (n2w o ORD) (explode (implode (MAP (CHR o w2n) bs))) = bs:word8 list
Proof
  simp [MAP_MAP_o, combinTheory.o_DEF, w2n_lt_256, ORD_CHR_RWT]
QED

(* The CF spec of main. *)
Theorem main_spec:
  c ≠ 3w ∧ bs ≠ [] ∧ LENGTH bs ≤ 100 ⇒
  app (p:'ffi ffi_proj) main_v [Conv NONE []]
    (SOCKETS (echo_world c bs rest))
    (POSTv uv. &UNIT_TYPE () uv * SOCKETS (echo_final c bs rest))
Proof
  strip_tac
  \\ xcf "main" st
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ qmatch_goalsub_abbrev_tac ‘SOCKETS s0’
  \\ xlet ‘POSTv v. SOCKETS (tick s0)’
  >- (xapp_spec Socket_poll_spec
      \\ qexistsl [‘emp’, ‘s0’, ‘[3w]’] \\ xsimpl
      \\ fs [LIST_TYPE_def, sock_poll_def] \\ rw [] \\ xsimpl)
  \\ simp [Abbr ‘s0’, echo_round]
  \\ qmatch_goalsub_abbrev_tac ‘SOCKETS s1’
  \\ qabbrev_tac ‘s2 = s1 with listeners := [(3w, [])]’
  \\ ‘sock_accept 3w s1 = SOME (SOME c, s2)’
    by simp [Abbr ‘s1’, Abbr ‘s2’, sock_accept_def, AFUPDKEY_def]
  \\ xlet ‘POSTv v. &OPTION_TYPE NUM (OPTION_MAP w2n (SOME c)) v * SOCKETS s2’
  >- (xapp_spec Socket_accept_spec \\ xsimpl
      \\ qexistsl [‘emp’, ‘s2’, ‘s1’, ‘SOME c’, ‘3w’] \\ xsimpl)
  \\ qabbrev_tac ‘s3 = s2 with conns := [(c, empty_conn)]’
  \\ ‘sock_read c 100 s2 = SOME (SOME bs, s3)’
    by (simp [Abbr ‘s1’, Abbr ‘s2’, Abbr ‘s3’, sock_read_def, AFUPDKEY_def]
        \\ simp [TAKE_LENGTH_TOO_LONG, DROP_LENGTH_TOO_LONG, empty_conn_def])
  \\ ‘sock_write c bs s3 = SOME (echo_final c bs rest)’
    by simp [Abbr ‘s1’, Abbr ‘s2’, Abbr ‘s3’, sock_write_def, AFUPDKEY_def,
             echo_final_def, empty_conn_def]
  \\ fs [std_preludeTheory.OPTION_TYPE_def] \\ rveq
  \\ xmatch
  \\ xlet ‘POSTv v. &OPTION_TYPE STRING_TYPE
                        (OPTION_MAP (λd. implode (MAP (CHR o w2n) d)) (SOME bs)) v *
                      SOCKETS s3’
  >- (xapp_spec Socket_read_spec \\ xsimpl
      \\ qexistsl [‘emp’, ‘s3’, ‘s2’, ‘SOME bs’, ‘c’] \\ xsimpl)
  \\ fs [std_preludeTheory.OPTION_TYPE_def] \\ rveq
  \\ xmatch
  \\ xapp_spec Socket_write_spec \\ xsimpl
  \\ qexistsl [‘c’, ‘implode (MAP (CHR o w2n) bs)’]
  \\ simp [bytes_roundtrip]
QED

(* main as a whole program of the socket world: it leaves the file system
   alone and ends in echo_final. *)
Theorem main_whole_prog_spec:
  c ≠ 3w ∧ bs ≠ [] ∧ LENGTH bs ≤ 100 ⇒
  socket_whole_prog_spec main_v cl fs clk (echo_world c bs rest)
    (λfs' sk'. fs' = fs ∧ sk' = echo_final c bs rest)
Proof
  rw [socket_whole_prog_spec_def]
  \\ qexists_tac ‘fs’ \\ simp [with_same_numchars]
  \\ mp_tac (main_spec |> Q.GEN ‘p’ |> ISPEC “(socket_proj1, socket_proj2)”)
  \\ simp [] \\ strip_tac
  \\ first_x_assum (match_mp_tac o MP_CANON o MATCH_MP app_wgframe)
  \\ xsimpl
QED

(* The source semantics of the whole program (basis, Socket, main and a
   call to main), from the CF spec. *)
val echo_example_sem_thm =
  prove_sem_thm "main" "echo_example_prog" main_whole_prog_spec;

(* MAIN: in a socket world where connection c (≠ 3) with 1-100 bytes bs
   arrives on listener 3 in the first round, the one-shot echo program
   terminates successfully, leaves the file system unchanged, and its run
   ends with the outgoing log of c equal to bs. *)
Theorem echo_example_semantics:
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧
  c ≠ 3w ∧ bs ≠ [] ∧ LENGTH bs ≤ 100 ⇒
  ∃io_events ffi'.
    semantics_dec_list
      (init_state (socket_world_ffi cl fs clk (echo_world c bs rest)))
      init_env echo_example_prog (Terminate Success io_events) ∧
    socket_extract_fs cl fs io_events = SOME fs ∧
    call_FFI_rel^* (socket_world_ffi cl fs clk (echo_world c bs rest)) ffi' ∧
    ffi'.io_events = io_events ∧
    ALOOKUP (SND ffi'.ffi_state).conns c =
      SOME <| incoming := []; peer_closed := F; outgoing := bs |>
Proof
  strip_tac
  \\ mp_tac echo_example_sem_thm \\ simp []
  \\ strip_tac \\ gvs []
  \\ first_x_assum (irule_at Any) \\ simp [echo_final_def]
QED
