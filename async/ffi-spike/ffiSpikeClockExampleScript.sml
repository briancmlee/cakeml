(*
  End-to-end example: a program that reads the clock twice and prints
  both readings, one per line, with a whole-program theorem about its
  behaviour in our clock world.
*)
Theory ffiSpikeClockExample
Ancestors
  ml_translator cfMain basis_ffi TextIOProof mlint
  ffiSpikeClockFFI ffiSpikeClockProof ffiSpikeClockWorld
Libs
  preamble basis ffiSpikeClockWorldLib

val _ = translation_extends "ffiSpikeClockProg";

Quote add_cakeml:
  fun main u =
    let
      val t1 = Clock.now ()
      val t2 = Clock.now ()
    in
      TextIO.print (Int.toString t1 ^ "\n" ^ Int.toString t2 ^ "\n")
    end
End

val st = get_ml_prog_state ();

(* What the example prints, given the two readings t1 and t2. *)
Definition clock_example_output_def:
  clock_example_output t1 t2 =
    mlint$toString (&t1) ^ «\n» ^ mlint$toString (&t2) ^ «\n»
End

(* The CF spec of main: it consumes two readings and prints them. *)
Theorem main_spec:
  t1 < 256 ** 8 ∧ t2 < 256 ** 8 ⇒
  app (p:'ffi ffi_proj) main_v [Conv NONE []]
    (STDIO fs * CLOCK (t1 ::: t2 ::: rest))
    (POSTv uv. &UNIT_TYPE () uv *
               STDIO (add_stdout fs (clock_example_output t1 t2)) *
               CLOCK rest)
Proof
  strip_tac
  \\ xcf "main" st
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet ‘POSTv v. &NUM t1 v * STDIO fs * CLOCK (t2 ::: rest)’
  >- (xapp_spec Clock_now_spec
      \\ qexistsl [‘STDIO fs’, ‘t1’, ‘t2 ::: rest’] \\ xsimpl)
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet ‘POSTv v. &NUM t2 v * STDIO fs * CLOCK rest’
  >- (xapp_spec Clock_now_spec
      \\ qexistsl [‘STDIO fs’, ‘t2’, ‘rest’] \\ xsimpl)
  (* convert and concatenate, then print *)
  \\ rpt (xlet_auto >- xsimpl)
  \\ xapp
  \\ qexistsl [‘CLOCK rest’, ‘clock_example_output t1 t2’, ‘fs’]
  \\ xsimpl \\ simp [clock_example_output_def]
QED

(* main as a whole program of our clock world: it prints the first two
   readings of the schedule. *)
Theorem main_whole_prog_spec:
  t1 < 256 ** 8 ∧ t2 < 256 ** 8 ⇒
  clock_whole_prog_spec main_v cl fs (t1 ::: t2 ::: rest)
    ((=) (add_stdout fs (clock_example_output t1 t2)))
Proof
  rw [clock_whole_prog_spec_def]
  \\ qmatch_goalsub_abbrev_tac ‘fs1 = _ with numchars := _’
  \\ qexists_tac ‘fs1’
  \\ simp [Abbr ‘fs1’, GSYM add_stdo_with_numchars, with_same_numchars]
  \\ mp_tac (main_spec |> Q.GEN ‘p’ |> ISPEC “(clock_proj1, clock_proj2)”)
  \\ simp [] \\ strip_tac
  \\ first_x_assum (match_mp_tac o MP_CANON o MATCH_MP app_wgframe)
  \\ xsimpl
QED

(* The source semantics of the whole program (the basis library, Clock,
   main, and a call to main), from the CF spec. *)
val clock_example_sem_thm =
  prove_sem_thm "main" "clock_example_prog" main_whole_prog_spec;

(* MAIN: in a clock world whose schedule starts with readings t1, t2 and is
   monotone and fits in 8 bytes, the example program terminates
   successfully, its file-system events append exactly
   "<t1>\n<t2>\n" to standard output, and t1 ≤ t2. *)
Theorem clock_example_semantics:
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ clock_ok (t1 ::: t2 ::: rest) ⇒
  ∃io_events.
    semantics_dec_list (init_state (clock_world_ffi cl fs (t1 ::: t2 ::: rest)))
      init_env clock_example_prog (Terminate Success io_events) ∧
    clock_extract_fs cl fs io_events =
      SOME (add_stdout fs (clock_example_output t1 t2)) ∧
    t1 ≤ t2
Proof
  strip_tac
  \\ drule clock_ok_first_two \\ strip_tac
  \\ mp_tac clock_example_sem_thm \\ simp []
  \\ strip_tac \\ gvs []
  \\ first_x_assum (irule_at Any) \\ simp []
QED
