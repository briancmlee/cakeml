(*
  The clock as a separation-logic resource, and the CF spec of Clock.now.
  Like the basis specs, the spec is generic in the FFI world
  (p:'ffi ffi_proj): it only needs the clock part to be present.
*)
Theory ffiSpikeClockProof
Ancestors
  ml_translator cfHeapsBase cfMain Marshalling Word8ArrayProof
  ffiSpikeClockFFI ffiSpikeClockProg
Libs
  preamble ml_translatorLib ml_progLib cfLib basisFunctionsLib

val _ = translation_extends "ffiSpikeClockProg";

(* CLOCK clk: the program owns the clock part, whose remaining schedule
   of readings is clk. *)
Definition CLOCK_def:
  CLOCK clk = IOx clock_ffi_part clk
End

(* CLOCK is backed by an FFI part (needed to use it in a postcondition of
   a whole-program spec). *)
Theorem CLOCK_FFI_part_hprop:
  FFI_part_hprop (CLOCK clk)
Proof
  rw [CLOCK_def, IOx_def, IO_def, clock_ffi_part_def, FFI_part_hprop_def,
      SEP_CLAUSES, SEP_EXISTS_THM, cond_STAR]
  \\ fs [one_def]
QED

(* The initial heap of a program holds the clock part with no events yet. *)
Theorem CLOCK_precond:
  CLOCK clk {FFI_part (clock_encode clk) (mk_ffi_next clock_ffi_part)
               [«now»] events}
Proof
  rw [CLOCK_def, IOx_def, IO_def, clock_ffi_part_def, SEP_EXISTS_THM,
      cond_STAR, one_def]
QED

(* The decoding function inverts the FFI's encoding. *)
Theorem bytes_to_num_n2w8:
  t < 256 ** 8 ⇒
  bytes_to_num (EL 0 (n2w8 t)) (EL 1 (n2w8 t)) (EL 2 (n2w8 t))
               (EL 3 (n2w8 t)) (EL 4 (n2w8 t)) (EL 5 (n2w8 t))
               (EL 6 (n2w8 t)) (EL 7 (n2w8 t)) = t
Proof
  strip_tac
  \\ ‘w82n (n2w8 t) = t’ by (irule w82n_n2w8 \\ decide_tac)
  \\ fs [bytes_to_num_def, n2w8_def]
QED

(* CF tactic: Word8Array.sub b i on the clock buffer returns byte i. *)
fun read_byte i =
  xlet [QUOTE ("POSTv w. &WORD (EL " ^ Int.toString i ^
               " (n2w8 t)) w * W8ARRAY bv (n2w8 t) * CLOCK rest")]
  >- (xapp \\ xsimpl \\ simp [LENGTH_n2w8]);

(* MAIN: Clock.now () returns the next reading t of the schedule and
   consumes it, provided t fits in 8 bytes. *)
Theorem Clock_now_spec:
  t < 256 ** 8 ∧ UNIT_TYPE () uv ⇒
  app (p:'ffi ffi_proj) Clock_now_v [uv]
    (CLOCK (t ::: rest))
    (POSTv v. &NUM t v * CLOCK rest)
Proof
  strip_tac
  \\ xcf_with_def Clock_now_v_def
  \\ gvs [UNIT_TYPE_def]
  \\ xmatch
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ rename1 ‘W8ARRAY bv (REPLICATE 8 0w)’
  (* the FFI call writes the reading into the buffer *)
  \\ xlet ‘POSTv uv. W8ARRAY bv (n2w8 t) * CLOCK rest’
  >- (qpat_abbrev_tac ‘Q = $POSTv _’
      \\ simp [CLOCK_def, IOx_def, IO_def, clock_ffi_part_def]
      \\ xpull \\ qunabbrev_tac ‘Q’
      \\ xffi \\ xsimpl
      \\ qmatch_goalsub_abbrev_tac ‘FFI_part s u ns events’
      \\ qexistsl [‘emp’, ‘s’, ‘u’, ‘ns’, ‘events’] \\ xsimpl
      \\ simp [Abbr ‘s’, Abbr ‘u’, Abbr ‘ns’, mk_ffi_next_def, ffi_now_LCONS]
      \\ simp [CLOCK_def, IOx_def, IO_def, clock_ffi_part_def]
      \\ xsimpl
      \\ qmatch_goalsub_abbrev_tac ‘events ++ new_events’
      \\ qexists_tac ‘events ++ new_events’ \\ xsimpl)
  (* read the eight bytes back *)
  \\ EVERY (map read_byte [7,6,5,4,3,2,1,0])
  (* and decode them *)
  \\ xapp
  \\ qexistsl [‘W8ARRAY bv (n2w8 t) * CLOCK rest’,
               ‘EL 7 (n2w8 t)’, ‘EL 6 (n2w8 t)’, ‘EL 5 (n2w8 t)’,
               ‘EL 4 (n2w8 t)’, ‘EL 3 (n2w8 t)’, ‘EL 2 (n2w8 t)’,
               ‘EL 1 (n2w8 t)’, ‘EL 0 (n2w8 t)’]
  \\ xsimpl
  \\ mp_tac bytes_to_num_n2w8 \\ simp []
QED
