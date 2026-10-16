(*
  Logical model of a clock, as a new FFI part.

  The clock's state is the stream of readings it will return, in order:
  an arbitrary schedule chosen by the environment, like the numchars
  stream of fsFFI.  Each call to the FFI function «now» consumes the head
  of the stream and writes it into the 8-byte buffer (big-endian, as
  Marshalling's n2w8).  Nothing here mentions the basis library's world.
*)
Theory clockFFI
Ancestors
  cfHeapsBase cfFFIType llist Marshalling
Libs
  preamble

val _ = option_monadsyntax.temp_add_option_monadsyntax();

(* The single FFI function of the clock: given an 8-byte buffer, write the
   next reading into it and drop that reading from the schedule.  It fails
   (NONE) on a buffer of the wrong size or an exhausted schedule. *)
Definition ffi_now_def:
  ffi_now (conf:word8 list) (bytes:word8 list) (clk:num llist) =
    do
      assert (LENGTH bytes = 8);
      t <- LHD clk;
      rest <- LTL clk;
      return (FFIreturn (n2w8 t) rest)
    od
End

(* The call on a non-empty schedule, as a rewrite. *)
Theorem ffi_now_LCONS:
  LENGTH bytes = 8 ⇒
  ffi_now conf bytes (t ::: rest) = SOME (FFIreturn (n2w8 t) rest)
Proof
  rw [ffi_now_def]
QED

(* Like every FFI function, ffi_now returns a buffer of the size it got. *)
Theorem ffi_now_length:
  ffi_now conf bytes clk = SOME (FFIreturn bytes' clk') ⇒
  LENGTH bytes' = LENGTH bytes
Proof
  rw [ffi_now_def] \\ simp [LENGTH_n2w8]
QED

(* The clock never makes the program diverge. *)
Theorem ffi_now_not_diverge:
  ffi_now conf bytes clk ≠ SOME FFIdiverge
Proof
  rw [ffi_now_def] \\ Cases_on ‘LHD clk’ \\ Cases_on ‘LTL clk’ \\ simp []
QED

(* Assumptions on a schedule.  Readings must fit the 8-byte encoding, and
   the clock is monotone: each reading is at least the previous one. *)
Definition clock_fits_def:
  clock_fits (clk:num llist) ⇔ ∀n t. LNTH n clk = SOME t ⇒ t < 256 ** 8
End

Definition clock_mono_def:
  clock_mono (clk:num llist) ⇔
    ∀n t t'. LNTH n clk = SOME t ∧ LNTH (SUC n) clk = SOME t' ⇒ t ≤ t'
End

Definition clock_ok_def:
  clock_ok (clk:num llist) ⇔ clock_fits clk ∧ clock_mono clk
End

(* The facts about the first two readings that the example needs. *)
Theorem clock_ok_first_two:
  clock_ok (t1 ::: t2 ::: rest) ⇒ t1 < 256 ** 8 ∧ t2 < 256 ** 8 ∧ t1 ≤ t2
Proof
  rw [clock_ok_def, clock_fits_def, clock_mono_def]
  >- (qpat_x_assum ‘∀n t. _ ⇒ t < _’ (qspecl_then [‘0’, ‘t1’] mp_tac)
      \\ simp [])
  >- (qpat_x_assum ‘∀n t. _ ⇒ t < _’ (qspecl_then [‘SUC 0’, ‘t2’] mp_tac)
      \\ simp [])
  \\ qpat_x_assum ‘∀n t t'. _’ (qspecl_then [‘0’, ‘t1’, ‘t2’] mp_tac)
  \\ simp []
QED

(* Packaging the model as an FFI part: the state is encoded with the
   Stream constructor of the universal ffi type. *)
Definition clock_encode_def:
  clock_encode (clk:num llist) = Stream clk
End

Theorem clock_encode_11[local]:
  ∀x y. clock_encode x = clock_encode y ⇔ x = y
Proof
  rw [clock_encode_def]
QED

Theorem clock_decode_exists[local]:
  ∃decode. ∀clk. decode (clock_encode clk) = SOME clk
Proof
  qexists_tac ‘λf. some c. clock_encode c = f’ \\ simp [clock_encode_11]
QED

val clock_decode_encode = new_specification (
  "clock_decode_encode", ["clock_decode"], clock_decode_exists);
val _ = export_rewrites ["clock_decode_encode"];

(* The clock part: one FFI name, «now». *)
Definition clock_ffi_part_def:
  clock_ffi_part = (clock_encode, clock_decode, [(«now», ffi_now)])
End
