(*
  The CakeML side of the clock: a module Clock with one function
    now : unit -> int
  which calls the FFI function «now» with an 8-byte buffer and decodes
  the reading from it.  Built on top of the whole basis library.
*)
Theory ffiSpikeClockProg
Ancestors
  ml_translator basisProg Marshalling
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib

val _ = translation_extends "basisProg";

val _ = ml_prog_update (open_module "Clock");

val _ = ml_prog_update open_local_block;

(* Decoding a big-endian 8-byte reading, as a pure function translated
   into CakeML (so that its spec comes for free). *)
Definition bytes_to_num_def:
  bytes_to_num (b7:word8) b6 b5 b4 b3 b2 b1 b0 =
    w82n [b7; b6; b5; b4; b3; b2; b1; b0]
End

val r = translate (REWRITE_RULE [w82n_def] bytes_to_num_def);

val _ = ml_prog_update open_local_in_block;

Quote add_cakeml:
  fun now u =
    case u of () =>
    let
      val b = Word8Array.array 8 (Word8.fromInt 0)
      val u = #(now) "" b
    in
      bytes_to_num (Word8Array.sub b 0) (Word8Array.sub b 1)
                   (Word8Array.sub b 2) (Word8Array.sub b 3)
                   (Word8Array.sub b 4) (Word8Array.sub b 5)
                   (Word8Array.sub b 6) (Word8Array.sub b 7)
    end
End

val _ = ml_prog_update close_local_blocks;

val _ = ml_prog_update (close_module NONE);
