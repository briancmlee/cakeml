(*
  The CakeML side of the sockets: a module Socket with
    poll   : int list -> int list        (the ready fds among the given)
    accept : int -> int option           (NONE: would block)
    read   : int -> int -> string option (at most n bytes; SOME "": EOF;
                                          NONE: would block)
    write  : int -> string -> unit
  each a single FFI call.  Marshalling to and from the byte buffers is
  done by pure functions, translated into CakeML (so their specs come
  for free).  Built on top of the whole basis library.
*)
Theory socketProg
Ancestors
  ml_translator basisProg Marshalling
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib

val _ = translation_extends "basisProg";

val _ = ml_prog_update (open_module "Socket");

val _ = ml_prog_update open_local_block;

(* Encoding fds as 8-byte (8-character) strings. *)
Definition byte_char_def:
  byte_char (w:word8) = CHR (w2n w)
End

Definition fd_chars_def:
  fd_chars n = MAP byte_char (n2w8 n)
End

Definition fd_conf_def:
  fd_conf n = implode (fd_chars n)
End

Definition fds_conf_def:
  fds_conf ns = implode (FLAT (MAP fd_chars ns))
End

(* Decoding: a big-endian number from characters. *)
Definition chars_num_def:
  chars_num acc [] = acc ∧
  chars_num acc (c::cs) = chars_num (acc * 256 + ORD c) cs
End

(* The fds whose flag character is not 0.  (Monomorphic, so that its
   translation is about lists of ints.) *)
Definition ready_of_def:
  ready_of ([]:num list) cs = [] ∧
  ready_of (n::ns) cs =
    case cs of
    | [] => []
    | c::cs => if c = CHR 0 then ready_of ns cs else n :: ready_of ns cs
End

Definition decode_accept_def:
  decode_accept s =
    case explode s of
    | [] => NONE
    | c::rest => if c = CHR 1 then SOME (chars_num 0 (TAKE 8 rest)) else NONE
End

Definition decode_read_def:
  decode_read s =
    case explode s of
    | [] => NONE
    | c::rest =>
        if c = CHR 0 then
          SOME (implode (TAKE (chars_num 0 (TAKE 8 rest)) (DROP 8 rest)))
        else if c = CHR 2 then SOME (strlit "")
        else NONE
End

val r = translate byte_char_def;

Theorem byte_char_side[local]:
  byte_char_side w
Proof
  simp [fetch "-" "byte_char_side_def", w2n_lt_256]
QED

val _ = update_precondition byte_char_side;

val r = translate (n2w8_def |> SIMP_RULE arith_ss []);
val r = translate fd_chars_def;
val r = translate fd_conf_def;
val r = translate fds_conf_def;
val r = translate chars_num_def;
val r = translate ready_of_def;
val r = translate (decode_accept_def
                   |> REWRITE_RULE [GSYM mllistTheory.take_def]);
val r = translate (decode_read_def
                   |> REWRITE_RULE [GSYM mllistTheory.take_def,
                                    GSYM mllistTheory.drop_def]);

val _ = ml_prog_update open_local_in_block;

Quote add_cakeml:
  fun poll fds =
    let
      val n = List.length fds
      val a = Word8Array.array n (Word8.fromInt 0)
      val u = #(sock_poll) (fds_conf fds) a
    in
      ready_of fds (String.explode (Word8Array.substring a 0 n))
    end
End

Quote add_cakeml:
  fun accept l =
    let
      val a = Word8Array.array 9 (Word8.fromInt 0)
      val u = #(sock_accept) (fd_conf l) a
    in
      decode_accept (Word8Array.substring a 0 9)
    end
End

Quote add_cakeml:
  fun read c n =
    let
      val a = Word8Array.array (n + 9) (Word8.fromInt 0)
      val u = #(sock_read) (fd_conf c) a
    in
      decode_read (Word8Array.substring a 0 (n + 9))
    end
End

Quote add_cakeml:
  fun write c s =
    let
      val a = Word8Array.array 0 (Word8.fromInt 0)
      val u = #(sock_write) (fd_conf c ^ s) a
    in
      ()
    end
End

val _ = ml_prog_update close_local_blocks;

val _ = ml_prog_update (close_module NONE);
