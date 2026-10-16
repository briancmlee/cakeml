(*
  The CakeML side of «sock_close»: a module SocketClose with
    close : int -> unit
  a single FFI call, the 8-byte fd as its config.

  It is appended to the version-1 echo program's translation state
  (echoSockServer: the basis, the Socket module, the Async library,
  the loops and the socket-vocabulary echo server), whose Socket.poll,
  accept, read and write make exactly the calls the version-2 world
  answers (same names, same encodings).
*)
Theory lifetimeProg
Ancestors
  ml_translator echoSockServer Marshalling
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib

val _ = translation_extends "echoSockServer";

val _ = ml_prog_update (open_module "SocketClose");

val _ = ml_prog_update open_local_block;

(* The fd as an 8-character string (as the Socket module's fd_conf) *)
Definition cl_byte_char_def:
  cl_byte_char (w:word8) = CHR (w2n w)
End

Definition cl_n2w8_def:
  cl_n2w8 (i:num) = n2w8 i
End

Definition cl_conf_def:
  cl_conf n = implode (MAP cl_byte_char (cl_n2w8 n))
End

val r = translate cl_byte_char_def;

Theorem cl_byte_char_side[local]:
  cl_byte_char_side w
Proof
  simp [fetch "-" "cl_byte_char_side_def", w2n_lt_256]
QED

val _ = update_precondition cl_byte_char_side;

val r = translate (cl_n2w8_def |> REWRITE_RULE [n2w8_def] |> SIMP_RULE arith_ss []);
val r = translate cl_conf_def;

val _ = ml_prog_update open_local_in_block;

Quote add_cakeml:
  fun close c =
    let
      val a = Word8Array.array 0 (Word8.fromInt 0)
      val u = #(sock_close) (cl_conf c) a
    in
      ()
    end
End

val _ = ml_prog_update close_local_blocks;

val _ = ml_prog_update (close_module NONE);
