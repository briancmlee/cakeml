(*
  The CakeML side of the honest L0 FFI (design/36 §3.2): a module L0 with
  one function per C entry point,

     L0.listen, L0.accept, L0.recv, L0.send, L0.shutdown, L0.close,
     L0.fdok (D33) : string -> int -> string
     L0.poll : string -> string -> string

  Each makes exactly one FFI call: L0.x conf n calls «sys_x» with the
  configuration conf on a fresh buffer of n zero bytes, and returns the
  buffer the call leaves (the 13-byte result header, then recv's data).
  L0.poll conf buf (D20) calls «sys_poll» on a copy of buf (the header's
  room, then the struct pollfd entries) and returns it as the call leaves
  it (the result header, then the entries with their revents).  Nothing is decoded here: L1's model (honestL1Model's
  sys_* / l0_do) builds the configurations and decodes the results, and
  its code is pure (translated).

  Appended to the version-1 echo program's translation state
  (asyncM4SockServer: the basis, the Async library and the socket-vocabulary
  echo server), the chain the servers live in.
*)
Theory honestL0Prog
Ancestors
  ml_translator asyncM4SockServer
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncM4SockServer";

val _ = ml_prog_update (open_module "L0");

Quote add_cakeml:
  fun listen conf n =
    let
      val a = Word8Array.array n (Word8.fromInt 0)
      val u = #(sys_listen) conf a
    in
      Word8Array.substring a 0 n
    end;
  fun poll conf buf =
    let
      val n = String.size buf
      val a = Word8Array.array n (Word8.fromInt 0)
      val u = Word8Array.copyVec buf 0 n a 0
      val u = #(sys_poll) conf a
    in
      Word8Array.substring a 0 n
    end;
  fun accept conf n =
    let
      val a = Word8Array.array n (Word8.fromInt 0)
      val u = #(sys_accept) conf a
    in
      Word8Array.substring a 0 n
    end;
  fun recv conf n =
    let
      val a = Word8Array.array n (Word8.fromInt 0)
      val u = #(sys_recv) conf a
    in
      Word8Array.substring a 0 n
    end;
  fun send conf n =
    let
      val a = Word8Array.array n (Word8.fromInt 0)
      val u = #(sys_send) conf a
    in
      Word8Array.substring a 0 n
    end;
  fun shutdown conf n =
    let
      val a = Word8Array.array n (Word8.fromInt 0)
      val u = #(sys_shutdown) conf a
    in
      Word8Array.substring a 0 n
    end;
  fun close conf n =
    let
      val a = Word8Array.array n (Word8.fromInt 0)
      val u = #(sys_close) conf a
    in
      Word8Array.substring a 0 n
    end;
  fun fdok conf n =
    let
      val a = Word8Array.array n (Word8.fromInt 0)
      val u = #(sys_fdok) conf a
    in
      Word8Array.substring a 0 n
    end;
End

val _ = ml_prog_update (close_module NONE);
