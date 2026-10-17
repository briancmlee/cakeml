(*
  The KV program on the honest L0 world (P4 step F, design/46):

      fun main u = l1_main kv_port_conf kv_hw gkv_server

  l1_main (honestL1MainProg) checks fds 0, 1 and 2 with sys_fdok (D33),
  listens on kv_port_conf (8081), and runs the prefetching L1 loop with
  the key-value server on the returned listener fd.  The server is the
  version-2 KV server with the generated handler (asyncTranslateKv's
  gkv_server, whose spec is kv_server_spec's statement), unchanged.
*)
Theory honestKvL0Prog
Ancestors
  ml_translator Marshalling honestL0 honestL0World honestL1MainProg asyncTranslateKv
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib

val _ = translation_extends "asyncTranslateKv";

(* The listener's port, as sys_listen's 2-byte configuration *)
Definition kv_port_conf_def:
  kv_port_conf : word8 list = [31w; 145w]
End

Theorem kv_port:
  w22n kv_port_conf = 8081
Proof
  EVAL_TAC
QED

(* The outbox high-water mark: L1 stops fetching from a connection whose
   outbox is above it *)
Definition kv_hw_def:
  kv_hw = 65536n
End

val r = translate kv_port_conf_def;
val r = translate kv_hw_def;

Quote add_cakeml:
  fun main u = l1_main kv_port_conf kv_hw gkv_server;
End
