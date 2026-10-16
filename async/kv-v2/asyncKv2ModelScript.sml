(*
  THE MODEL RESULT for the key-value server on the version-2 handle layer
  (kv2_model): in every fair version-2 server world with one listener, the
  handle loop's run of kv_server is linearizable per episode (kv2_safe),
  live per client (kv2_live), and closes every episode whose client's EOF
  it read (gen_closes2): HttpKvSpec2's three clauses.
*)
Theory asyncKv2Model
Ancestors
  HttpKvSpec2 EchoSpec2 socketV2FFI socketV2Fair asyncProto2Model
  asyncKvModel asyncKv2Live asyncKv2Safe
Libs
  preamble

Theorem kv2_model:
  s2.listening = [(n2w lfdn, [])] ∧ s2.clients = [] ∧ s2.open_fds = [] ∧
  alloc_ok s2.alloc ∧ sched_wf2 s2 ∧ lfdn < dimword (:64) ⇒
  kv_safe2 (gtrace2 (kv_server lfdn) lfdn s2) ∧
  kv_live2 s2 (gtrace2 (kv_server lfdn) lfdn s2) ∧
  echo_closes2 (gtrace2 (kv_server lfdn) lfdn s2)
Proof
  simp[kv2_safe, kv2_live, gen_closes2]
QED
