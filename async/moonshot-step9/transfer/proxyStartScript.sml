(*
  Moonshot step 9, item 5: the world facts at the proxy's start (R2 for
  honest-ffi's liveness lift).  After proxy_start, the world w4 where E1's
  rounds begin satisfies the rely, the fd bound, and has the listener k
  and stdin in use: e1-driver's e1World.e1_start_world and
  e1_start_stdio_used, at port a.
*)
Theory proxyStart
Ancestors
  proxyL0Run proxyL0Stmts e1World e1DriverMain e1DriverProg
Libs
  preamble

(* l0sysInv's fds_lt is a verbatim copy of honestL0WorldProps' *)
Theorem fds_lt_copy:
  l0sysInv$fds_lt w ⇔ honestL0WorldProps$fds_lt w
Proof
  simp[l0sysInvTheory.fds_lt_def, honestL0WorldPropsTheory.fds_lt_def]
QED

Theorem proxy_start_facts:
  proxy_start a w0 pre w4 k ⇒
  l0_rely w4 ∧ honestL0WorldProps$fds_lt w4 ∧ l0sysInv$fds_lt w4 ∧
  MEM (n2w k : word64) (l0_used w4) ∧ MEM (0w : word64) (l0_used w4)
Proof
  simp[proxy_start_def, l0_proxy_world_def, fds_lt_copy] >> strip_tac >>
  ‘sys_listen_port a w3 = SOME (out, w4, ev)’ by simp[sys_listen_port_def] >>
  ‘listen_fd out = SOME k’ by simp[listen_fd_def] >>
  ‘fdok_all [1w] [1w] [1w]’ by simp[fdok_all_def] >>
  drule_all e1_start_world >> strip_tac >>
  drule_all e1_start_stdio_used >> strip_tac >>
  simp[]
QED
