(*
  The chat program meets all of spec/ChatSpec: chat_spec 3w chat_prog.
   - safety and the run: chat_semantics_prog (M3);
   - liveness: chat_live_accepts, chat_live_reads, chat_live_deliver (M4),
     with lfdn = 3, for the same trace.
*)
Theory asyncChatLiveHeadline
Ancestors
  words llist EchoSpec ChatSpec ffiSpikeSocketFFI asyncM4ReadSoon
  asyncHeadline asyncChatSemantics asyncChatLiveAccept asyncChatLiveReadRun
  asyncChatLiveDeliverRun
Libs
  preamble

(* The program's trace is the trace the liveness clauses talk about *)
Theorem chat_live_trace:
  server_world 3w s0 ⇒ chat_live s0 (chat_trace s0)
Proof
  rw[server_world_def, chat_live_def] >>
  ‘3 < dimword (:64)’ by EVAL_TAC
  >- (irule chat_live_accepts >> simp[] >> metis_tac[])
  >- (irule chat_live_reads >> simp[])
  >> irule chat_live_deliver >> simp[]
QED

(* MAIN: the chat program satisfies ChatSpec's chat_spec 3w: in every fair
   world with one listener 3w it runs forever, and its I/O trace is safe
   (every client is only ever sent a prefix of what it is owed) and live
   (connections are accepted, complete lines are read, and what is owed is
   eventually written). *)
Theorem chat_prog_spec:
  chat_spec 3w chat_prog
Proof
  rw[chat_spec_def] >> qexists_tac ‘chat_trace sk’ >>
  drule chat_live_trace >>
  ‘sk.listeners = [(3w, [])] ∧ sk.conns = []’ by fs[server_world_def] >>
  qspec_then ‘sk’ mp_tac (Q.GEN ‘s0’ chat_semantics_prog) >>
  simp[socket_only_ffi_eq]
QED
