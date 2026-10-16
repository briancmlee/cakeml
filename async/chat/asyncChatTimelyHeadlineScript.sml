(*
  The chat program meets the candidate spec ChatSpecTimely with latency
  bound B = 4 polls, accept bound A = 3 polls per waiting connection and
  read bound R = 4 polls per arrived connection and per byte:

     chat_prog_timely : chat_spec_timely 4 3 4 3w chat_prog

  From the M3/M4 headline's ingredients (chat_semantics_prog, chat_live_trace)
  and asyncChatTimely (chat_prompt_trace, chat_accept_trace).
*)
Theory asyncChatTimelyHeadline
Ancestors
  words llist EchoSpec ChatSpec ChatSpecTimely ChatSpecTimelyBite
  ffiSpikeSocketFFI asyncM4ReadSoon asyncHeadline asyncChatSemantics
  asyncChatLiveHeadline asyncChatTimely asyncChatTimely2
Libs
  preamble

Theorem chat_timely_trace:
  server_world 3w s0 ⇒
  chat_prompt 4 (chat_trace s0) ∧ chat_accept_prompt 3 s0 (chat_trace s0) ∧
  chat_read_prompt 4 s0 (chat_trace s0)
Proof
  rw[server_world_def] >> ‘3 < dimword (:64)’ by EVAL_TAC
  >- (rw[chat_prompt_def] >>
      drule_all chat_prompt_trace >> disch_then (qspec_then ‘d’ strip_assume_tac) >>
      qexists_tac ‘evs'’ >> simp[] >>
      metis_tac[IS_PREFIX_TRANS, owed_open_prefix])
  >- (rw[chat_accept_prompt_def] >> irule chat_accept_backlog >> simp[])
  >> rw[chat_read_prompt_def] >>
  qspecl_then [‘3’, ‘s0’, ‘c’, ‘n’] mp_tac
    (Q.GENL [‘lfdn’, ‘s0’, ‘c’, ‘n’] chat_read_trace) >>
  simp[] >> strip_tac >> qexists_tac ‘evs’ >> simp[]
QED

(* MAIN: the chat program meets ChatSpecTimely: in every fair world with
   one listener 3w it runs forever, its trace is safe, live (with the
   departed-client fix), every client gets what it is owed within 4 polls,
   and every connection is accepted within 3 polls per connection that had
   arrived by then. *)
Theorem chat_prog_timely:
  chat_spec_timely 4 3 4 3w chat_prog
Proof
  rw[chat_spec_timely_def] >> qexists_tac ‘chat_trace sk’ >>
  drule chat_live_trace >> strip_tac >>
  drule chat_timely_trace >> strip_tac >>
  ‘sk.listeners = [(3w, [])] ∧ sk.conns = []’ by fs[server_world_def] >>
  qspec_then ‘sk’ mp_tac (Q.GEN ‘s0’ chat_semantics_prog) >>
  simp[socket_only_ffi_eq, chat_live_open_of_chat_live]
QED
