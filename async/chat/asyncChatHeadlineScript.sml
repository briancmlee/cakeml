(*
  The chat program, stated in spec/ChatSpec's own terms.
*)
Theory asyncChatHeadline
Ancestors
  EchoSpec ChatSpec asyncHeadline asyncChatMain asyncChatSemantics
Libs
  preamble

(* MAIN: the chat program satisfies the safety half of ChatSpec's
   chat_spec 3w: in every fair world with one listener 3w, it runs forever,
   and at every point of its I/O trace, for every connection d, the bytes
   written to d are a prefix of the lines the server completed reading
   after it accepted d, in the order it completed them. *)
Theorem chat_prog_safe:
  ∀sk. server_world 3w sk ⇒
       ∃io. semantics_prog (init_state (socket_ffi sk)) init_env chat_prog
              (Diverge io) ∧
            chat_safe io
Proof
  rw[server_world_def] >>
  qspec_then ‘sk’ mp_tac (Q.GEN ‘s0’ chat_semantics_prog) >>
  simp[socket_only_ffi_eq] >> metis_tac[]
QED
