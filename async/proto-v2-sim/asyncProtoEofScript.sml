(*
  The generic protocol handler does nothing on its connection after
  reading its EOF (proto_handler_eof_last), as echo's handler
  (asyncHLEof.handler_eof_last).  Through server_with, a server whose
  handlers have this property has it on every accepted connection
  (sw_eof_last); so does the generic protocol server
  (proto_server_eof_last).  This is what the handle layer, which closes a
  connection as soon as a read returns EOF, needs of a server.
*)
Theory asyncProtoEof
Ancestors
  asyncCore asyncLevel1 asyncTranscript asyncServer asyncServerSafety
  asyncProgress asyncServerWith asyncSWProgress asyncProto asyncProtoServer
  asyncProtoLive asyncHLEof
Libs
  preamble

(* A server whose transcript, restricted to an accepted connection, ends
   at that connection's EOF *)
Definition srv_eof_last_def:
  srv_eof_last m ⇔
    ∀h fd. fresh (trans m h) ∧ prompt m h ∧ MEM fd (accepted (trans m h)) ⇒
           eof_last fd (FILTER (on_fd fd) (trans m h))
End

(* MAIN: the protocol handler's transcript ends at its EOF *)
Theorem proto_handler_eof_last:
  ∀h buf. eof_last fd (trans (proto_handler P resp (fd, buf)) h)
Proof
  gen_tac >> measureInduct_on ‘LENGTH h’ >> gen_tac
  >> ONCE_REWRITE_TAC[proto_handler_unfold]
  >> Cases_on ‘P.parse buf’ >> simp[trans_return, eof_last_def]
  (* a complete request: answer it, then continue *)
  >- (rename1 ‘PComplete req rest’
      >> qspecl_then [‘emit (asyncServer$Write fd (resp req))’,
                      ‘λw. proto_handler P resp (fd, rest)’, ‘h’] mp_tac
           (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
      >> simp[wf_emit, settled_emit] >> strip_tac
      >- simp[trans_emit, eof_last_def]
      >> drule first_done_emit >> strip_tac >> gvs[trans_emit, eof_last_def]
      >> first_x_assum irule >> Cases_on ‘h1’ >> gvs[])
  (* incomplete: wait until fd is readable, read it *)
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (readable fd) K0) h’
  >> qspecl_then [‘readable fd’, ‘K0’, ‘h’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[readable_def, wf_wait, settled_wait] >> strip_tac >> simp[eof_last_def]
  >> drule first_done_wait_nonempty >> strip_tac
  >> simp[Abbr ‘K0’]
  >> qmatch_goalsub_abbrev_tac ‘trans (bind (emit (asyncServer$Read fd)) K1) h2’
  >> qspecl_then [‘emit (asyncServer$Read fd)’, ‘K1’, ‘h2’] mp_tac
       (Q.GENL [‘m’, ‘f’, ‘h’] trans_bind_cases)
  >> simp[wf_emit, settled_emit] >> strip_tac
  >- (simp[trans_emit] >> rw[eof_last_def])
  >> drule first_done_emit >> strip_tac >> gvs[trans_emit]
  >> rename1 ‘oHD s.results = SOME res’
  >> ‘LENGTH h2' < LENGTH h1 + (LENGTH h2' + 1)’ by (Cases_on ‘h1’ >> gvs[])
  >> simp[Abbr ‘K1’, eof_last_def]
  >> Cases_on ‘res’ >> simp[trans_return, eof_last_def]
QED

(* MAIN: through server_with, per accepted connection *)
Theorem sw_eof_last:
  hok hf ∧ (∀fd g. eof_last fd (trans (hf fd) g)) ⇒ srv_eof_last (server_with hf lfd)
Proof
  rw[srv_eof_last_def] >>
  drule_all sw_handler_view >> strip_tac >> simp[]
QED

(* MAIN: the generic protocol server *)
Theorem proto_server_eof_last:
  proto_ok P ⇒ srv_eof_last (proto_server P resp lfd)
Proof
  strip_tac >> simp[proto_server_def] >> irule sw_eof_last >>
  simp[hok_proto, proto_handler_eof_last]
QED
