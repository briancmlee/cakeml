(*
  The concurrent echo server, in the model (M4's core property, before any
  CakeML).

  The server accepts connections on a listening fd.  For each accepted
  connection fd it runs that connection's echo handler concurrently with
  the rest of the server, using `both` (fork per connection by recursion;
  the scheduler's task pool stays fixed, see 06-scheduler.md §4):

     server lfd = wait until lfd is readable;
                  accept;
                  on Accepted fd: both (handler fd) (server lfd)
                  otherwise:      server lfd

  Vocabulary: the actions and responses of asyncEcho, extended
  conservatively with Accept / Accepted / NoConn (an assumption recorded in
  design/08-echo-server.md).  This theory does not build on asyncEcho, so
  the constructor names do not clash.
*)
Theory echoServer
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncLoop
Libs
  BasicProvers

Datatype:
  event = Readable num | Writable num | Timer num | Always
End

Datatype:
  action = Read num | Write num string | Accept num
End

(* Accept yields a new connection's fd, or NoConn ("would block") *)
Datatype:
  response = Data string | WouldBlock | Eof | Written | Accepted num | NoConn
End

Definition readable_def:
  readable fd = wait (λs. if Readable fd ∈ s.ready then SOME () else NONE)
End

(* ------------------------------------------------------------------------
   One connection: the echo handler
   ------------------------------------------------------------------------ *)

Definition handler_body_def:
  handler_body r fd =
    bind (readable fd) (λu.
    bind (emit (Read fd)) (λres.
      case res of
        Data d => bind (emit (Write fd d)) (λw. r fd)
      | Eof => return ()
      | _ => r fd))
End

Theorem handler_body_contractive:
  contractive handler_body
Proof
  rw[contractive_def, handler_body_def]
  >> ho_match_mp_tac guarded_bind
  >> simp[readable_def, wait_needs_snapshot]
  >> rpt gen_tac >> ho_match_mp_tac nonexpansive_bind >> simp[nonexpansive_const]
  >> Cases >> simp[nonexpansive_call, nonexpansive_const]
  >> ho_match_mp_tac nonexpansive_bind >> simp[nonexpansive_const, nonexpansive_call]
QED

Definition handler_def:
  handler = fix handler_body
End

Theorem handler_unfold:
  handler fd = handler_body handler fd
Proof
  simp[handler_def, Once (MATCH_MP fix_unfold handler_body_contractive)]
QED

(* ------------------------------------------------------------------------
   The server
   ------------------------------------------------------------------------ *)

Definition server_body_def:
  server_body r lfd =
    bind (readable lfd) (λu.
    bind (emit (Accept lfd)) (λres.
      case res of
        Accepted fd => map (λp. ()) (both (handler fd) (r lfd))
      | _ => r lfd))
End

(* MAIN: the server is a well-defined recursive definition: the recursive
   call (the rest of the server, alongside the new connection's handler)
   comes after waiting for the listener *)
Theorem server_body_contractive:
  contractive server_body
Proof
  rw[contractive_def, server_body_def]
  >> ho_match_mp_tac guarded_bind
  >> simp[readable_def, wait_needs_snapshot]
  >> rpt gen_tac >> ho_match_mp_tac nonexpansive_bind >> simp[nonexpansive_const]
  >> Cases >> simp[nonexpansive_call]
  >> ho_match_mp_tac nonexpansive_map >> ho_match_mp_tac nonexpansive_both
  >> simp[nonexpansive_const, nonexpansive_call]
QED

Definition server_def:
  server = fix server_body
End

(* MAIN: the server satisfies its recursive equation *)
Theorem server_unfold:
  server lfd =
    bind (readable lfd) (λu.
    bind (emit (Accept lfd)) (λres.
      case res of
        Accepted fd => map (λp. ()) (both (handler fd) (server lfd))
      | _ => server lfd))
Proof
  simp[server_def, Once (MATCH_MP fix_unfold server_body_contractive)]
  >> simp[server_body_def]
QED

(* ------------------------------------------------------------------------
   Well-formed and settled
   ------------------------------------------------------------------------ *)

Theorem wf_handler:
  wf (handler fd)
Proof
  simp[handler_def] >> irule wf_fix >> simp[handler_body_contractive]
  >> rw[handler_body_def]
  >> irule wf_bind >> simp[readable_def, wf_wait]
  >> irule wf_bind >> simp[wf_emit] >> Cases
  >> simp[wf_return] >> irule wf_bind >> simp[wf_emit]
QED

Theorem settled_handler:
  settled (handler fd)
Proof
  simp[handler_def] >> irule settled_fix >> simp[handler_body_contractive]
  >> rw[handler_body_def]
  >> irule settled_bind >> simp[readable_def, wf_wait, settled_wait]
  >> irule settled_bind >> simp[wf_emit, settled_emit] >> Cases
  >> simp[settled_return] >> irule settled_bind >> simp[wf_emit, settled_emit]
QED

(* MAIN: the server is well-formed *)
Theorem wf_server:
  wf (server lfd)
Proof
  simp[server_def] >> irule wf_fix >> simp[server_body_contractive]
  >> rw[server_body_def]
  >> irule wf_bind >> simp[readable_def, wf_wait]
  >> irule wf_bind >> simp[wf_emit] >> Cases >> simp[]
  >> irule wf_map >> irule wf_both >> simp[wf_handler]
QED

(* MAIN: the server never loses a response *)
Theorem settled_server:
  settled (server lfd)
Proof
  simp[server_def] >> irule settled_fix >> simp[server_body_contractive]
  >> rw[server_body_def]
  >> irule settled_bind >> simp[readable_def, wf_wait, settled_wait]
  >> irule settled_bind >> simp[wf_emit, settled_emit] >> Cases >> simp[]
  >> irule settled_map >> irule settled_both >> simp[settled_handler]
QED
