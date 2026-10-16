(*
  protoSockModel: the server skeleton and the generic protocol
  handler in the socket vocabulary (model), as echoSockModel does for
  the echo server.

  srelabel (server_with h lfd) and srelabel (proto_handler P resp (fd, buf))
  unfold (by relabelDist) to library computations over socket
  actions, which is what the CakeML code of protoProg mirrors:
    - the skeleton waits for the listener, accepts, and runs each new
      connection's handler beside the rest of the server
      (sserver_with_unfold, for any handler);
    - the protocol handler writes the response's bytes, reads at most
      bufsz bytes, treats Got (SOME []) as EOF, and appends what it read
      to its buffer as characters (sproto_handler_unfold, for every
      protocol).
*)
Theory protoSockModel
Ancestors
  pair list rich_list arithmetic option pred_set string words
  asyncCore asyncLevel1 asyncLevel2 echoServer loopPollWorld
  relabel relabelDist echoSockModel skeleton
  protoInterface protoServer
Libs
  BasicProvers wordsLib

(* MAIN: the server skeleton in the socket vocabulary, unfolded: wait until
   the listener is ready; accept; on a new connection c, run c's handler
   alongside the rest of the server; otherwise continue. *)
Theorem sserver_with_unfold:
  srelabel (server_with h lfd) =
    bind (sreadable lfd) (λu.
    bind (emit (loopPollWorld$Accept (n2w lfd))) (λr.
      case r of
        loopPollWorld$Accepted (SOME c) =>
          map (λp. ()) (both (srelabel (h (w2n c))) (srelabel (server_with h lfd)))
      | _ => srelabel (server_with h lfd)))
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [server_with_unfold])) >>
  simp[relabel_bind, relabel_emit, srelabel_readable, bind_map, sfa_def] >>
  AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> ABS_TAC >> rename1 ‘sfr r’ >>
  Cases_on ‘r’
  >- (rename1 ‘Accepted ro’ >> Cases_on ‘ro’ >>
      simp[sfr_def, relabel_map, relabel_both])
  >- (rename1 ‘Got ro’ >> Cases_on ‘ro’ >> simp[sfr_def] >> rw[])
  >> simp[sfr_def]
QED

Theorem wf_sserver_with:
  (∀fd. wf (h fd)) ⇒ wf (srelabel (server_with h lfd))
Proof
  strip_tac >> irule wf_relabel >> simp[wf_server_with]
QED

(* MAIN: the protocol handler in the socket vocabulary, unfolded *)
Theorem sproto_handler_unfold:
  srelabel (proto_handler P resp (fd, buf)) =
    case P.parse buf of
      PComplete req rest =>
        bind (emit (loopPollWorld$Write (n2w fd) (MAP (n2w o ORD) (resp req))))
             (λw. srelabel (proto_handler P resp (fd, rest)))
    | PIncomplete =>
        bind (sreadable fd) (λu.
        bind (emit (loopPollWorld$Read (n2w fd) bufsz)) (λr.
          case r of
            Got (SOME bs) =>
              if bs = [] then return ()
              else srelabel (proto_handler P resp (fd, buf ++ MAP (CHR o w2n) bs))
          | _ => srelabel (proto_handler P resp (fd, buf))))
    | PInvalid => return ()
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [proto_handler_unfold])) >>
  Cases_on ‘P.parse buf’ >>
  simp[relabel_bind, relabel_emit, srelabel_readable, bind_map, sfa_def,
       relabel_return] >>
  AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> ABS_TAC >> rename1 ‘sfr r’ >>
  Cases_on ‘r’
  >- (rename1 ‘Accepted ro’ >> Cases_on ‘ro’ >> simp[sfr_def])
  >- (rename1 ‘Got ro’ >> Cases_on ‘ro’ >> simp[sfr_def] >>
      rw[relabel_return])
  >> simp[sfr_def]
QED

Theorem wf_sproto_handler:
  wf (srelabel (proto_handler P resp p))
Proof
  irule wf_relabel >> simp[wf_proto_handler]
QED

Theorem wf_sproto_server:
  wf (srelabel (proto_server P resp lfd))
Proof
  irule wf_relabel >> simp[wf_proto_server]
QED
