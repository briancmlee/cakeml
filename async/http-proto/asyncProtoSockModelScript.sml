(*
  asyncProtoSockModel: the generic handler in the socket vocabulary
  (model), as asyncHttpSockModelH's shttp_handler_h_unfold, for every
  protocol.  The server skeleton's unfolding (sserver_with_unfold) is
  reused as is.
*)
Theory asyncProtoSockModel
Ancestors
  pair list rich_list arithmetic option pred_set string words
  asyncCore asyncLevel1 asyncLevel2 asyncServer asyncM3World
  asyncM4Relabel asyncM4RelabelDist asyncM4SockModel asyncServerWith
  asyncProto asyncProtoServer
Libs
  BasicProvers wordsLib

(* MAIN: the protocol handler in the socket vocabulary, unfolded *)
Theorem sproto_handler_unfold:
  srelabel (proto_handler P resp (fd, buf)) =
    case P.parse buf of
      PComplete req rest =>
        bind (emit (asyncM3World$Write (n2w fd) (MAP (n2w o ORD) (resp req))))
             (λw. srelabel (proto_handler P resp (fd, rest)))
    | PIncomplete =>
        bind (sreadable fd) (λu.
        bind (emit (asyncM3World$Read (n2w fd) bufsz)) (λr.
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
