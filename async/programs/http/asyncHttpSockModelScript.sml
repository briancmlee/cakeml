(*
  The server skeleton and the HTTP server in the socket vocabulary (model):
  asyncM4SockModel's treatment of the echo server, for server_with h and
  http_handler.

  srelabel (server_with h lfd) and srelabel (http_handler files (fd, buf))
  unfold (by asyncM4RelabelDist) to library computations over socket
  actions, which is what the CakeML code of asyncHttpSockProg mirrors:
    - the skeleton is sserver_unfold with any handler;
    - the HTTP handler writes the printed response's bytes, reads at most
      bufsz bytes, treats Got (SOME []) as EOF, and appends what it read
      to its buffer as characters (MAP (CHR o w2n)).
*)
Theory asyncHttpSockModel
Ancestors
  pair list rich_list arithmetic option pred_set string words
  asyncCore asyncLevel1 asyncLevel2 asyncServer asyncM3World
  asyncM4Relabel asyncM4RelabelDist asyncM4SockModel asyncServerWith
  HttpSpec asyncHttpParse asyncHttpServer
Libs
  BasicProvers wordsLib

(* MAIN: the server skeleton in the socket vocabulary, unfolded: wait until
   the listener is ready; accept; on a new connection c, run c's handler
   alongside the rest of the server; otherwise continue. *)
Theorem sserver_with_unfold:
  srelabel (server_with h lfd) =
    bind (sreadable lfd) (λu.
    bind (emit (asyncM3World$Accept (n2w lfd))) (λr.
      case r of
        asyncM3World$Accepted (SOME c) =>
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

(* MAIN: the HTTP handler in the socket vocabulary, unfolded: if the buffer
   starts with a complete request, write the bytes of its response and
   continue with the rest; if it is incomplete, wait until fd is ready,
   read at most bufsz bytes, and continue with the buffer extended by them
   (stop on EOF); if it is invalid, stop. *)
Theorem shttp_handler_unfold:
  srelabel (http_handler files (fd, buf)) =
    case parse_request buf of
      Complete req rest =>
        bind (emit (asyncM3World$Write (n2w fd)
                      (MAP (n2w o ORD) (print_response (handle files req)))))
             (λw. srelabel (http_handler files (fd, rest)))
    | Incomplete =>
        bind (sreadable fd) (λu.
        bind (emit (asyncM3World$Read (n2w fd) bufsz)) (λr.
          case r of
            Got (SOME bs) =>
              if bs = [] then return ()
              else srelabel (http_handler files (fd, buf ++ MAP (CHR o w2n) bs))
          | _ => srelabel (http_handler files (fd, buf))))
    | Invalid => return ()
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [http_handler_unfold])) >>
  Cases_on ‘parse_request buf’ >>
  simp[relabel_bind, relabel_emit, srelabel_readable, bind_map, sfa_def,
       relabel_return] >>
  AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> ABS_TAC >> rename1 ‘sfr r’ >>
  Cases_on ‘r’
  >- (rename1 ‘Accepted ro’ >> Cases_on ‘ro’ >> simp[sfr_def])
  >- (rename1 ‘Got ro’ >> Cases_on ‘ro’ >> simp[sfr_def] >>
      rw[relabel_return])
  >> simp[sfr_def]
QED

Theorem wf_shttp_handler:
  wf (srelabel (http_handler files p))
Proof
  irule wf_relabel >> simp[wf_http_handler]
QED

Theorem wf_sserver_with:
  (∀fd. wf (h fd)) ⇒ wf (srelabel (server_with h lfd))
Proof
  strip_tac >> irule wf_relabel >> simp[wf_server_with]
QED

Theorem wf_shttp_server:
  wf (srelabel (http_server files lfd))
Proof
  irule wf_relabel >> simp[wf_http_server]
QED
