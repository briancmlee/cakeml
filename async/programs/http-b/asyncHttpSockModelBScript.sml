(*
  The bodies HTTP handler in the socket vocabulary (model):
  asyncHttpSockModel's shttp_handler_unfold for http_handler_b.  The
  server skeleton's unfolding (sserver_with_unfold) is reused as is.
*)
Theory asyncHttpSockModelB
Ancestors
  pair list rich_list arithmetic option pred_set string words
  asyncCore asyncLevel1 asyncLevel2 asyncServer asyncM3World
  asyncM4Relabel asyncM4RelabelDist asyncM4SockModel asyncServerWith
  HttpSpec HttpSpecHeaders HttpSpecBodies asyncHttpParseH asyncHttpParseB
  asyncHttpServerB asyncHttpSockModel
Libs
  BasicProvers wordsLib

(* MAIN: the bodies HTTP handler in the socket vocabulary,
   unfolded (as shttp_handler_unfold, with parse_brequest and bhandle) *)
Theorem shttp_handler_b_unfold:
  srelabel (http_handler_b files (fd, buf)) =
    case parse_brequest buf of
      BComplete req rest =>
        bind (emit (asyncM3World$Write (n2w fd)
                      (MAP (n2w o ORD) (print_response (bhandle files req)))))
             (λw. srelabel (http_handler_b files (fd, rest)))
    | BIncomplete =>
        bind (sreadable fd) (λu.
        bind (emit (asyncM3World$Read (n2w fd) bufsz)) (λr.
          case r of
            Got (SOME bs) =>
              if bs = [] then return ()
              else srelabel (http_handler_b files (fd, buf ++ MAP (CHR o w2n) bs))
          | _ => srelabel (http_handler_b files (fd, buf))))
    | BInvalid => return ()
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [http_handler_b_unfold])) >>
  Cases_on ‘parse_brequest buf’ >>
  simp[relabel_bind, relabel_emit, srelabel_readable, bind_map, sfa_def,
       relabel_return] >>
  AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> ABS_TAC >> rename1 ‘sfr r’ >>
  Cases_on ‘r’
  >- (rename1 ‘Accepted ro’ >> Cases_on ‘ro’ >> simp[sfr_def])
  >- (rename1 ‘Got ro’ >> Cases_on ‘ro’ >> simp[sfr_def] >>
      rw[relabel_return])
  >> simp[sfr_def]
QED

Theorem wf_shttp_handler_b:
  wf (srelabel (http_handler_b files p))
Proof
  irule wf_relabel >> simp[wf_http_handler_b]
QED

Theorem wf_shttp_server_b:
  wf (srelabel (http_server_b files lfd))
Proof
  irule wf_relabel >> simp[wf_http_server_b]
QED
