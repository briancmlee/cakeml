(*
  The key-value server in the socket vocabulary (model).

  srelabel (kv_server lfd) = with_store kv_delta (λk. NONE) (krelabel (kv_inner lfd))
  (relabel_with_store), where krelabel relabels the Sock actions as
  srelabel does and keeps the Kv queries.  krelabel of the skeleton and
  of the handler unfold to library computations over socket actions and
  queries, which is what the CakeML code (kvProg) mirrors.
*)
Theory kvSockModel
Ancestors
  pair list rich_list arithmetic option pred_set string words
  asyncCore asyncLevel1 asyncLevel2 echoServer loopPollWorld
  relabel relabelDist echoSockModel withStore
  withStoreStep skeletonK kvHandler kvModel
  HttpGetSpec HttpHeadersSpec HttpSpec httpHeadersParse httpParse
Libs
  BasicProvers wordsLib

Overload krelabel = “relabel (kfa sfa) (snap_map sfe (kfr sfr))”

(* MAIN: the server in the socket vocabulary is with_store of the inner
   server in the socket-and-query vocabulary *)
Theorem srelabel_kv_server:
  srelabel (kv_server lfd) = with_store kv_delta (λk. NONE) (krelabel (kv_inner lfd))
Proof
  simp[kv_server_def, relabel_with_store]
QED

Theorem krelabel_readable:
  krelabel (readable fd) = sreadable fd
Proof
  simp[readable_def, sreadable_def, relabel_wait, combinTheory.o_DEF,
       snap_map_def, sfe_def] >>
  AP_TERM_TAC >> simp[FUN_EQ_THM] >> metis_tac[]
QED

(* MAIN: the skeleton, unfolded *)
Theorem kserver_with_k_unfold:
  krelabel (server_with_k h lfd) =
    bind (sreadable lfd) (λu.
    bind (emit (Sock (loopPollWorld$Accept (n2w lfd)))) (λr.
      case r of
        SockR (loopPollWorld$Accepted (SOME c)) =>
          map (λp. ()) (both (krelabel (h (w2n c))) (krelabel (server_with_k h lfd)))
      | _ => krelabel (server_with_k h lfd)))
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [server_with_k_unfold])) >>
  simp[relabel_bind, relabel_emit, krelabel_readable, bind_map, kfa_def, sfa_def] >>
  AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> ABS_TAC >> rename1 ‘kfr sfr r’ >>
  Cases_on ‘r’ >> simp[kfr_def]
  >- (rename1 ‘sfr r0’ >> Cases_on ‘r0’
      >- (rename1 ‘Accepted ro’ >> Cases_on ‘ro’ >>
          simp[sfr_def, relabel_map, relabel_both])
      >- (rename1 ‘Got ro’ >> Cases_on ‘ro’ >> simp[sfr_def] >> rw[])
      >> simp[sfr_def])
QED

(* MAIN: the handler, unfolded *)
Theorem kkv_handler_unfold:
  krelabel (kv_handler (fd, buf)) =
    case parse_brequest buf of
      BComplete req rest =>
        bind (emit (Kv (fd, req))) (λa.
          case a of
            KvR ans =>
              bind (emit (Sock (loopPollWorld$Write (n2w fd)
                                  (MAP (n2w o ORD) (print_response ans)))))
                   (λw. krelabel (kv_handler (fd, rest)))
          | _ => return ())
    | BIncomplete =>
        bind (sreadable fd) (λu.
        bind (emit (Sock (loopPollWorld$Read (n2w fd) bufsz))) (λr.
          case r of
            SockR (Got (SOME bs)) =>
              if bs = [] then return ()
              else krelabel (kv_handler (fd, buf ++ MAP (CHR o w2n) bs))
          | _ => krelabel (kv_handler (fd, buf))))
    | BInvalid => return ()
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [kv_handler_unfold])) >>
  Cases_on ‘parse_brequest buf’ >>
  simp[relabel_bind, relabel_emit, krelabel_readable, bind_map, kfa_def, sfa_def,
       relabel_return]
  >- (AP_TERM_TAC >> ABS_TAC >> rename1 ‘kfr sfr a’ >>
      Cases_on ‘a’ >> simp[kfr_def, relabel_return, relabel_bind, relabel_emit,
                           bind_map, kfa_def, sfa_def]) >>
  AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> ABS_TAC >> rename1 ‘kfr sfr r’ >>
  Cases_on ‘r’ >> simp[kfr_def]
  >- (rename1 ‘sfr r0’ >> Cases_on ‘r0’
      >- (rename1 ‘Accepted ro’ >> Cases_on ‘ro’ >> simp[sfr_def])
      >- (rename1 ‘Got ro’ >> Cases_on ‘ro’ >> simp[sfr_def] >>
          rw[relabel_return])
      >> simp[sfr_def])
QED

Theorem wf_kkv_handler:
  wf (krelabel (kv_handler p))
Proof
  irule wf_relabel >> simp[wf_kv_handler]
QED

Theorem wf_kkv_inner:
  wf (krelabel (kv_inner lfd))
Proof
  irule wf_relabel >> simp[wf_kv_inner]
QED

Theorem wf_skv_server:
  wf (srelabel (kv_server lfd))
Proof
  irule wf_relabel >> simp[wf_kv_server]
QED
