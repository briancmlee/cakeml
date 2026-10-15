(*
  The chat server in the socket vocabulary (model).

     srelabel (chat_server lfd) =
       with_tap chat_tap_s chat_delta empty_store (krelabel (chat_inner lfd))

  (srelabel_chat_server, by relabel_with_tap): the socket-level tap
  chat_tap_s is the model's tap read through the relabelling.  The hub is
  keyed by 64-bit words, so this holds exactly, for every fd.

  krelabel of the skeleton and of the handler's parts unfold to library
  computations over socket actions and hub queries; the CakeML code
  (asyncChatProg) mirrors these equations.
*)
Theory asyncChatSockModel
Ancestors
  pair list rich_list arithmetic option pred_set string words
  asyncCore asyncLevel1 asyncLevel2 asyncServer asyncM3World
  asyncM4Relabel asyncM4RelabelDist asyncM4SockModel asyncWithStore
  asyncWithTap asyncWithTapStep asyncChatSW asyncChatModel
Libs
  BasicProvers wordsLib

Overload krelabel = “relabel (kfa sfa) (snap_map sfe (kfr sfr))”

(* A socket action, as the model's *)
Definition unsfa_def:
  unsfa (asyncM3World$Accept l) = asyncServer$Accept (w2n l) ∧
  unsfa (asyncM3World$Read c n) = asyncServer$Read (w2n c) ∧
  unsfa (asyncM3World$Write c bs) =
    asyncServer$Write (w2n c) (MAP (CHR o w2n) bs)
End

(* The tap, on socket actions and responses *)
Definition chat_tap_s_def:
  chat_tap_s st a r = chat_tap st (unsfa a) (sfr r)
End

Theorem n2w_MOD64[local]:
  (n2w (n MOD 18446744073709551616) : word64) = n2w n
Proof
  ONCE_REWRITE_TAC[GSYM wordsTheory.n2w_mod] >> simp[]
QED

Theorem chat_tap_s_sfa:
  chat_tap_s st (sfa a) r = chat_tap st a (sfr r)
Proof
  Cases_on ‘a’ >> simp[chat_tap_s_def, sfa_def, unsfa_def] >>
  simp[chat_tap_def] >> every_case_tac >> simp[n2w_MOD64]
QED

(* MAIN: the server in the socket vocabulary is with_tap of the inner
   server in the socket-and-query vocabulary *)
Theorem srelabel_chat_server:
  srelabel (chat_server lfd) =
  with_tap chat_tap_s chat_delta empty_store (krelabel (chat_inner lfd))
Proof
  simp[chat_server_def] >> irule relabel_with_tap >> simp[chat_tap_s_sfa]
QED

Theorem krelabel_readable:
  krelabel (readable fd) = sreadable fd
Proof
  simp[readable_def, sreadable_def, relabel_wait, combinTheory.o_DEF,
       snap_map_def, sfe_def] >>
  AP_TERM_TAC >> simp[FUN_EQ_THM] >> metis_tac[]
QED

(* MAIN: the skeleton, unfolded *)
Theorem kcserver_with_unfold:
  krelabel (cserver_with h lfd) =
    bind (sreadable lfd) (λu.
    bind (emit (Sock (asyncM3World$Accept (n2w lfd)))) (λr.
      case r of
        SockR (asyncM3World$Accepted (SOME c)) =>
          map (λp. ()) (both (krelabel (h (w2n c))) (krelabel (cserver_with h lfd)))
      | _ => krelabel (cserver_with h lfd)))
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [cserver_with_unfold])) >>
  simp[relabel_bind, relabel_emit, krelabel_readable, bind_map, kfa_def, sfa_def] >>
  AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> ABS_TAC >> rename1 ‘kfr sfr r’ >>
  Cases_on ‘r’ >> simp[kfr_def]
  >- (rename1 ‘sfr r0’ >> Cases_on ‘r0’
      >- (rename1 ‘Accepted ro’ >> Cases_on ‘ro’ >>
          simp[sfr_def, relabel_map, relabel_both])
      >- (rename1 ‘Got ro’ >> Cases_on ‘ro’ >> simp[sfr_def] >> rw[])
      >> simp[sfr_def])
QED

(* MAIN: the reader, unfolded *)
Theorem kreader_unfold:
  krelabel (reader fd) =
    bind (sreadable fd) (λu.
    bind (emit (Sock (asyncM3World$Read (n2w fd) bufsz))) (λr.
      case r of
        SockR (Got (SOME bs)) =>
          if bs = [] then return () else krelabel (reader fd)
      | _ => krelabel (reader fd)))
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [reader_unfold])) >>
  simp[relabel_bind, relabel_emit, krelabel_readable, bind_map, kfa_def, sfa_def] >>
  AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> ABS_TAC >> rename1 ‘kfr sfr r’ >>
  Cases_on ‘r’ >> simp[kfr_def]
  >- (rename1 ‘sfr r0’ >> Cases_on ‘r0’
      >- (rename1 ‘Accepted ro’ >> Cases_on ‘ro’ >> simp[sfr_def])
      >- (rename1 ‘Got ro’ >> Cases_on ‘ro’ >> simp[sfr_def] >>
          rw[relabel_return])
      >> simp[sfr_def])
QED

(* MAIN: the write loop, unfolded *)
Theorem kwloop_unfold:
  krelabel (wloop (fd, i)) =
    bind (emit (Kv (fd, Fetch i))) (λa.
      case a of
        KvR (Lines s) =>
          if s = "" then krelabel (wloop (fd, i))
          else bind (emit (Sock (asyncM3World$Write (n2w fd) (MAP (n2w o ORD) s))))
                    (λw. krelabel (wloop (fd, i + LENGTH s)))
      | _ => return ())
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [wloop_unfold])) >>
  simp[relabel_bind, relabel_emit, bind_map, kfa_def, sfa_def] >>
  AP_TERM_TAC >> ABS_TAC >> rename1 ‘kfr sfr a’ >> Cases_on ‘a’ >>
  simp[kfr_def, relabel_return] >>
  TRY (rename1 ‘KvR b’) >> TRY (Cases_on ‘b’) >> simp[relabel_return] >>
  rw[] >> simp[relabel_bind, relabel_emit, kfa_def, sfa_def, bind_map]
QED

(* MAIN: the writer, unfolded *)
Theorem kwriter_unfold:
  krelabel (writer fd) =
    bind (emit (Kv (fd, Start))) (λa.
      case a of
        KvR (Pos j) => krelabel (wloop (fd, j))
      | _ => return ())
Proof
  simp[writer_def, relabel_bind, relabel_emit, bind_map, kfa_def] >>
  AP_TERM_TAC >> ABS_TAC >> rename1 ‘kfr sfr a’ >> Cases_on ‘a’ >>
  simp[kfr_def, relabel_return] >>
  TRY (rename1 ‘KvR b’) >> TRY (Cases_on ‘b’) >> simp[relabel_return]
QED

(* MAIN: the handler, unfolded *)
Theorem kchat_handler_unfold:
  krelabel (chat_handler fd) =
    map (λp. ()) (both (krelabel (reader fd)) (krelabel (writer fd)))
Proof
  simp[chat_handler_def, relabel_map, relabel_both]
QED

Theorem wf_kchat_inner:
  wf (krelabel (chat_inner lfd))
Proof
  irule wf_relabel >> simp[wf_chat_inner]
QED

Theorem wf_schat_server:
  wf (srelabel (chat_server lfd))
Proof
  irule wf_relabel >> simp[wf_chat_server]
QED
