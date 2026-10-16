(*
  The echo server in the socket vocabulary (model).

  M3's event loop runs computations over the socket actions and responses
  of loopPollWorld (sact: Accept l | Read c n | Write c bs; sresp:
  Accepted (fd option) | Got (bytes option) | Wrote; ready sets of
  word64 fds).  The model's echo server (echoServer) speaks the model's
  own vocabulary.  The translation (design/15-m4-server.md §3.2):

     sfa: model action  -> socket action      (fds by n2w, strings as bytes,
                                                reads of at most bufsz bytes)
     sfr: socket response -> model response   (Got (SOME []) is Eof)
     sfs: socket snapshot -> model snapshot   (ready fd c gives Readable (w2n c))

  The socket-vocabulary server is  relabel sfa sfs (server lfd).  By
  relabelDist it unfolds to a library computation over socket
  actions (shandler_unfold, sserver_unfold), which is what the CakeML
  code of echoSockServer mirrors.
*)
Theory echoSockModel
Ancestors
  pair list rich_list arithmetic option pred_set string words
  asyncCore asyncLevel1 asyncLevel2 echoServer loopPollWorld
  relabel relabelDist
Libs
  BasicProvers wordsLib

(* The read size of the server's reads (any 0 < bufsz < 256 ** 8 works) *)
Definition bufsz_def:
  bufsz = 4096n
End

Definition sfa_def:
  sfa (echoServer$Accept l) = loopPollWorld$Accept (n2w l) ∧
  sfa (echoServer$Read fd) = loopPollWorld$Read (n2w fd) bufsz ∧
  sfa (echoServer$Write fd d) = loopPollWorld$Write (n2w fd) (MAP (n2w o ORD) d)
End

Definition sfr_def:
  sfr (loopPollWorld$Accepted (SOME c)) = echoServer$Accepted (w2n c) ∧
  sfr (loopPollWorld$Accepted NONE) = NoConn ∧
  sfr (Got NONE) = WouldBlock ∧
  sfr (Got (SOME bs)) =
    (if bs = [] then Eof else Data (MAP (CHR o w2n) (bs : word8 list))) ∧
  sfr Wrote = Written
End

Definition sfe_def:
  sfe (rdy : word64 set) = IMAGE (Readable o w2n) rdy
End

Overload sfs = “snap_map sfe sfr”

(* The socket-vocabulary version of a model computation *)
Overload srelabel = “relabel sfa sfs”

(* Waiting until some ready fd c has w2n c = fd *)
Definition sreadable_def:
  sreadable fd =
    wait (λs. if ∃c. c ∈ s.ready ∧ w2n c = fd then SOME () else NONE)
End

Theorem srelabel_readable:
  srelabel (readable fd) = sreadable fd
Proof
  simp[readable_def, sreadable_def, relabel_wait, combinTheory.o_DEF,
       snap_map_def, sfe_def] >>
  AP_TERM_TAC >> simp[FUN_EQ_THM] >> metis_tac[]
QED

Theorem bytes_round_trip:
  MAP (n2w o ORD) (MAP (CHR o w2n) (bs : word8 list)) = bs
Proof
  Induct_on ‘bs’ >> simp[] >> rpt strip_tac >>
  ‘w2n h < 256’ by (assume_tac (INST_TYPE [alpha |-> “:8”] w2n_lt) >> fs[]) >>
  simp[ORD_CHR_RWT]
QED

(* MAIN: the echo handler in the socket vocabulary, unfolded: wait until
   fd is ready; read at most bufsz bytes; on data bs, write bs back and
   continue; on EOF stop; otherwise continue. *)
Theorem shandler_unfold:
  srelabel (handler fd) =
    bind (sreadable fd) (λu.
    bind (emit (loopPollWorld$Read (n2w fd) bufsz)) (λr.
      case r of
        Got (SOME bs) =>
          if bs = [] then return ()
          else bind (emit (loopPollWorld$Write (n2w fd) bs))
                    (λw. srelabel (handler fd))
      | _ => srelabel (handler fd)))
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [handler_unfold])) >>
  simp[handler_body_def, relabel_bind, relabel_emit, srelabel_readable,
       bind_map, sfa_def] >>
  AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> ABS_TAC >> rename1 ‘sfr r’ >>
  Cases_on ‘r’
  >- (rename1 ‘Accepted ro’ >> Cases_on ‘ro’ >> simp[sfr_def])
  >- (rename1 ‘Got ro’ >> Cases_on ‘ro’ >> simp[sfr_def] >>
      rw[relabel_return, relabel_bind, relabel_emit, bind_map, sfa_def,
         bytes_round_trip])
  >> simp[sfr_def]
QED

(* MAIN: the echo server in the socket vocabulary, unfolded: wait until the
   listener is ready; accept; on a new connection c, run c's handler
   alongside the rest of the server; otherwise continue. *)
Theorem sserver_unfold:
  srelabel (server lfd) =
    bind (sreadable lfd) (λu.
    bind (emit (loopPollWorld$Accept (n2w lfd))) (λr.
      case r of
        loopPollWorld$Accepted (SOME c) =>
          map (λp. ()) (both (srelabel (handler (w2n c))) (srelabel (server lfd)))
      | _ => srelabel (server lfd)))
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [server_unfold])) >>
  simp[relabel_bind, relabel_emit, srelabel_readable, bind_map, sfa_def] >>
  AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> ABS_TAC >> rename1 ‘sfr r’ >>
  Cases_on ‘r’
  >- (rename1 ‘Accepted ro’ >> Cases_on ‘ro’ >>
      simp[sfr_def, relabel_map, relabel_both])
  >- (rename1 ‘Got ro’ >> Cases_on ‘ro’ >> simp[sfr_def] >> rw[])
  >> simp[sfr_def]
QED

Theorem wf_shandler:
  wf (srelabel (handler fd))
Proof
  irule wf_relabel >> simp[wf_handler]
QED

Theorem wf_sserver:
  wf (srelabel (server lfd))
Proof
  irule wf_relabel >> simp[wf_server]
QED

Theorem wf_sreadable:
  wf (sreadable fd)
Proof
  simp[sreadable_def, wf_wait]
QED

Theorem sreadable_NIL:
  (sreadable fd []).result = NONE
Proof
  simp[sreadable_def, wait_needs_snapshot]
QED
