(*
  asyncProtoV: the generic protocol handler over an action vocabulary V
  (asyncServerV), with an optional query per request (design/32 §2.3, for
  KV; additive over asyncProtoServer).

     proto_handler_v V P ansq fin (fd, buf) =
       case P.parse buf of
         PComplete req rest =>
           (case ansq req of
              NONE   => write (fin req NONE); continue with rest
            | SOME q => emit the query q; write (fin req (answer)); continue)
       | PIncomplete => wait until readable, read, continue
       | PInvalid    => stop

  ansq says whether a request needs a query (for KV: a store operation),
  fin computes the response from the request and the query's answer.
  The existing handler is the case of the identity vocabulary and no
  queries (proto_handler_idV), so every result about proto_handler is one
  about proto_handler_v.
*)
Theory asyncProtoV
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncLoop asyncLevel2 asyncTranscript asyncServer
  asyncServerSafety asyncServerWith asyncServerV asyncProto asyncProtoServer
Libs
  BasicProvers

Definition proto_body_v_def:
  proto_body_v V P ansq fin r p =
    case p of
      (fd, buf) =>
        case P.parse buf of
          PComplete req rest =>
            (case ansq req of
               NONE =>
                 bind (emit (V.wr fd (fin req NONE))) (λw. r (fd, rest))
             | SOME q =>
                 bind (emit (V.qry q)) (λa.
                 bind (emit (V.wr fd (fin req (V.kans a)))) (λw. r (fd, rest))))
        | PIncomplete =>
            bind (readable fd) (λu.
            bind (emit (V.rd fd)) (λres.
              case V.sres res of
                SOME (Data d) => r (fd, buf ++ d)
              | SOME Eof => return ()
              | _ => r (fd, buf)))
        | PInvalid => return ()
End

Theorem proto_body_v_contractive:
  contractive (proto_body_v V P ansq fin)
Proof
  rw[contractive_def] >> PairCases_on ‘p’ >> simp[proto_body_v_def] >>
  Cases_on ‘P.parse p1’ >> simp[guarded_const]
  >- (CASE_TAC
      >- (ho_match_mp_tac guarded_bind >> simp[emit_needs_snapshot, nonexpansive_call])
      >> ho_match_mp_tac guarded_bind >> simp[emit_needs_snapshot] >>
      rpt gen_tac >> ho_match_mp_tac nonexpansive_bind >>
      simp[nonexpansive_const, nonexpansive_call])
  >> ho_match_mp_tac guarded_bind
  >> simp[readable_def, wait_needs_snapshot]
  >> rpt gen_tac >> ho_match_mp_tac nonexpansive_bind >> simp[nonexpansive_const]
  >> gen_tac >> rpt CASE_TAC >> simp[nonexpansive_call, nonexpansive_const]
QED

Definition proto_handler_v_def:
  proto_handler_v V P ansq fin = fix (proto_body_v V P ansq fin)
End

(* MAIN: the handler satisfies its recursive equation *)
Theorem proto_handler_v_unfold:
  proto_handler_v V P ansq fin (fd, buf) =
    case P.parse buf of
      PComplete req rest =>
        (case ansq req of
           NONE =>
             bind (emit (V.wr fd (fin req NONE)))
                  (λw. proto_handler_v V P ansq fin (fd, rest))
         | SOME q =>
             bind (emit (V.qry q)) (λa.
             bind (emit (V.wr fd (fin req (V.kans a))))
                  (λw. proto_handler_v V P ansq fin (fd, rest))))
    | PIncomplete =>
        bind (readable fd) (λu.
        bind (emit (V.rd fd)) (λres.
          case V.sres res of
            SOME (Data d) => proto_handler_v V P ansq fin (fd, buf ++ d)
          | SOME Eof => return ()
          | _ => proto_handler_v V P ansq fin (fd, buf)))
    | PInvalid => return ()
Proof
  simp[proto_handler_v_def, Once (MATCH_MP fix_unfold proto_body_v_contractive)]
  >> simp[proto_body_v_def]
QED

Theorem wf_proto_handler_v:
  wf (proto_handler_v V P ansq fin p)
Proof
  simp[proto_handler_v_def] >> irule wf_fix >> simp[proto_body_v_contractive]
  >> rw[] >> PairCases_on ‘p’ >> simp[proto_body_v_def] >> CASE_TAC >> simp[wf_return]
  >- (CASE_TAC >> irule wf_bind >> simp[wf_emit] >> rw[] >>
      irule wf_bind >> simp[wf_emit])
  >> irule wf_bind >> simp[readable_def, wf_wait]
  >> irule wf_bind >> simp[wf_emit] >> rw[] >> rpt CASE_TAC >> simp[wf_return]
QED

Theorem settled_proto_handler_v:
  settled (proto_handler_v V P ansq fin p)
Proof
  simp[proto_handler_v_def] >> irule settled_fix >> simp[proto_body_v_contractive]
  >> rw[] >> PairCases_on ‘p’ >> simp[proto_body_v_def] >> CASE_TAC
  >> simp[settled_return]
  >- (CASE_TAC
      >- (irule settled_bind >> simp[wf_emit, settled_emit])
      >> irule settled_bind >> simp[wf_emit, settled_emit] >> rw[] >>
      irule settled_bind >> simp[wf_emit, settled_emit])
  >> irule settled_bind >> simp[readable_def, wf_wait, settled_wait]
  >> irule settled_bind >> simp[wf_emit, settled_emit] >> rw[]
  >> rpt CASE_TAC >> simp[settled_return]
QED

(* MAIN: the existing handler is the identity-vocabulary, query-free case *)
Theorem proto_handler_idV:
  proto_handler P resp = proto_handler_v idV P (K NONE) (λr k. resp r)
Proof
  simp[proto_handler_v_def] >> ONCE_REWRITE_TAC[EQ_SYM_EQ] >>
  irule proto_handler_fix >>
  rpt gen_tac >> PairCases_on ‘p’ >>
  simp[proto_body_def, proto_body_v_def, idV_def] >>
  CASE_TAC >> simp[] >>
  AP_TERM_TAC >> simp[FUN_EQ_THM] >> rw[] >>
  AP_TERM_TAC >> simp[FUN_EQ_THM] >> Cases >> simp[]
QED
