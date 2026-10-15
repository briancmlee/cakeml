(*
  Option C (design/33 §2.2): the generic protocol server at Level 2.

  The server skeleton over a vocabulary (asyncServerV's server_v) and the
  generic protocol handler with optional queries (asyncProtoV's
  proto_handler_v), written with the Level 2 combinators, so that each
  declares what it waits for:
  - the skeleton: the listener (wait_on (Readable lfd)), and whatever its
    running handlers declare (both2);
  - the handler: Readable fd while it needs more input; nothing while a
    Write or a query is outstanding (emit2), or once it has finished.

  Each erases to its Level 1 original (erase_server_v2,
  erase_proto_handler_v2, erase_proto_server_v2), so the generic safety and
  liveness proved for proto_handler_v / server_v hold unchanged; and each
  is wf2, hence quiet: the select loop may block on the declared interest.
  HTTP is the instance idV / K NONE (proto_handler_idV); KV is a
  vocabulary with queries.
*)
Theory asyncProtoV2
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncLoop asyncLevel2 asyncLoop2 asyncServer asyncServer2
  asyncServerWith asyncServerV asyncProto asyncProtoServer asyncProtoV
Libs
  BasicProvers

(* ------------------------------------------------------------------------
   The server skeleton over a vocabulary, at Level 2
   ------------------------------------------------------------------------ *)

Definition server_v_body2_def:
  server_v_body2 V h2 R lfd =
    bind2 (wait_on (Readable lfd) (λs. SOME ())) (λu.
    bind2 (emit2 (V.acc lfd)) (λres.
      case vaccd V res of
        SOME fd => map2 (λp. ()) (both2 (h2 fd) (R lfd))
      | NONE => R lfd))
End

Theorem server_v_body2_contractive:
  contractive2 (server_v_body2 V h2)
Proof
  rw[contractive2_def, server_v_body2_def]
  >> ho_match_mp_tac guarded2_bind2
  >> simp[wait_on_def, wait_needs_snapshot]
  >> rpt gen_tac >> ho_match_mp_tac nonexpansive2_bind2 >> simp[nonexpansive2_const]
  >> gen_tac >> CASE_TAC >> simp[nonexpansive2_call]
  >> ho_match_mp_tac nonexpansive2_map2 >> ho_match_mp_tac nonexpansive2_both2
  >> simp[nonexpansive2_const, nonexpansive2_call]
QED

Definition server_v2_def:
  server_v2 V h2 = fix2 (server_v_body2 V h2)
End

(* The skeleton satisfies its recursive equation *)
Theorem server_v2_unfold:
  server_v2 V h2 lfd = server_v_body2 V h2 (server_v2 V h2) lfd
Proof
  simp[server_v2_def, Once (MATCH_MP fix2_unfold server_v_body2_contractive)]
QED

Theorem erase_server_v_body2:
  (∀fd. erase (h2 fd) = h fd) ⇒
  erase (server_v_body2 V h2 R lfd) = server_v_body V h (λq. erase (R q)) lfd
Proof
  strip_tac
  >> simp[server_v_body2_def, server_v_body_def, erase_bind2, erase_wait_on,
          erase_emit2, readable_def]
  >> AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> ABS_TAC
  >> CASE_TAC >> simp[erase_map2, erase_both2]
QED

(* MAIN: the Level 2 skeleton erases to the Level 1 skeleton *)
Theorem erase_server_v2:
  (∀fd. erase (h2 fd) = h fd) ⇒ erase (server_v2 V h2 lfd) = server_v V h lfd
Proof
  strip_tac >> simp[server_v2_def, server_v_def]
  >> qspecl_then [‘server_v_body V h’, ‘server_v_body2 V h2’] mp_tac
       (Q.GENL [‘body1’, ‘body2’] erase_fix2)
  >> simp[server_v_body_contractive, server_v_body2_contractive,
          erase_server_v_body2]
QED

(* MAIN: the skeleton is wf2 (hence quiet) if its handlers are *)
Theorem wf2_server_v2:
  (∀fd. wf2 (h2 fd)) ⇒ wf2 (server_v2 V h2 lfd)
Proof
  strip_tac >> simp[server_v2_def] >> irule wf2_fix2
  >> simp[server_v_body2_contractive]
  >> rw[server_v_body2_def]
  >> irule wf2_bind2 >> simp[wf2_wait_on]
  >> irule wf2_bind2 >> simp[wf2_emit2] >> gen_tac >> CASE_TAC >> simp[]
  >> irule wf2_map2 >> irule wf2_both2 >> simp[]
QED

(* ------------------------------------------------------------------------
   The protocol handler at Level 2
   ------------------------------------------------------------------------ *)

Definition proto_body_v2_def:
  proto_body_v2 V P ansq fin R p =
    case p of
      (fd, buf) =>
        case P.parse buf of
          PComplete req rest =>
            (case ansq req of
               NONE =>
                 bind2 (emit2 (V.wr fd (fin req NONE))) (λw. R (fd, rest))
             | SOME q =>
                 bind2 (emit2 (V.qry q)) (λa.
                 bind2 (emit2 (V.wr fd (fin req (V.kans a)))) (λw. R (fd, rest))))
        | PIncomplete =>
            bind2 (wait_on (Readable fd) (λs. SOME ())) (λu.
            bind2 (emit2 (V.rd fd)) (λres.
              case V.sres res of
                SOME (Data d) => R (fd, buf ++ d)
              | SOME Eof => return2 ()
              | _ => R (fd, buf)))
        | PInvalid => return2 ()
End

Theorem proto_body_v2_contractive:
  contractive2 (proto_body_v2 V P ansq fin)
Proof
  rw[contractive2_def] >> PairCases_on ‘p’ >> simp[proto_body_v2_def]
  >> Cases_on ‘P.parse p1’ >> simp[]
  >- (CASE_TAC
      >- (ho_match_mp_tac guarded2_bind2
          >> simp[emit2_def, emit_needs_snapshot, nonexpansive2_call])
      >> ho_match_mp_tac guarded2_bind2
      >> simp[emit2_def, emit_needs_snapshot]
      >> rpt gen_tac >> ho_match_mp_tac nonexpansive2_bind2
      >> simp[nonexpansive2_const, nonexpansive2_call])
  >- (ho_match_mp_tac guarded2_bind2
      >> simp[wait_on_def, wait_needs_snapshot]
      >> rpt gen_tac >> ho_match_mp_tac nonexpansive2_bind2 >> simp[nonexpansive2_const]
      >> gen_tac >> rpt CASE_TAC >> simp[nonexpansive2_call, nonexpansive2_const])
  >> simp[guarded2_def, guarded_const]
QED

Definition proto_handler_v2_def:
  proto_handler_v2 V P ansq fin = fix2 (proto_body_v2 V P ansq fin)
End

(* MAIN: the Level 2 handler satisfies its recursive equation *)
Theorem proto_handler_v2_unfold:
  proto_handler_v2 V P ansq fin p =
    proto_body_v2 V P ansq fin (proto_handler_v2 V P ansq fin) p
Proof
  simp[proto_handler_v2_def,
       Once (MATCH_MP fix2_unfold proto_body_v2_contractive)]
QED

Theorem erase_proto_body_v2:
  erase (proto_body_v2 V P ansq fin R p) =
  proto_body_v V P ansq fin (λq. erase (R q)) p
Proof
  PairCases_on ‘p’ >> simp[proto_body_v2_def, proto_body_v_def]
  >> Cases_on ‘P.parse p1’
  >> simp[erase_bind2, erase_emit2, erase_return2, erase_wait_on, readable_def]
  >- (CASE_TAC >> simp[erase_bind2, erase_emit2])
  >> AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> ABS_TAC
  >> rpt CASE_TAC >> simp[erase_return2]
QED

(* MAIN: the Level 2 handler erases to the Level 1 handler *)
Theorem erase_proto_handler_v2:
  erase (proto_handler_v2 V P ansq fin p) = proto_handler_v V P ansq fin p
Proof
  simp[proto_handler_v2_def, proto_handler_v_def]
  >> qspecl_then [‘proto_body_v V P ansq fin’, ‘proto_body_v2 V P ansq fin’]
       mp_tac (Q.GENL [‘body1’, ‘body2’] erase_fix2)
  >> simp[proto_body_v_contractive, proto_body_v2_contractive, erase_proto_body_v2]
QED

(* MAIN: the Level 2 handler is wf2, hence quiet *)
Theorem wf2_proto_handler_v2:
  wf2 (proto_handler_v2 V P ansq fin p)
Proof
  simp[proto_handler_v2_def] >> irule wf2_fix2 >> simp[proto_body_v2_contractive]
  >> rw[] >> PairCases_on ‘p’ >> simp[proto_body_v2_def] >> CASE_TAC
  >> simp[wf2_return2]
  >- (CASE_TAC >> irule wf2_bind2 >> simp[wf2_emit2] >> rw[] >>
      irule wf2_bind2 >> simp[wf2_emit2])
  >> irule wf2_bind2 >> simp[wf2_wait_on]
  >> irule wf2_bind2 >> simp[wf2_emit2] >> rw[] >> rpt CASE_TAC >> simp[wf2_return2]
QED

(* ------------------------------------------------------------------------
   The protocol server at Level 2
   ------------------------------------------------------------------------ *)

Definition proto_server_v2_def:
  proto_server_v2 V P ansq fin lfd =
    server_v2 V (λfd. proto_handler_v2 V P ansq fin (fd, "")) lfd
End

(* MAIN: the Level 2 protocol server erases to the Level 1 one *)
Theorem erase_proto_server_v2:
  erase (proto_server_v2 V P ansq fin lfd) =
  server_v V (λfd. proto_handler_v V P ansq fin (fd, "")) lfd
Proof
  simp[proto_server_v2_def] >> irule erase_server_v2 >>
  simp[erase_proto_handler_v2]
QED

Theorem wf2_proto_server_v2:
  wf2 (proto_server_v2 V P ansq fin lfd)
Proof
  simp[proto_server_v2_def] >> irule wf2_server_v2 >> simp[wf2_proto_handler_v2]
QED

(* MAIN: the HTTP instance: the identity vocabulary, no queries, erases
   to cf-actions' proto_server *)
Theorem erase_proto_server_idV2:
  erase (proto_server_v2 idV P (K NONE) (λr k. resp r) lfd) = proto_server P resp lfd
Proof
  simp[erase_proto_server_v2, proto_server_def, GSYM proto_handler_idV] >>
  simp[GSYM server_with_eq_v]
QED
