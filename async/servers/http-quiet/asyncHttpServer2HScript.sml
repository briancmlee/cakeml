(*
  The header-tolerant HTTP server at Level 2: no busy-waiting.

  As asyncServer2 does for echo: the server declares what it waits for (the
  listener, and each connection whose buffer holds no complete request
  becoming readable), it erases to the Level 1 server (asyncHttpServerH),
  and it is quiet.  So M2's no-busy-waiting theorem applies: a scheduler
  may block until the listener or a connection is readable, with exactly
  the behaviour of one that polls every round.

  The accept/fork skeleton is lifted once, for any Level 2 handler
  (server_with2, erasing to server_with).  The HTTP handler's new case, a
  complete request already buffered, answers with emit2, which declares
  no interest; so the handler only waits when it needs more input.
*)
Theory asyncHttpServer2H
Ancestors
  pair list rich_list arithmetic option pred_set string
  asyncCore asyncLevel1 asyncLoop asyncLevel2 asyncLoop2 asyncSched asyncSched2
  asyncServer asyncServer2 asyncServerWith HttpSpec HttpSpecHeaders
  asyncHttpParseH asyncHttpServerH
Libs
  BasicProvers

(* ------------------------------------------------------------------------
   The generic skeleton at Level 2
   ------------------------------------------------------------------------ *)

Definition server_with_body2_def:
  server_with_body2 h2 R lfd =
    bind2 (wait_on (Readable lfd) (λs. SOME ())) (λu.
    bind2 (emit2 (Accept lfd)) (λres.
      case res of
        Accepted fd => map2 (λp. ()) (both2 (h2 fd) (R lfd))
      | _ => R lfd))
End

Theorem server_with_body2_contractive:
  contractive2 (server_with_body2 h2)
Proof
  rw[contractive2_def, server_with_body2_def]
  >> ho_match_mp_tac guarded2_bind2
  >> simp[wait_on_def, wait_needs_snapshot]
  >> rpt gen_tac >> ho_match_mp_tac nonexpansive2_bind2 >> simp[nonexpansive2_const]
  >> Cases >> simp[nonexpansive2_call]
  >> ho_match_mp_tac nonexpansive2_map2 >> ho_match_mp_tac nonexpansive2_both2
  >> simp[nonexpansive2_const, nonexpansive2_call]
QED

Definition server_with2_def:
  server_with2 h2 = fix2 (server_with_body2 h2)
End

Theorem erase_server_with_body2:
  (∀fd. erase (h2 fd) = h fd) ⇒
  erase (server_with_body2 h2 R lfd) = server_with_body h (λq. erase (R q)) lfd
Proof
  strip_tac
  >> simp[server_with_body2_def, server_with_body_def, erase_bind2, erase_wait_on,
          erase_emit2, readable_def]
  >> AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> ABS_TAC
  >> Cases_on ‘res’ >> simp[erase_map2, erase_both2]
QED

(* The Level 2 skeleton erases to the Level 1 skeleton *)
Theorem erase_server_with2:
  (∀fd. erase (h2 fd) = h fd) ⇒ erase (server_with2 h2 lfd) = server_with h lfd
Proof
  strip_tac >> simp[server_with2_def, server_with_def]
  >> qspecl_then [‘server_with_body h’, ‘server_with_body2 h2’] mp_tac
       (Q.GENL [‘body1’, ‘body2’] erase_fix2)
  >> simp[server_with_body_contractive, server_with_body2_contractive,
          erase_server_with_body2]
QED

Theorem wf2_server_with2:
  (∀fd. wf2 (h2 fd)) ⇒ wf2 (server_with2 h2 lfd)
Proof
  strip_tac >> simp[server_with2_def] >> irule wf2_fix2
  >> simp[server_with_body2_contractive]
  >> rw[server_with_body2_def]
  >> irule wf2_bind2 >> simp[wf2_wait_on]
  >> irule wf2_bind2 >> simp[wf2_emit2] >> Cases >> simp[]
  >> irule wf2_map2 >> irule wf2_both2 >> simp[]
QED

(* ------------------------------------------------------------------------
   The HTTP handler at Level 2
   ------------------------------------------------------------------------ *)

Definition http_body2_h_def:
  http_body2_h files R p =
    case p of
      (fd, buf) =>
        case parse_hrequest buf of
          HComplete req rest =>
            bind2 (emit2 (Write fd (print_response (handle files (hpath req)))))
                  (λw. R (fd, rest))
        | HIncomplete =>
            bind2 (wait_on (Readable fd) (λs. SOME ())) (λu.
            bind2 (emit2 (Read fd)) (λres.
              case res of
                Data d => R (fd, buf ++ d)
              | Eof => return2 ()
              | _ => R (fd, buf)))
        | HInvalid => return2 ()
End

Theorem http_body2_h_contractive:
  contractive2 (http_body2_h files)
Proof
  rw[contractive2_def] >> PairCases_on ‘p’ >> simp[http_body2_h_def]
  >> Cases_on ‘parse_hrequest p1’ >> simp[]
  >- (ho_match_mp_tac guarded2_bind2
      >> simp[emit2_def, emit_needs_snapshot, nonexpansive2_call])
  >- (ho_match_mp_tac guarded2_bind2
      >> simp[wait_on_def, wait_needs_snapshot]
      >> rpt gen_tac >> ho_match_mp_tac nonexpansive2_bind2 >> simp[nonexpansive2_const]
      >> Cases >> simp[nonexpansive2_call, nonexpansive2_const])
  >> simp[guarded2_def, guarded_const]
QED

Definition http_handler2_h_def:
  http_handler2_h files = fix2 (http_body2_h files)
End

Theorem erase_http_body2_h:
  erase (http_body2_h files R p) = http_body_h files (λq. erase (R q)) p
Proof
  PairCases_on ‘p’ >> simp[http_body2_h_def, http_body_h_def]
  >> Cases_on ‘parse_hrequest p1’
  >> simp[erase_bind2, erase_emit2, erase_return2, erase_wait_on, readable_def]
  >> AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> ABS_TAC
  >> Cases_on ‘res’ >> simp[erase_return2]
QED

Theorem erase_http_handler2_h:
  erase (http_handler2_h files p) = http_handler_h files p
Proof
  simp[http_handler2_h_def, http_handler_h_def]
  >> qspecl_then [‘http_body_h files’, ‘http_body2_h files’] mp_tac
       (Q.GENL [‘body1’, ‘body2’] erase_fix2)
  >> simp[http_body_h_contractive, http_body2_h_contractive, erase_http_body2_h]
QED

Theorem wf2_http_handler2_h:
  wf2 (http_handler2_h files p)
Proof
  simp[http_handler2_h_def] >> irule wf2_fix2 >> simp[http_body2_h_contractive]
  >> rw[] >> PairCases_on ‘p’ >> simp[http_body2_h_def] >> CASE_TAC
  >> simp[wf2_return2]
  >- (irule wf2_bind2 >> simp[wf2_emit2])
  >> irule wf2_bind2 >> simp[wf2_wait_on]
  >> irule wf2_bind2 >> simp[wf2_emit2] >> Cases >> simp[wf2_return2]
QED

(* ------------------------------------------------------------------------
   The HTTP server at Level 2
   ------------------------------------------------------------------------ *)

Definition http_server2_h_def:
  http_server2_h files lfd = server_with2 (λfd. http_handler2_h files (fd, "")) lfd
End

(* MAIN: the Level 2 HTTP server erases to the Level 1 server, so the
   safety theorem (http_server_safety_h) holds for it *)
Theorem erase_http_server2_h:
  erase (http_server2_h files lfd) = http_server_h files lfd
Proof
  simp[http_server2_h_def, http_server_h_def]
  >> irule erase_server_with2 >> simp[erase_http_handler2_h]
QED

(* MAIN: the Level 2 HTTP server is well-formed and quiet: it waits only
   for the listener, and for connections that need more input *)
Theorem wf2_http_server2_h:
  wf2 (http_server2_h files lfd)
Proof
  simp[http_server2_h_def] >> irule wf2_server_with2 >> simp[wf2_http_handler2_h]
QED

(* MAIN: no busy-waiting for the HTTP server: a scheduler running it that
   blocks through every idle round (no request in flight, no responses, and
   neither the listener nor any connection it waits on readable) emits
   exactly the same actions, and gets exactly the same result, as one that
   polls every round *)
Theorem http_server_no_busy_waiting:
  ∀H. let K = blocked (sched_idle [http_server2_h files lfd]) [] H in
      sched_log [http_server_h files lfd] K = sched_log [http_server_h files lfd] H ∧
      ∀xs. LIST_REL (λt x. (t.comp t.view).result = SOME x)
                    (run [http_server_h files lfd] K) xs ⇔
           LIST_REL (λt x. (t.comp t.view).result = SOME x)
                    (run [http_server_h files lfd] H) xs
Proof
  qspec_then ‘[http_server2_h files lfd]’ mp_tac (Q.GEN ‘cs’ no_busy_waiting)
  >> simp[wf2_http_server2_h, erase_http_server2_h]
QED
