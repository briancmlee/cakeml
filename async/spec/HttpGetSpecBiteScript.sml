(*
  HttpGetSpec bites: the statement rules out plausible bugs, and its
  assumptions are satisfiable.  Everything here is proved.

  A one-file site  files = [("/a", "hi")]  and two requests
  r1 = GET /a (served) and r2 = GET /b (not found).
  - Broken servers: answering in the wrong order, answering 200 for a
    missing file, a wrong Content-Length, answering a request that has not
    fully arrived, and never answering, each violate the spec.
  - Non-vacuity: a fair world in which one client sends r1 exists, and the
    ideal trace (read r1, write its response) is safe and live.
*)
Theory HttpGetSpecBite
Ancestors
  HttpGetSpec EchoSpec EchoSpecBite socketWorld socketFair llist
  alist Marshalling ASCIInumbers
Libs
  preamble

Overload site = “[("/a", "hi")] : (string # string) list”
Overload r1 = “Get "/a"”
Overload r2 = “Get "/b"”

Theorem requests_NIL[local]:
  requests rs = [] ⇔ rs = []
Proof
  Cases_on ‘rs’ >> simp[requests_def, bytes_def] >>
  Cases_on ‘h’ >> simp[print_request_def]
QED

(* Nothing is a complete request in the empty rest *)
Theorem no_full_request_NIL[local]:
  no_full_request []
Proof
  rw[no_full_request_def, requests_NIL]
QED

(* ------------------------------------------------------------------------
   Broken servers violate safety
   ------------------------------------------------------------------------ *)

Theorem broken_wrong_order:
  starts_with [rd c1 (requests [r1; r2]) 100;
               wr c1 (responses site [r2; r1])] io ⇒
  ¬http_get_safe site io
Proof
  rw[http_get_safe_def] >>
  qexistsl [‘[rd c1 (requests [r1; r2]) 100; wr c1 (responses site [r2; r1])]’,
            ‘c1’, ‘[r1; r2]’, ‘[]’] >>
  simp[no_full_request_NIL] >> EVAL_TAC
QED

Theorem broken_200_for_missing_file:
  starts_with [rd c1 (requests [r2]) 100;
               wr c1 (bytes (print_response (Ok "")))] io ⇒
  ¬http_get_safe site io
Proof
  rw[http_get_safe_def] >>
  qexistsl [‘[rd c1 (requests [r2]) 100; wr c1 (bytes (print_response (Ok "")))]’,
            ‘c1’, ‘[r2]’, ‘[]’] >>
  simp[no_full_request_NIL] >> EVAL_TAC
QED

Theorem broken_wrong_content_length:
  starts_with [rd c1 (requests [r1]) 100;
               wr c1 (bytes "HTTP/1.0 200 OK\r\nContent-Length: 3\r\n\r\nhi")] io ⇒
  ¬http_get_safe site io
Proof
  rw[http_get_safe_def] >>
  qexistsl [‘[rd c1 (requests [r1]) 100;
              wr c1 (bytes "HTTP/1.0 200 OK\r\nContent-Length: 3\r\n\r\nhi")]’,
            ‘c1’, ‘[r1]’, ‘[]’] >>
  simp[no_full_request_NIL] >> EVAL_TAC
QED

(* A request missing its final blank line is not complete yet *)
Overload partial = “bytes "GET /a HTTP/1.0\r\n"”

Theorem no_full_request_partial[local]:
  no_full_request partial
Proof
  rw[no_full_request_def] >> strip_tac >>
  imp_res_tac IS_PREFIX_LENGTH >> Cases_on ‘r’ >>
  fs[requests_def, bytes_def, print_request_def, valid_request_def,
     valid_path_def] >>
  Cases_on ‘s’ >> fs[]
QED

Theorem broken_answers_partial_request:
  starts_with [rd c1 partial 100; wr c1 (responses site [r1])] io ⇒
  ¬http_get_safe site io
Proof
  rw[http_get_safe_def] >>
  qexistsl [‘[rd c1 partial 100; wr c1 (responses site [r1])]’,
            ‘c1’, ‘[]’, ‘partial’] >>
  simp[no_full_request_partial] >> EVAL_TAC
QED

(* ------------------------------------------------------------------------
   A fair world with one client sending bs on connection 4
   ------------------------------------------------------------------------ *)

Definition one_client_def:
  one_client bs =
    <| listeners := [(3w, [])]; conns := [];
       sched := [|[Connect 3w 4w; Data 4w bs]|] |>
End

Theorem ticks_quiet[local]:
  s.sched = [||] ⇒ ticks n s = s
Proof
  qid_spec_tac ‘s’ >> Induct_on ‘n’ >> rw[ticks_def] >>
  ‘tick s = s’ by simp[tick_def] >> simp[]
QED

Theorem one_client_sched_wf:
  sched_wf (one_client bs)
Proof
  rw [sched_wf_def] \\ Cases_on ‘n’
  >- simp [ticks_def, next_step_def, one_client_def, step_ok_def,
           arrival_ok_def, deliver1_def, is_listener_def, is_conn_def,
           AFUPDKEY_def, empty_conn_def]
  \\ ‘(tick (one_client bs)).sched = [||]’
    by simp [tick_def, one_client_def, deliver_sched]
  \\ simp [ticks_def, ticks_quiet, next_step_def, step_ok_def]
QED

Theorem server_world_one_client:
  server_world 3w (one_client bs)
Proof
  simp[server_world_def, one_client_sched_wf] >> simp[one_client_def]
QED

Theorem sent_upto_one_client[local]:
  sent_upto c n (one_client bs) = if n = 0 ∨ c ≠ 4w then [] else bs
Proof
  Cases_on ‘n’ >> simp[sent_upto_def, arrivals_upto_def, one_client_def] >>
  Cases_on ‘n'’ >> simp[arrivals_upto_def] >> rw[]
QED

(* ------------------------------------------------------------------------
   A server that never answers violates liveness
   ------------------------------------------------------------------------ *)

Theorem broken_never_answers:
  (∀evs. starts_with evs io ⇒ bytes_written_to 4w evs = []) ⇒
  ¬http_get_live site (one_client (requests [r1])) io
Proof
  rw[http_get_live_def] >> qexistsl [‘4w’, ‘1’, ‘[r1]’] >>
  simp[sent_upto_one_client] >> conj_tac >- EVAL_TAC >>
  rw[] >> Cases_on ‘LPREFIX (fromList evs) io’ >> simp[] >> res_tac >>
  simp[] >> EVAL_TAC
QED

(* ------------------------------------------------------------------------
   Non-vacuity: the ideal trace for one client sending r1 is safe and live
   ------------------------------------------------------------------------ *)

(* Requests can be read back uniquely: a valid request that is a prefix of
   another valid request followed by anything is that request. *)
Theorem bytes_char_11[local]:
  (n2w (ORD c) : word8) = n2w (ORD d) ⇔ c = d
Proof
  ‘ORD c < 256 ∧ ORD d < 256’ by simp[ORD_BOUND] >>
  simp[wordsTheory.n2w_11, ORD_11]
QED

Theorem ord_space[local]:
  ORD c MOD 256 = 32 ⇔ c = #" "
Proof
  ‘ORD c < 256’ by simp[ORD_BOUND] >> simp[] >> eq_tac >> rw[] >>
  ‘CHR (ORD c) = CHR 32’ by simp[] >> fs[CHR_ORD]
QED

Theorem path_prefix_unique[local]:
  ∀p q t1 t2 x.
    EVERY (λc. c ≠ #" ") p ∧ EVERY (λc. c ≠ #" ") q ∧
    bytes p ++ 32w :: t1 ≼ bytes q ++ 32w :: t2 ++ x ⇒ p = q
Proof
  ‘(32w : word8) = n2w (ORD #" ")’ by EVAL_TAC >>
  pop_assum SUBST1_TAC >>
  Induct >> Cases_on ‘q’ >> rw[bytes_def] >> gvs[bytes_char_11] >>
  fs[GSYM bytes_def] >>
  rpt (qpat_x_assum ‘ORD _ MOD 256 = ORD _ MOD 256’ mp_tac) >>
  simp[ORD_BOUND, ORD_11] >> rw[] >>
  TRY (first_x_assum (qspecl_then [‘t’, ‘t1’, ‘t2’, ‘x’] mp_tac) >> simp[] >> NO_TAC) >>
  gvs[ord_space]
QED

Theorem prefix_cancel[local]:
  ∀l a b. l ++ a ≼ l ++ b ⇔ a ≼ b
Proof
  Induct >> simp[]
QED

Theorem bytes_request[local]:
  bytes (print_request (Get p)) =
    bytes "GET " ++ bytes p ++ 32w :: bytes "HTTP/1.0\r\n\r\n"
Proof
  simp[print_request_def, bytes_def] >> EVAL_TAC
QED

Theorem request_prefix_unique[local]:
  valid_request r ∧ valid_request r' ∧
  bytes (print_request r) ≼ bytes (print_request r') ++ x ⇒ r = r'
Proof
  Cases_on ‘r’ >> Cases_on ‘r'’ >>
  rw[valid_request_def, valid_path_def, bytes_request] >>
  RULE_ASSUM_TAC (REWRITE_RULE [GSYM APPEND_ASSOC, prefix_cancel]) >>
  irule path_prefix_unique >> fs[EVERY_MEM] >> metis_tac[]
QED

Theorem requests_CONS[local]:
  requests [] = [] ∧
  requests (r :: rs) = bytes (print_request r) ++ requests rs
Proof
  simp[requests_def, bytes_def]
QED

Theorem LPREFIX_fromList_fromList[local]:
  LPREFIX (fromList xs) (fromList ys) ⇔ xs ≼ ys
Proof
  simp[LPREFIX_fromList, from_toList]
QED

Theorem prefix_two[local]:
  evs ≼ [x; y] ⇔ evs = [] ∨ evs = [x] ∨ evs = [x; y]
Proof
  Cases_on ‘evs’ >> simp[] >> Cases_on ‘t’ >> simp[] >>
  Cases_on ‘t'’ >> simp[]
QED

Overload ideal_http =
  “[rd c1 (requests [r1]) 100; wr c1 (responses site [r1])]”

(* The only valid request list whose bytes are a prefix of requests [r1]
   followed by something without a full request is [r1] (or []) *)
Theorem requests_of_r1[local]:
  EVERY valid_request rs ∧ requests rs ++ rest = requests [r1] ⇒
  rs = [] ∨ (rs = [r1] ∧ rest = [])
Proof
  Cases_on ‘rs’ >> rw[] >> fs[requests_CONS] >>
  ‘h = r1’
    by (irule request_prefix_unique >> simp[] >>
        conj_tac >- EVAL_TAC >>
        qexists_tac ‘[]’ >> simp[] >>
        qpat_x_assum ‘_ = _’ (SUBST1_TAC o SYM) >>
        simp[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]) >>
  gvs[] >> fs[APPEND_EQ_SELF, requests_NIL]
QED

(* What each event of the ideal trace contributes, per connection *)
Theorem ideal_events[local]:
  event_read c (rd c1 (requests [r1]) 100) =
    (if c = c1 then requests [r1] else []) ∧
  event_written c (rd c1 (requests [r1]) 100) = [] ∧
  event_read c (wr c1 (responses site [r1])) = [] ∧
  event_written c (wr c1 (responses site [r1])) =
    (if c = c1 then responses site [r1] else [])
Proof
  rw[] >> EVAL_TAC >> rw[] >> fs[]
QED

Theorem ideal_http_safe:
  http_get_safe site (fromList ideal_http)
Proof
  rw[http_get_safe_def, LPREFIX_fromList_fromList, prefix_two] >>
  gvs[bytes_read_from_def, bytes_written_to_def, ideal_events] >>
  Cases_on ‘c = c1’ >> gvs[] >>
  TRY (gvs[requests_NIL, APPEND_eq_NIL, responses_def] >> NO_TAC) >>
  ‘requests rs ++ rest = requests [r1]’ by simp[] >>
  drule_all requests_of_r1 >> rw[] >> gvs[] >>
  fs[no_full_request_def] >>
  first_x_assum (qspec_then ‘r1’ mp_tac) >> fs[requests_CONS] >>
  rw[] >> pop_assum mp_tac >> EVAL_TAC
QED

Theorem ideal_http_live:
  http_get_live site (one_client (requests [r1])) (fromList ideal_http)
Proof
  rw[http_get_live_def, sent_upto_one_client] >>
  Cases_on ‘c = 4w ∧ n ≠ 0’ >> gvs[]
  >- (fs[IS_PREFIX_APPEND] >> drule_all requests_of_r1 >> rw[]
      >- (qexists_tac ‘[]’ >> simp[responses_def, bytes_def, bytes_written_to_def])
      >- (qexists_tac ‘ideal_http’ >>
          simp[LPREFIX_fromList_fromList, bytes_written_to_def, ideal_events])) >>
  gvs[requests_NIL] >> qexists_tac ‘[]’ >>
  simp[responses_def, bytes_def, bytes_written_to_def]
QED

(* MAIN (non-vacuity): the ideal trace, in the fair world where one client
   sends r1, is both safe and live *)
Theorem ideal_http_trace_safe_and_live:
  http_get_safe site (fromList ideal_http) ∧
  http_get_live site (one_client (requests [r1])) (fromList ideal_http)
Proof
  simp[ideal_http_safe, ideal_http_live]
QED
